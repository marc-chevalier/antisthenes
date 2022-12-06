open Plato.Pathlib

module CharSet = Set.Make(Char)
module CharMap = Map.Make(Char)
module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)

type dictionary = {
  all: string list;
  words: string list IntMap.t CharMap.t;
}

let dictionary : dictionary =
  let all =
    Path.of_string "/usr/share/dict/french"
    |> Path.read
    |> String.split_on_char '\n'
    |> List.rev_map (fun word ->
        word
        |> Ubase.from_utf8
        |> String.lowercase_ascii
      )
    |> List.filter (Re.execp (Re.Perl.compile_pat "^[a-z]*$"))
  in
  let words =
    List.fold_left
      (fun acc word ->
         match word with
         | "" -> acc
         | _ ->
           let first_char = word.[0] in
           let length = String.length word in
           let int_map = CharMap.find_opt first_char acc |> Option.value ~default:IntMap.empty in
           let int_map =
             IntMap.update
               length
               (function
                 | None -> Some [word]
                 | Some l -> Some (word::l)
               )
               int_map
           in
           CharMap.add first_char int_map acc
      )
      CharMap.empty
      all
  in
  {all; words}

type truth =
  | Correct
  | Misplaced
  | Nope
let pp_truth (fmt: Format.formatter) (t: truth) : unit =
  Format.pp_print_string fmt (match t with | Correct -> "_" | Misplaced -> "*" | Nope -> ".")
let pp_truths (fmt: Format.formatter) (l: truth list) : unit =
  Ocolor_format.pp_list_generic ~left:"" ~sep:"" ~right:"" pp_truth fmt l
let pp_truths_and_word (fmt: Format.formatter) (l: (char * truth) list) : unit =
  Format.fprintf fmt "%a"
    (Ocolor_format.pp_list_generic
       ~left:"" ~sep:"" ~right:""
       (fun fmt (c, t) ->
          match t with
          | Correct -> Format.fprintf fmt "@{<white;bg_red>%c@}" c
          | Misplaced -> Format.fprintf fmt "@{<black;bg_yellow>%c@}" c
          | Nope -> Format.fprintf fmt "%c" c
       )
    )
    l

let truth_of_guess (reference: string) (guess: string) : (char * truth) list =
  let reference = reference |> String.to_seq |> List.of_seq in
  let guess = guess |> String.to_seq |> List.of_seq in
  let corrects =
    List.fold_left2
      (fun acc r g ->
         if Char.equal r g then
           Some Correct :: acc
         else
           None :: acc
      )
      []
      reference
      guess
    |> List.rev
  in
  let count_of_incorrect_letter =
    List.fold_left2
      (fun acc c r ->
         match c with
         | None -> CharMap.update r (function None -> Some 1 | Some n -> Some (n+1)) acc
         | Some _ -> acc
      )
      CharMap.empty
      corrects
      reference
  in
  let truth =
    let truth, _count =
      List.fold_left2
        (fun (acc, count) c g ->
           match c with
           | Some _ -> (g, Correct)::acc, count
           | None ->
             let expected_number = CharMap.find_opt g count_of_incorrect_letter |> Option.value ~default:0 in
             let current_number = CharMap.find_opt g count |> Option.value ~default:0 in
             if current_number < expected_number then
               (g, Misplaced)::acc, CharMap.add g (current_number + 1) count
             else
               (g, Nope)::acc, count
        )
        ([], CharMap.empty)
        corrects
        guess
    in
    List.rev truth
  in
  truth

type quantity =
  | Exactly of int
  | AtLeast of int
let pp_quantity (fmt: Format.formatter) (q: quantity) : unit =
  match q with
  | Exactly n -> Format.fprintf fmt "= %d" n
  | AtLeast n -> Format.fprintf fmt ">= %d" n

type known_facts = {
  known_positions: char option list;
  known_letters: (quantity * IntSet.t) CharMap.t;
}
let pp_known_facts (fmt: Format.formatter) (kf: known_facts) : unit =
  Format.fprintf fmt "%a|%a"
    (Ocolor_format.pp_list_generic ~left:"" ~sep:"" ~right:""
       (fun fmt o ->
          match o with
          | None -> Format.pp_print_string fmt "."
          | Some w -> Format.pp_print_char fmt w
       )
    ) kf.known_positions
    (Ocolor_format.pp_iterable_mapping CharMap.iter Format.pp_print_char (Ocolor_format.pp_pair pp_quantity (Ocolor_format.pp_iterable IntSet.iter Format.pp_print_int)))
    kf.known_letters
let initial_fact_from_string (reference: string) = {
  known_positions = List.init (String.length reference) (function 0 -> Some reference.[0] | _ -> None);
  known_letters = CharMap.empty;
}
let initial_fact_from_first_and_length (first:char) (length: int) = {
  known_positions = List.init length (function 0 -> Some first | _ -> None);
  known_letters = CharMap.empty;
}

let merge_known_facts (lhs: known_facts) (rhs: known_facts) : known_facts =
  let known_positions =
    List.fold_left2
      (fun acc l r ->
         match l with
         | Some letter -> Some letter :: acc
         | _ ->
           match r with
           | Some c -> Some c :: acc
           | None -> None :: acc
      )
      []
      lhs.known_positions
      rhs.known_positions
    |> List.rev
  in
  let known_letters =
    let all_letters =
      CharSet.union
        (CharMap.to_seq lhs.known_letters |> Seq.map fst |> CharSet.of_seq)
        (CharMap.to_seq rhs.known_letters |> Seq.map fst |> CharSet.of_seq)
    in
    CharSet.fold
      (fun letter acc ->
         let l_known_pos = List.find_all (Option.equal Char.equal (Some letter)) lhs.known_positions |> List.length in
         let l_known_letter = CharMap.find_opt letter lhs.known_letters |> Option.map fst |> Option.value ~default:(AtLeast 0) in
         let r_known_pos = List.find_all (Option.equal Char.equal (Some letter)) rhs.known_positions |> List.length in
         let r_known_letter = CharMap.find_opt letter rhs.known_letters |> Option.map fst |> Option.value ~default:(AtLeast 0) in
         let known_pos = List.find_all (Option.equal Char.equal (Some letter)) known_positions |> List.length in
         let quantity =
           match l_known_letter, r_known_letter with
           | Exactly n, _ -> Exactly (n + l_known_pos - known_pos)
           | _, Exactly n -> Exactly (n + r_known_pos - known_pos)
           | AtLeast m, AtLeast n -> AtLeast (max (l_known_pos + m) (r_known_pos + n) - known_pos)
         in
         let l_forbidden_cols = CharMap.find_opt letter lhs.known_letters |> Option.map snd |> Option.value ~default:IntSet.empty in
         let r_forbidden_cols = CharMap.find_opt letter rhs.known_letters |> Option.map snd |> Option.value ~default:IntSet.empty in
         let forbidden_cols = IntSet.union l_forbidden_cols r_forbidden_cols in
         CharMap.add letter (quantity, forbidden_cols) acc
      )
      all_letters
      CharMap.empty
  in
  let known_letters =
    known_letters
    |> CharMap.filter (fun _ (q, _) -> match q with AtLeast 0 -> false | _ -> true)
    |> CharMap.map (fun (q, _ as v) -> match q with Exactly 0 -> Exactly 0, IntSet.empty | _ -> v)
  in
  {
    known_positions: char option list;
    known_letters: (quantity * IntSet.t) CharMap.t;
  }

let facts_of_truth_status (guess: (char * truth) list) : known_facts =
  let known_positions =
    List.fold_left
      (fun acc (letter, g) ->
         match g with
         | Correct -> Some letter :: acc
         | _ -> None::acc
      )
      []
      guess
    |> List.rev
  in
  let _, known_letters =
    List.fold_left
      (fun (i, acc) (letter, g) ->
         let acc =
           match g, CharMap.find_opt letter acc, List.exists (Option.equal Char.equal (Some letter)) known_positions with
           | Correct, _, _ -> acc
           | Nope, None, _ -> CharMap.add letter (Exactly 0, IntSet.empty) acc
           | Nope, Some (Exactly _ as q, cols), _ -> CharMap.add letter (q, IntSet.add i cols) acc
           | Nope, Some (AtLeast n, cols), _ -> CharMap.add letter (Exactly n, IntSet.add i cols) acc
           | Misplaced, None, _ -> CharMap.add letter (AtLeast 1, IntSet.singleton i) acc
           | Misplaced, Some (AtLeast n, cols), _ -> CharMap.add letter (AtLeast (n + 1), IntSet.add i cols) acc
           | Misplaced, Some (Exactly n, cols), _ -> CharMap.add letter (Exactly (n + 1), IntSet.add i cols) acc
         in
         i+1, acc
      )
      (0, CharMap.empty)
      guess
  in
  let known_letters =
    known_letters
    |> CharMap.filter (fun _ (q, _) -> match q with AtLeast 0 -> false | _ -> true)
    |> CharMap.map (fun (q, _ as v) -> match q with Exactly 0 -> Exactly 0, IntSet.empty | _ -> v)
  in
  {
    known_positions: char option list;
    known_letters: (quantity * IntSet.t) CharMap.t;
  }

let satisfy_fact (fact: known_facts) (word: string) : bool =
  let satisfy_known_pos =
    List.fold_left2
      (fun acc fact w ->
         match fact with
         | None -> acc
         | Some letter -> acc && Char.equal letter w
      )
      true
      fact.known_positions
      (word |> String.to_seq |> List.of_seq)
  in
  if not satisfy_known_pos then
    false
  else
    let _, other_letters_count =
      List.fold_left
        (fun (i, acc) w ->
           if List.nth fact.known_positions i |> Option.is_some then
             i+1, acc
           else
             let acc =
               match CharMap.find_opt w acc with
               | None -> CharMap.add w (1, IntSet.singleton i) acc
               | Some (n, cols) -> CharMap.add w (n + 1, IntSet.add i cols) acc
             in
             i+1, acc
        )
        (0, CharMap.empty)
        (word |> String.to_seq |> List.of_seq)
    in
    let count_satisfies_fact =
      CharMap.fold
        (fun letter (quantity, forbidden) acc ->
           let actual_quantity, cols = CharMap.find_opt letter other_letters_count |> Option.value ~default:(0, IntSet.empty) in
           let number_ok =
             match quantity with
             | Exactly n when n = actual_quantity -> true
             | AtLeast n when n <= actual_quantity -> true
             | _ -> false
           in
           if not number_ok then false
           else if IntSet.inter forbidden cols |> IntSet.is_empty then acc
           else false
        )
        fact.known_letters
        true
    in
    count_satisfies_fact

let filter_by_fact (fact: known_facts) (words: string list) : string list =
  List.filter (satisfy_fact fact) words


let score (nb_of_candidates: int) (stats: int CharMap.t) (word: string) (fact: known_facts) : int =
  let count =
    String.fold_left
      (fun (i, acc) c ->
         let acc =
           if List.nth fact.known_positions i |> Option.is_some
           then acc
           else CharMap.update c (function None -> Some 1 | Some n -> Some (n+1)) acc
         in
         i+1, acc
      )
      (0, CharMap.empty)
      word
    |> snd
  in
  if false then
    CharMap.fold
      (fun letter nb acc ->
         match CharMap.find_opt letter stats with
         | None -> acc
         | Some nb_in_candidate ->
           if nb > 4 * nb_in_candidate / nb_of_candidates then
             acc + (nb_in_candidate * nb) / nb_of_candidates / 4
           else
             acc + (nb_in_candidate * nb) / nb_of_candidates
      )
      count
      0
  else
    CharMap.cardinal count

let pick_next ?(silent: bool = false) (dictionary: dictionary) (fact: known_facts) : string option =
  let printf f = if silent then Format.ifprintf Format.std_formatter f else Ocolor_format.printf f in
  let words = CharMap.find (List.nth fact.known_positions 0 |> Option.value ~default:'a') dictionary.words |> IntMap.find (List.length fact.known_positions) in
  let words = filter_by_fact fact words in
  let stats =
    List.fold_left
      (fun acc word ->
         String.fold_left
           (fun (i, acc) c ->
              let acc =
                if List.nth fact.known_positions i |> Option.is_some
                then acc
                else CharMap.update c (function None -> Some 1 | Some n -> Some (n+1)) acc
              in
              i+1, acc
           )
           (0, acc)
           word
         |> snd
      )
      CharMap.empty
      words
  in
  let words = List.map (fun s -> s, score (List.length words) stats s fact) words in
  let words = List.sort (fun (_, lv) (_, rv) -> compare rv lv) words in
  let nb_words = List.length words in
  match words with
  | (h, _)::_ ->
    if nb_words < 10 then
      let () =
        printf
          {|I found %d word%s: %a. I suggest "%s".@.|}
          nb_words (if nb_words = 1 then "" else "s")
          (Ocolor_format.pp_list_generic ~left:"" ~right:"" ~sep:", " Format.pp_print_string)
          (List.map fst words)
          h
      in
      Some h
    else
      let () = printf {|I found %d word%s. I picked "%s".@.|} nb_words (if nb_words = 1 then "" else "s") h in
      Some h
  | [] ->
    let () = printf {|I can't find any word matching this fact.@.|} in
    None

let resolution ?(silent: bool = false) (reference: string) : string list =
  let printf f = if silent then Format.ifprintf Format.std_formatter f else Ocolor_format.printf f in
  let () = printf {|Starting simulation from word "%s".@.|} reference in
  let fact = initial_fact_from_string reference in
  let rec aux fact =
    let guess = pick_next ~silent dictionary fact in
    match guess with
    | None -> []
    | Some guess ->
      let truth_status = truth_of_guess reference guess in
      let () = printf "%a@." pp_truths_and_word truth_status in
      if List.for_all (function (_, Correct) -> true | _ -> false) truth_status
      then
        let () = printf "Found it!@." in
        [reference]
      else
        let new_fact = facts_of_truth_status truth_status in
        let fact = merge_known_facts new_fact fact in
        let () = printf "%a@." pp_known_facts fact in
        guess::aux fact
  in
  let tries = aux fact in
  tries

let simulation_main ?(silent: bool = false) () : unit =
  let printf f = if silent then Format.ifprintf Format.std_formatter f else Ocolor_format.printf f in
  let () = Random.self_init () in
  let reference = List.nth dictionary.all (Random.int (List.length dictionary.all)) in
  let () = printf {|Starting simulation from word "%s".@.|} reference in
  let _ = resolution reference ~silent in
  ()

let read_interactive_truth (guess: string) : (char * truth) list =
  let rec aux () =
    let () = Format.printf {|Word you tried (leave empty if it's the guess: "%s"): %!|} guess in
    let tried_word = Scanf.scanf "%s\n" (fun s -> s) in
    let tried_word = if String.equal tried_word "" then guess else tried_word in
    if String.length guess <> String.length tried_word then
      let () = Format.printf {|Wrong length. Expected %d, got %d.|} (String.length guess) (String.length tried_word) in
      aux ()
    else
      let () = Format.printf {|Result (correct:_, misplaced: *, wrong: .): %!|} in
      let truth = Scanf.scanf "%s\n" (fun s -> s) in
      if String.length guess <> String.length truth then
        let () = Format.printf {|Wrong length. Expected %d, got %d. Try again.@.|} (String.length guess) (String.length tried_word) in
        aux ()
      else
        let truth =
          List.fold_left2
            (fun acc t w ->
               match acc with
               | None -> None
               | Some acc ->
                 let truth =
                   match t with
                   | '_' -> Some Correct
                   | '*' -> Some Misplaced
                   | '.' -> Some Nope
                   | _' -> None
                 in
                 match truth with
                 | Some t -> Some((w, t)::acc)
                 | None ->
                   let () = Format.printf "Illegal character '%c'" t in
                   None
            )
            (Some [])
            (String.to_seq truth |> List.of_seq)
            (String.to_seq tried_word |> List.of_seq)
        in
        match truth with
        | Some truth -> List.rev truth
        | None -> aux ()
  in
  aux ()

let interactive_main (first: char) (length: int) : unit =
  let fact = initial_fact_from_first_and_length first length in
  let rec aux fact =
    let guess = pick_next dictionary fact in
    match guess with
    | None -> ()
    | Some guess ->
      let () = Ocolor_format.printf "My best guess is: %s@." guess in
      let truth_status = read_interactive_truth guess in
      let () = Ocolor_format.printf "%a@." pp_truths_and_word truth_status in
      if List.for_all (function (_, Correct) -> true | _ -> false) truth_status
      then
        let () = Ocolor_format.printf "Congrats!@." in
        ()
      else
        let new_fact = facts_of_truth_status truth_status in
        let fact = merge_known_facts new_fact fact in
        let () = Ocolor_format.printf "%a@." pp_known_facts fact in
        aux fact
  in
  let () = aux fact in
  ()

let play_main (brag: bool) : unit =
  let () = Random.self_init () in
  let reference =
    let rec aux () =
      let w = List.nth dictionary.all (Random.int (List.length dictionary.all)) in
      if String.length w >= 4 && String.length w <= 8 then w else aux ()
    in
    aux ()
  in
  let () = Ocolor_format.printf "%c%s@." reference.[0] (String.make (String.length reference - 1) '.') in
  let rec aux tries =
    let () = Ocolor_format.printf "Guess: %!" in
    let guess = Scanf.scanf "%s\n" (fun s -> s) in
    if String.length guess <> String.length reference then
      let () = Ocolor_format.printf "Mismatching length. Expecting %d, got %d.@." (String.length reference) (String.length guess) in
      aux tries
    else if CharMap.find_opt reference.[0] dictionary.words |> Option.map (IntMap.find_opt (String.length reference)) |> Option.join |> Option.value ~default:[] |> List.mem guess |> not then
      let () = Ocolor_format.printf "Unknown word.@." in
      aux tries
    else
      let truth_status = truth_of_guess reference guess in
      let () = Ocolor_format.printf "%a@." pp_truths_and_word truth_status in
      if List.for_all (function (_, Correct) -> true | _ -> false) truth_status
      then
        let () = Ocolor_format.printf "Found it in %d step%s!@." (tries + 1) (if tries = 1 then "" else "s") in
        ()
      else
        aux (tries + 1)
  in
  let () = aux 0 in
  if brag then
    let tries = resolution reference ~silent:true in
    let () = Ocolor_format.printf "I can do it in %d step%s:@." (List.length tries) (match tries with [_] -> "" | _ -> "s") in
    let () =
      List.iter
        (fun guess ->
           let truth_status = truth_of_guess reference guess in
           let () = Ocolor_format.printf "%a@." pp_truths_and_word truth_status in
           ()
        )
        tries
    in
    ()


let main () =
  let usage_msg = Format.asprintf "%s [--simulation] [--first <letter>] [--length <length>]" Sys.argv.(0) in
  let simulation = ref false in
  let play = ref false in
  let brag = ref false in
  let first = ref "" in
  let length = ref 0 in
  let anon_fun _ = () in
  let speclist = [
    ("--simulation", Arg.Set simulation, "Play against itself");
    ("--play", Arg.Set play, "Play mode");
    ("--brag", Arg.Set brag, "Only with --play mode");
    ("--first", Arg.Set_string first, "First letter");
    ("--length", Arg.Set_int length, "Length");
  ]
  in
  let () = Arg.parse speclist anon_fun usage_msg in
  if !simulation then
    simulation_main ()
  else if !play then
    play_main !brag
  else
    interactive_main !first.[0] !length
