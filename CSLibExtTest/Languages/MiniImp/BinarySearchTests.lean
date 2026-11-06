/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.BinarySearch
public meta import CSLibExt.Languages.MiniImp.BinarySearch

open CSLibExt.Languages.MiniImp
open CSLibExt.Languages.MiniImp.BinarySearch

#eval run #[1, 3, 3, 7] 3
example : run #[1, 3, 3, 7] 3 = some 1 := by decide
example : run #[] 0 = some 0 := by decide
example : run #[4] 3 = some 0 := by decide
example : run #[4] 4 = some 0 := by decide
example : run #[4] 5 = some 1 := by decide
example : run #[1, 3, 3, 7] 0 = some 0 := by decide
example : run #[1, 3, 3, 7] 2 = some 1 := by decide
example : run #[1, 3, 3, 7] 4 = some 3 := by decide
example : run #[1, 3, 3, 7] 8 = some 4 := by decide
example : run #[2, 2, 2] 2 = some 0 := by decide

-- Arithmetic is Nat arithmetic, not modular machine arithmetic.
example : evalA (.sub (.lit 2) (.lit 5)) (fun _ => 0) = 0 := by decide
example : evalA (.div (.lit 5) (.lit 0)) (fun _ => 0) = 0 := by decide

-- Fail closed: both semantics and interpreter reject empty and one-past-end
-- reads.
example (fuel : Nat) (s : State) :
    exec fuel (.read "value" #[] (.lit 0)) s = none :=
  exec_read_invalid fuel (by simp [evalA])
example (s t : State) : ¬ BigStep (.read "value" #[7] (.lit 1)) s t :=
  read_no_bigStep (by simp [evalA])
example (s : State) : ¬ wp (.read "value" #[7] (.lit 1)) (fun _ => True) s := by
  simp [wp, evalA]
example : (exec 1 (.read "value" #[7] (.lit 0)) (fun _ => 99)).map
    (fun s => (s "value", s "unmodified")) = some (7, 99) := by decide
example : (exec 1 (.read "value" #[7] (.lit 1)) (fun _ => 99)).map
    (fun s => s "value") = none := by decide
example : (exec 0 (program #[1] 0) (fun _ => 0)).map
    (fun s => s "lo") = none := by decide

-- An explicitly false ghost annotation does not affect operational semantics.
example : (exec 1 (.while (.not .tru) (fun _ => False) .skip) (fun _ => 7)).map
    (fun s => s "lo") = some 7 := by decide

private def arraysOfLength : Nat → List (Array Nat)
  | 0 => [#[]]
  | n + 1 => (arraysOfLength n).flatMap (fun xs => (List.range 4).map xs.push)

-- Unsorted arrays are included: correspondence and termination do not require
-- sorting.
#eval do
  let arrays := (List.range 6).flatMap arraysOfLength
  let mut count := 0
  for xs in arrays do
    for key in List.range 6 do
      let got := run xs key
      let want := some (Cslib.Algorithms.Lean.TimeM.lowerBound xs key).ret
      unless got == want do
        throw (IO.userError (s!"mismatch: {xs}, key={key}, " ++
          s!"MiniImp={got}, reference={want}"))
      count := count + 1
  unless count == 8190 do
    throw (IO.userError s!"wrong enumeration size: {count}")
  IO.println (s!"PASS {count} actual MiniImp/reference comparisons " ++
    "(length 0..5, values 0..3, keys 0..5)")

#eval [run #[] 0, run #[4] 3, run #[4] 4, run #[4] 5,
  run #[1, 3, 3, 7] 0, run #[1, 3, 3, 7] 2, run #[1, 3, 3, 7] 3,
  run #[1, 3, 3, 7] 4, run #[1, 3, 3, 7] 8, run #[2, 2, 2] 2]

example : (exec 7 (loop #[1, 3, 3, 7] 3)
    (State.update (State.update (fun _ => 99) "lo" 2) "hi" 4)).map
    (fun s => s "lo") = some 2 := by
  decide

-- Exercise all valid initial intervals, including empty intervals and nonzero
-- lower bounds.
#eval do
  let arrays : List (Array Nat) := (List.range 4).flatMap arraysOfLength
  let mut count := 0
  for xs in arrays do
    let xs : Array Nat := xs
    for key in List.range 6 do
      for lo in List.range (xs.size + 1) do
        for hi in List.range (xs.size + 1) do
          if h : lo ≤ hi ∧ hi ≤ xs.size then
            let s := State.update (State.update (fun _ => 99) "lo" lo) "hi" hi
            let got := (exec (hi - lo + 5) (loop xs key) s).map
              (fun (t : State) => t "lo")
            let want := some
              (Cslib.Algorithms.Lean.TimeM.lowerBound.loop
                xs key lo hi h.1 h.2).ret
            unless got == want do
              throw (IO.userError (s!"interval mismatch: {xs}, key={key}, " ++
                s!"lo={lo}, hi={hi}"))
            count := count + 1
  unless count == 4494 do
    throw (IO.userError s!"wrong interval enumeration size: {count}")
  IO.println s!"PASS {count} actual MiniImp/reference interval comparisons"

#print axioms run
#print axioms Cslib.Algorithms.Lean.TimeM.lowerBound
#print axioms Cslib.Algorithms.Lean.TimeM.lowerBound_spec
#print axioms exec
#print axioms exec_sound
#print axioms wp_sound
#print axioms body_preserves
#print axioms program_exec_success
#print axioms program
#print axioms program_vc
#print axioms midpoint_safe
#print axioms bigStep_eq_lowerBound
#print axioms loop_exec_success
#print axioms run_eq_lowerBound
#print axioms total_correct
#print axioms read_no_bigStep
#print axioms exec_read_invalid
