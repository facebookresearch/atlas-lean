/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Data.List.TakeThroughAcc

@[expose] public section

open List

example {α γ : Type*} (f : γ → α → γ) (stop : γ → Bool) (c : γ) (xs : List α) :
    takeThroughAcc f stop c xs =
      match xs with
      | [] => []
      | x :: xs =>
        if stop (f c x) then [x] else x :: takeThroughAcc f stop (f c x) xs := by
  cases xs <;> rfl

example {α β δ : Type*} (p : β → Bool) (v : α → β) (a : δ) (xs : List α) :
    takeThroughAcc
        (fun found (x : δ × α) =>
          match found with
          | some old => some old
          | none => if p (v x.2) then some x.2 else none)
        Option.isSome none (xs.map fun x => (a, x)) =
      (takeThrough (fun x => p (v x)) xs).map fun x => (a, x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p (v x) <;> simp [h, ih]

example : takeThroughAcc (fun c x : Nat => c + x) (fun c => decide (5 ≤ c)) 0 [] = [] :=
  by decide

example :
    takeThroughAcc (fun c x : Nat => c + x) (fun c => decide (5 ≤ c)) 0 [5, 1, 2] = [5] :=
  by decide

example :
    takeThroughAcc (fun c x : Nat => c + x) (fun c => decide (20 ≤ c)) 0 [1, 2, 3, 4] =
      [1, 2, 3, 4] := by
  decide

example :
    takeThroughAcc (fun c x : Nat => c + x) (fun c => decide (5 ≤ c)) 0 [1, 2, 3, 4] =
      [1, 2, 3] := by
  decide

example :
    (takeThroughAcc (fun c x : Nat => c + x) (fun c => decide (5 ≤ c)) 0
      [1, 2, 3, 4]).foldl (· + ·) 0 = 6 := by
  decide

-- The initial accumulator already stops, but only the accumulator after an update is tested.
example :
    takeThroughAcc (fun _ x : Nat => x) (fun c => decide (5 ≤ c)) 99 [1, 6, 7] = [1, 6] := by
  decide

example :
    takeThroughAcc (fun found x : Bool => found || x) id false [false, false, true, false] =
      [false, false, true] := by
  decide

example :
    takeThroughAcc (fun found x : Bool => found || x) id false [false, false] =
      [false, false] := by
  decide

example :
    takeThroughAcc
        (fun found (x : Nat) =>
          match found with
          | some old => some old
          | none => if decide (3 ≤ x) then some x else none)
        Option.isSome none [1, 2, 3, 4] = [1, 2, 3] := by
  decide

example :
    (takeThrough (fun x : Nat => decide (3 ≤ x)) [1, 2, 3, 4]).foldl
        (fun found x =>
          match found with
          | some old => some old
          | none => if decide (3 ≤ x) then some x else none) none = some 3 := by
  decide

example :
    takeThroughAcc
        (fun found (x : Nat) =>
          match found with
          | some old => some old
          | none => if decide (5 ≤ x) then some x else none)
        Option.isSome none [1, 2, 3, 4] = [1, 2, 3, 4] := by
  decide

example :
    (takeThrough (fun x : Nat => decide (5 ≤ x)) [1, 2, 3, 4]).foldl
        (fun found x =>
          match found with
          | some old => some old
          | none => if decide (5 ≤ x) then some x else none) none = none := by
  decide

example :
    [1, 3, 4].foldl
        (fun found x =>
          match found with
          | some old => some old
          | none => if decide (3 ≤ x) then some x else none) none = some 3 := by
  decide

example :
    let update := fun found (x : Nat) =>
      match found with
      | some old => some old
      | none => if decide (3 ≤ x) then some x else none
    let visited := takeThroughAcc update Option.isSome (some 7) [4, 5]
    visited = [4] ∧ visited.foldl update (some 7) = some 7 := by
  decide

example {α γ : Type*} (f : γ → α → γ) (stop : γ → Bool) (c : γ) :
    takeThroughAcc f stop c [] = [] := takeThroughAcc_nil f stop c

example {α γ : Type*} (f : γ → α → γ) (stop : γ → Bool) (c : γ) (x : α)
    (xs : List α) (h : stop (f c x) = true) :
    takeThroughAcc f stop c (x :: xs) = [x] := takeThroughAcc_cons_of_stop h xs

example {α γ : Type*} (f : γ → α → γ) (stop : γ → Bool) (c : γ) (x : α)
    (xs : List α) (h : stop (f c x) = false) :
    takeThroughAcc f stop c (x :: xs) = x :: takeThroughAcc f stop (f c x) xs :=
  takeThroughAcc_cons_of_continue h xs

example {α γ : Type*} (f : γ → α → γ) (stop : γ → Bool) (c : γ) (xs : List α) :
    takeThroughAcc f stop c xs <+: xs := takeThroughAcc_prefix f stop c xs

example {α γ : Type*} (f : γ → α → γ) (stop : γ → Bool) (c : γ) (xs : List α)
    (x : α) (h : x ∈ takeThroughAcc f stop c xs) : x ∈ xs :=
  mem_of_mem_takeThroughAcc h

example {α : Type*} (p : α → Bool) (xs : List α) :
    takeThroughAcc (fun found x => found || p x) id false xs = takeThrough p xs :=
  takeThroughAcc_or p xs

example {α β δ : Type*} (p : β → Bool) (v : α → β) (w : α → δ) (xs : List α) :
    takeThroughAcc (fun found x =>
        match found with
        | some old => some old
        | none => if p (v x) then some (w x) else none)
        Option.isSome none xs = takeThrough (fun x => p (v x)) xs :=
  takeThroughAcc_first p v w xs

example {α β δ : Type*} (p : β → Bool) (v : α → β) (w : α → δ) (xs : List α) :
    (takeThrough (fun x => p (v x)) xs).foldl
        (fun found x =>
          match found with
          | some old => some old
          | none => if p (v x) then some (w x) else none) none =
      (xs.find? fun x => p (v x)).map w :=
  foldl_first_takeThrough p v w xs

example {α γ : Type*} (f : γ → α → γ) (stop : γ → Bool) (c : γ) (xs : List α) :
    takeThroughAcc f stop c xs =
      ((xs.zip (xs.scanl f c).tail).takeThrough (fun x => stop x.2)).map Prod.fst :=
  takeThroughAcc_eq_map_takeThrough_scanl f stop c xs

#reduce (
  takeThroughAcc (fun c x : Nat => c + x) (fun c => decide (5 ≤ c)) 0 [1, 2, 3, 4],
  (takeThroughAcc (fun c x : Nat => c + x) (fun c => decide (5 ≤ c)) 0
    [1, 2, 3, 4]).foldl (· + ·) 0,
  takeThroughAcc (fun _ x : Nat => x) (fun c => decide (5 ≤ c)) 99 [1, 6, 7],
  takeThroughAcc (fun found x : Bool => found || x) id false [false, false, true, false],
  takeThroughAcc
    (fun found (x : Nat) =>
      match found with
      | some old => some old
      | none => if decide (3 ≤ x) then some x else none)
    Option.isSome none [1, 2, 3, 4],
  [1, 3, 4].foldl
    (fun found x =>
      match found with
      | some old => some old
      | none => if decide (3 ≤ x) then some x else none) none,
  takeThroughAcc
    (fun found (x : Nat) =>
      match found with
      | some old => some old
      | none => if decide (3 ≤ x) then some x else none)
    Option.isSome (some 7) [4, 5],
  [4].foldl
    (fun found x =>
      match found with
      | some old => some old
      | none => if decide (3 ≤ x) then some x else none) (some 7))

#print axioms List.takeThroughAcc
#print axioms List.takeThroughAcc_nil
#print axioms List.takeThroughAcc_cons_of_stop
#print axioms List.takeThroughAcc_cons_of_continue
#print axioms List.takeThroughAcc_prefix
#print axioms List.mem_of_mem_takeThroughAcc
#print axioms List.takeThroughAcc_or
#print axioms List.takeThroughAcc_first
#print axioms List.foldl_first_takeThrough
#print axioms List.takeThroughAcc_eq_map_takeThrough_scanl
