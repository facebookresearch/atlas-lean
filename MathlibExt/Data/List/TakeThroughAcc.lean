/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: generalized the accumulator-stopped inclusive prefix from the ETH
development to arbitrary lists, moved it to the `List` namespace, related it to the canonical
list operations, and added importing-client tests.
-/
module

public import MathlibExt.Data.List.TakeThrough

/-! # Accumulator-stopped inclusive prefixes

Adapted from `met` and its laws in `eth/proof/threesat/Exits/Defs.lean` and
`eth/proof/threesat/Exits/Tested.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).

The ETH machine, cost, size, and encoding wrappers around `met` remain separate. This module
contains only the list operation and its machine-independent laws.
-/

@[expose] public section

namespace List

/-- The prefix through the first element after whose update the accumulator satisfies `stop`,
including that element. The initial accumulator is not tested. If no updated accumulator satisfies
`stop`, this is the whole list. -/
def takeThroughAcc {α γ : Type*} (f : γ → α → γ) (stop : γ → Bool) :
    γ → List α → List α
  | _, [] => []
  | c, x :: xs =>
    let c' := f c x
    if stop c' then [x] else x :: takeThroughAcc f stop c' xs

/-- An empty list has an empty accumulator-stopped prefix. -/
@[simp] theorem takeThroughAcc_nil {α γ : Type*} (f : γ → α → γ) (stop : γ → Bool)
    (c : γ) : takeThroughAcc f stop c [] = [] := rfl

/-- If the accumulator stops after the head update, the prefix contains only the head. -/
@[simp] theorem takeThroughAcc_cons_of_stop {α γ : Type*} {f : γ → α → γ}
    {stop : γ → Bool} {c : γ} {x : α} (h : stop (f c x) = true) (xs : List α) :
    takeThroughAcc f stop c (x :: xs) = [x] := by
  simp [takeThroughAcc, h]

/-- If the accumulator continues after the head update, the same updated accumulator processes the
tail. -/
@[simp] theorem takeThroughAcc_cons_of_continue {α γ : Type*} {f : γ → α → γ}
    {stop : γ → Bool} {c : γ} {x : α} (h : stop (f c x) = false) (xs : List α) :
    takeThroughAcc f stop c (x :: xs) = x :: takeThroughAcc f stop (f c x) xs := by
  simp [takeThroughAcc, h]

/-- The accumulator-stopped list is a prefix of its source list. -/
theorem takeThroughAcc_prefix {α γ : Type*} (f : γ → α → γ) (stop : γ → Bool)
    (c : γ) (xs : List α) : takeThroughAcc f stop c xs <+: xs := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
    cases h : stop (f c x) <;> simp [takeThroughAcc, h, ih]

/-- Every member of an accumulator-stopped prefix belongs to the source list. -/
theorem mem_of_mem_takeThroughAcc {α γ : Type*} {f : γ → α → γ} {stop : γ → Bool}
    {c : γ} {xs : List α} {x : α} (h : x ∈ takeThroughAcc f stop c xs) : x ∈ xs :=
  (takeThroughAcc_prefix f stop c xs).mem h

/-- Accumulating disjunction from `false` gives the ordinary inclusive first-hit prefix. -/
theorem takeThroughAcc_or {α : Type*} (p : α → Bool) (xs : List α) :
    takeThroughAcc (fun found x => found || p x) id false xs = takeThrough p xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x <;> simp [takeThroughAcc, h, ih]

/-- Accumulating a projection of the first witness in an `Option` gives the ordinary inclusive
first-hit prefix. -/
theorem takeThroughAcc_first {α β δ : Type*} (p : β → Bool) (v : α → β) (w : α → δ)
    (xs : List α) :
    takeThroughAcc (fun found x =>
        match found with
        | some old => some old
        | none => if p (v x) then some (w x) else none)
        Option.isSome none xs = takeThrough (fun x => p (v x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p (v x) <;> simp [takeThroughAcc, h, ih]

/-- Folding the first-witness update over the inclusive tested prefix returns the first witness in
the whole source list. -/
theorem foldl_first_takeThrough {α β δ : Type*} (p : β → Bool) (v : α → β) (w : α → δ)
    (xs : List α) :
    (takeThrough (fun x => p (v x)) xs).foldl
        (fun found x =>
          match found with
          | some old => some old
          | none => if p (v x) then some (w x) else none) none =
      (xs.find? fun x => p (v x)).map w := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : p (v x) <;> simp [h, ih]

/-- The recursive ETH operation is the ordinary inclusive first-hit prefix of the elements paired
with their updated accumulators. -/
theorem takeThroughAcc_eq_map_takeThrough_scanl {α γ : Type*} (f : γ → α → γ)
    (stop : γ → Bool) (c : γ) (xs : List α) :
    takeThroughAcc f stop c xs =
      ((xs.zip (xs.scanl f c).tail).takeThrough (fun x => stop x.2)).map Prod.fst := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih =>
    rw [takeThroughAcc]
    cases h : stop (f c x)
    · rw [ih (f c x)]
      cases xs <;> simp [h]
    · cases xs <;> simp [h]

end List
