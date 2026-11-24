/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Init

/-!
# List interleaving (`splice`) and its cost

`splice xs ys` interleaves two lists, starting with the first element
of `xs` and then swapping the argument order at every recursive call,
so ordinary list induction does not apply (`splice_ind`).

## Cost model

`Tsplice` counts one unit per call: the nil cases cost one, the cons
case costs one plus the recursive call. `Tsplice_le` bounds it by
`|xs| + |ys| + 1`.

## Provenance

A Lean formalisation of Chapter 11, §11.3 of Tobias Nipkow (ed.),
*Functional Data Structures and Algorithms* (ACM Books, 2025; text
version of July 27, 2026).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace BraunTree

variable {α : Type u}

/-- `splice xs ys` interleaves `xs` and `ys`, starting with `xs`. -/
def splice : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: splice ys xs
termination_by xs ys => xs.length + ys.length
decreasing_by simp only [List.length_cons]; omega

/-- Induction principle for `splice`: the recursive call swaps the two
lists, so ordinary list induction does not apply. -/
theorem splice_ind {α : Type u} {P : List α → List α → Prop}
    (hnil : ∀ (ys : List α), P [] ys)
    (hcons : ∀ (x : α) (xs ys : List α), P ys xs → P (x :: xs) ys)
    (xs ys : List α) : P xs ys := by
  have key : ∀ (n : ℕ) (xs ys : List α), xs.length + ys.length = n → P xs ys := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro xs ys hlen
      cases xs with
      | nil => exact hnil ys
      | cons x xs' =>
        apply hcons x xs' ys
        simp only [List.length_cons] at hlen
        exact ih (ys.length + xs'.length) (by omega) ys xs' rfl
  exact key _ xs ys rfl

/-- `(splice xs ys).length = xs.length + ys.length`. -/
theorem splice_length {xs ys : List α} :
    (splice xs ys).length = xs.length + ys.length := by
  refine splice_ind (P := fun xs ys => (splice xs ys).length = xs.length + ys.length) ?_ ?_ xs ys
  · intro ys; simp [splice]
  · intro x xs ys ih
    simp only [splice, List.length_cons]
    omega

/-- The `i`-th element of a splice. -/
theorem splice_getElem? {xs ys : List α}
    (h : ys.length ≤ xs.length ∧ xs.length ≤ ys.length + 1) (n : ℕ) :
    (splice xs ys)[n]? = if n % 2 = 0 then xs[n / 2]? else ys[n / 2]? := by
  refine splice_ind (P := fun xs ys =>
    (ys.length ≤ xs.length ∧ xs.length ≤ ys.length + 1) →
    ∀ n, (splice xs ys)[n]? = if n % 2 = 0 then xs[n / 2]? else ys[n / 2]?) ?_ ?_ xs ys h n
  · intro ys h n
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using h.1)
    subst hy; simp [splice]
  · intro x xs ys ih h n
    have hlen : (x :: xs).length = xs.length + 1 := rfl
    have h' : xs.length ≤ ys.length ∧ ys.length ≤ xs.length + 1 := by omega
    cases n with
    | zero => simp [splice]
    | succ m =>
      have e : (splice (x :: xs) ys)[m + 1]? = (splice ys xs)[m]? := by
        simp [splice, List.getElem?_cons_succ]
      rw [e, ih h']
      by_cases hm : m % 2 = 0
      · have h1 : (m + 1) % 2 ≠ 0 := by omega
        have hd : (m + 1) / 2 = m / 2 := by omega
        rw [ite_eq_left hm, ite_eq_right h1, hd]
      · have h1 : (m + 1) % 2 = 0 := by omega
        have hd : (m + 1) / 2 = m / 2 + 1 := by omega
        rw [ite_eq_right hm, ite_eq_left h1, hd, List.getElem?_cons_succ]

/-- (32) `splice_last`: appending to either argument of `splice` appends
to the result. The two statements are proved together by strong induction
on the total length, since the `splice` recursion swaps the arguments. -/
theorem splice_append_aux : ∀ (n : ℕ) (xs ys : List α) (x : α),
    xs.length + ys.length = n →
    (ys.length ≤ xs.length → splice (xs ++ [x]) ys = splice xs ys ++ [x]) ∧
    (xs.length ≤ ys.length + 1 → splice xs (ys ++ [x]) = splice xs ys ++ [x]) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro xs ys x htot
    cases xs with
    | nil =>
      constructor
      · intro h1
        have hy : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using h1)
        subst hy; simp [splice]
      · intro h2; simp [splice]
    | cons a xs' =>
      have hlen : (a :: xs').length = xs'.length + 1 := rfl
      constructor
      · intro h1
        have h2 := (ih (ys.length + xs'.length) (by omega) ys xs' x rfl).2 (by omega)
        simp only [List.cons_append, splice]
        rw [h2]
      · intro h2
        have h1 := (ih (ys.length + xs'.length) (by omega) ys xs' x rfl).1 (by omega)
        simp only [splice, List.cons_append]
        rw [h1]

/-- `splice (xs ++ [x]) ys = splice xs ys ++ [x]`. -/
theorem splice_append_left {xs ys : List α} (h : ys.length ≤ xs.length) (x : α) :
    splice (xs ++ [x]) ys = splice xs ys ++ [x] :=
  (splice_append_aux _ xs ys x rfl).1 h

/-- `splice xs (ys ++ [x]) = splice xs ys ++ [x]`. -/
theorem splice_append_right {xs ys : List α} (h : xs.length ≤ ys.length + 1) (x : α) :
    splice xs (ys ++ [x]) = splice xs ys ++ [x] :=
  (splice_append_aux _ xs ys x rfl).2 h

/-- `splice` of two constant lists is constant. -/
theorem splice_replicate {a b : ℕ} (x : α) :
    splice (List.replicate a x) (List.replicate b x) = List.replicate (a + b) x := by
  refine splice_ind (P := fun xs ys =>
    ∀ (a b : ℕ), xs = List.replicate a x → ys = List.replicate b x →
      splice xs ys = List.replicate (a + b) x) ?_ ?_ _ _ a b rfl rfl
  · intro ys a b h1 h2
    cases a with
    | zero => simp [splice, h2]
    | succ a' => simp at h1
  · intro x0 xs ys ih a b h1 h2
    cases a with
    | zero => simp at h1
    | succ a' =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj h1
      simp only [splice]
      rw [ih b a' h2 rfl, show a' + 1 + b = (b + a') + 1 from by omega, List.replicate_succ]

/-- `Tsplice xs ys`: running time of `splice xs ys` (1 per call). -/
def Tsplice : List α → List α → ℕ
  | [], _ => 1
  | _ :: xs, ys => 1 + Tsplice ys xs
  termination_by xs ys => xs.length + ys.length
  decreasing_by simp only [List.length_cons]; omega

/-- **(#33/§11.3.2)** `splice` costs proportionally to the list sizes:
`Tsplice xs ys ≤ |xs| + |ys| + 1`. -/
theorem Tsplice_le (xs ys : List α) : Tsplice xs ys ≤ xs.length + ys.length + 1 := by
  refine splice_ind (P := fun xs ys =>
    Tsplice xs ys ≤ xs.length + ys.length + 1) ?_ ?_ xs ys
  · intro ys; simp only [Tsplice, List.length_nil]; omega
  · intro x xs ys ih
    simp only [Tsplice, List.length_cons]
    omega

end BraunTree
end Cslib.Algorithms.Lean
