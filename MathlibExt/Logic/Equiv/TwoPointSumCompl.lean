/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Logic.Equiv.Sum

/-!
# Splitting two distinct points from a type

For a type `α` with decidable equality and distinct `a,b∈α`, there is an equivalence `Fin 2 ⊕ {x
: α : x≠a ∧ x≠b} ≃ α`.

The two finite points map to `a,b`, and the complementary summand maps to its underlying value.
No finiteness or cardinality assumption on `α` is required.
-/

@[expose] public section

namespace Equiv

variable {α : Type*} [DecidableEq α]

/-- **Equivalence isolating two distinct points and their complement.** Let `α` have decidable
equality and `a,b∈α` satisfy `a≠b`. `twoPointSumCompl a b` maps `inl 0` to `a`, `inl 1` to
`b`, and `inr x` to the underlying complement element `x`. Its inverse tests equality with
`a,b` and otherwise returns the complement summand. -/
def twoPointSumCompl (a b : α) (hab : a ≠ b) :
    Fin 2 ⊕ {x : α // x ≠ a ∧ x ≠ b} ≃ α where
  toFun
    | Sum.inl 0 => a
    | Sum.inl 1 => b
    | Sum.inr x => x.val
  invFun y :=
    if hya : y = a then Sum.inl 0
    else if hyb : y = b then Sum.inl 1
    else Sum.inr ⟨y, hya, hyb⟩
  left_inv := by
    intro s
    match s with
    | Sum.inl 0 =>
      simp
    | Sum.inl 1 =>
      simp [Ne.symm hab]
    | Sum.inr x =>
      have h1 : (x : α) ≠ a := x.2.1
      have h2 : (x : α) ≠ b := x.2.2
      simp [h1, h2]
  right_inv := by
    intro y
    by_cases hya : y = a
    · subst hya
      simp
    · by_cases hyb : y = b
      · subst hyb
        simp [Ne.symm hab]
      · simp [hya, hyb]

@[simp]
theorem twoPointSumCompl_symm_apply_first (a b : α) (hab : a ≠ b) :
    (twoPointSumCompl a b hab).symm a = Sum.inl (0 : Fin 2) := by
  simp [twoPointSumCompl]

@[simp]
theorem twoPointSumCompl_symm_apply_second (a b : α) (hab : a ≠ b) :
    (twoPointSumCompl a b hab).symm b = Sum.inl (1 : Fin 2) := by
  simp [twoPointSumCompl, Ne.symm hab]

@[simp]
theorem twoPointSumCompl_symm_apply_other (a b : α) (hab : a ≠ b)
    (x : α) (hxa : x ≠ a) (hxb : x ≠ b) :
    (twoPointSumCompl a b hab).symm x = Sum.inr ⟨x, hxa, hxb⟩ := by
  simp [twoPointSumCompl, hxa, hxb]

end Equiv
