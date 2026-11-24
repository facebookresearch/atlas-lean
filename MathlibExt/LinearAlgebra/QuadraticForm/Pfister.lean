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

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.Data.Fintype.Powerset

/-!
# Pfister forms

For units `a : Fin n → Fˣ`, this file defines the diagonal expansion of the
`n`-fold quadratic Pfister form

`\[ \langle\!\langle a_0,\ldots,a_{n-1}\rangle\!\rangle
     = \bigotimes_i \langle 1,-a_i\rangle. \]`

Its coordinates are indexed by subsets `s : Finset (Fin n)`.  The coefficient
at `s` is `∏ i ∈ s, -a i`, so the carrier has dimension `2 ^ n`.  The
diagonal expression makes sense over every field.  Under `NeZero (2 : F)`,
all its coefficients are nonzero and Mathlib's radical calculation shows
that the form is nondegenerate.

This is only the quadratic-form foundation.  It defines no
Grothendieck--Witt or Witt ring, hyperbolic quotient, fundamental ideal,
associated graded object, Milnor comparison, or form of the Milnor
conjecture.

## Main definitions

* `QuadraticForm.pfisterWeight`
* `QuadraticForm.pfister`

## Main results

* `QuadraticForm.pfister_apply`
* `QuadraticForm.pfisterWeight_ne_zero`
* `QuadraticForm.pfister_radical`
* `QuadraticForm.pfister_nondegenerate`
* `QuadraticForm.finrank_pfister_carrier`

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter X.
* R. Elman, N. Karpenko, A. Merkurjev,
  *The Algebraic and Geometric Theory of Quadratic Forms*.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

universe u

namespace QuadraticForm

variable (F : Type u) [Field F]

/-- Diagonal coefficient indexed by a subset in the standard expansion of
the `n`-fold Pfister form `⟨⟨a₀,…,aₙ₋₁⟩⟩`. -/
def pfisterWeight {n : ℕ} (a : Fin n → Fˣ) (s : Finset (Fin n)) : F :=
  ∏ i ∈ s, -(a i : F)

/-- The coefficient of the empty subset in a Pfister form is one. -/
@[simp]
theorem pfisterWeight_empty {n : ℕ} (a : Fin n → Fˣ) :
    pfisterWeight F a ∅ = 1 := by
  simp [pfisterWeight]

/-- Adding a fresh index multiplies the Pfister coefficient by the
corresponding negative unit. -/
@[simp]
theorem pfisterWeight_insert {n : ℕ} (a : Fin n → Fˣ)
    (s : Finset (Fin n)) (i : Fin n) (hi : i ∉ s) :
    pfisterWeight F a (insert i s) = -(a i : F) * pfisterWeight F a s := by
  simp [pfisterWeight, hi]

/-- Every diagonal coefficient of a Pfister form is nonzero. -/
theorem pfisterWeight_ne_zero {n : ℕ} (a : Fin n → Fˣ)
    (s : Finset (Fin n)) :
    pfisterWeight F a s ≠ 0 := by
  rw [pfisterWeight, Finset.prod_ne_zero_iff]
  intro i hi
  exact neg_ne_zero.mpr (Units.ne_zero (a i))

/-- The diagonal `n`-fold Pfister form, with one coordinate for each subset
of `Fin n` and coefficient `∏ i ∈ s, -a i` at the coordinate `s`. -/
def pfister {n : ℕ} (a : Fin n → Fˣ) :
    QuadraticForm F (Finset (Fin n) → F) :=
  QuadraticMap.weightedSumSquares F (pfisterWeight F a)

/-- Evaluation formula for the diagonal Pfister form. -/
@[simp]
theorem pfister_apply {n : ℕ} (a : Fin n → Fˣ)
    (x : Finset (Fin n) → F) :
    pfister F a x =
      ∑ s : Finset (Fin n), pfisterWeight F a s * (x s * x s) := by
  simp [pfister, QuadraticMap.weightedSumSquares_apply]

/-- Over a field of characteristic different from two, an `n`-fold Pfister
form has trivial radical. -/
theorem pfister_radical [NeZero (2 : F)] {n : ℕ} (a : Fin n → Fˣ) :
    (pfister F a).radical = ⊥ := by
  rw [pfister, radical_weightedSumSquares]
  ext x
  simp [pfisterWeight_ne_zero, Pi.mem_spanSubset_iff, funext_iff]

/-- Over a field of characteristic different from two, every Pfister form is
nondegenerate. -/
theorem pfister_nondegenerate [NeZero (2 : F)] {n : ℕ}
    (a : Fin n → Fˣ) :
    (pfister F a).Nondegenerate := by
  let _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne _)
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  exact pfister_radical F a

/-- The carrier of an `n`-fold Pfister form has dimension `2 ^ n`. -/
theorem finrank_pfister_carrier (n : ℕ) :
    Module.finrank F (Finset (Fin n) → F) = 2 ^ n := by
  rw [Module.finrank_pi, Fintype.card_finset, Fintype.card_fin]

end QuadraticForm

end
