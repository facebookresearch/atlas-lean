/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.LinearAlgebra.Matrix.ProductSymmetry

open Matrix

private def firstDiagonalAsymmetric : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℕ :=
  fun p q =>
    if p = (0, 0) ∧ q = (1, 1) then 7
    else if p = (1, 1) ∧ q = (0, 0) then 11
    else 0

private def secondDiagonalAsymmetric : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℕ :=
  fun p q =>
    if p = (0, 1) ∧ q = (1, 0) then 7
    else if p = (1, 0) ∧ q = (0, 1) then 11
    else 0

private def corrected : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℕ :=
  fun p q =>
    if (p = (0, 0) ∧ q = (1, 1)) ∨ (p = (1, 1) ∧ q = (0, 0)) then 7
    else if (p = (0, 1) ∧ q = (1, 0)) ∨ (p = (1, 0) ∧ q = (0, 1)) then 11
    else 0

-- Changing the first rectangle equality to inspect only the other diagonal makes these fail.
example : ∀ a, (firstDiagonalAsymmetric.submatrix (a, ·) (a, ·)).IsSymm := by decide
example : ∀ i, (firstDiagonalAsymmetric.submatrix (·, i) (·, i)).IsSymm := by decide
example : firstDiagonalAsymmetric (0, 1) (1, 0) = firstDiagonalAsymmetric (1, 0) (0, 1) := by
  decide
example : firstDiagonalAsymmetric (0, 0) (1, 1) ≠ firstDiagonalAsymmetric (1, 1) (0, 0) := by
  decide
example : ¬firstDiagonalAsymmetric.IsSymm := by decide

-- Changing the second rectangle equality to inspect only the first diagonal makes these fail.
example : ∀ a, (secondDiagonalAsymmetric.submatrix (a, ·) (a, ·)).IsSymm := by decide
example : ∀ i, (secondDiagonalAsymmetric.submatrix (·, i) (·, i)).IsSymm := by decide
example : secondDiagonalAsymmetric (0, 0) (1, 1) = secondDiagonalAsymmetric (1, 1) (0, 0) := by
  decide
example : secondDiagonalAsymmetric (0, 1) (1, 0) ≠ secondDiagonalAsymmetric (1, 0) (0, 1) := by
  decide
example : ¬secondDiagonalAsymmetric.IsSymm := by decide

-- Correcting both opposite-diagonal pairs satisfies the complete criterion.
example : corrected.IsSymm := by
  rw [Matrix.isSymm_prod_iff]
  decide

-- Empty rows make every matrix symmetric, even with infinitely many columns and arbitrary entries.
example {α : Type*} (A : Matrix (Fin 0 × ℤ) (Fin 0 × ℤ) α) : A.IsSymm := by
  rw [Matrix.isSymm_prod_iff]
  refine ⟨fun a => Fin.elim0 a, ?_, fun a => Fin.elim0 a⟩
  intro i
  rw [Matrix.IsSymm.ext_iff]
  intro a
  exact Fin.elim0 a

-- With one row, full symmetry is exactly symmetry of that row, without finiteness assumptions.
example {α : Type*} (A : Matrix (Fin 1 × ℤ) (Fin 1 × ℤ) α)
    (h : (A.submatrix (0, ·) (0, ·)).IsSymm) : A.IsSymm := by
  rw [Matrix.isSymm_prod_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simpa only [Subsingleton.elim a 0] using h
  · intro i
    rw [Matrix.IsSymm.ext_iff]
    intro a b
    rw [Subsingleton.elim a b]
  · intro a b _ _ hab
    rw [Subsingleton.elim a b] at hab
    exact (lt_irrefl _ hab).elim

-- The column-dual singleton boundary is also covered.
example {α : Type*} (A : Matrix (ℤ × Fin 1) (ℤ × Fin 1) α)
    (h : (A.submatrix (·, 0) (·, 0)).IsSymm) : A.IsSymm := by
  rw [Matrix.isSymm_prod_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    rw [Subsingleton.elim i j]
  · intro i
    simpa only [Subsingleton.elim i 0] using h
  · intro _ _ i j _ hij
    rw [Subsingleton.elim i j] at hij
    exact (lt_irrefl _ hij).elim

#print axioms Matrix.isSymm_prod_iff
