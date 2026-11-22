/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MvPolynomial.SymmetricPolynomialInCoefficients
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Fin.VecNotation

open scoped BigOperators

/-!
# Examples for symmetric polynomials in the coefficients

Exercises `Polynomial.symmetric_polynomial_in_esymm` on the polynomial
`(X - 1) * (X - 2)` over `ℚ`: the sum of the roots is `3`, the product of
the roots is `2`, and the theorem produces a polynomial in the signed
coefficients witnessing each symmetric evaluation. A one-variable case and
a constant symmetric polynomial are also covered.
-/

/-- A product of `n` linear factors is monic, splits, and has natural degree `n`. -/
private theorem prod_X_sub_C_monic_splits_natDegree (n : ℕ) (α : Fin n → ℚ) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))).Monic ∧
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))).Splits ∧
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))).natDegree = n := by
  refine ⟨Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _), ?_, ?_⟩
  · rw [Polynomial.splits_prod_iff (fun i _ => Polynomial.X_sub_C_ne_zero _)]
    exact fun i _ => Polynomial.Splits.X_sub_C _
  · have hdeg := Polynomial.natDegree_prod_of_monic Finset.univ
      (fun i => Polynomial.X - Polynomial.C (α i))
      (fun i _ => Polynomial.monic_X_sub_C (α i))
    rw [hdeg]
    simp

/-- The first elementary symmetric polynomial in two variables evaluated at
`(1, 2)` is the sum of the roots, `3`. -/
example : MvPolynomial.eval ![1, 2] (MvPolynomial.esymm (Fin 2) ℚ 1) = 3 := by
  have hcard : (Finset.univ : Finset (Fin 2)).powersetCard 1 = {{0}, {1}} := by decide
  simp [MvPolynomial.esymm, hcard]
  norm_num

/-- The second elementary symmetric polynomial in two variables evaluated at
`(1, 2)` is the product of the roots, `2`. -/
example : MvPolynomial.eval ![1, 2] (MvPolynomial.esymm (Fin 2) ℚ 2) = 2 := by
  have hcard : (Finset.univ : Finset (Fin 2)).powersetCard 2 = {{0, 1}} := by decide
  simp [MvPolynomial.esymm, hcard]

/-- The first elementary symmetric polynomial in one variable evaluated at
`(3,)` is `3`. -/
example : MvPolynomial.eval ![3] (MvPolynomial.esymm (Fin 1) ℚ 1) = 3 := by
  have hcard : (({0} : Finset (Fin 1))).powersetCard 1 = {{0}} := by decide
  simp [MvPolynomial.esymm, hcard]

/-- The sum of the roots `1, 2` is a polynomial in the signed coefficients of
`(X - 1) * (X - 2)`: the theorem's conclusion, applied directly. -/
example : ∃ q : MvPolynomial (Fin 2) ℚ,
    MvPolynomial.eval ![1, 2] (MvPolynomial.esymm (Fin 2) ℚ 1) =
      MvPolynomial.eval
        (fun i : Fin 2 => (-1 : ℚ) ^ (i.val + 1) *
          Polynomial.coeff (∏ j : Fin 2, (Polynomial.X - Polynomial.C (![1, 2] j)))
            (2 - (i.val + 1))) q := by
  obtain ⟨q, -, hq⟩ := Polynomial.symmetric_polynomial_in_esymm
    (MvPolynomial.esymm (Fin 2) ℚ 1) (MvPolynomial.esymm_isSymmetric (Fin 2) ℚ 1)
  exact ⟨q, hq rfl⟩

/-- A constant symmetric polynomial evaluated at the roots is a polynomial in
the signed coefficients (the one-variable case, root `3`). -/
example : ∃ q : MvPolynomial (Fin 1) ℚ,
    MvPolynomial.eval ![3] (MvPolynomial.C (5 : ℚ)) =
      MvPolynomial.eval
        (fun i : Fin 1 => (-1 : ℚ) ^ (i.val + 1) *
          Polynomial.coeff (∏ j : Fin 1, (Polynomial.X - Polynomial.C (![3] j)))
            (1 - (i.val + 1))) q := by
  obtain ⟨q, -, hq⟩ := Polynomial.symmetric_polynomial_in_esymm
    (MvPolynomial.C (5 : ℚ)) (MvPolynomial.IsSymmetric.C 5)
  exact ⟨q, hq rfl⟩

/-- The witness `q` depends only on the symmetric polynomial, not on the
split polynomial: one and the same `q` works for the two distinct root
tuples `(1, 2)` and `(1, 3)`. -/
example : ∃ q : MvPolynomial (Fin 2) ℚ,
    MvPolynomial.eval ![1, 2]
        (MvPolynomial.esymm (Fin 2) ℚ 1 + MvPolynomial.esymm (Fin 2) ℚ 2) =
      MvPolynomial.eval
        (fun i : Fin 2 => (-1 : ℚ) ^ (i.val + 1) *
          Polynomial.coeff (∏ j : Fin 2, (Polynomial.X - Polynomial.C (![1, 2] j)))
            (2 - (i.val + 1))) q ∧
    MvPolynomial.eval ![1, 3]
        (MvPolynomial.esymm (Fin 2) ℚ 1 + MvPolynomial.esymm (Fin 2) ℚ 2) =
      MvPolynomial.eval
        (fun i : Fin 2 => (-1 : ℚ) ^ (i.val + 1) *
          Polynomial.coeff (∏ j : Fin 2, (Polynomial.X - Polynomial.C (![1, 3] j)))
            (2 - (i.val + 1))) q := by
  obtain ⟨q, -, hq⟩ := Polynomial.symmetric_polynomial_in_esymm
    (MvPolynomial.esymm (Fin 2) ℚ 1 + MvPolynomial.esymm (Fin 2) ℚ 2)
    ((MvPolynomial.esymm_isSymmetric (Fin 2) ℚ 1).add
      (MvPolynomial.esymm_isSymmetric (Fin 2) ℚ 2))
  exact ⟨q, hq rfl, hq rfl⟩
