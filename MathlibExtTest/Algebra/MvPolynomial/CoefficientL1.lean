/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.MvPolynomial.CoefficientL1

open MvPolynomial Finset

@[expose] public section

local instance : Fact ((1 : NNReal) ≤ 1) := ⟨le_rfl⟩

private theorem norm_two_monomials {σ : Type*} (m n : σ →₀ ℕ) (hmn : m ≠ n)
    (a b : ℚ) :
    coeffL1Norm (monomial m a + monomial n b) = |a| + |b| := by
  classical
  have hs : (monomial m a + monomial n b).support ⊆ {m, n} :=
    (support_add).trans (union_subset
      ((support_monomial_subset).trans (by simp))
      ((support_monomial_subset).trans (by simp)))
  rw [coeffL1Norm_eq_sum hs]
  simp [AddMonoidAlgebra.coeff_add, coeff_monomial, hmn, Ne.symm hmn]

-- The exact source variable carrier, with signed coefficients.
example (m : ℕ+ →₀ ℕ) :
    coeffL1Norm (monomial m (-3) : MvPolynomial ℕ+ ℚ) = 3 := by
  rw [coeffL1Norm_monomial]
  norm_num

example (p q : MvPolynomial ℕ+ ℚ) :
    coeffL1Norm (p * q) ≤ coeffL1Norm p * coeffL1Norm q :=
  coeffL1Norm_mul_le p q

example (p : MvPolynomial (Fin 2) ℚ) : 0 ≤ coeffL1Norm p :=
  coeffL1Norm_nonneg p

example (p q : MvPolynomial (Fin 2) ℚ) :
    coeffL1Norm (p + q) ≤ coeffL1Norm p + coeffL1Norm q :=
  coeffL1Norm_add_le p q

example (p : MvPolynomial (Fin 2) ℚ) (T : Finset (Fin 2 →₀ ℕ)) :
    coeffL1Norm p = ∑ m ∈ p.support ∪ T, |p.coeff m| :=
  coeffL1Norm_eq_sum subset_union_left

example (m : Fin 2 →₀ ℕ) :
    coeffL1Norm (monomial m (0 : ℚ)) = 0 := by simp

example : coeffL1Norm (∑ i ∈ (∅ : Finset (Fin 2)), X i :
    MvPolynomial (Fin 2) ℚ) = 0 := by simp

example (p : MvPolynomial (Fin 2) ℚ) (S : Finset (Fin 2 →₀ ℕ))
    (hS : p.support ⊆ S) : coeffL1Norm p = ∑ m ∈ S, |p.coeff m| :=
  coeffL1Norm_eq_sum hS

example (p : MvPolynomial (Fin 2) ℚ) : coeffL1Norm ((0 : ℚ) • p : MvPolynomial (Fin 2) ℚ) = 0 :=
  by simp

example : coeffL1Norm (0 : MvPolynomial (Fin 2) ℚ) = 0 := by simp

example (p : MvPolynomial (Fin 2) ℚ) : coeffL1Norm (p + -p) = 0 := by simp

example (p : MvPolynomial (Fin 2) ℚ) : coeffL1Norm ((-2 : ℚ) • p) = 2 * coeffL1Norm p := by
  rw [coeffL1Norm_smul]
  norm_num

example (s : Finset ℕ) (f : ℕ → MvPolynomial (Fin 2) ℚ) :
    coeffL1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffL1Norm (f i) :=
  coeffL1Norm_sum_le s f

example : coeffL1Norm (monomial 0 (-7) : MvPolynomial (Fin 0) ℚ) = 7 := by
  rw [coeffL1Norm_monomial]
  norm_num

example (p q : MvPolynomial (Fin 0) ℚ) :
    coeffL1Norm (p * q) ≤ coeffL1Norm p * coeffL1Norm q :=
  coeffL1Norm_mul_le p q

private theorem norm_X_add_X :
    coeffL1Norm (X 0 + X 1 : MvPolynomial (Fin 2) ℚ) = 2 := by
  have h := norm_two_monomials
    (Finsupp.single (0 : Fin 2) 1) (Finsupp.single (1 : Fin 2) 1) (by
      intro h
      have he := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) h
      norm_num [Finsupp.single_apply, Finsupp.add_apply] at he) 1 1
  norm_num [X] at h
  exact h

private theorem norm_X_sub_X :
    coeffL1Norm (X 0 - X 1 : MvPolynomial (Fin 2) ℚ) = 2 := by
  rw [sub_eq_add_neg]
  have h := norm_two_monomials
    (Finsupp.single (0 : Fin 2) 1) (Finsupp.single (1 : Fin 2) 1) (by
      intro h
      have he := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) h
      norm_num [Finsupp.single_apply, Finsupp.add_apply] at he) 1 (-1)
  norm_num at h
  simpa [X] using h

-- Two variables and cancellation: actual norm two, product upper bound four.
example : coeffL1Norm ((X 0 + X 1) * (X 0 - X 1) : MvPolynomial (Fin 2) ℚ) = 2 := by
  have he : (X 0 + X 1) * (X 0 - X 1) =
      (X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 - X 1 ^ 2 := by ring
  rw [he, sub_eq_add_neg]
  have h := norm_two_monomials
      (Finsupp.single (0 : Fin 2) 2) (Finsupp.single (1 : Fin 2) 2) (by
      intro h
      have he := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) h
      norm_num [Finsupp.single_apply, Finsupp.add_apply] at he) 1 (-1)
  norm_num at h
  simpa [X, pow_two, monomial_mul_monomial, ← Finsupp.single_add] using h

example : coeffL1Norm (X 0 + X 1 : MvPolynomial (Fin 2) ℚ) *
    coeffL1Norm (X 0 - X 1 : MvPolynomial (Fin 2) ℚ) = 4 := by
  rw [norm_X_add_X, norm_X_sub_X]
  norm_num

example : coeffL1Norm ((X 0 + X 1) * (X 0 - X 1) : MvPolynomial (Fin 2) ℚ) ≤ 4 := by
  have h := coeffL1Norm_mul_le (X 0 + X 1 : MvPolynomial (Fin 2) ℚ)
    (X 0 - X 1 : MvPolynomial (Fin 2) ℚ)
  rw [norm_X_add_X, norm_X_sub_X] at h
  norm_num at h
  exact h

-- Two variables without cancellation: multiplying by 2X₀ gives norm four.
example : coeffL1Norm ((X 0 + X 1) * (2 * X 0) : MvPolynomial (Fin 2) ℚ) = 4 := by
  have hc : (2 : MvPolynomial (Fin 2) ℚ) = monomial 0 2 := rfl
  rw [add_mul, hc]
  simp only [X, monomial_mul_monomial, zero_add, one_mul, mul_one]
  have h := norm_two_monomials
    (Finsupp.single (0 : Fin 2) 2)
    (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) (by
      intro h
      have he := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) h
      norm_num [Finsupp.single_apply, Finsupp.add_apply] at he) 2 2
  norm_num at h
  simpa [← Finsupp.single_add, add_comm] using h

-- A multicoefficient metric check detects accidental replacement by the supremum norm.
example : dist (WithLp.toLp ((1 : NNReal) : ENNReal)
      (monomial (Finsupp.single (0 : Fin 2) 1) (3 : ℚ) +
       monomial (Finsupp.single (1 : Fin 2) 1) (-2)).coeff)
    (WithLp.toLp ((1 : NNReal) : ENNReal) (0 : (Fin 2 →₀ ℕ) →₀ ℚ)) = 5 := by
  rw [dist_coeff_zero_eq_coeffL1Norm]
  rw [norm_two_monomials _ _ (by
      intro h
      have he := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) h
      norm_num [Finsupp.single_apply, Finsupp.add_apply] at he)]
  norm_num

example (p : MvPolynomial ℕ+ ℚ) :
    dist (WithLp.toLp ((1 : NNReal) : ENNReal) p.coeff)
      (WithLp.toLp ((1 : NNReal) : ENNReal) (0 : (ℕ+ →₀ ℕ) →₀ ℚ)) =
      (coeffL1Norm p : ℝ) :=
  dist_coeff_zero_eq_coeffL1Norm p

#print axioms coeffL1Norm
#print axioms coeffL1Norm_eq_sum
#print axioms coeffL1Norm_nonneg
#print axioms coeffL1Norm_zero
#print axioms coeffL1Norm_add_le
#print axioms coeffL1Norm_sum_le
#print axioms coeffL1Norm_smul
#print axioms coeffL1Norm_monomial
#print axioms coeffL1Norm_monomial_le
#print axioms coeffL1Norm_mul_le
#print axioms dist_coeff_zero_eq_coeffL1Norm
