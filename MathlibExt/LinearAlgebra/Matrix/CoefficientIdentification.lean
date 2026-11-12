/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Identification of regression coefficients

A design matrix `X` identifies the coefficient vector `β` of the linear mean `X *ᵥ β` exactly when
its columns are linearly independent (full column rank); a rank-deficient design admits two
different coefficient vectors with the same mean.

## i. Overview

`CoefficientsIdentified X` says that equal means force equal coefficients, i.e. that
`β ↦ X *ᵥ β` is injective; Mathlib's `Matrix.mulVec_injective_iff` turns this into linear
independence of the columns. Uniqueness of the least-squares solution of the normal equations
under full rank is `MathlibExt.Probability.FiniteProbability.eq_olsEstimator_iff` together with
`isUnit_transpose_mul_self_iff` and is not restated here.

## ii. Main results

* `MathlibExt.CoefficientIdentification.coefficientsIdentified_iff`
* `MathlibExt.CoefficientIdentification.exists_ne_mulVec_eq_of_not_linearIndependent`

## iii. References

* J. M. Wooldridge, *Introductory Econometrics*, assumption MLR.3 (no perfect collinearity).
-/

@[expose] public section

open Matrix

namespace MathlibExt.CoefficientIdentification

/-- The design `X` *identifies* the coefficients of the linear mean `β ↦ X *ᵥ β`: two
coefficient vectors with the same mean vector are equal. -/
def CoefficientsIdentified {m k : Type*} [Fintype k] (X : Matrix m k ℝ) : Prop :=
  ∀ β β' : k → ℝ, X *ᵥ β = X *ᵥ β' → β = β'

/-- **Identification iff full column rank.** -/
theorem coefficientsIdentified_iff {m k : Type*} [Fintype k] (X : Matrix m k ℝ) :
    CoefficientsIdentified X ↔ LinearIndependent ℝ X.col := by
  unfold CoefficientsIdentified
  exact Matrix.mulVec_injective_iff

/-- **Rank-deficient designs do not identify.** If the columns of `X` are linearly dependent,
two different coefficient vectors give the same mean. -/
theorem exists_ne_mulVec_eq_of_not_linearIndependent {m k : Type*} [Fintype k]
    {X : Matrix m k ℝ} (hX : ¬ LinearIndependent ℝ X.col) :
    ∃ β β' : k → ℝ, β ≠ β' ∧ X *ᵥ β = X *ᵥ β' := by
  rw [← coefficientsIdentified_iff] at hX
  unfold CoefficientsIdentified at hX
  push Not at hX
  obtain ⟨β, β', hEq, hNe⟩ := hX
  exact ⟨β, β', hNe, hEq⟩

end MathlibExt.CoefficientIdentification
