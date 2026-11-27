/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.NumericalRangeRationalDenominators

namespace MathlibExtTest.Analysis.InnerProductSpace.NumericalRangeRationalDenominators

open MathlibExt.Analysis.InnerProductSpace.ToeplitzHausdorffWanted

private noncomputable def imaginaryIdentity : ℂ →L[ℂ] ℂ :=
  Complex.I • (1 : ℂ →L[ℂ] ℂ)

private noncomputable def polePolynomial : Polynomial ℂ :=
  Polynomial.X + Polynomial.C Complex.I

private noncomputable def rationalMatrix : Matrix (Fin 1) (Fin 1) (RatFunc ℂ) :=
  fun _ _ => (algebraMap (Polynomial ℂ) (RatFunc ℂ) 1) /
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) polePolynomial)

private theorem rationalMatrix_denom (i j : Fin 1) :
    (rationalMatrix i j).denom = polePolynomial := by
  have hm : polePolynomial.Monic := Polynomial.monic_X_add_C _
  change ((algebraMap (Polynomial ℂ) (RatFunc ℂ) 1) /
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) polePolynomial)).denom = polePolynomial
  rw [RatFunc.denom_div _ hm.ne_zero]
  simp [hm.leadingCoeff]

private theorem imaginaryIdentity_range : numericalRange imaginaryIdentity = {-Complex.I} := by
  have hinner (x : ℂ) (hx : ‖x‖ = 1) :
      inner ℂ (imaginaryIdentity x) x = -Complex.I := by
    change inner ℂ (Complex.I • x) x = -Complex.I
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K, hx]
    simp
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Set.mem_singleton_iff.mpr (hinner x hx)
  · intro hz
    exact ⟨1, norm_one, (hinner 1 norm_one).trans (Set.mem_singleton_iff.mp hz).symm⟩

private theorem noPoles : ∀ z ∈ star '' closure (numericalRange imaginaryIdentity),
    ∀ i j : Fin 1, (rationalMatrix i j).denom.eval z ≠ 0 := by
  intro z hz i j
  have hzi : z = Complex.I := by simpa [imaginaryIdentity_range] using hz
  rw [hzi, rationalMatrix_denom]
  simp only [polePolynomial, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    ← two_mul]
  exact mul_ne_zero two_ne_zero Complex.I_ne_zero

/-- The pole at `-I` is outside the conjugated closed numerical range `{I}`. -/
private theorem denominatorAtImaginaryIdentity :
    IsUnit (Polynomial.aeval imaginaryIdentity (rationalMatrix 0 0).denom) :=
  ContinuousLinearMap.isUnit_aeval_ratFunc_denom_of_no_poles_on_numericalRange
    imaginaryIdentity rationalMatrix noPoles 0 0

/-- Requiring pole avoidance on both ranges would exclude this invertible case. -/
private theorem not_noPolesOnBothRanges :
    ¬ (∀ z ∈ closure (numericalRange imaginaryIdentity) ∪
        star '' closure (numericalRange imaginaryIdentity),
      ∀ i j : Fin 1, (rationalMatrix i j).denom.eval z ≠ 0) := by
  intro h
  have hz : -Complex.I ∈ closure (numericalRange imaginaryIdentity) :=
    subset_closure (by simp [imaginaryIdentity_range])
  apply h (-Complex.I) (Or.inl hz) 0 0
  rw [rationalMatrix_denom]
  simp [polePolynomial]

end MathlibExtTest.Analysis.InnerProductSpace.NumericalRangeRationalDenominators
