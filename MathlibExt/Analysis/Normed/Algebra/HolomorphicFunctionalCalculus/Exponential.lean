/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Normed.Algebra.HolomorphicFunctionalCalculus.PowerSeries
public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Exponential under the Riesz calculus

For any element `a` of a complete unital complex normed algebra, the Riesz
functional-calculus value of the entire scalar exponential germ is the
ordinary Banach-algebra exponential `exp(a)`. No commutativity or nonzero-
algebra assumption is imposed; the powers and norm used by the exponential
series are the original algebra operations and norm.

## References

John B. Conway, *A Course in Functional Analysis*, second edition, Graduate Texts in
Mathematics 96, Springer (1990), Chapter VII, §4, pp. 199–204, Theorem 4.7 on the
Riesz functional calculus and its scalar power-series formula. The exponential
identity is its entire power-series specialization.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe uA

variable {A : Type uA} [NormedRing A] [NormedAlgebra ℂ A]
  [CompleteSpace A]

/-- **The Riesz calculus sends the scalar exponential to the algebra exponential.** Let `A` be
a complete unital complex normed algebra, `a∈A`, and `S=spectrum ℂ a`. The entire scalar
function `z↦exp(z)` gives a holomorphic germ at `S`. Its Riesz value is `exp(a)=∑ a^n/n!`,
the ordinary Banach-algebra exponential using the original multiplication and norm.
Equivalently, `rieszFunctionalCalculus a [exp]=NormedSpace.exp a`. This holds for every
`a`, including in noncommutative and zero algebras. -/
theorem rieszFunctionalCalculus_exp (a : A) :
    rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofFunction a NormedSpace.exp
          (fun z _ => NormedSpace.exp_analytic z)) =
      NormedSpace.exp a := by
  let c : ℕ → ℂ := fun n => (Nat.factorial n : ℂ)⁻¹
  have hradius :
      (FormalMultilinearSeries.ofScalars ℂ c).radius = ⊤ := by
    rw [← NormedSpace.expSeries_eq_ofScalars ℂ ℂ,
      NormedSpace.expSeries_radius_eq_top]
  have hfinite : spectralRadius ℂ a < (⊤ : ENNReal) := by
    have hle : spectralRadius ℂ a ≤ (‖a‖₊ : ENNReal) :=
      spectralRadius_le_nnNorm a
    exact hle.trans_lt ENNReal.coe_lt_top
  have h : spectralRadius ℂ a <
      (FormalMultilinearSeries.ofScalars ℂ c).radius := by
    rw [hradius]
    exact hfinite
  have hRiesz : HasSum (fun n : ℕ => c n • a ^ n)
      (rieszFunctionalCalculus a
        (HolomorphicNearSpectrum.ofScalars a c h)) :=
    hasSum_rieszFunctionalCalculus_ofScalars a c h
  have hExp : HasSum (fun n : ℕ => c n • a ^ n)
      (NormedSpace.exp a) := by
    simpa only [c] using
      (NormedSpace.exp_series_hasSum_exp' (𝔸 := A) a)
  have hvalue :
      rieszFunctionalCalculus a
          (HolomorphicNearSpectrum.ofScalars a c h) =
        NormedSpace.exp a :=
    hRiesz.unique hExp
  have hseries :
      NormedSpace.expSeries ℂ ℂ =
        FormalMultilinearSeries.ofScalars ℂ c := by
    simpa only [c] using
      (NormedSpace.expSeries_eq_ofScalars ℂ ℂ)
  have hfun :
      (FormalMultilinearSeries.ofScalars ℂ c).sum =
        (NormedSpace.exp : ℂ → ℂ) := by
    rw [← hseries]
    exact (NormedSpace.exp_eq_expSeries_sum (𝔸 := ℂ) ℂ).symm
  have hgerm :
      HolomorphicNearSpectrum.ofFunction a NormedSpace.exp
          (fun z _ => NormedSpace.exp_analytic z) =
        HolomorphicNearSpectrum.ofScalars a c h := by
    apply Subtype.ext
    change
      ((NormedSpace.exp : ℂ → ℂ) : SpectrumGerm a) =
        (((FormalMultilinearSeries.ofScalars ℂ c).sum) : SpectrumGerm a)
    rw [hfun]
  rw [hgerm]
  exact hvalue

#print axioms rieszFunctionalCalculus_exp
