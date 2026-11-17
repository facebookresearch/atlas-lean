/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.PoissonKernel
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Matrix.Mul

/-!
# Photon observation law

## i. Overview

For a finite ray set, positive source intensities `I0 j > 0` and a real
attenuation matrix `A`, the independent-Poisson count-vector law with
rates `I0 j * exp (-(A *ᵥ x) j)` (built from
`ProbabilityTheory.piPoissonKernel`) determines the attenuation
exactly up to the action of `A`: the laws at `x` and `x'` agree if and
only if `A *ᵥ x = A *ᵥ x'`. Independence is a declared observation
assumption of the model.

## ii. Key results

* `photon_rate_agree_iff`: the transmitted rates agree in every ray
  if and only if `A *ᵥ x = A *ᵥ x'`.
* `photonLaw` and `photon_law_agree_iff`: the same identification for
  the independent-Poisson count-vector law itself.

## iii. Table of contents

* A. Rate identification.
* B. Law identification.

## iv. References

* The Poisson kernel and its rate injectivity are
  `MathlibExt.Probability.Distributions.PoissonKernel`
  (`piPoissonKernel`, `pi_poissonMeasure_injective`).

-/

@[expose] public section

open Real Matrix ProbabilityTheory
open scoped NNReal

namespace PhyslibExt.BiomedicalImaging.PhotonObservation

/-! ## A. Rate identification. -/

set_option linter.unusedDecidableInType false in
/-- **Photon attenuation rate identification.** For a finite ray set
`ι`, positive source intensities `I0 j > 0` and a real attenuation
matrix `A`, the transmitted rates `I0 j * exp (-(A *ᵥ x) j)` agree at
two attenuation vectors `x`, `x'` in every ray if and only if
`A *ᵥ x = A *ᵥ x'`. Positive intensity in each ray is essential: a ray
with `I0 j = 0` carries no information about `(A *ᵥ x) j`. This is
the rate-level core of the independent-Poisson photon law; the law
itself is obtained from it with Poisson rate injectivity. -/
lemma photon_rate_agree_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {I0 : ι → ℝ} (hI0 : ∀ j, 0 < I0 j) {A : Matrix ι ι ℝ} {x x' : ι → ℝ} :
    (∀ j, I0 j * Real.exp (-(A *ᵥ x) j) = I0 j * Real.exp (-(A *ᵥ x') j)) ↔
    A *ᵥ x = A *ᵥ x' := by
  constructor
  · intro h
    funext j
    have hne : I0 j ≠ 0 := ne_of_gt (hI0 j)
    have hexp : Real.exp (-(A *ᵥ x) j) = Real.exp (-(A *ᵥ x') j) :=
      mul_left_cancel₀ hne (h j)
    have hneg : -(A *ᵥ x) j = -(A *ᵥ x') j := Real.exp_injective hexp
    exact neg_inj.mp hneg
  · intro h j
    rw [h]

/-! ## B. Law identification. -/

/-- The transmitted Poisson rate in ray `j`: source intensity times
the attenuation factor, as a nonnegative real. -/
noncomputable def transmittedRate {ι : Type*} [Fintype ι] (I0 : ι → ℝ≥0) (A : Matrix ι ι ℝ)
    (x : ι → ℝ) (j : ι) : ℝ≥0 :=
  I0 j * (Real.exp (-(A *ᵥ x) j)).toNNReal

/-- The independent-Poisson photon count law at attenuation `x`. -/
noncomputable def photonLaw {ι : Type*} [Fintype ι] (I0 : ι → ℝ≥0) (A : Matrix ι ι ℝ)
    (x : ι → ℝ) : MeasureTheory.Measure (ι → ℕ) :=
  MeasureTheory.Measure.pi fun j => ProbabilityTheory.poissonMeasure (transmittedRate I0 A x j)

/-- The photon law unfolded: the product of its Poisson rates. -/
theorem photonLaw_eq {ι : Type*} [Fintype ι] (I0 : ι → ℝ≥0) (A : Matrix ι ι ℝ)
    (x : ι → ℝ) :
    photonLaw I0 A x = MeasureTheory.Measure.pi
      fun j => ProbabilityTheory.poissonMeasure (transmittedRate I0 A x j) := rfl

/-- The transmitted rate as a real number. -/
theorem transmittedRate_coe {ι : Type*} [Fintype ι] (I0 : ι → ℝ≥0) (A : Matrix ι ι ℝ)
    (x : ι → ℝ) (j : ι) :
    ((transmittedRate I0 A x j : ℝ≥0) : ℝ) =
      (I0 j : ℝ) * Real.exp (-(A *ᵥ x) j) := by
  simp [transmittedRate, Real.coe_toNNReal _ (Real.exp_nonneg _)]

set_option linter.unusedDecidableInType false in
/-- **Photon law identification.** The independent-Poisson count laws
at `x` and `x'` agree if and only if `A *ᵥ x = A *ᵥ x'`. -/
theorem photon_law_agree_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {I0 : ι → ℝ≥0} (hI0 : ∀ j, 0 < I0 j) {A : Matrix ι ι ℝ} {x x' : ι → ℝ} :
    photonLaw I0 A x = photonLaw I0 A x' ↔ A *ᵥ x = A *ᵥ x' := by
  constructor
  · intro h
    have hr : transmittedRate I0 A x = transmittedRate I0 A x' :=
      ProbabilityTheory.pi_poissonMeasure_injective h
    apply (photon_rate_agree_iff (I0 := fun j => ((I0 j : ℝ≥0) : ℝ))
      (fun j => by exact_mod_cast hI0 j)).mp
    intro j
    have hj := congrFun hr j
    have h2 := congrArg (fun r : ℝ≥0 => (r : ℝ)) hj
    have e1 := transmittedRate_coe I0 A x j
    have e2 := transmittedRate_coe I0 A x' j
    rw [← e1, ← e2]
    exact h2
  · intro h
    unfold photonLaw transmittedRate
    rw [h]

end PhyslibExt.BiomedicalImaging.PhotonObservation
