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
attenuation matrix `A` (rays and attenuation cells may have
different index types), the independent-Poisson count-vector law with
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

/-- **Photon attenuation rate identification.** For a finite ray set
`ι`, positive source intensities `I0 j > 0` and a real attenuation
matrix `A`, the transmitted rates `I0 j * exp (-(A *ᵥ x) j)` agree at
two attenuation vectors `x`, `x'` in every ray if and only if
`A *ᵥ x = A *ᵥ x'`. Positive intensity in each ray is essential: a ray
with `I0 j = 0` carries no information about `(A *ᵥ x) j`. This is
the rate-level core of the independent-Poisson photon law; the law
itself is obtained from it with Poisson rate injectivity. -/
lemma photon_rate_agree_iff {ι κ : Type*} [Fintype κ]
    {I0 : ι → ℝ} (hI0 : ∀ j, 0 < I0 j) {A : Matrix ι κ ℝ} {x x' : κ → ℝ} :
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
noncomputable def transmittedRate {ι κ : Type*} [Fintype κ] (I0 : ι → ℝ≥0) (A : Matrix ι κ ℝ)
    (x : κ → ℝ) (j : ι) : ℝ≥0 :=
  I0 j * (Real.exp (-(A *ᵥ x) j)).toNNReal

/-- The independent-Poisson photon count law at attenuation `x`. -/
noncomputable def photonLaw {ι κ : Type*} [Fintype ι] [Fintype κ] (I0 : ι → ℝ≥0) (A : Matrix ι κ ℝ)
    (x : κ → ℝ) : MeasureTheory.Measure (ι → ℕ) :=
  MeasureTheory.Measure.pi fun j => ProbabilityTheory.poissonMeasure (transmittedRate I0 A x j)

/-- The photon law unfolded: the product of its Poisson rates. -/
lemma photonLaw_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (I0 : ι → ℝ≥0) (A : Matrix ι κ ℝ)
    (x : κ → ℝ) :
    photonLaw I0 A x = MeasureTheory.Measure.pi
      fun j => ProbabilityTheory.poissonMeasure (transmittedRate I0 A x j) := rfl

/-- The transmitted rate as a real number. -/
lemma transmittedRate_coe {ι κ : Type*} [Fintype κ] (I0 : ι → ℝ≥0) (A : Matrix ι κ ℝ)
    (x : κ → ℝ) (j : ι) :
    ((transmittedRate I0 A x j : ℝ≥0) : ℝ) =
      (I0 j : ℝ) * Real.exp (-(A *ᵥ x) j) := by
  simp [transmittedRate, Real.coe_toNNReal _ (Real.exp_nonneg _)]

/-- **Photon law identification.** The independent-Poisson count laws
at `x` and `x'` agree if and only if `A *ᵥ x = A *ᵥ x'`. -/
lemma photon_law_agree_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    {I0 : ι → ℝ≥0} (hI0 : ∀ j, 0 < I0 j) {A : Matrix ι κ ℝ} {x x' : κ → ℝ} :
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

/-- **Identification on an admissible set.** With positive source
intensities, the photon law is injective on an admissible set `D`
exactly when the attenuation action `A.mulVec` is injective on
`D`. -/
lemma photon_identify_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    {I0 : ι → ℝ≥0} (hI0 : ∀ j, 0 < I0 j) (A : Matrix ι κ ℝ)
    (D : Set (κ → ℝ)) :
    Set.InjOn (fun x => photonLaw I0 A x) D ↔ Set.InjOn (A *ᵥ ·) D := by
  constructor
  · intro h x hx y hy hxy
    exact h hx hy ((photon_law_agree_iff hI0).mpr hxy)
  · intro h x hx y hy hxy
    exact h hx hy ((photon_law_agree_iff hI0).mp hxy)

/-- **Rank deficiency defeats photon-law identification.** If
`A *ᵥ v = 0` for `v ≠ 0` and both `x` and `x + v` are admissible,
the photon law is not injective on `D`. -/
lemma photon_not_identify_of_kernel {ι κ : Type*} [Fintype ι] [Fintype κ]
    {I0 : ι → ℝ≥0} (A : Matrix ι κ ℝ)
    (D : Set (κ → ℝ)) {v x : κ → ℝ} (hv : v ≠ 0) (hk : A *ᵥ v = 0)
    (hx : x ∈ D) (hxv : x + v ∈ D) :
    ¬ Set.InjOn (fun x => photonLaw I0 A x) D := by
  intro hInj
  have hne : x ≠ x + v := by
    intro h
    apply hv
    have h2 : x + 0 = x + v := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have hmap : A *ᵥ (x + v) = A *ᵥ x := by
    rw [Matrix.mulVec_add, hk, add_zero]
  have hlaw : photonLaw I0 A (x + v) = photonLaw I0 A x := by
    unfold photonLaw transmittedRate
    rw [hmap]
  exact hne (hInj hx hxv hlaw.symm)


/-- Equal design measurements give equal transmitted rates. -/
lemma transmittedRate_eq_of_mulVec_eq {ι κ : Type*} [Fintype κ]
    (I0 : ι → ℝ≥0) (A : Matrix ι κ ℝ) (x y : κ → ℝ)
    (h : A *ᵥ x = A *ᵥ y) (j : ι) :
    transmittedRate I0 A x j = transmittedRate I0 A y j := by
  unfold transmittedRate
  rw [h]

end PhyslibExt.BiomedicalImaging.PhotonObservation
