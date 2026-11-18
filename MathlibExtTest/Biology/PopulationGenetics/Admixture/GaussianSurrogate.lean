/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Admixture.GaussianSurrogate

/-!
# Tests for the Gaussian drift surrogate

The examples evaluate the one-population and two-population cases and the zero-variance
endpoint.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.GaussianSurrogate

open MathlibExt.Biology.PopulationGenetics.Admixture

open MathlibExt.Biology.PopulationGenetics.Admixture

/-- One population, one edge of length `1`, root mean `1/2`: `Σ = 1`. -/
example : driftCov (P := Unit) (E := Unit) (fun _ _ => 1) (fun _ => 1) () () = 1 := by
  simp [driftCov_apply]

/-- Acceptance 1, evaluated: `P(Z < 0) > 0` for root mean `1/2` and one unit edge. -/
example : 0 < gaussianSurrogate (P := Unit) (E := Unit) (1 / 2) (fun _ _ => 1) (fun _ => 1)
    {x | x () < 0} :=
  gaussianSurrogate_coord_neg_pos _ _ (by simp [driftCov_apply])

/-- A two-population tree (shared edge `0`, private edges `1`, `2`): `Σ_00 = ℓ₀ + ℓ₁ > 0` as soon
as the shared edge has positive length, even if the private edge has length `0`. -/
example : 0 < gaussianSurrogate (P := Fin 2) (E := Fin 3) (1 / 2)
    (fun X e => if e = 0 ∨ e = X.succ then 1 else 0) ![1, 0, 1] {x | x 0 < 0} := by
  refine gaussianSurrogate_coord_neg_pos _ _ ?_
  simp [driftCov_apply, Fin.sum_univ_succ]

/-- The f2 of that surrogate is the tree distance `ℓ₁ + ℓ₂ = 1`, as for any drift model. -/
example : f2 (gaussianSurrogate (P := Fin 2) (E := Fin 3) (1 / 2)
    (fun X e => if e = 0 ∨ e = X.succ then 1 else 0) ![1, 0, 1]) coordFreq 0 1 = 1 := by
  rw [f2_eq_f4, f4_gaussianSurrogate]
  simp [Fin.sum_univ_succ]

/-- Zero-length edge: `Σ = 0` and `Z = m` almost surely (here `m = 1/2 ∈ [0, 1]`). -/
example : ∀ᵐ x ∂(gaussianSurrogate (P := Unit) (E := Unit) (1 / 2) (fun _ _ => 1) (fun _ => 0)),
    x () = 1 / 2 :=
  gaussianSurrogate_coord_ae_eq _ _ (by simp [driftCov_apply])


#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.f4_gaussianSurrogate_eq
#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.gaussianSurrogate_coord_neg_pos
#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.gaussianSurrogate_coord_ae_eq

end MathlibExtTest.Biology.PopulationGenetics.Admixture.GaussianSurrogate
