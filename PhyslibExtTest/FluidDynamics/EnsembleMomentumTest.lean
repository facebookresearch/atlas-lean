/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.EnsembleMomentum

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.FluidDynamics.EnsembleMomentum`

Two equally likely flow realizations with velocities `(2, 1)` and `(0, -1)`, constant in space and
time:

- they form a probability space, the mean velocity is `(1, 0)`, and every entry of the Reynolds
  stress is `1`, the shear entries included;
- through `reynoldsStress_posSemidef` the stress is positive semidefinite; its quadratic form is
  `4` along `(1, 1)` and `0` along `(1, -1)`, so it is nonzero and singular;
- with zero stress and body force the ensemble meets every hypothesis of `mean_momentum`;
- each realization is divergence free, so `divergence_ensembleMean_eq_zero` makes the mean
  velocity divergence free.

An ensemble whose realizations all equal one field `U` has mean `U` and zero Reynolds stress
(`reynoldsStress_eq_zero_of_ae_eq`). The escaping profile on `(0, 1]` has realizations with
derivative `0` at `s = 0`, a mean with derivative `1` there, and derivatives that no integrable
function dominates near `0` (`escapingProfile_interchange_fails`).
-/

@[expose] public section

namespace PhyslibExtTest.FluidDynamics.EnsembleMomentum

open MeasureTheory ProbabilityTheory
open _root_.FluidDynamics.EnsembleMomentum
open ControlVolumes (momentumFlux)
open MathlibExt.Probability.FokkerPlanck (divergence)

/-- Fixture: two equally likely flow realizations, `true` and `false`. -/
noncomputable def twoScenarioMeasure : Measure Bool :=
  (2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)

/-- Fixture: in the realization `true` the velocity is `(2, 1)` everywhere, in `false` it is
`(0, -1)`. -/
noncomputable def twoScenarioVelocity (b : Bool) (_τ : ℝ) (_y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  if b then ![2, 1] else ![0, -1]

/-- Integral over the two equally likely realizations. -/
private lemma integral_twoScenario (g : Bool → ℝ) :
    ∫ b, g b ∂twoScenarioMeasure = (g true + g false) / 2 := by
  rw [twoScenarioMeasure, integral_smul_measure,
    integral_add_measure (Integrable.of_finite) (Integrable.of_finite), integral_dirac,
    integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- Fixture, a nonzero two-scenario fluctuation covariance: the two realizations form a
probability space, the mean velocity is `(1, 0)`, the fluctuations are `±(1, 1)`, and every
entry of the Reynolds stress is `1`, the shear entries included. -/
lemma twoScenario_reynoldsStress (τ : ℝ) (y : Fin 2 → ℝ) :
    IsProbabilityMeasure twoScenarioMeasure ∧
      ensembleMean twoScenarioMeasure twoScenarioVelocity τ y = ![1, 0] ∧
      ∀ j i, reynoldsStress twoScenarioMeasure twoScenarioVelocity τ y j i = 1 := by
  have hprob : IsProbabilityMeasure twoScenarioMeasure := by
    constructor
    simp only [twoScenarioMeasure, Measure.smul_apply, Measure.add_apply, measure_univ,
      smul_eq_mul]
    rw [one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have hmean : ensembleMean twoScenarioMeasure twoScenarioVelocity τ y = ![1, 0] := by
    funext i
    simp only [ensembleMean, integral_twoScenario, twoScenarioVelocity]
    fin_cases i <;> norm_num
  refine ⟨hprob, hmean, fun j i => ?_⟩
  simp only [reynoldsStress, covariance, integral_twoScenario, twoScenarioVelocity]
  fin_cases j <;> fin_cases i <;> norm_num

instance : IsProbabilityMeasure twoScenarioMeasure := (twoScenario_reynoldsStress 0 0).1

-- The two-scenario Reynolds stress through `reynoldsStress_posSemidef`: the quadratic form is
-- nonnegative for every vector, `4` along `(1, 1)` and `0` along `(1, -1)`.
example (τ : ℝ) (y a : Fin 2 → ℝ) :
    0 ≤ ∑ j, ∑ i, a j * a i * reynoldsStress twoScenarioMeasure twoScenarioVelocity τ y j i ∧
      ∑ j, ∑ i, (![1, 1] : Fin 2 → ℝ) j * (![1, 1] : Fin 2 → ℝ) i *
        reynoldsStress twoScenarioMeasure twoScenarioVelocity τ y j i = 4 ∧
      ∑ j, ∑ i, (![1, -1] : Fin 2 → ℝ) j * (![1, -1] : Fin 2 → ℝ) i *
        reynoldsStress twoScenarioMeasure twoScenarioVelocity τ y j i = 0 := by
  have hR := (twoScenario_reynoldsStress τ y).2.2
  refine ⟨reynoldsStress_posSemidef (fun _ => MemLp.of_discrete) a, ?_, ?_⟩ <;>
    simp only [Fin.sum_univ_two, hR] <;> norm_num

-- Non-vacuity of `mean_momentum`: the two-scenario ensemble with zero stress and body force meets
-- every hypothesis (`L²` velocity, integrable stress, differentiability, measurable derivatives,
-- the bound `B = 0` and the local law), so the mean momentum equation holds for it.
example (ρ t : ℝ) (x : Fin 2 → ℝ) (j : Fin 2) :
    deriv (fun τ => ρ * ensembleMean twoScenarioMeasure twoScenarioVelocity τ x j) t +
        divergence (momentumFlux (fun _ => ρ)
          (ensembleMean twoScenarioMeasure twoScenarioVelocity t)
          (ensembleMeanStress twoScenarioMeasure (fun _ _ _ _ _ => (0 : ℝ)) t) j) x =
      (∫ _ω, (0 : ℝ) ∂twoScenarioMeasure) -
        ρ * divergence
          (fun y i => reynoldsStress twoScenarioMeasure twoScenarioVelocity t y j i) x :=
  mean_momentum (μ := twoScenarioMeasure) (ρ := ρ) (t := t) (ε := 1) (x := x)
    (u := twoScenarioVelocity) (f := fun _ _ _ _ => 0) (σ := fun _ _ _ _ _ => 0)
    (B := fun _ => 0) one_pos (fun _ _ _ => MemLp.of_discrete) (fun _ _ _ => integrable_const _)
    (Filter.Eventually.of_forall fun _ _ _ _ => by unfold twoScenarioVelocity; fun_prop)
    (Filter.Eventually.of_forall fun _ _ _ _ => by unfold twoScenarioVelocity; fun_prop)
    (Filter.Eventually.of_forall fun _ _ _ _ _ => by fun_prop)
    (fun _ => StronglyMeasurable.of_discrete.aestronglyMeasurable)
    (fun _ => StronglyMeasurable.of_discrete.aestronglyMeasurable)
    (fun _ _ => StronglyMeasurable.of_discrete.aestronglyMeasurable) (integrable_const _)
    (Filter.Eventually.of_forall fun _ => ⟨fun _ _ _ => by simp [twoScenarioVelocity],
      fun _ _ _ _ => by simp [twoScenarioVelocity]⟩)
    (Filter.Eventually.of_forall fun _ _ => by
      simp [twoScenarioVelocity, momentumFlux, divergence,
        MathlibExt.Probability.FokkerPlanck.pderiv]) j

-- Mean incompressibility through `divergence_ensembleMean_eq_zero`: each two-scenario
-- realization is constant in space, hence divergence free, and so is the mean velocity.
example (t : ℝ) (x : Fin 2 → ℝ) :
    divergence (ensembleMean twoScenarioMeasure twoScenarioVelocity t) x = 0 :=
  divergence_ensembleMean_eq_zero (μ := twoScenarioMeasure) (ε := 1) (B := fun _ => 0) one_pos
    (fun _ _ => Integrable.of_finite)
    (Filter.Eventually.of_forall fun _ _ _ _ => by unfold twoScenarioVelocity; fun_prop)
    (fun _ => StronglyMeasurable.of_discrete.aestronglyMeasurable) (integrable_const _)
    (Filter.Eventually.of_forall fun _ _ _ _ => by simp [twoScenarioVelocity])
    (Filter.Eventually.of_forall fun _ => by
      simp [twoScenarioVelocity, divergence, MathlibExt.Probability.FokkerPlanck.pderiv])

-- Zero fluctuation through `reynoldsStress_eq_zero_of_ae_eq`: when both realizations equal one
-- field `U`, the mean is `U` and the Reynolds stress and its divergence vanish.
example (U : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) (τ : ℝ) (x y : Fin 2 → ℝ) (j : Fin 2) :
    ensembleMean twoScenarioMeasure (fun _ => U) τ y = U τ y ∧
      reynoldsStress twoScenarioMeasure (fun _ => U) τ y = 0 ∧
      divergence (fun y' i => reynoldsStress twoScenarioMeasure (fun _ => U) τ y' j i) x = 0 :=
  reynoldsStress_eq_zero_of_ae_eq (μ := twoScenarioMeasure) (u := fun _ => U) (U := U)
    (fun _ _ => Filter.Eventually.of_forall fun _ => rfl) τ x y j

-- Without domination the interchange fails: every realization of the escaping profile has
-- derivative `0` at `s = 0`, the ensemble mean has derivative `1` there, and no integrable
-- function dominates the derivatives near `0`.
example :
    (∀ ω : ℝ, HasDerivAt (fun s => escapingProfile s ω) 0 0) ∧
      HasDerivAt (fun s => ∫ ω in Set.Ioc (0 : ℝ) 1, escapingProfile s ω) 1 0 ∧
      ¬ ∃ ε > 0, ∃ B : ℝ → ℝ, Integrable B (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
        ∀ᵐ ω ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ∀ s ∈ Metric.ball (0 : ℝ) ε,
          ‖(3 * s ^ 2 / ω ^ 2 - 2 * s ^ 4 / ω ^ 3) * Real.exp (-s ^ 2 / ω)‖ ≤ B ω := by
  obtain ⟨-, hd, -, hG, hno⟩ := escapingProfile_interchange_fails
  exact ⟨fun ω => by simpa using hd ω 0, hG, hno⟩

end PhyslibExtTest.FluidDynamics.EnsembleMomentum
