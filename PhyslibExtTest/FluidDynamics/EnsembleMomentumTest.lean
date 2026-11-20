/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.EnsembleMomentum

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
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
- with zero stress and body force the ensemble meets every hypothesis of `mean_momentum` (the
  velocities are constant, so every term of that equation is `0`);
- each realization is divergence free, so `divergence_ensembleMean_eq_zero` makes the mean
  velocity divergence free.

A spatially varying ensemble: two equally likely steady realizations `u = (1 ± y₀, y₀ ± 3)`, the
stress whose only nonzero entry is `σ₁₀ = y₀`, and in each realization the body force its local
law at density `2` requires. The mean velocity is `(1, y₀)` and the Reynolds stress is
`(y₀, 3) ⊗ (y₀, 3)`. At the point `(2, 5)`, direct computation from the definitions gives the
mean-flow side `0` and `1` for the components `0` and `1`, the mean body force `8` and `7`, and the
nonzero Reynolds correction `2 * div 𝔼[u'ⱼ u']` equal to `8` and `6`; `mean_momentum`, whose
hypotheses all hold for this ensemble, relates them by `0 = 8 - 8` and `1 = 7 - 6`.

An ensemble whose realizations all equal one field `U` has mean `U` and zero Reynolds stress
(`reynoldsStress_eq_zero_of_ae_eq`). The escaping profile on `(0, 1]` has realizations with
derivative `0` at `s = 0`, a mean with derivative `1` there, and derivatives that no integrable
function dominates near `0` (`escapingProfile_interchange_fails`).

The eddy-viscosity closure. On the simple shear `U = (2 y, 0, 0)`, with `S₀₁ = S₁₀ = 1`, the model
has the down-gradient shear entry `Rm₀₁ = -2` for `νt = 1` and extracts `P = 4` for every `k`, so
`meanFlowExtraction_modeledReynoldsStress` gives `‖S‖² = 2`; every `νt ≥ 0` extracts a nonnegative
amount from it. On the plane strain `diag(1, -1, 0)`, `νt = -1` returns energy to the mean flow
(`meanFlowExtraction_modeledReynoldsStress_nonneg_iff`); at `k = νt = 1` the model has the first
normal stress `-4/3` and trace `2 = 2 k` (`modeledReynoldsStress_planeStrain`), so through
`reynoldsStress_posSemidef` it is not the Reynolds stress of any ensemble with `L²` velocity
components, while `νt = 1/4` gives a positive semidefinite model. A negative eddy viscosity extracts
nothing from the zero strain (`meanFlowExtraction_nonneg_converse_fails`). On the model domain the
closure is Hermitian, and the domain contains a point where it is not positive semidefinite
(`modeledReynoldsStress_realizability_fails`).
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

/-! ### A spatially varying ensemble -/

/-- `±1` for the two realizations of the spatially varying ensemble. -/
noncomputable def shearSign (b : Bool) : ℝ := if b then 1 else -1

/-- Velocity of realization `b` of the spatially varying ensemble, steady and varying in the first
coordinate: `(1 + s * y₀, y₀ + 3 * s)` with `s = shearSign b`. The mean is `(1, y₀)` and the
fluctuations are `±(y₀, 3)`. -/
noncomputable def shearVelocity (b : Bool) (_τ : ℝ) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![1 + shearSign b * y 0, y 0 + 3 * shearSign b]

/-- Stress of every realization: the traction component `σ₁₀ = y₀` (component `1` on the surface
of normal `e₀`) and all other entries `0`, so the stress is not symmetric. -/
noncomputable def shearStress (_b : Bool) (_τ : ℝ) (y : Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![0, 0], ![y 0, 0]]

/-- Body force of realization `b`, defined from its local momentum law at density `2`. -/
noncomputable def shearForce (b : Bool) (t : ℝ) (y : Fin 2 → ℝ) : Fin 2 → ℝ := fun j =>
  deriv (fun τ => 2 * shearVelocity b τ y j) t +
    divergence (momentumFlux (fun _ => 2) (shearVelocity b t) (shearStress b t) j) y

/-- The point `x = (2, 5)` where the spatially varying ensemble is checked. -/
def shearPoint : Fin 2 → ℝ := ![2, 5]

private lemma pderiv_quad (α β γ : ℝ) (i : Fin 2) (x : Fin 2 → ℝ) :
    MathlibExt.Probability.FokkerPlanck.pderiv i
        (fun y : Fin 2 → ℝ => α * y 0 ^ 2 + β * y 0 + γ) x =
      (2 * α * x 0 + β) * (Pi.single i (1 : ℝ) : Fin 2 → ℝ) 0 := by
  have hp : HasFDerivAt (fun y : Fin 2 → ℝ => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) x :=
    hasFDerivAt_apply 0 x
  have hF : HasFDerivAt (fun y : Fin 2 → ℝ => α * y 0 ^ 2 + β * y 0 + γ)
      (α • (2 • x 0 ^ (2 - 1)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
        β • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) x :=
    (((hp.pow 2).const_mul α).add (hp.const_mul β)).add_const γ
  rw [MathlibExt.Probability.FokkerPlanck.pderiv, hF.fderiv]
  fin_cases i <;> simp
  ring

/-- The divergence of a plane field whose components are quadratics in the first coordinate. -/
private lemma divergence_quad (a b c : Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    divergence (fun y i => a i * y 0 ^ 2 + b i * y 0 + c i) x = 2 * a 0 * x 0 + b 0 := by
  simp [MathlibExt.Probability.FokkerPlanck.divergence, Fin.sum_univ_two, pderiv_quad]

private lemma shear_mean (τ : ℝ) (y : Fin 2 → ℝ) :
    ensembleMean twoScenarioMeasure shearVelocity τ y = ![1, y 0] := by
  funext i
  change ∫ b, shearVelocity b τ y i ∂twoScenarioMeasure = ![1, y 0] i
  rw [integral_twoScenario]
  fin_cases i <;> simp [shearVelocity, shearSign] <;> ring

private lemma shear_meanStress (τ : ℝ) (y : Fin 2 → ℝ) :
    ensembleMeanStress twoScenarioMeasure shearStress τ y = ![![0, 0], ![y 0, 0]] := by
  funext j i
  change ∫ b, shearStress b τ y j i ∂twoScenarioMeasure = ![![0, 0], ![y 0, 0]] j i
  rw [integral_twoScenario]
  simp only [shearStress]
  ring

private lemma shear_reynolds (τ : ℝ) (y : Fin 2 → ℝ) (j i : Fin 2) :
    reynoldsStress twoScenarioMeasure shearVelocity τ y j i = ![y 0, 3] j * ![y 0, 3] i := by
  simp only [reynoldsStress, covariance, integral_twoScenario, shearVelocity, shearSign]
  fin_cases j <;> fin_cases i <;> simp <;> ring

private lemma contDiff_shearVelocity (b : Bool) (τ : ℝ) (i : Fin 2) :
    ContDiff ℝ 1 (fun y => shearVelocity b τ y i) := by
  have h0 : ContDiff ℝ 1 (fun y : Fin 2 → ℝ => y 0) :=
    contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0
  fin_cases i
  · exact contDiff_const.add (contDiff_const.mul h0)
  · exact h0.add contDiff_const

private lemma contDiff_shearStress (b : Bool) (τ : ℝ) (j i : Fin 2) :
    ContDiff ℝ 1 (fun y => shearStress b τ y j i) := by
  have h0 : ContDiff ℝ 1 (fun y : Fin 2 → ℝ => y 0) :=
    contDiff_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0
  fin_cases j <;> fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · exact h0
  · exact contDiff_const

private lemma exists_bound_fderiv {F : (Fin 2 → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) (x : Fin 2 → ℝ) :
    ∃ C, ∀ y ∈ Metric.ball x 1, ‖fderiv ℝ F y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn
    (hF.continuous_fderiv (by simp)).continuousOn
  exact ⟨C, fun y hy => hC y (Metric.ball_subset_closedBall hy)⟩

/-- `mean_momentum` for the spatially varying ensemble: every hypothesis holds, with the bound
on the derivatives from compactness of the closed unit ball around the point. -/
private lemma shear_mean_momentum (t : ℝ) (j : Fin 2) :
    deriv (fun τ => 2 * ensembleMean twoScenarioMeasure shearVelocity τ shearPoint j) t +
        divergence (momentumFlux (fun _ => 2) (ensembleMean twoScenarioMeasure shearVelocity t)
          (ensembleMeanStress twoScenarioMeasure shearStress t) j) shearPoint =
      (∫ ω, shearForce ω t shearPoint j ∂twoScenarioMeasure) -
        2 * divergence
          (fun y i => reynoldsStress twoScenarioMeasure shearVelocity t y j i) shearPoint := by
  have hC : ∀ k : Bool × Fin 2 × Fin 2, ∃ C, ∀ y ∈ Metric.ball shearPoint 1,
      ‖fderiv ℝ (fun y' => shearVelocity k.1 t y' k.2.2) y‖ ≤ C ∧
        ‖fderiv ℝ (fun y' => shearVelocity k.1 t y' k.2.1 * shearVelocity k.1 t y' k.2.2) y‖ ≤ C ∧
        ‖fderiv ℝ (fun y' => shearStress k.1 t y' k.2.1 k.2.2) y‖ ≤ C := by
    rintro ⟨b, j', i⟩
    obtain ⟨C₁, h₁⟩ := exists_bound_fderiv (contDiff_shearVelocity b t i) shearPoint
    obtain ⟨C₂, h₂⟩ := exists_bound_fderiv
      ((contDiff_shearVelocity b t j').mul (contDiff_shearVelocity b t i)) shearPoint
    obtain ⟨C₃, h₃⟩ := exists_bound_fderiv (contDiff_shearStress b t j' i) shearPoint
    exact ⟨max C₁ (max C₂ C₃), fun y hy => ⟨(h₁ y hy).trans (le_max_left _ _),
      (h₂ y hy).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (h₃ y hy).trans ((le_max_right _ _).trans (le_max_right _ _))⟩⟩
  choose C hC using hC
  have hCB : ∀ k, C k ≤ ∑ k', |C k'| := fun k => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun k' => |C k'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k))
  have hB0 : 0 ≤ ∑ k', |C k'| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  exact mean_momentum (μ := twoScenarioMeasure) (ρ := 2) (t := t) (ε := 1) (x := shearPoint)
    (u := shearVelocity) (f := shearForce) (σ := shearStress) (B := fun _ => ∑ k', |C k'|)
    one_pos (fun _ _ _ => MemLp.of_discrete) (fun _ _ _ => Integrable.of_finite)
    (Filter.Eventually.of_forall fun _ _ _ _ => by unfold shearVelocity; fun_prop)
    (Filter.Eventually.of_forall fun b y _ i =>
      (contDiff_shearVelocity b t i).differentiable (by simp) y)
    (Filter.Eventually.of_forall fun b y _ j' i =>
      (contDiff_shearStress b t j' i).differentiable (by simp) y)
    (fun _ => StronglyMeasurable.of_discrete.aestronglyMeasurable)
    (fun _ => StronglyMeasurable.of_discrete.aestronglyMeasurable)
    (fun _ _ => StronglyMeasurable.of_discrete.aestronglyMeasurable) (integrable_const _)
    (Filter.Eventually.of_forall fun b => ⟨fun _ _ _ => by simp [shearVelocity, hB0],
      fun y hy j' i => ⟨(hC (b, j', i) y hy).1.trans (hCB _),
        (hC (b, j', i) y hy).2.1.trans (hCB _), (hC (b, j', i) y hy).2.2.trans (hCB _)⟩⟩)
    (Filter.Eventually.of_forall fun _ _ => rfl) j

-- The spatially varying ensemble at the point `x = (2, 5)`, by direct computation from the
-- definitions: the mean-flow side `∂ₜ(2 * 𝔼[uⱼ]) + div (momentumFlux 2 𝔼[u] 𝔼[σ] j)` is `0` and
-- `1` for the components `j = 0, 1`, the mean of the body forces that the realizations' local laws
-- require is `8` and `7`, and the Reynolds correction `2 * div 𝔼[u'ⱼ u']` is `8` and `6`, not zero.
-- `mean_momentum` relates the three, `0 = 8 - 8` and `1 = 7 - 6`: without the Reynolds correction
-- the mean flow would not satisfy the law in either component.
example (t : ℝ) :
    (deriv (fun τ => 2 * ensembleMean twoScenarioMeasure shearVelocity τ shearPoint 0) t +
        divergence (momentumFlux (fun _ => 2) (ensembleMean twoScenarioMeasure shearVelocity t)
          (ensembleMeanStress twoScenarioMeasure shearStress t) 0) shearPoint = 0 ∧
      ∫ ω, shearForce ω t shearPoint 0 ∂twoScenarioMeasure = 8 ∧
      2 * divergence (fun y i => reynoldsStress twoScenarioMeasure shearVelocity t y 0 i)
        shearPoint = 8) ∧
    (deriv (fun τ => 2 * ensembleMean twoScenarioMeasure shearVelocity τ shearPoint 1) t +
        divergence (momentumFlux (fun _ => 2) (ensembleMean twoScenarioMeasure shearVelocity t)
          (ensembleMeanStress twoScenarioMeasure shearStress t) 1) shearPoint = 1 ∧
      ∫ ω, shearForce ω t shearPoint 1 ∂twoScenarioMeasure = 7 ∧
      2 * divergence (fun y i => reynoldsStress twoScenarioMeasure shearVelocity t y 1 i)
        shearPoint = 6) ∧
    ∀ j : Fin 2,
      deriv (fun τ => 2 * ensembleMean twoScenarioMeasure shearVelocity τ shearPoint j) t +
          divergence (momentumFlux (fun _ => 2) (ensembleMean twoScenarioMeasure shearVelocity t)
            (ensembleMeanStress twoScenarioMeasure shearStress t) j) shearPoint =
        (∫ ω, shearForce ω t shearPoint j ∂twoScenarioMeasure) -
          2 * divergence
            (fun y i => reynoldsStress twoScenarioMeasure shearVelocity t y j i) shearPoint := by
  have hmean : ensembleMean twoScenarioMeasure shearVelocity t = fun y => ![1, y 0] :=
    funext (shear_mean t)
  have hstress : ensembleMeanStress twoScenarioMeasure shearStress t =
      fun y => ![![0, 0], ![y 0, 0]] := funext (shear_meanStress t)
  have htime : ∀ j : Fin 2,
      deriv (fun τ => 2 * ensembleMean twoScenarioMeasure shearVelocity τ shearPoint j) t = 0 := by
    intro j
    simp [shear_mean]
  have hflux0 : momentumFlux (fun _ => (2 : ℝ)) (fun y : Fin 2 → ℝ => ![1, y 0])
      (fun y => ![![0, 0], ![y 0, 0]]) 0 = fun y i => ![0, 0] i * y 0 ^ 2 + ![0, 2] i * y 0 +
        ![2, 0] i := by
    funext y i
    fin_cases i <;> simp [momentumFlux]
  have hflux1 : momentumFlux (fun _ => (2 : ℝ)) (fun y : Fin 2 → ℝ => ![1, y 0])
      (fun y => ![![0, 0], ![y 0, 0]]) 1 = fun y i => ![0, 2] i * y 0 ^ 2 + ![1, 0] i * y 0 +
        ![0, 0] i := by
    funext y i
    fin_cases i <;> simp [momentumFlux] <;> ring
  have hR0 : (fun y i => reynoldsStress twoScenarioMeasure shearVelocity t y 0 i) =
      fun y i => ![1, 0] i * y 0 ^ 2 + ![0, 3] i * y 0 + ![0, 0] i := by
    funext y i
    rw [shear_reynolds]
    fin_cases i <;> simp <;> ring
  have hR1 : (fun y i => reynoldsStress twoScenarioMeasure shearVelocity t y 1 i) =
      fun y i => ![0, 0] i * y 0 ^ 2 + ![3, 0] i * y 0 + ![0, 9] i := by
    funext y i
    rw [shear_reynolds]
    fin_cases i <;> simp
    ring
  have hforce : ∀ (b : Bool) (j : Fin 2), shearForce b t shearPoint j =
      divergence (momentumFlux (fun _ => 2) (shearVelocity b t) (shearStress b t) j)
        shearPoint := by
    intro b j
    simp [shearForce, shearVelocity]
  have hT0 : momentumFlux (fun _ => (2 : ℝ)) (shearVelocity true t) (shearStress true t) 0 =
      fun y i => ![2, 2] i * y 0 ^ 2 + ![4, 8] i * y 0 + ![2, 6] i := by
    funext y i
    fin_cases i <;> simp [momentumFlux, shearVelocity, shearStress, shearSign] <;> ring
  have hT1 : momentumFlux (fun _ => (2 : ℝ)) (shearVelocity true t) (shearStress true t) 1 =
      fun y i => ![2, 2] i * y 0 ^ 2 + ![7, 12] i * y 0 + ![6, 18] i := by
    funext y i
    fin_cases i <;> simp [momentumFlux, shearVelocity, shearStress, shearSign] <;> ring
  have hF0 : momentumFlux (fun _ => (2 : ℝ)) (shearVelocity false t) (shearStress false t) 0 =
      fun y i => ![2, -2] i * y 0 ^ 2 + ![-4, 8] i * y 0 + ![2, -6] i := by
    funext y i
    fin_cases i <;> simp [momentumFlux, shearVelocity, shearStress, shearSign] <;> ring
  have hF1 : momentumFlux (fun _ => (2 : ℝ)) (shearVelocity false t) (shearStress false t) 1 =
      fun y i => ![-2, 2] i * y 0 ^ 2 + ![7, -12] i * y 0 + ![-6, 18] i := by
    funext y i
    fin_cases i <;> simp [momentumFlux, shearVelocity, shearStress, shearSign] <;> ring
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, shear_mean_momentum t⟩
  · rw [htime, hmean, hstress, hflux0, divergence_quad]
    simp [shearPoint]
  · rw [integral_twoScenario, hforce, hforce, hT0, hF0, divergence_quad, divergence_quad]
    simp [shearPoint]
    norm_num
  · rw [hR0, divergence_quad]
    simp [shearPoint]
    norm_num
  · rw [htime, hmean, hstress, hflux1, divergence_quad]
    simp [shearPoint]
  · rw [integral_twoScenario, hforce, hforce, hT1, hF1, divergence_quad, divergence_quad]
    simp [shearPoint]
    norm_num
  · rw [hR1, divergence_quad]
    simp [shearPoint]
    norm_num

/-! ### The eddy-viscosity closure -/

section Closure

open scoped Matrix.Norms.Frobenius

-- Simple shear `U = (2 y, 0, 0)`: the shear entry of the model is `-νt γ = -2` (down-gradient),
-- the direct extraction is `4` for every `k`, and `meanFlowExtraction_modeledReynoldsStress`
-- turns it into `‖S‖² = 2`.
example (k : ℝ) :
    modeledReynoldsStress k 1 !![0, 1, 0; 1, 0, 0; 0, 0, 0] 0 1 = -2 ∧
      meanFlowExtraction (modeledReynoldsStress k 1 !![0, 1, 0; 1, 0, 0; 0, 0, 0])
        !![0, 1, 0; 1, 0, 0; 0, 0, 0] = 4 ∧
      ‖(!![0, 1, 0; 1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ)‖ ^ 2 = 2 := by
  have htr : (!![0, 1, 0; 1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ).trace = 0 := by
    simp [Matrix.trace_fin_three]
  have hP : meanFlowExtraction (modeledReynoldsStress k 1 !![0, 1, 0; 1, 0, 0; 0, 0, 0])
      !![0, 1, 0; 1, 0, 0; 0, 0, 0] = 4 := by
    norm_num [meanFlowExtraction, modeledReynoldsStress, Fin.sum_univ_three, Matrix.one_apply]
  refine ⟨by norm_num [modeledReynoldsStress, Matrix.one_apply], hP, ?_⟩
  have h := meanFlowExtraction_modeledReynoldsStress k 1 htr
  linarith

-- Every nonnegative eddy viscosity extracts a nonnegative amount from the simple shear.
example (k νt : ℝ) (hνt : 0 ≤ νt) :
    0 ≤ meanFlowExtraction (modeledReynoldsStress k νt !![0, 1, 0; 1, 0, 0; 0, 0, 0])
      !![0, 1, 0; 1, 0, 0; 0, 0, 0] :=
  meanFlowExtraction_modeledReynoldsStress_nonneg k (by simp [Matrix.trace_fin_three]) hνt

-- On the nonzero plane strain the eddy viscosity `νt = -1` returns energy to the mean flow.
example :
    meanFlowExtraction (modeledReynoldsStress 1 (-1) (Matrix.diagonal ![1, -1, 0]))
      (Matrix.diagonal ![1, -1, 0]) < 0 := by
  have htr : (Matrix.diagonal ![(1 : ℝ), -1, 0]).trace = 0 := by
    rw [Matrix.trace_fin_three]
    norm_num [Matrix.diagonal_apply]
  have hne : Matrix.diagonal ![(1 : ℝ), -1, 0] ≠ 0 := fun h => by
    simpa using congrFun (congrFun h 0) 0
  by_contra hP
  have h := (meanFlowExtraction_modeledReynoldsStress_nonneg_iff 1 htr hne).1 (not_lt.1 hP)
  norm_num at h

-- A negative eddy viscosity extracts nothing from the zero strain.
example : ∃ k νt : ℝ, 0 ≤ k ∧ 0 ≤ meanFlowExtraction (modeledReynoldsStress k νt 0) 0 ∧
    νt < 0 := by
  by_contra h
  exact meanFlowExtraction_nonneg_converse_fails fun k νt hk hP =>
    not_lt.1 fun hν => h ⟨k, νt, hk, hP, hν⟩

-- The plane-strain fixture: first normal stress `-4/3`, trace `2 = 2 k`.
example : modeledReynoldsStress 1 1 (Matrix.diagonal ![1, -1, 0]) 0 0 = -4 / 3 ∧
    (modeledReynoldsStress 1 1 (Matrix.diagonal ![1, -1, 0])).trace = 2 := by
  rw [modeledReynoldsStress_planeStrain.1]
  refine ⟨by simp, ?_⟩
  rw [Matrix.trace_fin_three]
  norm_num

-- On the model domain the closure is Hermitian, so the Hermitian part of `Matrix.PosSemidef`
-- holds there and a failure of positive semidefiniteness is a failure of the quadratic form.
example (k νt : ℝ) {S : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.IsSymm) :
    (modeledReynoldsStress k νt S).IsHermitian := by
  have h : (modeledReynoldsStress k νt S).IsSymm :=
    (Matrix.isSymm_one.smul _).sub (hS.smul _)
  simpa [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using h

-- The model domain contains a point where the closure is not positive semidefinite.
example : ∃ (k νt : ℝ) (S : Matrix (Fin 3) (Fin 3) ℝ), 0 ≤ k ∧ 0 < νt ∧ S.IsSymm ∧
    S.trace = 0 ∧ ¬ (modeledReynoldsStress k νt S).PosSemidef := by
  by_contra h
  exact modeledReynoldsStress_realizability_fails fun k νt S hk hν hS htr =>
    not_not.1 fun hn => h ⟨k, νt, S, hk, hν, hS, htr, hn⟩

-- The plane-strain model is not the Reynolds stress of any ensemble with `L²` velocity
-- components: `reynoldsStress_posSemidef` along `e₀` against the fixture's entry `-4/3`.
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Ω → ℝ → (Fin 3 → ℝ) → Fin 3 → ℝ) (τ : ℝ) (y : Fin 3 → ℝ)
    (hu : ∀ i, MemLp (fun ω => u ω τ y i) 2 μ) :
    reynoldsStress μ u τ y ≠ modeledReynoldsStress 1 1 (Matrix.diagonal ![1, -1, 0]) := by
  intro h
  have hq := reynoldsStress_posSemidef hu ![1, 0, 0]
  rw [h, modeledReynoldsStress_planeStrain.1] at hq
  norm_num [Fin.sum_univ_succ, Matrix.diagonal_apply] at hq

-- Control: the same plane strain with `νt = 1/4` gives `diag(1/6, 7/6, 2/3)`, a positive
-- semidefinite model.
example : (modeledReynoldsStress 1 (1 / 4) (Matrix.diagonal ![1, -1, 0])).PosSemidef := by
  have h : modeledReynoldsStress 1 (1 / 4) (Matrix.diagonal ![1, -1, 0]) =
      Matrix.diagonal ![1 / 6, 7 / 6, 2 / 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [modeledReynoldsStress, Matrix.one_apply, Matrix.diagonal_apply]
  rw [h, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num

end Closure

end PhyslibExtTest.FluidDynamics.EnsembleMomentum
