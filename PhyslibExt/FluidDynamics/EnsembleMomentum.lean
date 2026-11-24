/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Moments.Covariance
public import MathlibExt.Probability.Diffusion.FokkerPlanckGradient
public import PhyslibExt.ContinuumMechanics.ControlVolumes

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Ensemble-averaged momentum: the exact mean momentum equation

## i. Overview

An ensemble of flow realizations is a probability space `(Ω, μ)`; realization `ω` has velocity
`u ω τ y`, Cauchy stress `σ ω τ y` (`σ ω τ y j i` is the `j`-th traction component on a surface of
unit normal `eᵢ`; for a fluid `σ = -p I + τ` with pressure `p`) and body force density `f ω τ y`,
on `Fin (n + 1) → ℝ` at constant density `ρ`. Each realization obeys, almost surely, the local
Cauchy momentum law of `PhyslibExt.ContinuumMechanics.ControlVolumes`,
`∂ₜ(ρ uⱼ) + div (momentumFlux ρ u σ j) = fⱼ`, whose flux has the components
`ρ uⱼ uᵢ - σⱼᵢ`. Ensemble means are `𝔼[·] = ∫ · ∂μ`, the fluctuation is `u' = u - 𝔼[u]`, and the
Reynolds stress per unit density is `𝔼[u'ⱼ u'ᵢ]`, the covariance of the velocity components.
Constant density alone does not make the flow incompressible: no continuity equation or
divergence-free condition is assumed by the mean momentum equation, and `div u = 0` enters only
`divergence_ensembleMean_eq_zero`, as its hypothesis.

Averaging the law needs three facts, all proved from stated hypotheses rather than assumed:
differentiation under the ensemble integral in time and in space (Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` and its Fréchet counterpart), which is
licensed by almost-sure differentiability, measurable derivatives and one integrable bound
dominating every derivative and product derivative near the point; and the covariance identity
`𝔼[uⱼ uᵢ] = 𝔼[uⱼ] 𝔼[uᵢ] + 𝔼[u'ⱼ u'ᵢ]` for `L²` velocity components (`covariance_eq_sub`). The
result is the exact mean momentum equation
`∂ₜ(ρ 𝔼[uⱼ]) + div (momentumFlux ρ 𝔼[u] 𝔼[σ] j) = 𝔼[fⱼ] - ρ div 𝔼[u'ⱼ u']`: the mean flow obeys
the same law with the extra divergence of the Reynolds stress. That stress is a positive
semidefinite form, the covariance form of the velocity law (`isPosSemidef_covarianceBilin`), and
it vanishes when the realizations do not fluctuate, which recovers the laminar law. If almost
every realization is divergence free at a point, so is the mean there. Without the domination
hypothesis the interchange of derivative and ensemble mean fails: section C gives an ensemble on
`(0, 1]` whose realizations all have derivative `0` at a point where the mean has derivative `1`.

Section D models the Reynolds stress by Boussinesq's turbulent-viscosity hypothesis in three
dimensions, `Rm = (2 k / 3) I - 2 νt S`, from the turbulent kinetic energy `k`, an eddy viscosity
`νt` and the mean rate of strain `S` (`modeledReynoldsStress`). The model domain is `k ≥ 0`, a
real `νt` and a symmetric `S`, trace free when the mean flow is divergence free; the closure is a
chosen model, not a measured property of turbulence. The Reynolds stress acts on the mean flow as
the stress `-ρ 𝔼[u'ⱼ u'ᵢ]` (tension positive), so the model adds the viscous-like stress
`2 ρ νt S` and the isotropic pressure `(2 / 3) ρ k`.

The production of turbulent kinetic energy, the rate per unit mass at which the Reynolds stress
takes kinetic energy from the mean flow, is written with the mean rate of strain `S` as
`P = -∑ᵢ ∑ⱼ Rᵢⱼ Sᵢⱼ` (`meanFlowExtraction`); energy leaves the mean flow when `P > 0`. For the
model and a trace-free `S` the isotropic part does no work and `P = 2 νt ‖S‖²` with the Frobenius
norm, `‖S‖² = ∑ᵢ ∑ⱼ Sᵢⱼ²`. So `νt ≥ 0` gives `P ≥ 0`; for `S ≠ 0` the converse holds, and at
`S = 0` it fails, since there `P = 0` whatever `νt`. Dissipation does not give realizability: for
`k = 1`, `νt = 1` and the plane strain `S = diag(1, -1, 0)` of the mean flow `U = (x, -y, 0)`,
the model is `Rm = diag(-4/3, 8/3, 2/3)` and extracts `P = 4 > 0`, yet its entry `Rm₀₀ = -4/3` is
negative: its quadratic form is negative along `e₀`, so it is not positive semidefinite
(`Matrix.PosSemidef`), while `reynoldsStress_posSemidef` makes that form nonnegative for every
Reynolds stress of `L²` velocities. Section D has no transport equations for `k` or `νt`, no
realizability criterion or limiter, and no empirical adequacy or system safety claim.

## ii. Key results

- `FluidDynamics.EnsembleMomentum.ensembleMean`, `ensembleMeanStress` and `reynoldsStress`: the
  ensemble means and the Reynolds stress `𝔼[u'ⱼ u'ᵢ]`.
- `FluidDynamics.EnsembleMomentum.reynoldsStress_eq`: the covariance identity.
- `FluidDynamics.EnsembleMomentum.reynoldsStress_posSemidef`: the Reynolds stress is positive
  semidefinite.
- `FluidDynamics.EnsembleMomentum.reynoldsStress_eq_zero_of_ae_eq`: zero fluctuation gives zero
  Reynolds stress and the laminar mean.
- `FluidDynamics.EnsembleMomentum.mean_momentum`: the exact mean momentum equation.
- `FluidDynamics.EnsembleMomentum.divergence_ensembleMean_eq_zero`: divergence-free realizations
  have a divergence-free mean.
- `FluidDynamics.EnsembleMomentum.escapingProfile_interchange_fails`: without domination the
  interchange of derivative and ensemble mean fails.
- `FluidDynamics.EnsembleMomentum.modeledReynoldsStress`: the closure
  `Rm = (2 k / 3) I - 2 νt S`.
- `FluidDynamics.EnsembleMomentum.meanFlowExtraction`: the production `P = -∑ᵢ ∑ⱼ Rᵢⱼ Sᵢⱼ`.
- `FluidDynamics.EnsembleMomentum.meanFlowExtraction_modeledReynoldsStress`: `P = 2 νt ‖S‖²`
  for a trace-free `S`.
- `FluidDynamics.EnsembleMomentum.meanFlowExtraction_modeledReynoldsStress_nonneg`: for a
  trace-free `S`, `νt ≥ 0` gives `P ≥ 0`.
- `FluidDynamics.EnsembleMomentum.meanFlowExtraction_modeledReynoldsStress_nonneg_iff`: for a
  nonzero trace-free `S`, `P ≥ 0` exactly when `νt ≥ 0`.
- `FluidDynamics.EnsembleMomentum.meanFlowExtraction_nonneg_converse_fails`: at `S = 0`, with
  `k ≥ 0`, nonnegative extraction does not force `νt ≥ 0`.
- `FluidDynamics.EnsembleMomentum.modeledReynoldsStress_planeStrain`: at `k = νt = 1` and
  `S = diag(1, -1, 0)`, `Rm = diag(-4/3, 8/3, 2/3)` and `P = 4`.
- `FluidDynamics.EnsembleMomentum.modeledReynoldsStress_realizability_fails`: for `k ≥ 0`,
  `νt > 0` and a symmetric trace-free `S`, the model need not be positive semidefinite
  (`Matrix.PosSemidef`).

## iii. Table of contents

- A. Ensemble means and the Reynolds stress
- B. The mean momentum equation
- C. The interchange without domination
- D. Closure dissipation versus realizability

## iv. References

- O. Reynolds, *On the dynamical theory of incompressible viscous fluids and the determination of
  the criterion*, Phil. Trans. R. Soc. Lond. A 186 (1895), 123-164 (the averaged equations and
  the stresses due to the fluctuations).
- S. B. Pope, *Turbulent Flows*, Cambridge University Press, 2000, Chapter 4 (the Reynolds
  equations; the Reynolds stresses `⟨uᵢ uⱼ⟩` form a symmetric positive semidefinite tensor; the
  turbulent-viscosity hypothesis) and Chapter 5 (the production of turbulent kinetic energy).
- U. Schumann, *Realizability of Reynolds-stress turbulence models*, Phys. Fluids 20 (1977),
  721-725 (a modeled Reynolds stress must be positive semidefinite).
- `ControlVolumes.momentumFlux` (`PhyslibExt.ContinuumMechanics.ControlVolumes`) and
  `MathlibExt.Probability.FokkerPlanck.divergence`
  (`MathlibExt.Probability.Diffusion.FokkerPlanckGradient`).
- Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
  `hasFDerivAt_integral_of_dominated_of_fderiv_le`, `ProbabilityTheory.covariance_eq_sub`,
  `ProbabilityTheory.isPosSemidef_covarianceBilin` and the Frobenius norm on matrices (scope
  `Matrix.Norms.Frobenius`, `Matrix.frobenius_norm_def`).
-/

@[expose] public section

namespace FluidDynamics.EnsembleMomentum

open MeasureTheory ProbabilityTheory
open ControlVolumes (momentumFlux)
open MathlibExt.Probability.FokkerPlanck (divergence)

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-! ## A. Ensemble means and the Reynolds stress -/

/-- Ensemble mean of a vector field over the realizations:
`ensembleMean μ v τ y i = 𝔼[vᵢ (τ, y)] = ∫ ω, v ω τ y i ∂μ`. -/
noncomputable def ensembleMean (μ : Measure Ω)
    (v : Ω → ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (τ : ℝ) (y : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => ∫ ω, v ω τ y i ∂μ

/-- Ensemble mean of a stress field, `𝔼[σⱼᵢ (τ, y)]`. -/
noncomputable def ensembleMeanStress (μ : Measure Ω)
    (σ : Ω → ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ) (τ : ℝ)
    (y : Fin (n + 1) → ℝ) : Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun j i => ∫ ω, σ ω τ y j i ∂μ

/-- Reynolds stress per unit density, `𝔼[u'ⱼ u'ᵢ]` with the fluctuation `u' = u - 𝔼[u]`: the
covariance of the velocity components at `(τ, y)`. As a stress acting on the mean flow it enters
as `-ρ 𝔼[u'ⱼ u'ᵢ]`. -/
noncomputable def reynoldsStress (μ : Measure Ω)
    (u : Ω → ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (τ : ℝ) (y : Fin (n + 1) → ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun j i => cov[fun ω => u ω τ y j, fun ω => u ω τ y i; μ]

/-- Covariance identity for the Reynolds stress: for `L²` velocity components,
`𝔼[u'ⱼ u'ᵢ] = 𝔼[uⱼ uᵢ] - 𝔼[uⱼ] 𝔼[uᵢ]` (`covariance_eq_sub`). -/
lemma reynoldsStress_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {τ : ℝ} {y : Fin (n + 1) → ℝ}
    {j i : Fin (n + 1)} (hj : MemLp (fun ω => u ω τ y j) 2 μ)
    (hi : MemLp (fun ω => u ω τ y i) 2 μ) :
    reynoldsStress μ u τ y j i =
      (∫ ω, u ω τ y j * u ω τ y i ∂μ) - ensembleMean μ u τ y j * ensembleMean μ u τ y i := by
  simp only [reynoldsStress, ensembleMean]
  rw [covariance_eq_sub hj hi]
  rfl

/-- The Reynolds stress is positive semidefinite: `∑ⱼ ∑ᵢ aⱼ aᵢ 𝔼[u'ⱼ u'ᵢ] ≥ 0` for every vector
`a`, for `L²` velocity components. It is the covariance form of the law of the velocity at
`(τ, y)`, so this is Mathlib's `isPosSemidef_covarianceBilin`, not a new proof. -/
lemma reynoldsStress_posSemidef {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {τ : ℝ} {y : Fin (n + 1) → ℝ}
    (hu : ∀ i, MemLp (fun ω => u ω τ y i) 2 μ) (a : Fin (n + 1) → ℝ) :
    0 ≤ ∑ j, ∑ i, a j * a i * reynoldsStress μ u τ y j i := by
  set V : Ω → EuclideanSpace ℝ (Fin (n + 1)) := fun ω => WithLp.toLp 2 (fun i => u ω τ y i)
    with hV
  have hVL2 : MemLp V 2 μ := by
    rw [memLp_piLp_iff]
    intro i
    simpa [hV] using hu i
  have hVm : AEMeasurable V μ := hVL2.aestronglyMeasurable.aemeasurable
  have hid : MemLp id 2 (μ.map V) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hVm]
    exact hVL2
  set a' : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 a with ha'
  have hpsd := (isPosSemidef_covarianceBilin (μ := μ.map V)).isNonneg.nonneg a'
  rw [ContinuousLinearMap.toBilinForm_apply, covarianceBilin_apply_eq_cov hid] at hpsd
  have hL : AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin (n + 1)) => inner ℝ a' v)
      (μ.map V) := (continuous_const.inner continuous_id).aestronglyMeasurable
  rw [covariance_map hL hL hVm] at hpsd
  have hfun : ((fun v : EuclideanSpace ℝ (Fin (n + 1)) => inner ℝ a' v) ∘ V) =
      fun ω => ∑ i, a i * u ω τ y i := by
    funext ω
    simp [hV, ha', PiLp.inner_apply, mul_comm]
  rw [hfun, covariance_fun_sum_fun_sum (fun i => (hu i).const_mul (a i))
    (fun i => (hu i).const_mul (a i))] at hpsd
  simp only [covariance_const_mul_left, covariance_const_mul_right] at hpsd
  calc (0 : ℝ) ≤ _ := hpsd
    _ = ∑ j, ∑ i, a j * a i * reynoldsStress μ u τ y j i := by
      simp only [reynoldsStress]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      ring

/-- Zero fluctuation recovers the laminar mean: if at every `(τ, y)` almost every realization
equals the field `U τ y`, then the ensemble mean is `U` and the Reynolds stress and its
divergence vanish, so the mean momentum equation is the laminar law for `U`. -/
lemma reynoldsStress_eq_zero_of_ae_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    {U : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hU : ∀ τ y, ∀ᵐ ω ∂μ, u ω τ y = U τ y)
    (τ : ℝ) (x y : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    ensembleMean μ u τ y = U τ y ∧ reynoldsStress μ u τ y = 0 ∧
      divergence (fun y' i => reynoldsStress μ u τ y' j i) x = 0 := by
  have hmean : ∀ τ' y', ensembleMean μ u τ' y' = U τ' y' := by
    intro τ' y'
    funext i
    simp only [ensembleMean]
    rw [integral_congr_ae (g := fun _ => U τ' y' i)
      (by filter_upwards [hU τ' y'] with ω hω; rw [hω])]
    simp
  have hcov : ∀ τ' y', reynoldsStress μ u τ' y' = 0 := by
    intro τ' y'
    funext j' i
    simp only [reynoldsStress, Pi.zero_apply, covariance]
    have hj : ∫ ω, u ω τ' y' j' ∂μ = U τ' y' j' := congrFun (hmean τ' y') j'
    have hi : ∫ ω, u ω τ' y' i ∂μ = U τ' y' i := congrFun (hmean τ' y') i
    rw [hj, hi, integral_congr_ae (g := fun _ => (0 : ℝ))
      (by filter_upwards [hU τ' y'] with ω hω; simp [hω])]
    simp
  refine ⟨hmean τ y, hcov τ y, ?_⟩
  simp [MathlibExt.Probability.FokkerPlanck.divergence, MathlibExt.Probability.FokkerPlanck.pderiv,
    hcov]

/-! ## B. The mean momentum equation -/

/-- Differentiation in space under the ensemble integral (Mathlib's
`hasFDerivAt_integral_of_dominated_of_fderiv_le`), with the integrability of the derivative. -/
private lemma hasFDerivAt_ensemble_space {μ : Measure Ω} {m : ℕ}
    {G : Ω → (Fin m → ℝ) → ℝ} {B : Ω → ℝ} {x : Fin m → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hG : ∀ y, AEStronglyMeasurable (fun ω => G ω y) μ) (hGx : Integrable (fun ω => G ω x) μ)
    (hdiff : ∀ᵐ ω ∂μ, ∀ y ∈ Metric.ball x ε, DifferentiableAt ℝ (G ω) y)
    (hmeas : AEStronglyMeasurable (fun ω => fderiv ℝ (G ω) x) μ) (hB : Integrable B μ)
    (hbound : ∀ᵐ ω ∂μ, ∀ y ∈ Metric.ball x ε, ‖fderiv ℝ (G ω) y‖ ≤ B ω) :
    Integrable (fun ω => fderiv ℝ (G ω) x) μ ∧
      HasFDerivAt (fun y => ∫ ω, G ω y ∂μ) (∫ ω, fderiv ℝ (G ω) x ∂μ) x := by
  refine ⟨hB.mono' hmeas (hbound.mono fun _ h => h x (Metric.mem_ball_self hε)), ?_⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun y ω => G ω y)
    (F' := fun y ω => fderiv ℝ (G ω) y) (Metric.ball_mem_nhds x hε)
    (Filter.Eventually.of_forall hG) hGx hmeas hbound hB
    (hdiff.mono fun _ h y hy => (h y hy).hasFDerivAt)

/-- The partial derivative of an ensemble mean is the mean of the partial derivatives. -/
private lemma pderiv_ensemble {μ : Measure Ω} {m : ℕ} {G : Ω → (Fin m → ℝ) → ℝ}
    {x : Fin m → ℝ} {L : (Fin m → ℝ) →L[ℝ] ℝ}
    (hint : Integrable (fun ω => fderiv ℝ (G ω) x) μ)
    (h : HasFDerivAt (fun y => ∫ ω, G ω y ∂μ) L x) (hL : L = ∫ ω, fderiv ℝ (G ω) x ∂μ)
    (i : Fin m) :
    MathlibExt.Probability.FokkerPlanck.pderiv i (fun y => ∫ ω, G ω y ∂μ) x =
      ∫ ω, MathlibExt.Probability.FokkerPlanck.pderiv i (G ω) x ∂μ := by
  simp only [MathlibExt.Probability.FokkerPlanck.pderiv]
  rw [h.fderiv, hL, ContinuousLinearMap.integral_apply hint]

/-- **Exact ensemble-averaged momentum equation.** At a point `(t, x)` and for constant density
`ρ`, suppose: the velocity components are `L²` and the stress components are integrable over
the realizations; almost every realization is differentiable in time near `t`
(velocity at `x`) and in space near `x` (velocity and stress at time `t`); the derivatives at the
point are a.e.-strongly measurable; one integrable `B` dominates, almost surely, the time
derivatives of the velocity on `ball t ε` and the space derivatives of the velocity, of the
velocity products `uⱼ uᵢ` and of the stress on `ball x ε`; and almost every realization obeys the
local Cauchy law `∂ₜ(ρ uⱼ) + div (momentumFlux ρ u σ j) = fⱼ` at the point. Then the ensemble
means obey the same law with the extra divergence of the Reynolds stress:
`∂ₜ(ρ 𝔼[uⱼ]) + div (momentumFlux ρ 𝔼[u] 𝔼[σ] j) = 𝔼[fⱼ] - ρ div 𝔼[u'ⱼ u']`. No integrability of
the body force is assumed: the law makes it almost surely equal to an integrable function. -/
lemma mean_momentum {μ : Measure Ω} [IsProbabilityMeasure μ] {ρ t ε : ℝ}
    {x : Fin (n + 1) → ℝ} {u f : Ω → ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    {σ : Ω → ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ} {B : Ω → ℝ}
    (hε : 0 < ε) (hu : ∀ τ y i, MemLp (fun ω => u ω τ y i) 2 μ)
    (hσ : ∀ y j i, Integrable (fun ω => σ ω t y j i) μ)
    (hut : ∀ᵐ ω ∂μ, ∀ τ ∈ Metric.ball t ε, ∀ j,
      DifferentiableAt ℝ (fun τ' => u ω τ' x j) τ)
    (hux : ∀ᵐ ω ∂μ, ∀ y ∈ Metric.ball x ε, ∀ i,
      DifferentiableAt ℝ (fun y' => u ω t y' i) y)
    (hσx : ∀ᵐ ω ∂μ, ∀ y ∈ Metric.ball x ε, ∀ j i,
      DifferentiableAt ℝ (fun y' => σ ω t y' j i) y)
    (hut_meas : ∀ j, AEStronglyMeasurable (fun ω => deriv (fun τ => u ω τ x j) t) μ)
    (hux_meas : ∀ i, AEStronglyMeasurable (fun ω => fderiv ℝ (fun y => u ω t y i) x) μ)
    (hσx_meas : ∀ j i, AEStronglyMeasurable (fun ω => fderiv ℝ (fun y => σ ω t y j i) x) μ)
    (hB : Integrable B μ)
    (hdom : ∀ᵐ ω ∂μ, (∀ τ ∈ Metric.ball t ε, ∀ j, ‖deriv (fun τ' => u ω τ' x j) τ‖ ≤ B ω) ∧
      ∀ y ∈ Metric.ball x ε, ∀ j i, ‖fderiv ℝ (fun y' => u ω t y' i) y‖ ≤ B ω ∧
        ‖fderiv ℝ (fun y' => u ω t y' j * u ω t y' i) y‖ ≤ B ω ∧
        ‖fderiv ℝ (fun y' => σ ω t y' j i) y‖ ≤ B ω)
    (hlaw : ∀ᵐ ω ∂μ, ∀ j, deriv (fun τ => ρ * u ω τ x j) t +
      divergence (momentumFlux (fun _ => ρ) (u ω t) (σ ω t) j) x = f ω t x j)
    (j : Fin (n + 1)) :
    deriv (fun τ => ρ * ensembleMean μ u τ x j) t +
        divergence (momentumFlux (fun _ => ρ) (ensembleMean μ u t) (ensembleMeanStress μ σ t) j)
          x =
      (∫ ω, f ω t x j ∂μ) - ρ * divergence (fun y i => reynoldsStress μ u t y j i) x := by
  open MathlibExt.Probability.FokkerPlanck in
  have hx : x ∈ Metric.ball x ε := Metric.mem_ball_self hε
  -- time
  obtain ⟨hint_t, hder_t⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun τ ω => u ω τ x j) (F' := fun τ ω => deriv (fun τ' => u ω τ' x j) τ)
    (Metric.ball_mem_nhds t hε)
    (Filter.Eventually.of_forall fun τ => (hu τ x j).aestronglyMeasurable)
    ((hu t x j).integrable one_le_two) (hut_meas j) (hdom.mono fun _ h τ hτ => h.1 τ hτ j) hB
    (hut.mono fun _ h τ hτ => (h τ hτ j).hasDerivAt)
  have hT : deriv (fun τ => ρ * ensembleMean μ u τ x j) t =
      ρ * ∫ ω, deriv (fun τ => u ω τ x j) t ∂μ := (hder_t.const_mul ρ).deriv
  -- space: velocity, velocity products, stress
  have hS_u : ∀ i, Integrable (fun ω => fderiv ℝ (fun y => u ω t y i) x) μ ∧
      HasFDerivAt (fun y => ∫ ω, u ω t y i ∂μ)
        (∫ ω, fderiv ℝ (fun y => u ω t y i) x ∂μ) x := fun i =>
    hasFDerivAt_ensemble_space (G := fun ω y => u ω t y i) hε
      (fun y => (hu t y i).aestronglyMeasurable) ((hu t x i).integrable one_le_two)
      (hux.mono fun _ h y hy => h y hy i) (hux_meas i) hB
      (hdom.mono fun _ h y hy => (h.2 y hy j i).1)
  have hmeas_uu : ∀ i, AEStronglyMeasurable
      (fun ω => fderiv ℝ (fun y => u ω t y j * u ω t y i) x) μ := by
    intro i
    have hae : (fun ω => fderiv ℝ (fun y => u ω t y j * u ω t y i) x) =ᵐ[μ]
        fun ω => u ω t x j • fderiv ℝ (fun y => u ω t y i) x +
          u ω t x i • fderiv ℝ (fun y => u ω t y j) x := by
      filter_upwards [hux] with ω h
      exact ((h x hx j).hasFDerivAt.mul (h x hx i).hasFDerivAt).fderiv
    refine AEStronglyMeasurable.congr ?_ hae.symm
    exact ((hu t x j).aestronglyMeasurable.smul (hux_meas i)).add
      ((hu t x i).aestronglyMeasurable.smul (hux_meas j))
  have hS_uu : ∀ i, Integrable (fun ω => fderiv ℝ (fun y => u ω t y j * u ω t y i) x) μ ∧
      HasFDerivAt (fun y => ∫ ω, u ω t y j * u ω t y i ∂μ)
        (∫ ω, fderiv ℝ (fun y => u ω t y j * u ω t y i) x ∂μ) x := fun i =>
    hasFDerivAt_ensemble_space (G := fun ω y => u ω t y j * u ω t y i) hε
      (fun y => (hu t y j).aestronglyMeasurable.mul (hu t y i).aestronglyMeasurable)
      ((hu t x j).integrable_mul (hu t x i))
      (hux.mono fun _ h y hy => (h y hy j).mul (h y hy i)) (hmeas_uu i) hB
      (hdom.mono fun _ h y hy => (h.2 y hy j i).2.1)
  have hS_σ : ∀ i, Integrable (fun ω => fderiv ℝ (fun y => σ ω t y j i) x) μ ∧
      HasFDerivAt (fun y => ∫ ω, σ ω t y j i ∂μ)
        (∫ ω, fderiv ℝ (fun y => σ ω t y j i) x ∂μ) x := fun i =>
    hasFDerivAt_ensemble_space (G := fun ω y => σ ω t y j i) hε
      (fun y => (hσ y j i).aestronglyMeasurable) (hσ x j i)
      (hσx.mono fun _ h y hy => h y hy j i) (hσx_meas j i) hB
      (hdom.mono fun _ h y hy => (h.2 y hy j i).2.2)
  -- the mean side, one flux component at a time
  have hmean_i : ∀ i,
      pderiv i (fun y => momentumFlux (fun _ => ρ) (ensembleMean μ u t)
          (ensembleMeanStress μ σ t) j y i) x +
        ρ * pderiv i (fun y => reynoldsStress μ u t y j i) x =
      ρ * (∫ ω, pderiv i (fun y => u ω t y j * u ω t y i) x ∂μ) -
        ∫ ω, pderiv i (fun y => σ ω t y j i) x ∂μ := by
    intro i
    have hUj := (hS_u j).2
    have hUi := (hS_u i).2
    have hP := (hS_uu i).2
    have hS := (hS_σ i).2
    have hR : (fun y => reynoldsStress μ u t y j i) = fun y =>
        (∫ ω, u ω t y j * u ω t y i ∂μ) -
          (∫ ω, u ω t y j ∂μ) * ∫ ω, u ω t y i ∂μ :=
      funext fun y => reynoldsStress_eq (hu t y j) (hu t y i)
    have hF : (fun y => momentumFlux (fun _ => ρ) (ensembleMean μ u t)
        (ensembleMeanStress μ σ t) j y i) = fun y =>
          ρ * (∫ ω, u ω t y j ∂μ) * (∫ ω, u ω t y i ∂μ) - ∫ ω, σ ω t y j i ∂μ := rfl
    have hdF : DifferentiableAt ℝ (fun y =>
        ρ * (∫ ω, u ω t y j ∂μ) * (∫ ω, u ω t y i ∂μ) - ∫ ω, σ ω t y j i ∂μ) x :=
      ((hUj.differentiableAt.const_mul ρ).mul hUi.differentiableAt).sub hS.differentiableAt
    have hdR : DifferentiableAt ℝ (fun y => (∫ ω, u ω t y j * u ω t y i ∂μ) -
        (∫ ω, u ω t y j ∂μ) * ∫ ω, u ω t y i ∂μ) x :=
      hP.differentiableAt.sub (hUj.differentiableAt.mul hUi.differentiableAt)
    have hsum : (fun y => (ρ * (∫ ω, u ω t y j ∂μ) * (∫ ω, u ω t y i ∂μ) -
        ∫ ω, σ ω t y j i ∂μ) + ρ * ((∫ ω, u ω t y j * u ω t y i ∂μ) -
          (∫ ω, u ω t y j ∂μ) * ∫ ω, u ω t y i ∂μ)) = fun y =>
        ρ * (∫ ω, u ω t y j * u ω t y i ∂μ) - ∫ ω, σ ω t y j i ∂μ := by
      funext y
      ring
    have hlin : pderiv i (fun y => (ρ * (∫ ω, u ω t y j ∂μ) * (∫ ω, u ω t y i ∂μ) -
        ∫ ω, σ ω t y j i ∂μ) + ρ * ((∫ ω, u ω t y j * u ω t y i ∂μ) -
          (∫ ω, u ω t y j ∂μ) * ∫ ω, u ω t y i ∂μ)) x =
        pderiv i (fun y => ρ * (∫ ω, u ω t y j ∂μ) * (∫ ω, u ω t y i ∂μ) -
          ∫ ω, σ ω t y j i ∂μ) x +
        ρ * pderiv i (fun y => (∫ ω, u ω t y j * u ω t y i ∂μ) -
          (∫ ω, u ω t y j ∂μ) * ∫ ω, u ω t y i ∂μ) x := by
      simp only [pderiv]
      rw [fderiv_fun_add hdF (hdR.const_mul ρ), fderiv_const_mul hdR]
      simp
    have hPS : pderiv i (fun y => ρ * (∫ ω, u ω t y j * u ω t y i ∂μ) -
        ∫ ω, σ ω t y j i ∂μ) x =
        ρ * (∫ ω, pderiv i (fun y => u ω t y j * u ω t y i) x ∂μ) -
          ∫ ω, pderiv i (fun y => σ ω t y j i) x ∂μ := by
      have h1 := pderiv_ensemble (hS_uu i).1 hP rfl i
      have h2 := pderiv_ensemble (hS_σ i).1 hS rfl i
      have hPS' : HasFDerivAt (fun y => ρ * (∫ ω, u ω t y j * u ω t y i ∂μ) -
          ∫ ω, σ ω t y j i ∂μ) (ρ • (∫ ω, fderiv ℝ (fun y => u ω t y j * u ω t y i) x ∂μ) -
            ∫ ω, fderiv ℝ (fun y => σ ω t y j i) x ∂μ) x := (hP.const_mul ρ).sub hS
      simp only [pderiv] at h1 h2 ⊢
      rw [hPS'.fderiv]
      simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul]
      rw [← h1, ← h2, hP.fderiv, hS.fderiv]
    rw [hF, hR, ← hlin, hsum, hPS]
  -- the scenario side, one flux component at a time
  have hscen : ∀ᵐ ω ∂μ, ∀ i,
      pderiv i (fun y => momentumFlux (fun _ => ρ) (u ω t) (σ ω t) j y i) x =
        ρ * pderiv i (fun y => u ω t y j * u ω t y i) x - pderiv i (fun y => σ ω t y j i) x := by
    filter_upwards [hux, hσx] with ω hu' hσ' i
    have hd1 : DifferentiableAt ℝ (fun y => u ω t y j * u ω t y i) x :=
      (hu' x hx j).mul (hu' x hx i)
    have hd2 : DifferentiableAt ℝ (fun y => σ ω t y j i) x := hσ' x hx j i
    have hF : (fun y => momentumFlux (fun _ => ρ) (u ω t) (σ ω t) j y i) =
        fun y => ρ * (u ω t y j * u ω t y i) - σ ω t y j i := by
      funext y
      simp only [momentumFlux]
      ring
    simp only [pderiv]
    rw [hF, fderiv_fun_sub (hd1.const_mul ρ) hd2, fderiv_const_mul hd1]
    simp
  have hdt : ∀ᵐ ω ∂μ, deriv (fun τ => ρ * u ω τ x j) t = ρ * deriv (fun τ => u ω τ x j) t := by
    filter_upwards [hut] with ω h
    exact deriv_const_mul ρ (h t (Metric.mem_ball_self hε) j)
  -- integrate the scenario law
  have hint_uu : ∀ i, Integrable (fun ω => pderiv i (fun y => u ω t y j * u ω t y i) x) μ :=
    fun i => (hS_uu i).1.apply_continuousLinearMap _
  have hint_σ : ∀ i, Integrable (fun ω => pderiv i (fun y => σ ω t y j i) x) μ :=
    fun i => (hS_σ i).1.apply_continuousLinearMap _
  have hlaw' : ∀ᵐ ω ∂μ, ρ * deriv (fun τ => u ω τ x j) t +
      ∑ i, (ρ * pderiv i (fun y => u ω t y j * u ω t y i) x -
        pderiv i (fun y => σ ω t y j i) x) = f ω t x j := by
    filter_upwards [hlaw, hscen, hdt] with ω hl hs hd
    rw [← hl j, hd, divergence]
    congr 1
    exact Finset.sum_congr rfl fun i _ => (hs i).symm
  have hint_i : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), Integrable (fun ω =>
      ρ * pderiv i (fun y => u ω t y j * u ω t y i) x - pderiv i (fun y => σ ω t y j i) x) μ :=
    fun i _ => ((hint_uu i).const_mul ρ).sub (hint_σ i)
  have hint_sum : Integrable (fun ω => ∑ i, (ρ * pderiv i (fun y => u ω t y j * u ω t y i) x -
      pderiv i (fun y => σ ω t y j i) x)) μ := integrable_finsetSum _ hint_i
  have hI : ρ * (∫ ω, deriv (fun τ => u ω τ x j) t ∂μ) +
      ∑ i, (ρ * (∫ ω, pderiv i (fun y => u ω t y j * u ω t y i) x ∂μ) -
        ∫ ω, pderiv i (fun y => σ ω t y j i) x ∂μ) = ∫ ω, f ω t x j ∂μ := by
    rw [← integral_congr_ae hlaw', integral_add (hint_t.const_mul ρ) hint_sum,
      integral_const_mul, integral_finsetSum _ hint_i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_sub ((hint_uu i).const_mul ρ) (hint_σ i), integral_const_mul]
  -- assemble
  have hdivR : ρ * divergence (fun y i => reynoldsStress μ u t y j i) x =
      ∑ i, ρ * pderiv i (fun y => reynoldsStress μ u t y j i) x := by
    rw [divergence, Finset.mul_sum]
  rw [hT, eq_sub_iff_add_eq, add_assoc, hdivR, divergence, ← Finset.sum_add_distrib]
  rw [← hI]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hmean_i i

/-- The mean of an incompressible ensemble is incompressible: with integrable velocity
components, almost-sure differentiability near `x`, measurable derivatives at `x` and an
integrable bound on the velocity derivatives near `x`, if almost every realization has
`div u = 0` at `(t, x)` then `div 𝔼[u] = 0` there. -/
lemma divergence_ensembleMean_eq_zero {μ : Measure Ω} [IsProbabilityMeasure μ] {t ε : ℝ}
    {x : Fin (n + 1) → ℝ} {u : Ω → ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {B : Ω → ℝ}
    (hε : 0 < ε) (hu : ∀ y i, Integrable (fun ω => u ω t y i) μ)
    (hux : ∀ᵐ ω ∂μ, ∀ y ∈ Metric.ball x ε, ∀ i,
      DifferentiableAt ℝ (fun y' => u ω t y' i) y)
    (hux_meas : ∀ i, AEStronglyMeasurable (fun ω => fderiv ℝ (fun y => u ω t y i) x) μ)
    (hB : Integrable B μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ y ∈ Metric.ball x ε, ∀ i, ‖fderiv ℝ (fun y' => u ω t y' i) y‖ ≤ B ω)
    (hdiv : ∀ᵐ ω ∂μ, divergence (u ω t) x = 0) :
    divergence (ensembleMean μ u t) x = 0 := by
  open MathlibExt.Probability.FokkerPlanck in
  have hS_u : ∀ i, Integrable (fun ω => fderiv ℝ (fun y => u ω t y i) x) μ ∧
      HasFDerivAt (fun y => ∫ ω, u ω t y i ∂μ)
        (∫ ω, fderiv ℝ (fun y => u ω t y i) x ∂μ) x := fun i =>
    hasFDerivAt_ensemble_space (G := fun ω y => u ω t y i) hε
      (fun y => (hu y i).aestronglyMeasurable) (hu x i)
      (hux.mono fun _ h y hy => h y hy i) (hux_meas i) hB
      (hdom.mono fun _ h y hy => h y hy i)
  have hint : ∀ i, Integrable (fun ω => pderiv i (fun y => u ω t y i) x) μ :=
    fun i => (hS_u i).1.apply_continuousLinearMap _
  have h1 : divergence (ensembleMean μ u t) x =
      ∑ i, ∫ ω, pderiv i (fun y => u ω t y i) x ∂μ := by
    simp only [divergence]
    exact Finset.sum_congr rfl fun i _ => pderiv_ensemble (hS_u i).1 (hS_u i).2 rfl i
  rw [h1, ← integral_finsetSum _ fun i _ => hint i]
  rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (by
    filter_upwards [hdiv] with ω hω
    simpa [divergence] using hω)]
  simp

/-! ## C. The interchange without domination -/

/-- Counterexample profile for the case without domination:
`escapingProfile s ω = s ^ 3 / ω ^ 2 * exp (-s ^ 2 / ω)`. -/
noncomputable def escapingProfile (s ω : ℝ) : ℝ := s ^ 3 / ω ^ 2 * Real.exp (-s ^ 2 / ω)

/-- Derivative in `s` of the escaping profile, for every realization `ω`. -/
private lemma hasDerivAt_escapingProfile (ω s : ℝ) :
    HasDerivAt (fun s' => escapingProfile s' ω)
      ((3 * s ^ 2 / ω ^ 2 - 2 * s ^ 4 / ω ^ 3) * Real.exp (-s ^ 2 / ω)) s := by
  have h1 : HasDerivAt (fun s' : ℝ => s' ^ 3 / ω ^ 2) (3 * s ^ 2 / ω ^ 2) s := by
    simpa using (hasDerivAt_pow 3 s).div_const (ω ^ 2)
  have h2 : HasDerivAt (fun s' : ℝ => -s' ^ 2 / ω) (-(2 * s) / ω) s := by
    simpa using ((hasDerivAt_pow 2 s).neg).div_const ω
  have h := h1.mul h2.exp
  unfold escapingProfile
  convert h using 1
  ring

/-- The ensemble mean of the escaping profile for `s > 0`, by the fundamental theorem of
calculus with the antiderivative `s * exp (-s ^ 2 / ω)`, extended by `0` at `ω = 0`. -/
private lemma integral_escapingProfile_of_pos {s : ℝ} (hs : 0 < s) :
    ∫ ω in Set.Ioc (0 : ℝ) 1, escapingProfile s ω = s * Real.exp (-s ^ 2) := by
  set A : ℝ → ℝ := fun ω => if ω = 0 then 0 else s * Real.exp (-s ^ 2 / ω) with hA
  have hs2 : 0 < s ^ 2 := by positivity
  have hderiv : ∀ ω ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt A (escapingProfile s ω) ω := by
    intro ω hω
    have hω0 : ω ≠ 0 := ne_of_gt hω.1
    have hg : HasDerivAt (fun ω' => s * Real.exp (-s ^ 2 / ω')) (escapingProfile s ω) ω := by
      have h1 : HasDerivAt (fun ω' : ℝ => -s ^ 2 / ω') (s ^ 2 / ω ^ 2) ω := by
        have := (hasDerivAt_inv hω0).const_mul (-s ^ 2)
        convert this using 1
        · funext ω'
          simp [div_eq_mul_inv]
        · field_simp
      have h2 := (h1.exp).const_mul s
      convert h2 using 1
      unfold escapingProfile
      field_simp
    refine hg.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hω0] with ω' hω'
    simp [hA, hω']
  have hcont : ContinuousOn A (Set.Icc 0 1) := by
    intro ω hω
    rcases eq_or_lt_of_le hω.1 with h0 | hpos
    · subst h0
      have hlim : Filter.Tendsto (fun ω' => s * Real.exp (-s ^ 2 / ω'))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h1 : Filter.Tendsto (fun ω' : ℝ => -s ^ 2 / ω') (nhdsWithin 0 (Set.Ioi 0))
            Filter.atBot := by
          have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop_of_neg
            (show -s ^ 2 < 0 by linarith)
          refine this.congr fun ω' => ?_
          simp [div_eq_mul_inv]
        simpa using (Real.tendsto_exp_atBot.comp h1).const_mul s
      have hA0 : A 0 = 0 := by simp [hA]
      rw [ContinuousWithinAt, hA0]
      have hsplit : nhdsWithin (0 : ℝ) (Set.Icc 0 1) ≤
          nhdsWithin 0 {0} ⊔ nhdsWithin 0 (Set.Ioi 0) := by
        rw [← nhdsWithin_union]
        exact nhdsWithin_mono _ fun ω' hω' => by
          rcases eq_or_lt_of_le hω'.1 with h | h
          · exact Or.inl h.symm
          · exact Or.inr h
      refine Filter.Tendsto.mono_left ?_ hsplit
      refine Filter.Tendsto.sup ?_ ?_
      · rw [nhdsWithin_singleton]
        simpa [hA] using tendsto_pure_nhds A 0
      · refine hlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ω' hω'
        simp [hA, ne_of_gt (Set.mem_Ioi.mp hω')]
    · have hne : ω ≠ 0 := ne_of_gt hpos
      refine ContinuousAt.continuousWithinAt ?_
      have hc : ContinuousAt (fun ω' => s * Real.exp (-s ^ 2 / ω')) ω :=
        (continuousAt_const.mul ((continuousAt_const.div continuousAt_id hne).rexp))
      refine hc.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hne] with ω' hω'
      simp [hA, hω']
  have hnonneg : ∀ ω ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ escapingProfile s ω := by
    intro ω _
    unfold escapingProfile
    positivity
  have hint : IntegrableOn (fun ω => escapingProfile s ω) (Set.Ioc 0 1) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hnonneg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hint)
  rw [intervalIntegral.integral_of_le zero_le_one] at hftc
  rw [hftc]
  simp [hA]

/-- Without domination the interchange is not licensed. On the probability space `(0, 1]` with
Lebesgue measure every realization `s ↦ escapingProfile s ω` is differentiable, with derivative
`(3 s ^ 2 / ω ^ 2 - 2 s ^ 4 / ω ^ 3) exp (-s ^ 2 / ω)`, which is `0` at `s = 0`; but the ensemble
mean is `s * exp (-s ^ 2)`, whose derivative at `0` is `1`, not the mean `0` of the
derivatives. Hence no integrable function dominates the derivatives on any neighbourhood of
`0`. -/
lemma escapingProfile_interchange_fails :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
      (∀ ω s : ℝ, HasDerivAt (fun s' => escapingProfile s' ω)
        ((3 * s ^ 2 / ω ^ 2 - 2 * s ^ 4 / ω ^ 3) * Real.exp (-s ^ 2 / ω)) s) ∧
      (∀ s : ℝ, ∫ ω in Set.Ioc (0 : ℝ) 1, escapingProfile s ω = s * Real.exp (-s ^ 2)) ∧
      HasDerivAt (fun s => ∫ ω in Set.Ioc (0 : ℝ) 1, escapingProfile s ω) 1 0 ∧
      ¬ ∃ ε > 0, ∃ B : ℝ → ℝ, Integrable B (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
        ∀ᵐ ω ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ∀ s ∈ Metric.ball (0 : ℝ) ε,
          ‖(3 * s ^ 2 / ω ^ 2 - 2 * s ^ 4 / ω ^ 3) * Real.exp (-s ^ 2 / ω)‖ ≤ B ω := by
  have hprob : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    constructor
    simp
  have hodd : ∀ s ω, escapingProfile (-s) ω = -escapingProfile s ω := by
    intro s ω
    unfold escapingProfile
    ring_nf
  have hmean : ∀ s : ℝ, ∫ ω in Set.Ioc (0 : ℝ) 1, escapingProfile s ω = s * Real.exp (-s ^ 2) := by
    intro s
    rcases lt_trichotomy s 0 with hs | hs | hs
    · have h := integral_escapingProfile_of_pos (neg_pos.mpr hs)
      have h' : ∫ ω in Set.Ioc (0 : ℝ) 1, escapingProfile s ω =
          -∫ ω in Set.Ioc (0 : ℝ) 1, escapingProfile (-s) ω := by
        rw [← integral_neg]
        congr 1
        funext ω
        rw [hodd, neg_neg]
      rw [h', h]
      ring_nf
    · subst hs
      simp [escapingProfile]
    · exact integral_escapingProfile_of_pos hs
  have hG : HasDerivAt (fun s => ∫ ω in Set.Ioc (0 : ℝ) 1, escapingProfile s ω) 1 0 := by
    have hfun : (fun s => ∫ ω in Set.Ioc (0 : ℝ) 1, escapingProfile s ω) =
        fun s => s * Real.exp (-s ^ 2) := funext hmean
    rw [hfun]
    have h1 : HasDerivAt (fun s : ℝ => -s ^ 2) (-((2 : ℕ) * (0 : ℝ) ^ (2 - 1))) 0 :=
      (hasDerivAt_pow 2 (0 : ℝ)).neg
    have h : HasDerivAt (fun s : ℝ => s * Real.exp (-s ^ 2))
        (1 * Real.exp (-(0 : ℝ) ^ 2) +
          0 * (Real.exp (-(0 : ℝ) ^ 2) * -((2 : ℕ) * (0 : ℝ) ^ (2 - 1)))) 0 :=
      (hasDerivAt_id (0 : ℝ)).mul h1.exp
    convert h using 1
    norm_num
  refine ⟨hprob, hasDerivAt_escapingProfile, hmean, hG, ?_⟩
  rintro ⟨ε, hε, B, hB, hbound⟩
  have hmeasF : ∀ s : ℝ, AEStronglyMeasurable (fun ω => escapingProfile s ω)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro s
    unfold escapingProfile
    fun_prop
  have hmeasF' : AEStronglyMeasurable
      (fun ω : ℝ => (3 * (0 : ℝ) ^ 2 / ω ^ 2 - 2 * (0 : ℝ) ^ 4 / ω ^ 3) *
        Real.exp (-(0 : ℝ) ^ 2 / ω)) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    fun_prop
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s ω => escapingProfile s ω)
    (F' := fun s ω => (3 * s ^ 2 / ω ^ 2 - 2 * s ^ 4 / ω ^ 3) * Real.exp (-s ^ 2 / ω))
    (Metric.ball_mem_nhds (0 : ℝ) hε) (Filter.Eventually.of_forall hmeasF)
    (by simp [escapingProfile]) hmeasF' hbound hB
    (Filter.Eventually.of_forall fun ω s _ => hasDerivAt_escapingProfile ω s)).2
  have h0 : ∫ ω in Set.Ioc (0 : ℝ) 1, (3 * (0 : ℝ) ^ 2 / ω ^ 2 - 2 * (0 : ℝ) ^ 4 / ω ^ 3) *
      Real.exp (-(0 : ℝ) ^ 2 / ω) = 0 := by
    simp
  rw [h0] at h
  have := hG.unique h
  norm_num at this

/-! ## D. Closure dissipation versus realizability -/

section Closure

open scoped Matrix.Norms.Frobenius

/-- Boussinesq closure of the Reynolds stress per unit density in three dimensions,
`Rm = (2 k / 3) I - 2 νt S`, from the turbulent kinetic energy `k`, the eddy viscosity `νt` and
the mean rate of strain `S`. It models `𝔼[u'ᵢ u'ⱼ]` (`reynoldsStress`); the stress it exerts on
the mean flow is `-ρ Rm = 2 ρ νt S - (2 / 3) ρ k I`, tension positive. The definition is total;
the model domain is `k ≥ 0` and a symmetric trace-free `S`, and each result below assumes the
part of it that it uses. -/
noncomputable def modeledReynoldsStress (k νt : ℝ) (S : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (2 * k / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ) - (2 * νt) • S

/-- Mean-flow extraction: the production of turbulent kinetic energy per unit mass written with
the mean rate of strain, `P = -∑ᵢ ∑ⱼ Rᵢⱼ Sᵢⱼ`, for a Reynolds stress per unit density `R` and a
mean flow with rate of strain `S`. Energy leaves the mean flow when `P > 0`. -/
def meanFlowExtraction (R S : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  -∑ i, ∑ j, R i j * S i j

/-- The squared Frobenius norm of a `3 × 3` real matrix is the sum of its squared entries. -/
private lemma frobenius_norm_sq_fin_three (S : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖S‖ ^ 2 = ∑ i, ∑ j, S i j ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- **Mean-flow extraction of the closure.** For a trace-free mean rate of strain `S` the
isotropic part `(2 k / 3) I` does no work, and the closure extracts `P = 2 νt ‖S‖²`, where `‖S‖`
is the Frobenius norm, `‖S‖² = ∑ᵢ ∑ⱼ Sᵢⱼ²`; an identity for all real `k` and `νt`. -/
lemma meanFlowExtraction_modeledReynoldsStress (k νt : ℝ) {S : Matrix (Fin 3) (Fin 3) ℝ}
    (hS : S.trace = 0) :
    meanFlowExtraction (modeledReynoldsStress k νt S) S = 2 * νt * ‖S‖ ^ 2 := by
  rw [frobenius_norm_sq_fin_three, Matrix.trace_fin_three] at *
  simp [meanFlowExtraction, modeledReynoldsStress, Fin.sum_univ_three, Matrix.one_apply]
  linear_combination (-(2 * k / 3)) * hS

/-- **A nonnegative eddy viscosity extracts energy from the mean flow.** If `νt ≥ 0`, the
closure's extraction `2 νt ‖S‖²` is nonnegative, for every trace-free `S` and every real `k`. -/
lemma meanFlowExtraction_modeledReynoldsStress_nonneg (k : ℝ) {νt : ℝ}
    {S : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.trace = 0) (hνt : 0 ≤ νt) :
    0 ≤ meanFlowExtraction (modeledReynoldsStress k νt S) S := by
  rw [meanFlowExtraction_modeledReynoldsStress k νt hS]
  exact mul_nonneg (mul_nonneg zero_le_two hνt) (sq_nonneg _)

/-- **The converse needs a nonzero strain.** For a nonzero trace-free `S` and every real `k`, the
closure's extraction is nonnegative exactly when `νt ≥ 0`. -/
lemma meanFlowExtraction_modeledReynoldsStress_nonneg_iff (k : ℝ) {νt : ℝ}
    {S : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.trace = 0) (hS₀ : S ≠ 0) :
    0 ≤ meanFlowExtraction (modeledReynoldsStress k νt S) S ↔ 0 ≤ νt := by
  rw [meanFlowExtraction_modeledReynoldsStress k νt hS,
    mul_nonneg_iff_of_pos_right (pow_pos (norm_pos_iff.mpr hS₀) 2)]
  constructor <;> intro h <;> linarith

/-- **Without `S ≠ 0` the converse fails.** At the zero strain, which is symmetric and trace free,
the closure extracts nothing whatever the eddy viscosity, so nonnegative extraction does not
force `νt ≥ 0`: `k = 1` with `νt = -1` is a counterexample. -/
lemma meanFlowExtraction_nonneg_converse_fails :
    ¬ ∀ k νt : ℝ, 0 ≤ k →
      0 ≤ meanFlowExtraction (modeledReynoldsStress k νt 0) 0 → 0 ≤ νt := by
  intro h
  have h1 := h 1 (-1) zero_le_one (by simp [meanFlowExtraction])
  norm_num at h1

/-- **Plane-strain fixture.** For `k = 1`, `νt = 1` and the plane strain `S = diag(1, -1, 0)` (the
mean flow `U = (x, -y, 0)`), the closure is `Rm = diag(-4/3, 8/3, 2/3)`, with the negative entry
`Rm₀₀ = -4/3`, and it extracts `P = 4` from the mean flow. -/
lemma modeledReynoldsStress_planeStrain :
    modeledReynoldsStress 1 1 (Matrix.diagonal ![1, -1, 0]) =
        Matrix.diagonal ![-4 / 3, 8 / 3, 2 / 3] ∧
      meanFlowExtraction (modeledReynoldsStress 1 1 (Matrix.diagonal ![1, -1, 0]))
        (Matrix.diagonal ![1, -1, 0]) = 4 := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [modeledReynoldsStress, Matrix.one_apply, Matrix.diagonal_apply]
  · norm_num [meanFlowExtraction, modeledReynoldsStress, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.diagonal_apply]

/-- **A positive eddy viscosity does not give realizability.** For `k ≥ 0`, `νt > 0` and a
symmetric trace-free `S` the closure need not be positive semidefinite (`Matrix.PosSemidef`),
although the quadratic form of every Reynolds stress of `L²` velocities is nonnegative
(`reynoldsStress_posSemidef`): for the plane-strain fixture the quadratic form of the closure
along `e₀` is `Rm₀₀ = -4/3 < 0`. -/
lemma modeledReynoldsStress_realizability_fails :
    ¬ ∀ (k νt : ℝ) (S : Matrix (Fin 3) (Fin 3) ℝ), 0 ≤ k → 0 < νt → S.IsSymm → S.trace = 0 →
      (modeledReynoldsStress k νt S).PosSemidef := by
  intro h
  have htr : (Matrix.diagonal ![(1 : ℝ), -1, 0]).trace = 0 := by
    rw [Matrix.trace_fin_three]
    norm_num [Matrix.diagonal_apply]
  have hq := (h 1 1 (Matrix.diagonal ![1, -1, 0]) zero_le_one one_pos
    (Matrix.isSymm_diagonal _) htr).dotProduct_mulVec_nonneg ![1, 0, 0]
  rw [modeledReynoldsStress_planeStrain.1] at hq
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.diagonal_apply] at hq

end Closure

end FluidDynamics.EnsembleMomentum
