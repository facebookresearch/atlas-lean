/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Tests for `MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables`

* Finite-sample values of `attenuationFactor` and `correctedSlope`, computed from the
  definitions, including the boundaries `σ_u² = 0` (no attenuation, no correction).
* Non-vacuity of `ClassicalErrorsInVariables`: an i.i.d. Gaussian model with
  `Var ξ = Var u = 1`, built on `Measure.infinitePi`, satisfies every field and the variance
  hypotheses; the attenuation factor of this model is `1 / 2`, and the moment form of the
  population identity gives the population slope `β / 2` from its fields.
* `measurementError_population_attenuation` on a concrete model: independent Gaussian
  coordinates with `Var X = 4`, `Var e = 1`, a nonconstant equation error and `β = 2` give the
  population slope `8 / 5`; by `measurementError_population_slope_of_cov_eq_zero`, `8 / 5` is the
  unique `b` with `cov[W, Y - b W] = 0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open MathlibExt.Probability.FiniteProbability
open MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables

namespace MathlibExtTest.ErrorsInVariables

/-! ### Attenuation factor -/

example : attenuationFactor 3 1 = 3 / 4 := by norm_num [attenuationFactor]

example : attenuationFactor 1 1 = 1 / 2 := by norm_num [attenuationFactor]

/-- Boundary: without measurement error there is no attenuation. -/
example {σξ2 : ℝ} (h : σξ2 ≠ 0) : attenuationFactor σξ2 0 = 1 := by
  simp [attenuationFactor, h]

/-- Measurement error strictly attenuates: `λ < 1` when `σ_u² > 0`. -/
example {σξ2 σu2 : ℝ} (hξ : 0 < σξ2) (hu : 0 < σu2) : attenuationFactor σξ2 σu2 < 1 := by
  rw [attenuationFactor, div_lt_one (by linarith)]
  linarith

/-! ### Finite-sample slopes on concrete data -/

/-- Observed regressor `x = (0, 1, 2)`. -/
noncomputable def x₀ : Fin 3 → ℝ := ![0, 1, 2]

/-- Response `y = 1 + 2 x`. -/
noncomputable def y₀ : Fin 3 → ℝ := ![1, 3, 5]

theorem sxy_x₀_x₀ : sxy x₀ x₀ = 2 := by
  norm_num [sxy, sampleMean_eq_sum_div, Fin.sum_univ_three, x₀]

theorem sxy_x₀_y₀ : sxy x₀ y₀ = 4 := by
  norm_num [sxy, sampleMean_eq_sum_div, Fin.sum_univ_three, x₀, y₀]

/-- The naive slope recovers `2` on exact data. -/
example : olsSlope x₀ y₀ = 2 := by
  rw [olsSlope, sxy_x₀_y₀, sxy_x₀_x₀]; norm_num

/-- Boundary `σu2 = 0`: no correction, computed from the definition. -/
example : correctedSlope x₀ y₀ 0 = 2 := by
  rw [correctedSlope, sxy_x₀_y₀, sxy_x₀_x₀]; norm_num

/-- A positive assumed measurement-error variance inflates the slope:
`4 / (2 - 3 · (1/3)) = 4`. -/
example : correctedSlope x₀ y₀ (1 / 3) = 4 := by
  rw [correctedSlope, sxy_x₀_y₀, sxy_x₀_x₀]; norm_num

/-- Junk value when the corrected denominator vanishes: `σu2 = s_x² = 2/3`. -/
example : correctedSlope x₀ y₀ (2 / 3) = 0 := by
  rw [correctedSlope, sxy_x₀_y₀, sxy_x₀_x₀]; norm_num

/-- The reliability-ratio form agrees with the definition on this data. -/
example : correctedSlope x₀ y₀ (1 / 3) = olsSlope x₀ y₀ / ((sampleVar x₀ - 1 / 3) / sampleVar x₀) :=
  correctedSlope_eq_olsSlope_div (by rw [sxy_x₀_x₀]; norm_num) _ _

example : sampleVar x₀ = 2 / 3 := by
  rw [sampleVar_eq_sxy_div, sxy_x₀_x₀]; norm_num

/-- `sxy_div_eq` on the sequence `a i = i`, `b i = 1 + 2 i`, first three terms. -/
example :
    sxy (fun i : Fin 3 => ((i : ℕ) : ℝ)) (fun i => 1 + 2 * ((i : ℕ) : ℝ)) / (3 : ℕ) = 4 / 3 := by
  rw [sxy_div_eq (fun i => (i : ℝ)) (fun i => 1 + 2 * (i : ℝ)) 3]
  norm_num [Finset.sum_range_succ]

/-! ### Non-vacuity: an i.i.d. Gaussian errors-in-variables model -/

/-- Per-observation law of `(ξ, u)`: independent standard normals. -/
noncomputable abbrev ν : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- The i.i.d. sequence of pairs `(ξ i, u i)`. -/
noncomputable abbrev P : Measure (ℕ → ℝ × ℝ) := Measure.infinitePi fun _ => ν

/-- Latent regressor. -/
abbrev ξ : ℕ → (ℕ → ℝ × ℝ) → ℝ := fun i ω => (ω i).1

/-- Measurement error. -/
abbrev u : ℕ → (ℕ → ℝ × ℝ) → ℝ := fun i ω => (ω i).2

/-- Equation error (identically zero). -/
abbrev ε : ℕ → (ℕ → ℝ × ℝ) → ℝ := fun _ _ => 0

theorem memLp_fst : MemLp (fun p : ℝ × ℝ => p.1) 2 ν :=
  (memLp_id_gaussianReal 2).comp_fst _

theorem memLp_snd : MemLp (fun p : ℝ × ℝ => p.2) 2 ν :=
  (memLp_id_gaussianReal 2).comp_snd _

theorem map_eval_zero : P.map (fun ω => ω 0) = ν :=
  Measure.infinitePi_map_eval _ 0

theorem variance_fst : Var[fun p : ℝ × ℝ => p.1; ν] = 1 := by
  have h := variance_map (μ := ν) (X := id) (Y := Prod.fst) aemeasurable_id (by fun_prop)
  rw [Measure.map_fst_prod, measure_univ, one_smul, variance_id_gaussianReal] at h
  exact_mod_cast h.symm

theorem variance_snd : Var[fun p : ℝ × ℝ => p.2; ν] = 1 := by
  have h := variance_map (μ := ν) (X := id) (Y := Prod.snd) aemeasurable_id (by fun_prop)
  rw [Measure.map_snd_prod, measure_univ, one_smul, variance_id_gaussianReal] at h
  exact_mod_cast h.symm

theorem variance_ξ : Var[ξ 0; P] = 1 := by
  have h := variance_map (μ := P) (X := fun p : ℝ × ℝ => p.1) (Y := fun ω => ω 0)
    (by fun_prop) (measurable_pi_apply 0).aemeasurable
  rw [map_eval_zero, variance_fst] at h
  exact h.symm

theorem variance_u : Var[u 0; P] = 1 := by
  have h := variance_map (μ := P) (X := fun p : ℝ × ℝ => p.2) (Y := fun ω => ω 0)
    (by fun_prop) (measurable_pi_apply 0).aemeasurable
  rw [map_eval_zero, variance_snd] at h
  exact h.symm

/-- The Gaussian model satisfies every hypothesis of `ClassicalErrorsInVariables`. -/
theorem classicalErrorsInVariables_gaussian : ClassicalErrorsInVariables P ξ u ε where
  indepFun := fun _ _ hij =>
    (iIndepFun_infinitePi (P := fun _ => ν) (X := fun _ p => (p.1, p.2, (0 : ℝ)))
      (fun _ => by fun_prop)).indepFun hij
  identDistrib := fun i =>
    (IdentDistrib.mk (μ := P) (ν := P) (f := fun ω : ℕ → ℝ × ℝ => ω i)
      (g := fun ω : ℕ → ℝ × ℝ => ω 0) (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply 0).aemeasurable
      (by rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval])).comp
      (u := fun p : ℝ × ℝ => (p.1, p.2, (0 : ℝ))) (by fun_prop)
  memLp_signal := memLp_fst.comp_measurePreserving (measurePreserving_eval_infinitePi _ 0)
  memLp_measurementError :=
    memLp_snd.comp_measurePreserving (measurePreserving_eval_infinitePi _ 0)
  memLp_equationError := memLp_const 0
  cov_signal_measurementError := by
    have h := covariance_map (μ := P) (X := fun p : ℝ × ℝ => p.1) (Y := fun p => p.2)
      (Z := fun ω => ω 0) (by fun_prop) (by fun_prop) (measurable_pi_apply 0).aemeasurable
    rw [map_eval_zero, covariance_fst_snd_prod (X := fun x => x) (Y := fun x => x)
      (memLp_id_gaussianReal 2) (memLp_id_gaussianReal 2)] at h
    exact h.symm
  cov_signal_equationError := covariance_const_right 0
  cov_measurementError_equationError := covariance_const_right 0

/-- The variance hypotheses of the main theorems hold in the Gaussian model. -/
example : 0 < Var[ξ 0; P] + Var[u 0; P] ∧ Var[ξ 0; P] ≠ 0 := by
  rw [variance_ξ, variance_u]; norm_num

/-- The Gaussian model has attenuation factor `1 / 2`. -/
theorem attenuationFactor_gaussian : attenuationFactor Var[ξ 0; P] Var[u 0; P] = 1 / 2 := by
  rw [variance_ξ, variance_u]; norm_num [attenuationFactor]

/-- Usage: the moment form of the population identity takes the fields of
`ClassicalErrorsInVariables` directly; in the Gaussian model the population slope of `y` on `x`
is `β / 2`. -/
example (β₀ β : ℝ) :
    cov[fun ω => ξ 0 ω + u 0 ω, fun ω => β₀ + β * ξ 0 ω + ε 0 ω; P] /
      Var[fun ω => ξ 0 ω + u 0 ω; P] = 1 / 2 * β := by
  have h := classicalErrorsInVariables_gaussian
  rw [measurementError_population_attenuation_of_cov_eq_zero h.memLp_signal
    h.memLp_measurementError h.memLp_equationError h.cov_signal_measurementError
    h.cov_signal_equationError h.cov_measurementError_equationError, attenuationFactor_gaussian]

/-- Usage: in the Gaussian model the naive slope converges almost surely to `β / 2`. -/
example (β₀ β : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => olsSlope (fun i : Fin n => ξ i ω + u i ω)
      (fun i => β₀ + β * ξ i ω + ε i ω)) atTop (𝓝 (1 / 2 * β)) := by
  have h := classicalErrorsInVariables_gaussian.ae_tendsto_olsSlope_attenuation β₀ β
    (by rw [variance_ξ, variance_u]; norm_num)
  rwa [attenuationFactor_gaussian] at h

/-- Usage: the corrected slope with the known `σ_u² = 1` converges almost surely to `β`. -/
example (β₀ β : ℝ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => correctedSlope (fun i : Fin n => ξ i ω + u i ω)
      (fun i => β₀ + β * ξ i ω + ε i ω) 1) atTop (𝓝 β) := by
  have h := classicalErrorsInVariables_gaussian.ae_tendsto_correctedSlope β₀ β
    (by rw [variance_ξ]; norm_num)
  rwa [variance_u] at h

/-! ### Population attenuation on a concrete Gaussian model -/

/-- Variances of the coordinates `(X, e, ε)` of the population model. -/
noncomputable abbrev σ2 : Fin 3 → NNReal := ![4, 1, 1]

/-- Law of `(X, e, ε)`: independent centered normals with variances `4`, `1` and `1`. -/
noncomputable abbrev Q : Measure (Fin 3 → ℝ) := Measure.pi fun i => gaussianReal 0 (σ2 i)

theorem memLp_coord (i : Fin 3) : MemLp (fun ω : Fin 3 → ℝ => ω i) 2 Q :=
  (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_eval _ i)

theorem indepFun_coord {i j : Fin 3} (hij : i ≠ j) :
    IndepFun (fun ω : Fin 3 → ℝ => ω i) (fun ω => ω j) Q :=
  (iIndepFun_pi (μ := fun i => gaussianReal 0 (σ2 i))
    (X := fun (_ : Fin 3) (x : ℝ) => x) (fun _ => aemeasurable_id)).indepFun hij

theorem variance_coord (i : Fin 3) : Var[fun ω : Fin 3 → ℝ => ω i; Q] = σ2 i := by
  have h := variance_map (μ := Q) (X := id) (Y := fun ω => ω i) aemeasurable_id
    (measurable_pi_apply i).aemeasurable
  rw [(measurePreserving_eval _ i).map_eq, variance_id_gaussianReal] at h
  exact h.symm

/-- The observed regressor `W = X + e` has variance `4 + 1 = 5`. -/
theorem variance_W : Var[fun ω : Fin 3 → ℝ => ω 0 + ω 1; Q] = 5 := by
  have h := (indepFun_coord (i := 0) (j := 1) (by decide)).variance_add (memLp_coord 0)
    (memLp_coord 1)
  rw [show (fun ω : Fin 3 → ℝ => ω 0 + ω 1) = (fun ω => ω 0) + (fun ω => ω 1) from rfl, h,
    variance_coord, variance_coord]
  norm_num [σ2]

/-- Non-degenerate population attenuation: `X`, `e` and the equation error `ε` are nonconstant
and independent, `Var X = 4` differs from `Var e = 1`, and `β = 2` differs from its reciprocal.
The slope of `Y = 1 + 2 X + ε` on `W = X + e` is `λ β = (4 / 5) · 2 = 8 / 5`, strictly between
`0` and `β`; the reverse slope `cov[W, Y] / Var[Y]` is `8 / 17`. -/
example : cov[fun ω : Fin 3 → ℝ => ω 0 + ω 1, fun ω => 1 + 2 * ω 0 + ω 2; Q] /
    Var[fun ω : Fin 3 → ℝ => ω 0 + ω 1; Q] = 8 / 5 := by
  have h := measurementError_population_attenuation (μ := Q) (X := fun ω => ω 0)
    (e := fun ω => ω 1) (ε := fun ω => ω 2) (α := 1) (β := 2) (memLp_coord 0) (memLp_coord 1)
    (memLp_coord 2) (indepFun_coord (by decide)) (indepFun_coord (by decide))
    (indepFun_coord (by decide)) (by rw [variance_W]; norm_num)
  rw [h, variance_coord, variance_coord]
  norm_num [attenuationFactor, σ2]

/-- The nondegenerate slope form on the same model: `8 / 5` is the unique `b` for which the
residual `Y - b W` is uncorrelated with `W`. -/
example (b : ℝ) :
    cov[fun ω : Fin 3 → ℝ => ω 0 + ω 1, fun ω => 1 + 2 * ω 0 + ω 2 - b * (ω 0 + ω 1); Q] = 0 ↔
      b = 8 / 5 := by
  have h := measurementError_population_slope_of_cov_eq_zero (μ := Q) (X := fun ω => ω 0)
    (e := fun ω => ω 1) (ε := fun ω => ω 2) (α := 1) (β := 2) (memLp_coord 0) (memLp_coord 1)
    (memLp_coord 2)
    ((indepFun_coord (by decide)).covariance_eq_zero (memLp_coord 0) (memLp_coord 1))
    ((indepFun_coord (by decide)).covariance_eq_zero (memLp_coord 0) (memLp_coord 2))
    ((indepFun_coord (by decide)).covariance_eq_zero (memLp_coord 1) (memLp_coord 2))
    (by rw [variance_W]; norm_num) b
  rw [h, variance_coord, variance_coord]
  norm_num [attenuationFactor, σ2]

end MathlibExtTest.ErrorsInVariables
