/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.StochasticSIRDiffusion
import MathlibExt.Biology.Epidemiology.StochasticSIRKurtz
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Tests for the SIR diffusion approximation.

* A concrete parameter set (`β = 2`, `γ = log 2`, `s(0) = 0`, `i(0) = 1`), where the limit
  covariance at `t = 1` is computed from the Lyapunov equation and its uniqueness:
  `V(1) = (0, 0, 1/4)`.
* The degenerate case of zero initial infectives, where the limit covariance vanishes and the
  diffusion approximation applies with the zero fluctuation path. A constant driving path has
  no increments, so it leaves the zero fluctuation path unchanged, and every fluctuation path
  starts at its initial value.
* `StochasticSIR.tendsto_measure_deviation` concludes the hypothesis of
  `tendsto_measure_norm_sub_of_deviation`.
* A case where the CLT scaling fails: for `N = 1` the scaled fluctuation of the infectives at
  `t = 1` lives on the two points `±1/2`, so its law is not the Gaussian limit law. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal

namespace MathlibExtTest.Biology.Epidemiology.StochasticSIRDiffusion

open MathlibExt.Biology.Epidemiology
open MathlibExt.Biology.Epidemiology.StochasticSIRDiffusion

/-! ### A concrete parameter set: `β = 2`, `γ = log 2`, `s(0) = 0`, `i(0) = 1` -/

/-- The infective density with no susceptibles: `i(t) = e^{-γ t} = 2^{-t}` for `γ = log 2`. -/
noncomputable def infected (t : ℝ) : ℝ := exp (-(log 2 * t))

theorem hasDerivAt_infected (t : ℝ) : HasDerivAt infected (-(log 2 * infected t)) t := by
  have h1 := ((hasDerivAt_id' t).const_mul (log 2)).neg
  have h2 : HasDerivAt infected (exp (-(log 2 * t)) * -(log 2 * 1)) t := h1.exp
  exact h2.congr_deriv (by simp only [infected]; ring)

theorem infected_zero : infected 0 = 1 := by simp [infected]

theorem infected_one : infected 1 = 1 / 2 := by
  simp [infected, exp_neg, exp_log (by norm_num : (0 : ℝ) < 2)]

/-- `s ≡ 0`, `i(t) = 2^{-t}`, `r(t) = 1 - 2^{-t}` solves the SIR system with `β = 2`,
`γ = log 2` in densities. -/
theorem isSolution_removal :
    SIR.IsSolution 2 (log 2) 1 (fun _ => 0) infected (fun t => 1 - infected t) where
  hasDerivAt_susceptible t _ := by simpa using hasDerivAt_const t (0 : ℝ)
  hasDerivAt_infected t _ := by simpa using hasDerivAt_infected t
  hasDerivAt_removed t _ := by simpa using (hasDerivAt_infected t).const_sub 1

/-- The candidate limit covariance `V(t) = (0, 0, i(t) - i(t)²)`. -/
noncomputable def covRemoval (t : ℝ) : ℝ × ℝ × ℝ := (0, 0, infected t - infected t ^ 2)

/-- `covRemoval` solves the Lyapunov equation around `x = (0, i)` from `V(0) = 0`. Here
`DF(x) = [[-2 i, 0], [2 i, -γ]]` and `G(x) = diag(0, γ i)`, so `V₂₂' = -2 γ V₂₂ + γ i`. -/
theorem isLimitCovariance_removal :
    IsLimitCovariance 2 (log 2) (fun t => (0, infected t)) 0 covRemoval where
  initial := by simp [covRemoval, infected_zero]
  hasDerivAt t _ := by
    have hi := hasDerivAt_infected t
    have h : HasDerivAt covRemoval ((0 : ℝ), (0 : ℝ),
        -(log 2 * infected t) - ((2 : ℕ) : ℝ) * infected t ^ (2 - 1) * -(log 2 * infected t)) t :=
      (hasDerivAt_const t (0 : ℝ)).prodMk ((hasDerivAt_const t (0 : ℝ)).prodMk (hi.sub (hi.pow 2)))
    refine h.congr_deriv ?_
    simp only [lyapunovField_apply, covRemoval, Prod.mk.injEq]
    refine ⟨by ring, by ring, by norm_num; ring⟩

/-- **Limit covariance at `t = 1`, computed from the definitions.** Any limit covariance of
the concrete parameter set started from `0` equals `(0, 0, 1/4)` at `t = 1`: the susceptible
fluctuation and the cross term vanish, and the infective fluctuation has variance
`i(1) (1 - i(1)) = 1/4`, the binomial variance of independent removals. -/
theorem limitCovariance_one {V : ℝ → ℝ × ℝ × ℝ}
    (hV : IsLimitCovariance 2 (log 2) (fun t => (0, infected t)) 0 V) :
    V 1 = (0, 0, 1 / 4) := by
  have hxc : ContinuousOn (fun t => ((0 : ℝ), infected t)) (Icc 0 1) :=
    (continuous_const.prodMk (continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_infected t).continuousAt)).continuousOn
  rw [hV.eqOn (by norm_num) (log_nonneg (by norm_num)) hxc isLimitCovariance_removal
    ⟨zero_le_one, le_rfl⟩]
  simp only [covRemoval, infected_one, Prod.mk.injEq]
  norm_num

/-! ### Degenerate case: zero initial infectives -/

/-- The disease-free state `(s, i, r) = (1, 0, 0)` solves the SIR system. -/
theorem isSolution_diseaseFree (β γ : ℝ) :
    SIR.IsSolution β γ 1 (fun _ => 1) (fun _ => 0) (fun _ => 0) where
  hasDerivAt_susceptible t _ := by simpa using hasDerivAt_const t (1 : ℝ)
  hasDerivAt_infected t _ := by simpa using hasDerivAt_const t (0 : ℝ)
  hasDerivAt_removed t _ := by simpa using hasDerivAt_const t (0 : ℝ)

/-- With zero infectives the Lyapunov field vanishes at `V = 0`: `G(1, 0) = 0`. -/
theorem lyapunovField_diseaseFree (β γ : ℝ) : lyapunovField β γ (1, 0) 0 = 0 := by
  simp [lyapunovField_apply]

/-- **Fluctuations vanish (covariance).** With zero initial infectives, every limit covariance
started from `0` is identically `0`. -/
theorem limitCovariance_diseaseFree {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    {V : ℝ → ℝ × ℝ × ℝ} (hV : IsLimitCovariance β γ (fun _ => (1, 0)) 0 V) {t : ℝ}
    (ht : 0 ≤ t) : V t = 0 := by
  have h0 : IsLimitCovariance β γ (fun _ => (1, 0)) 0 (fun _ => 0) :=
    ⟨rfl, fun t _ => by rw [lyapunovField_diseaseFree]; exact hasDerivAt_const t _⟩
  exact hV.eqOn hβ hγ continuousOn_const h0 ⟨ht, le_rfl⟩

/-- **Fluctuations vanish (paths).** With zero initial infectives the chain never moves, so its
density path is constant at `(1, 0)`. All hypotheses of the diffusion approximation hold with
`U₀ = 0`, `M = 0`, `U = 0`, and the theorem gives `√N (X_N - x) → 0` uniformly in
probability. -/
theorem tendsto_fluctuation_diseaseFree {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {β γ T ε : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hε : 0 < ε) :
    Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      ε ≤ ‖fluctuation (fun _ (_ : Ω) _ => ((1 : ℝ), (0 : ℝ))) (fun _ => (1, 0)) N ω t -
        (0 : ℝ × ℝ)‖}) atTop (𝓝 0) :=
  tendsto_measure_fluctuation_sub (μ := μ) hβ hγ (isSolution_diseaseFree β γ)
    (X := fun _ _ _ => ((1 : ℝ), (0 : ℝ))) (fun _ _ => measurable_const)
    (fun δ hδ => by simp [not_le.2 hδ]) (U₀ := fun _ => 0) measurable_const
    (fun δ hδ => by simp [fluctuation, not_le.2 hδ]) (M := fun _ _ => 0)
    (fun _ => continuousOn_const) (fun _ => measurable_const)
    (fun δ hδ => by simp [scaledMartingale, drift, not_le.2 hδ]) (U := fun _ _ => 0)
    (fun _ => ⟨continuousOn_const, fun t _ => by simp⟩) hε

/-- The zero path is the only fluctuation path with zero initial value and zero driving noise
around the disease-free state. -/
theorem isFluctuationPath_diseaseFree_eq_zero {β γ T : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    {U : ℝ → ℝ × ℝ} (hU : IsFluctuationPath β γ T (fun _ => (1, 0)) 0 (fun _ => 0) U) :
    ∀ t ∈ Icc 0 T, U t = 0 :=
  hU.unique hβ hγ continuousOn_const ⟨continuousOn_const, fun t _ => by simp⟩

/-- The driving path enters only through its increments: the constant path `m ≡ (5, 5)` drives
nothing, so the fluctuation path from `0` around the disease-free state is still `0`. -/
example {β γ T : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {U : ℝ → ℝ × ℝ}
    (hU : IsFluctuationPath β γ T (fun _ => (1, 0)) 0 (fun _ => ((5 : ℝ), (5 : ℝ))) U) :
    ∀ t ∈ Icc 0 T, U t = 0 :=
  hU.unique hβ hγ continuousOn_const ⟨continuousOn_const, fun t _ => by simp⟩

/-- A solution driven by a path with `m(0) ≠ 0` exists and starts at its initial value. -/
example : ∃ U, IsFluctuationPath 2 1 1 (fun _ => (1, 0)) (1, 1) (fun t => (t + 5, 5)) U ∧
    U 0 = (1, 1) := by
  obtain ⟨U, hU⟩ := exists_isFluctuationPath (β := 2) (γ := 1) (T := 1) (by norm_num)
    (by norm_num) continuousOn_const (1, 1) (m := fun t => (t + 5, 5)) (by fun_prop)
  exact ⟨U, hU, hU.initial zero_le_one⟩

/-- `StochasticSIR.tendsto_measure_deviation` concludes exactly the hypothesis of
`tendsto_measure_norm_sub_of_deviation`: its `deviation` is the `ℓ¹` sum used there. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S I R : ℕ → Ω → ℝ → ℕ}
    {s i r : ℝ → ℝ} {T : ℝ}
    (h : ∀ ε, 0 < ε → Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      ε ≤ StochasticSIR.deviation N (S N ω) (I N ω) (R N ω) s i r t}) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      δ ≤ ‖((S N ω t : ℝ) / N, (I N ω t : ℝ) / N) - (s t, i t)‖}) atTop (𝓝 0) :=
  tendsto_measure_norm_sub_of_deviation h hδ

/-! ### Failure of the CLT scaling for small `N` -/

/-- **The Gaussian limit is wrong at `N = 1`.** In the concrete parameter set with population
size `N = 1`, the single individual is infective or removed, so `X_1(1) ∈ {(0, 0), (0, 1)}`
while `x(1) = (0, 1/2)`. The scaled infective fluctuation `√1 (I(1) - i(1))` then takes only the
values `±1/2`, and its law is not a non-degenerate Gaussian; in particular it is not the CLT
limit law `N(0, V₂₂(1)) = N(0, 1/4)` (`limitCovariance_one`). -/
theorem map_fluctuation_ne_gaussianReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ → ℝ × ℝ)
    (hX : ∀ ω, X 1 ω 1 = (0, 0) ∨ X 1 ω 1 = (0, 1))
    (hmeas : Measurable fun ω => (fluctuation X (fun t => (0, infected t)) 1 ω 1).2)
    {v : ℝ≥0} (hv : v ≠ 0) :
    μ.map (fun ω => (fluctuation X (fun t => (0, infected t)) 1 ω 1).2) ≠ gaussianReal 0 v := by
  intro h
  set S : Set ℝ := {-(1 / 2), 1 / 2}
  have hpre : (fun ω => (fluctuation X (fun t => (0, infected t)) 1 ω 1).2) ⁻¹' S = univ := by
    ext ω
    simp only [mem_preimage, mem_univ, iff_true, S, fluctuation, Nat.cast_one, sqrt_one,
      one_smul, Prod.snd_sub, infected_one, mem_insert_iff, mem_singleton_iff]
    rcases hX ω with h0 | h1
    · left; rw [h0]; norm_num
    · right; rw [h1]; norm_num
  have hmap : μ.map (fun ω => (fluctuation X (fun t => (0, infected t)) 1 ω 1).2) S = 1 := by
    rw [Measure.map_apply hmeas (Set.toFinite S).measurableSet, hpre, measure_univ]
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  have hgauss : gaussianReal 0 v S = 0 := (Set.toFinite S).measure_zero _
  rw [h, hgauss] at hmap
  exact zero_ne_one hmap

/-- The two facts side by side: the CLT variance at `t = 1` is `1/4`, and at `N = 1` the law of
the scaled fluctuation is not `N(0, 1/4)`. -/
theorem clt_fails_at_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ → ℝ × ℝ)
    (hX : ∀ ω, X 1 ω 1 = (0, 0) ∨ X 1 ω 1 = (0, 1))
    (hmeas : Measurable fun ω => (fluctuation X (fun t => (0, infected t)) 1 ω 1).2) :
    (covRemoval 1).2.2 = 1 / 4 ∧
      μ.map (fun ω => (fluctuation X (fun t => (0, infected t)) 1 ω 1).2) ≠
        gaussianReal 0 (1 / 4) := by
  refine ⟨by rw [limitCovariance_one isLimitCovariance_removal], ?_⟩
  exact map_fluctuation_ne_gaussianReal μ X hX hmeas (by norm_num)

end MathlibExtTest.Biology.Epidemiology.StochasticSIRDiffusion
