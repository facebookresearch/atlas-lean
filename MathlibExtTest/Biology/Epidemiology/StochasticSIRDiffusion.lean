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
import Mathlib.Probability.Moments.Variance

/-! Tests for the SIR diffusion approximation.

* A concrete parameter set (`β = 2`, `γ = log 2`, `s(0) = 0`, `i(0) = 1`), where the limit
  covariance at `t = 1` is computed from the Lyapunov equation and its uniqueness:
  `V(1) = (0, 0, 1/4)`.
* The degenerate case of zero initial infectives, where the limit covariance vanishes and the
  diffusion approximation (both forms) applies with the zero fluctuation path. A constant
  driving path has no increments, so it leaves the zero fluctuation path unchanged, and every
  fluctuation path starts at its initial value. The Lyapunov equation constrains the covariance
  path only on `[0, ∞)`: changing it at negative times, even discontinuously, keeps it a limit
  covariance.
* `StochasticSIR.tendsto_measure_deviation` concludes the hypothesis of
  `tendsto_measure_norm_sub_of_deviation`.
* A case where the CLT scaling fails: for `N = 1` the scaled fluctuation of the infectives at
  `t = 1` lives on the two points `±1/2`, so its law is not the Gaussian limit law.
* The Gaussian limit in the concrete parameter set: for Gaussian driving data with the
  martingale covariance `quadCov`, `U(1)` is centered Gaussian with covariance
  `V(1) = (0, 0, 1/4)`, and its infective coordinate has law `N(0, 1/4)`.
* A fully discharged instance of the Gaussian limit: a standard Gaussian initial infective
  fluctuation, no driving noise, `β = γ = 1` around the disease-free state, where
  `U(2)` is Gaussian with covariance `(4, -2, 1)`, the solution of the Lyapunov equation.
* Without Gaussian driving data the Gaussian conclusion fails: a Rademacher initial value gives a
  fluctuation path whose second moments match the limit covariance but whose law is not
  Gaussian. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal ProbabilityTheory

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
  hasDerivWithinAt t _ := by
    have hi := hasDerivAt_infected t
    have h : HasDerivAt covRemoval ((0 : ℝ), (0 : ℝ),
        -(log 2 * infected t) - ((2 : ℕ) : ℝ) * infected t ^ (2 - 1) * -(log 2 * infected t)) t :=
      (hasDerivAt_const t (0 : ℝ)).prodMk ((hasDerivAt_const t (0 : ℝ)).prodMk (hi.sub (hi.pow 2)))
    refine (h.congr_deriv ?_).hasDerivWithinAt
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
    ⟨rfl, fun t _ => by
      rw [lyapunovField_diseaseFree]; exact (hasDerivAt_const t _).hasDerivWithinAt⟩
  exact hV.eqOn hβ hγ continuousOn_const h0 ⟨ht, le_rfl⟩

/-- The Lyapunov equation constrains `V` only on `[0, ∞)`: the disease-free covariance path with
a jump to `1` at negative times, which has no two-sided derivative at `t = 0`, is still a limit
covariance. -/
example (β γ : ℝ) :
    IsLimitCovariance β γ (fun _ => (1, 0)) 0 (fun t => if 0 ≤ t then 0 else 1) := by
  refine ⟨by simp, fun t ht => ?_⟩
  rw [ite_eq_left ht, lyapunovField_diseaseFree]
  exact (hasDerivWithinAt_const t (Ici 0) 0).congr_of_mem (fun u hu => ite_eq_left hu) ht

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

/-- The supremum form of the diffusion approximation applies to the same data. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {β γ T ε : ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hε : 0 < ε) :
    Tendsto (fun N => μ {ω | ENNReal.ofReal ε ≤ ⨆ t ∈ Icc 0 T, ENNReal.ofReal
      ‖fluctuation (fun _ (_ : Ω) _ => ((1 : ℝ), (0 : ℝ))) (fun _ => (1, 0)) N ω t -
        (0 : ℝ × ℝ)‖}) atTop (𝓝 0) :=
  tendsto_measure_iSup_fluctuation_sub (μ := μ) hβ hγ (isSolution_diseaseFree β γ)
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

/-! ### The Gaussian limit -/

theorem gaussianLimit_removal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace C(Icc (0 : ℝ) 1, ℝ × ℝ)] [BorelSpace C(Icc (0 : ℝ) 1, ℝ × ℝ)]
    {U₀ : Ω → ℝ × ℝ} {M : Ω → ℝ → ℝ × ℝ} {Z : Ω → (ℝ × ℝ) × C(Icc (0 : ℝ) 1, ℝ × ℝ)}
    (hZ : HasGaussianLaw Z P) (hZU₀ : ∀ ω, (Z ω).1 = U₀ ω)
    (hZM : ∀ ω (s : Icc (0 : ℝ) 1), (Z ω).2 s = M ω s)
    (hmean₀ : ∫ ω, U₀ ω ∂P = 0) (hmeanM : ∀ s ∈ Icc (0 : ℝ) 1, ∫ ω, (M ω s - M ω 0) ∂P = 0)
    (hcov₀ : ∀ a b, ∫ ω, dot a (U₀ ω) * dot b (U₀ ω) ∂P = quadForm 0 a b)
    (hcross : ∀ a b, ∀ s ∈ Icc (0 : ℝ) 1, ∫ ω, dot a (U₀ ω) * dot b (M ω s - M ω 0) ∂P = 0)
    (hcovM : ∀ a b, ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1,
      ∫ ω, dot a (M ω s - M ω 0) * dot b (M ω r - M ω 0) ∂P =
        quadForm (quadCov 2 (log 2) (fun t => (0, infected t)) (min s r)) a b)
    {U : Ω → ℝ → ℝ × ℝ}
    (hU : ∀ ω, IsFluctuationPath 2 (log 2) 1 (fun t => (0, infected t)) (U₀ ω) (M ω) (U ω)) :
    HasGaussianLaw (fun ω => U ω 1) P ∧
      cov[fun ω => (U ω 1).1, fun ω => (U ω 1).1; P] = 0 ∧
      cov[fun ω => (U ω 1).1, fun ω => (U ω 1).2; P] = 0 ∧
      cov[fun ω => (U ω 1).2, fun ω => (U ω 1).2; P] = 1 / 4 ∧
      P.map (fun ω => (U ω 1).2) = gaussianReal 0 (1 / 4) := by
  have hxc : ContinuousOn (fun t => ((0 : ℝ), infected t)) (Icc 0 1) :=
    (continuous_const.prodMk (continuous_iff_continuousAt.2 fun t =>
      (hasDerivAt_infected t).continuousAt)).continuousOn
  have hβ : (0 : ℝ) ≤ 2 := by norm_num
  have hγ : 0 ≤ log 2 := log_nonneg (by norm_num)
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hV1 : covRemoval 1 = (0, 0, 1 / 4) := limitCovariance_one isLimitCovariance_removal
  obtain ⟨hG, hmean, -⟩ := hasGaussianLaw_isFluctuationPath hβ hγ hxc isLimitCovariance_removal
    hZ hZU₀ hZM hmean₀ hmeanM hcov₀ hcross hcovM hU ht
  obtain ⟨c11, c12, c22⟩ := covariance_isFluctuationPath hβ hγ hxc isLimitCovariance_removal
    hZ hZU₀ hZM hmean₀ hmeanM hcov₀ hcross hcovM hU ht
  rw [hV1] at c11 c12 c22
  refine ⟨hG, c11, c12, c22, ?_⟩
  have h2 : HasGaussianLaw (fun ω => (U ω 1).2) P :=
    hG.map_fun (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hm2 : ∫ ω, (U ω 1).2 ∂P = 0 := by
    have := (ContinuousLinearMap.snd ℝ ℝ ℝ).integral_comp_comm hG.integrable
    simp only [ContinuousLinearMap.coe_snd', hmean, Prod.snd_zero] at this
    exact this
  rw [h2.map_eq_gaussianReal, hm2, ← covariance_self h2.aemeasurable, c22]
  congr 1
  rw [Real.toNNReal_div' (by norm_num)]
  norm_num

/-! A concrete, fully discharged instance. -/

/-- The limit covariance around the disease-free state for `β = γ = 1` from `V₀ = diag(0, 1)`:
`V(t) = (t², -t, 1)`. -/
noncomputable def covShear (t : ℝ) : ℝ × ℝ × ℝ := (t ^ 2, -t, 1)

theorem isLimitCovariance_shear :
    IsLimitCovariance 1 1 (fun _ => (1, 0)) (0, 0, 1) covShear where
  initial := by simp [covShear]
  hasDerivWithinAt t _ := by
    have h : HasDerivAt covShear (((2 : ℕ) : ℝ) * t ^ (2 - 1), -1, 0) t :=
      (hasDerivAt_pow 2 t).prodMk ((hasDerivAt_id t).neg.prodMk (hasDerivAt_const t (1 : ℝ)))
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [lyapunovField_apply, covShear, Prod.mk.injEq]
    refine ⟨by norm_num, by ring, by ring⟩

theorem gaussianLimit_shear [MeasurableSpace C(Icc (0 : ℝ) 2, ℝ × ℝ)]
    [BorelSpace C(Icc (0 : ℝ) 2, ℝ × ℝ)] {U : ℝ → ℝ → ℝ × ℝ}
    (hU : ∀ ω, IsFluctuationPath 1 1 2 (fun _ => (1, 0)) (0, ω) (fun _ => 0) (U ω)) :
    HasGaussianLaw (fun ω => U ω 2) (gaussianReal 0 1) ∧
      cov[fun ω => (U ω 2).1, fun ω => (U ω 2).1; gaussianReal 0 1] = 4 ∧
      cov[fun ω => (U ω 2).1, fun ω => (U ω 2).2; gaussianReal 0 1] = -2 ∧
      cov[fun ω => (U ω 2).2, fun ω => (U ω 2).2; gaussianReal 0 1] = 1 := by
  set L : ℝ →L[ℝ] (ℝ × ℝ) × C(Icc (0 : ℝ) 2, ℝ × ℝ) :=
    (ContinuousLinearMap.inl ℝ (ℝ × ℝ) C(Icc (0 : ℝ) 2, ℝ × ℝ)).comp
      (ContinuousLinearMap.inr ℝ ℝ ℝ)
  have hZ : HasGaussianLaw (fun ω : ℝ => L ω) (gaussianReal 0 1) :=
    (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 1)).map_fun L
  have hint : Integrable (fun ω : ℝ => ω) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hsq : ∫ ω, ω ^ 2 ∂gaussianReal 0 1 = 1 := by
    have := variance_of_integral_eq_zero (μ := gaussianReal 0 1) (X := fun ω => ω)
      aemeasurable_id' integral_id_gaussianReal
    rw [variance_fun_id_gaussianReal] at this
    exact_mod_cast this.symm
  have hquad : ∀ s, quadCov 1 1 (fun _ => ((1 : ℝ), (0 : ℝ))) s = 0 := fun s => by
    simp [quadCov, diffusionMatrix]
  have ht : (2 : ℝ) ∈ Icc (0 : ℝ) 2 := ⟨by norm_num, le_rfl⟩
  have hV2 : covShear 2 = (4, -2, 1) := by norm_num [covShear]
  have key := fun hb => covariance_isFluctuationPath (β := 1) (γ := 1) zero_le_one zero_le_one
    continuousOn_const isLimitCovariance_shear hZ (U₀ := fun ω => (0, ω)) (M := fun _ _ => 0)
    (fun ω => rfl) (fun ω s => rfl)
    (by rw [integral_pair (integrable_const _) hint, integral_id_gaussianReal]; simp)
    (fun s _ => by simp) hb (fun a b s _ => by simp [dot])
    (fun a b s _ r _ => by simp [dot, hquad, quadForm, symmApply]) hU ht
  have hcov₀ : ∀ a b, ∫ ω, dot a (0, ω) * dot b (0, ω) ∂gaussianReal 0 1 =
      quadForm (0, 0, 1) a b := fun a b => by
    have : (fun ω : ℝ => dot a (0, ω) * dot b (0, ω)) = fun ω => (a.2 * b.2) * ω ^ 2 := by
      funext ω; simp only [dot]; ring
    rw [this, integral_const_mul, hsq]
    simp only [quadForm, dot, symmApply]; ring
  obtain ⟨c11, c12, c22⟩ := key hcov₀
  rw [hV2] at c11 c12 c22
  refine ⟨?_, c11, c12, c22⟩
  exact (hasGaussianLaw_isFluctuationPath (β := 1) (γ := 1) zero_le_one zero_le_one
    continuousOn_const isLimitCovariance_shear hZ (U₀ := fun ω => (0, ω)) (M := fun _ _ => 0)
    (fun ω => rfl) (fun ω s => rfl)
    (by rw [integral_pair (integrable_const _) hint, integral_id_gaussianReal]; simp)
    (fun s _ => by simp) hcov₀ (fun a b s _ => by simp [dot])
    (fun a b s _ r _ => by simp [dot, hquad, quadForm, symmApply]) hU ht).1

/-- The hypothesis on `U` in `gaussianLimit_shear` is satisfiable. -/
example : ∃ U : ℝ → ℝ → ℝ × ℝ,
    ∀ ω, IsFluctuationPath 1 1 2 (fun _ => (1, 0)) (0, ω) (fun _ => 0) (U ω) :=
  ⟨fun ω => Classical.choose (exists_isFluctuationPath (β := 1) (γ := 1) (T := 2) zero_le_one
      zero_le_one continuousOn_const (0, ω) (m := fun _ => 0) continuousOn_const),
    fun ω => Classical.choose_spec (exists_isFluctuationPath (β := 1) (γ := 1) (T := 2) zero_le_one
      zero_le_one continuousOn_const (0, ω) (m := fun _ => 0) continuousOn_const)⟩


/-! ### Without Gaussian driving data the limit is not Gaussian -/

/-- A Rademacher initial value: `U₀ = (±1, 0)`. -/
def rademacher (b : Bool) : ℝ × ℝ := (if b then 1 else -1, 0)

/-- A fair coin on `Bool`. -/
noncomputable def coinFlip : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

/-- With `β = γ = 0` around the disease-free state and no driving noise, the fluctuation path is
constant at its initial value. -/
theorem isFluctuationPath_rademacher (T : ℝ) (b : Bool) :
    IsFluctuationPath 0 0 T (fun _ => (1, 0)) (rademacher b) (fun _ => 0)
      (fun _ => rademacher b) :=
  ⟨continuousOn_const, fun t _ => by simp [jacobian]⟩

/-- **The Gaussian hypothesis cannot be dropped.** With the Rademacher initial value, no driving
noise, `β = γ = 0` and the disease-free state, the fluctuation path is `U(t) = U₀`. Its second
moments are those of the limit covariance `V ≡ diag(1, 0)` (which solves the Lyapunov equation
here), but `U(t)` is not Gaussian. `hasGaussianLaw_isFluctuationPath` does not apply because the
driving data `(U₀, 0)` is not Gaussian; the integration-by-parts representation of `U(t)` still
holds pathwise, and the second-moment computation alone does not give Gaussianity. -/
theorem not_hasGaussianLaw_rademacher (t : ℝ) :
    (∀ a b, ∫ ω, dot a (rademacher ω) * dot b (rademacher ω) ∂coinFlip = quadForm (1, 0, 0) a b) ∧
      IsLimitCovariance 0 0 (fun _ => (1, 0)) (1, 0, 0) (fun _ => (1, 0, 0)) ∧
      ¬ HasGaussianLaw (fun ω => (fun _ : ℝ => rademacher ω) t) coinFlip := by
  refine ⟨fun a b => ?_, ⟨rfl, fun s _ => ?_⟩, fun h => ?_⟩
  · rw [coinFlip, integral_smul_measure, integral_add_measure (Integrable.of_finite)
      (Integrable.of_finite), integral_dirac, integral_dirac]
    simp only [rademacher, dot, quadForm, symmApply, ite_true, Bool.false_eq_true, ite_false]
    norm_num
    ring
  · have : lyapunovField 0 0 ((1 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ), (0 : ℝ)) = 0 := by
      simp [lyapunovField_apply]
    rw [this]
    exact (hasDerivWithinAt_const s _ _)
  · have h1 : HasGaussianLaw (fun ω => (rademacher ω).1) coinFlip :=
      h.map_fun (ContinuousLinearMap.fst ℝ ℝ ℝ)
    have hpre : (fun ω => (rademacher ω).1) ⁻¹' {1} = {true} := by
      ext b; cases b <;> norm_num [rademacher]
    have hX : coinFlip.map (fun ω => (rademacher ω).1) {1} = 2⁻¹ := by
      rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton 1), hpre]
      simp [coinFlip]
    rw [h1.map_eq_gaussianReal] at hX
    generalize coinFlip[fun ω => (rademacher ω).1] = m at hX
    generalize Var[fun ω => (rademacher ω).1; coinFlip].toNNReal = v at hX
    by_cases hv : v = 0
    · subst hv
      rw [gaussianReal_zero_var] at hX
      by_cases hm : m = 1
      · subst hm
        rw [Measure.dirac_apply_of_mem (Set.mem_singleton 1)] at hX
        exact absurd hX.symm (by simp)
      · rw [Measure.dirac_apply' _ (measurableSet_singleton 1),
          Set.indicator_of_notMem (by simpa using hm)] at hX
        exact absurd hX.symm (by simp)
    · have := nullSingletonClass_gaussianReal (μ := m) hv
      rw [measure_singleton] at hX
      exact absurd hX.symm (by simp)

end MathlibExtTest.Biology.Epidemiology.StochasticSIRDiffusion
