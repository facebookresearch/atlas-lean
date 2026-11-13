/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.StochasticSIRKurtz
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-! Tests for Kurtz's law of large numbers for the stochastic SIR epidemic:

* conservation `S + I + R = N`, on a concrete one-jump chain path computed from the definition;
* a concrete parameter set (`β = 1`, `γ = 0`, `s₀ = i₀ = 1/2`) whose ODE solution is the
  logistic curve, with `i(1) = e / (1 + e) ∈ (0.731, 0.732)`, and the expected scaled infective
  count at `t = 1` converging to it (order `o(1)` as `N → ∞`);
* the small-`N` case `N = 1`, where every sample path is more than `1/4` away from `i(1)`, so
  no limit statement is claimed at fixed `N`;
* non-vacuity: the full hypothesis bundle of Kurtz's theorem is satisfied by genuine unit Poisson
  processes (exponential interarrivals on an infinite product space) and the disease-free chain.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal

namespace MathlibExtTest.Biology.Epidemiology.StochasticSIRKurtz

open MathlibExt.Biology.Epidemiology
open MathlibExt.Biology.Epidemiology.StochasticSIR

/-! ### Conservation on a concrete chain path -/

/-- One infective, recovery rate `γ = 1`, recovery clock jumping at `1`: the infective recovers
at time `1`. -/
noncomputable def oneJumpI : ℝ → ℕ := fun t => if t < 1 then 1 else 0

/-- The removed count of the one-jump path. -/
noncomputable def oneJumpR : ℝ → ℕ := fun t => if t < 1 then 0 else 1

/-- The one-jump recovery clock path: unit jump at `1`. -/
noncomputable def oneJumpY : ℝ≥0 → ℕ := fun u => if u < 1 then 0 else 1

private theorem intervalIntegrable_oneJumpI (a b : ℝ) :
    IntervalIntegrable (fun x => (1 : ℝ) * (oneJumpI x : ℝ)) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun ?_ (ae_of_all _ fun x => ?_)
  · exact (measurable_const.mul (measurable_from_nat.comp
      (Measurable.ite measurableSet_Iio measurable_const measurable_const))).aestronglyMeasurable
  · simp only [oneJumpI]
    split_ifs <;> simp

/-- The recovery clock of the one-jump path: `∫₀ᵗ I = min t 1` for `t ≥ 0`. -/
theorem integral_oneJumpI {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in (0 : ℝ)..t, (1 : ℝ) * (oneJumpI x : ℝ) = min t 1 := by
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [ae_iff]
    simp
  have hle : ∀ {c : ℝ}, 0 ≤ c → c ≤ 1 →
      ∫ x in (0 : ℝ)..c, (1 : ℝ) * (oneJumpI x : ℝ) = c := by
    intro c hc0 hc1
    have : ∫ x in (0 : ℝ)..c, (1 : ℝ) * (oneJumpI x : ℝ) = ∫ x in (0 : ℝ)..c, (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hne] with x hx1 hx
      rw [uIoc_of_le hc0] at hx
      have : x < 1 := lt_of_le_of_ne (hx.2.trans hc1) hx1
      simp [oneJumpI, this]
    rw [this]
    simp
  rcases le_or_gt t 1 with h1 | h1
  · rw [min_eq_left h1, hle ht h1]
  · rw [min_eq_right h1.le, ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_oneJumpI 0 1) (intervalIntegrable_oneJumpI 1 t), hle zero_le_one le_rfl]
    have : ∫ x in (1 : ℝ)..t, (1 : ℝ) * (oneJumpI x : ℝ) = ∫ x in (1 : ℝ)..t, (0 : ℝ) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [uIcc_of_le h1.le] at hx
      simp [oneJumpI, not_lt.2 hx.1]
    rw [this]
    simp

/-- **A concrete chain path with a jump** (non-vacuity of `IsChainPath`): population `N = 1`,
no susceptibles, one infective, recovery rate `γ = 1`, recovery clock jumping at `1`. The
infective recovers at time `1`. -/
theorem oneJump_isChainPath (β : ℝ) :
    IsChainPath β 1 1 (fun _ => 0) oneJumpY (fun _ => 0) oneJumpI oneJumpR where
  total_zero := by simp [oneJumpI, oneJumpR]
  measurable_susceptible := measurable_const
  measurable_infected := Measurable.ite measurableSet_Iio measurable_const measurable_const
  measurable_removed := Measurable.ite measurableSet_Iio measurable_const measurable_const
  susceptible_eq t _ := by simp
  infected_eq t ht := by
    unfold recoveryClock
    rw [integral_oneJumpI ht]
    rcases lt_or_ge t 1 with h1 | h1
    · have : Real.toNNReal t < 1 := by rw [Real.toNNReal_lt_one]; exact h1
      simp [oneJumpI, oneJumpY, h1, min_eq_left h1.le, this]
    · simp [oneJumpI, oneJumpY, not_lt.2 h1, min_eq_right h1]
  removed_eq t ht := by
    unfold recoveryClock
    rw [integral_oneJumpI ht]
    rcases lt_or_ge t 1 with h1 | h1
    · have : Real.toNNReal t < 1 := by rw [Real.toNNReal_lt_one]; exact h1
      simp [oneJumpR, oneJumpY, h1, min_eq_left h1.le, this]
    · simp [oneJumpR, oneJumpY, not_lt.2 h1, min_eq_right h1]

/-- Conservation, computed directly from the path before and after the jump. -/
example : (0 : ℕ) + oneJumpI (1 / 2) + oneJumpR (1 / 2) = 1 ∧
    (0 : ℕ) + oneJumpI 2 + oneJumpR 2 = 1 := by
  norm_num [oneJumpI, oneJumpR]

/-- Conservation via `IsChainPath.total_eq`, at every `t ≥ 0`. -/
example {t : ℝ} (ht : 0 ≤ t) : (0 : ℕ) + oneJumpI t + oneJumpR t = 1 :=
  (oneJump_isChainPath 0).total_eq ht

/-- Conservation `S + I + R = N` along any chain path. -/
example {β γ : ℝ} {N : ℕ} {y₁ y₂ : ℝ≥0 → ℕ} {S I R : ℝ → ℕ}
    (h : IsChainPath β γ N y₁ y₂ S I R) {t : ℝ} (ht : 0 ≤ t) : S t + I t + R t = N :=
  h.total_eq ht

/-! ### A concrete parameter set: the logistic SI epidemic -/

/-- Logistic susceptible fraction `s(t) = 1 / (1 + e^t)`. -/
noncomputable def sL (t : ℝ) : ℝ := 1 / (1 + exp t)

/-- Logistic infective fraction `i(t) = e^t / (1 + e^t)`. -/
noncomputable def iL (t : ℝ) : ℝ := exp t / (1 + exp t)

/-- For `β = 1`, `γ = 0` and `(s₀, i₀, r₀) = (1/2, 1/2, 0)`, the SIR system is solved by the
logistic curve. -/
theorem logistic_isSolution : SIR.IsSolution 1 0 1 sL iL (fun _ => 0) where
  hasDerivAt_susceptible t _ := by
    have hpos : 0 < 1 + exp t := by positivity
    have := ((hasDerivAt_exp t).const_add 1).inv hpos.ne'
    convert this.const_mul (1 : ℝ) using 1
    · funext x; simp [sL, div_eq_mul_inv]
    · simp only [sL, iL]; field_simp
  hasDerivAt_infected t _ := by
    have hpos : 0 < 1 + exp t := by positivity
    have := (hasDerivAt_exp t).div ((hasDerivAt_exp t).const_add 1) hpos.ne'
    convert this using 1
    · rfl
    · simp only [sL, iL]
      field_simp
      ring
  hasDerivAt_removed t _ := by simpa using hasDerivAt_const t (0 : ℝ)

theorem sL_zero : sL 0 = 1 / 2 := by norm_num [sL]

theorem iL_zero : iL 0 = 1 / 2 := by norm_num [iL]

/-- **The ODE solution at `t = 1`:** `i(1) = e / (1 + e)`, numerically in `(0.731, 0.732)`. -/
theorem iL_one : iL 1 = exp 1 / (1 + exp 1) ∧ 0.731 < iL 1 ∧ iL 1 < 0.732 := by
  have h1 := exp_one_gt_d9
  have h2 := exp_one_lt_d9
  have hpos : 0 < 1 + exp 1 := by positivity
  refine ⟨rfl, ?_, ?_⟩ <;> unfold iL
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-- `⌊N / 2⌋ / N → 1 / 2`. -/
theorem tendsto_half_div : Tendsto (fun N : ℕ => ((N / 2 : ℕ) : ℝ) / N) atTop (𝓝 (1 / 2)) := by
  have hlo : Tendsto (fun N : ℕ => (1 / 2 : ℝ) - (1 / 2) / N) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have h : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
      have := Nat.div_add_mod N 2
      have hm := Nat.mod_lt N (show 0 < 2 by norm_num)
      have : N ≤ 2 * (N / 2) + 1 := by omega
      exact_mod_cast this
    rw [le_div_iff₀ hNr]
    field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have h : 2 * ((N / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N 2
    rw [div_le_iff₀ hNr]
    linarith

/-- `(N - ⌊N / 2⌋) / N → 1 / 2`. -/
theorem tendsto_sub_half_div :
    Tendsto (fun N : ℕ => ((N - N / 2 : ℕ) : ℝ) / N) atTop (𝓝 (1 / 2)) := by
  have : Tendsto (fun N : ℕ => (1 : ℝ) - ((N / 2 : ℕ) : ℝ) / N) atTop (𝓝 (1 - 1 / 2)) :=
    tendsto_const_nhds.sub tendsto_half_div
  norm_num at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [Nat.cast_sub (Nat.div_le_self N 2)]
  field_simp

/-- **The scaled chain's mean at `t = 1` matches the ODE solution** (to order `o(1)` as
`N → ∞`): for the logistic parameters `β = 1`, `γ = 0`, with initial counts
`(N - ⌊N/2⌋, ⌊N/2⌋, 0)`, the expected infective fraction at time `1` converges to
`i(1) = e / (1 + e) ≈ 0.7311`. -/
theorem tendsto_mean_infected_logistic {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y₁ Y₂ : ℕ → ℝ≥0 → Ω → ℕ}
    (hY₁ : ∀ N, IsPoissonProcess (Y₁ N) 1 μ) (hY₂ : ∀ N, IsPoissonProcess (Y₂ N) 1 μ)
    {S I R : ℕ → Ω → ℝ → ℕ}
    (hchain : ∀ N, ∀ᵐ ω ∂μ, IsChainPath 1 0 N (fun u => Y₁ N u ω) (fun u => Y₂ N u ω)
      (S N ω) (I N ω) (R N ω))
    (hS₀ : ∀ N, ∀ᵐ ω ∂μ, S N ω 0 = N - N / 2) (hI₀ : ∀ N, ∀ᵐ ω ∂μ, I N ω 0 = N / 2)
    (hR₀ : ∀ N, ∀ᵐ ω ∂μ, R N ω 0 = 0) (hmeas : ∀ N, Measurable fun ω => I N ω 1) :
    Tendsto (fun N => ∫ ω, (I N ω 1 : ℝ) / N ∂μ) atTop (𝓝 (exp 1 / (1 + exp 1))) := by
  have hs0 : sL 0 = 1 / 2 := sL_zero
  have hi0 : iL 0 = 1 / 2 := iL_zero
  refine tendsto_integral_infected (s := sL) (i := iL) (r := fun _ => 0) zero_le_one le_rfl
    hY₁ hY₂ hchain logistic_isSolution (by rw [hs0]; norm_num) (by rw [hi0]; norm_num) le_rfl
    (by rw [hs0, hi0]; norm_num) (fun δ hδ => ?_) zero_le_one hmeas
  refine tendsto_measure_deviation_zero_of_initial (S₀ := fun N => N - N / 2)
    (I₀ := fun N => N / 2) (R₀ := fun _ => 0) hS₀ hI₀ hR₀ ?_ ?_ ?_ hδ
  · rw [hs0]; exact tendsto_sub_half_div
  · rw [hi0]; exact tendsto_half_div
  · simp

/-! ### Small `N`: no limit is claimed -/

/-- **At `N = 1` the scaled chain is far from the ODE.** For the logistic parameters, every
chain path of population size `1` has `I(1) ∈ {0, 1}` (by conservation), while
`i(1) ≈ 0.7311`; so `|I(1) / 1 - i(1)| > 1/4` on every path. Kurtz's theorem is a statement
about `N → ∞` only. -/
theorem smallN_far {y₁ y₂ : ℝ≥0 → ℕ} {S I R : ℝ → ℕ}
    (h : IsChainPath 1 0 1 y₁ y₂ S I R) : 1 / 4 < |(I 1 : ℝ) / (1 : ℕ) - iL 1| := by
  have htot := h.total_eq zero_le_one
  have hI : I 1 = 0 ∨ I 1 = 1 := by omega
  obtain ⟨-, h1, h2⟩ := iL_one
  rcases hI with hI | hI
  · rw [hI, show ((0 : ℕ) : ℝ) / (1 : ℕ) - iL 1 = -iL 1 by simp, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  · rw [hI, show ((1 : ℕ) : ℝ) / (1 : ℕ) - iL 1 = 1 - iL 1 by simp,
      abs_of_pos (by linarith)]
    linarith

/-- Hence at `N = 1` the deviation at `t = 1` exceeds `1/4` almost surely. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {Y₁ Y₂ : ℝ≥0 → Ω → ℕ}
    {S I R : Ω → ℝ → ℕ}
    (hchain : ∀ᵐ ω ∂μ, IsChainPath 1 0 1 (fun u => Y₁ u ω) (fun u => Y₂ u ω)
      (S ω) (I ω) (R ω)) :
    ∀ᵐ ω ∂μ, 1 / 4 < deviation 1 (S ω) (I ω) (R ω) sL iL (fun _ => 0) 1 := by
  filter_upwards [hchain] with ω hω
  have := smallN_far hω
  unfold deviation
  linarith [abs_nonneg ((S ω 1 : ℝ) / (1 : ℕ) - sL 1),
    abs_nonneg ((R ω 1 : ℝ) / (1 : ℕ) - (fun _ => (0 : ℝ)) 1)]

/-! ### Non-vacuity of Kurtz's theorem with genuine Poisson processes -/

/-- The coordinates of the infinite product of rate-`1` exponential laws. -/
theorem expCoord_hasLaw (i : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω i) (expMeasure ((1 : ℝ≥0) : ℝ))
      (Measure.infinitePi fun _ : ℕ => expMeasure 1) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  exact ⟨(measurable_pi_apply i).aemeasurable, by
    simpa using Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) i⟩

/-- The coordinate counting process is a unit-rate Poisson process. -/
theorem isPoissonProcess_expCount :
    IsPoissonProcess (PoissonProcess.count fun (i : ℕ) (ω : ℕ → ℝ) => ω i) 1
      (Measure.infinitePi fun _ : ℕ => expMeasure 1) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  exact PoissonProcess.isPoissonProcess_count (by norm_num) expCoord_hasLaw
    (iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) fun _ => measurable_id)

/-- The disease-free chain `(N, 0, 0)` is a chain path for any clocks starting at `0`. -/
theorem diseaseFree_isChainPath (β γ : ℝ) (N : ℕ) {y₁ y₂ : ℝ≥0 → ℕ} (h₁ : y₁ 0 = 0)
    (h₂ : y₂ 0 = 0) : IsChainPath β γ N y₁ y₂ (fun _ => N) (fun _ => 0) (fun _ => 0) where
  total_zero := by simp
  measurable_susceptible := measurable_const
  measurable_infected := measurable_const
  measurable_removed := measurable_const
  susceptible_eq t _ := by simp [infectionClock, h₁]
  infected_eq t _ := by simp [infectionClock, recoveryClock, h₁, h₂]
  removed_eq t _ := by simp [recoveryClock, h₂]

/-- **All hypotheses of `tendsto_measure_deviation` are satisfiable** by genuine unit Poisson
processes: on the product of exponential laws, the coordinate Poisson process drives the
disease-free chain, whose limit is the disease-free equilibrium `(1, 0, 0)`. -/
example (β γ : ℝ) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (T ε : ℝ) (hε : 0 < ε) :
    haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
    Tendsto (fun N : ℕ => Measure.infinitePi (fun _ : ℕ => expMeasure 1)
      {ω | ∃ t ∈ Icc 0 T, ε ≤ deviation N (fun _ => N) (fun _ => 0) (fun _ => 0)
        (fun _ => 1) (fun _ => 0) (fun _ => 0) t}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have hY := isPoissonProcess_expCount
  have hode : SIR.IsSolution β γ 1 (fun _ => 1) (fun _ => 0) (fun _ => 0) :=
    ⟨fun t _ => by simpa using hasDerivAt_const t (1 : ℝ),
      fun t _ => by simpa using hasDerivAt_const t (0 : ℝ),
      fun t _ => by simpa using hasDerivAt_const t (0 : ℝ)⟩
  refine tendsto_measure_deviation (Y₁ := fun _ => _) (Y₂ := fun _ => _)
    (S := fun N _ _ => N) (I := fun _ _ _ => 0) (R := fun _ _ _ => 0) hβ hγ
    (fun _ => hY) (fun _ => hY) (fun N => ?_) hode zero_le_one le_rfl le_rfl (by norm_num)
    (fun δ hδ => ?_) T hε
  · filter_upwards [hY.ae_zero] with ω hω
    exact diseaseFree_isChainPath β γ N hω hω
  · refine tendsto_measure_deviation_zero_of_initial (S₀ := fun N => N) (I₀ := fun _ => 0)
      (R₀ := fun _ => 0) (fun _ => ae_of_all _ fun _ => rfl) (fun _ => ae_of_all _ fun _ => rfl)
      (fun _ => ae_of_all _ fun _ => rfl) ?_ (by simp) (by simp) hδ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [div_self (Nat.cast_ne_zero.2 hN.ne')]

end MathlibExtTest.Biology.Epidemiology.StochasticSIRKurtz
