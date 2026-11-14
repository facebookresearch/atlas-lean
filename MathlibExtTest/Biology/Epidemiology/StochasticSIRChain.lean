/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Epidemiology.StochasticSIRChain

/-! Tests for the pathwise construction of the stochastic SIR chain:

* a concrete clock outcome (`β = γ = 2`, `N = 2`, from `(1, 1)`, infection interarrivals `1/4`
  and recovery interarrivals `1`): the three jumps, their times `1/4, 3/8, 7/8` and the path at
  four times are computed from the definitions, and the outcome is an instance of
  `isChainPath_sir`;
* the logistic test's `hchain` (`β = 1`, `γ = 0`, initial counts `(N - ⌊N/2⌋, ⌊N/2⌋, 0)`) is
  satisfied by the constructed chain driven by independent unit Poisson clocks, and Kurtz's
  limit `E[I(1)/N] → e / (1 + e)` follows with no chain assumed;
* dependent clocks (one clock for both channels): existence still holds almost surely, but the
  law identification is not claimed: every outcome of the shared-clock chain makes a first jump
  that the jump chain makes with probability `0`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal

namespace MathlibExtTest.Biology.Epidemiology.StochasticSIRChain

open MathlibExt.Biology.Epidemiology
open MathlibExt.Biology.Epidemiology.StochasticSIR
open MathlibExt.Biology.Epidemiology.StochasticSIR.TwoChannel

/-! ### A concrete clock outcome -/

/-- Infection interarrivals `1/4, 1/4, …`. -/
noncomputable def e₁ : ℕ → ℝ := fun _ => 1 / 4

/-- Recovery interarrivals `1, 1, …`. -/
noncomputable def e₂ : ℕ → ℝ := fun _ => 1

/-- One susceptible and one infective in a population of `2`. -/
def x₀ : SIRState 2 := (1, 1)

/-- The SIR channels with `β = γ = 2` and `N = 2`. -/
noncomputable abbrev K₀ : TwoChannel (SIRState 2) := sirChannels 2 2 2

/-- The starting state and clocks. -/
noncomputable abbrev p₀ : SIRState 2 × ClockConfig := (x₀, initClock e₁ e₂)

/-- **First jump**: at `(1, 1)` the infection rate is `2 · 1 · 1 / 2 = 1` and the recovery rate
is `2 · 1 = 2`; the residual clocks are `1/4` and `1`, so the infection rings first
(`2 · 1/4 < 1 · 1`), after time `1/4`; the recovery residual drops to `1 - 2 · 1/4 = 1/2`. -/
theorem config_one : K₀.config 1 p₀ = ((0, 2), ((1 / 4, 1 / 2), (seqTail (seqTail e₁),
    seqTail e₂))) := by
  simp [K₀, config, step, next, nextClock, hold, sirChannels, x₀, initClock, e₁, e₂, totalRate,
    seqTail]
  norm_num

/-- **Second jump**: at `(0, 2)` only recovery is active, at rate `4`; its residual `1/2` rings
after time `1/8`, leading to `(0, 1)` with a fresh recovery residual `1`. -/
theorem config_two : K₀.config 2 p₀ = ((0, 1), ((1 / 4, 1), (seqTail (seqTail e₁),
    seqTail (seqTail e₂)))) := by
  rw [config_succ', config_one]
  simp [K₀, step, next, nextClock, hold, sirChannels, e₁, e₂, totalRate, seqTail]

/-- **Third jump**: at `(0, 1)` recovery rings after time `1 / 2`, leading to `(0, 0)`. -/
theorem config_three : K₀.config 3 p₀ = ((0, 0), ((1 / 4, 1), (seqTail (seqTail e₁),
    seqTail (seqTail (seqTail e₂))))) := by
  rw [config_succ', config_two]
  simp [K₀, step, next, nextClock, hold, sirChannels, e₁, e₂, totalRate, seqTail]

/-- The state `(0, 0)` is absorbing. -/
theorem totalRate_three : K₀.totalRate (K₀.config 3 p₀).1 = 0 := by
  rw [config_three]
  simp [K₀, sirChannels, totalRate]

theorem e₁_pos : ∀ n, 0 < e₁ n := fun _ => by norm_num [e₁]

theorem e₂_pos : ∀ n, 0 < e₂ n := fun _ => by norm_num [e₂]

theorem x₀_le : ((x₀.1 : ℕ) + x₀.2) ≤ 2 := by decide

/-- The first three states are active. -/
theorem active_lt_three : ∀ j < 3, K₀.totalRate (K₀.config j p₀).1 ≠ 0 := by
  intro j hj
  interval_cases j
  · norm_num [K₀, sirChannels, totalRate, x₀]
  · rw [config_one]; simp [K₀, sirChannels, totalRate]
  · rw [config_two]; simp [K₀, sirChannels, totalRate]

/-- **The jump times** `1/4`, `3/8`, `7/8`, computed from the durations `1/4`, `1/8`, `1/2`. -/
theorem eventTimes : K₀.eventTime p₀ 1 = 1 / 4 ∧ K₀.eventTime p₀ 2 = 3 / 8 ∧
    K₀.eventTime p₀ 3 = 7 / 8 := by
  have h0 : K₀.dur (K₀.config 0 p₀).1 (K₀.config 0 p₀).2.1 = 1 / 4 := by
    simp [K₀, dur, hold, sirChannels, totalRate, x₀, initClock, e₁, e₂]
    norm_num
  have h1 : K₀.dur (K₀.config 1 p₀).1 (K₀.config 1 p₀).2.1 = 1 / 8 := by
    rw [config_one]
    simp [K₀, dur, hold, sirChannels, totalRate]
    norm_num
  have h2 : K₀.dur (K₀.config 2 p₀).1 (K₀.config 2 p₀).2.1 = 1 / 2 := by
    rw [config_two]
    simp [K₀, dur, hold, sirChannels, totalRate]
  have hE1 : K₀.eventTime p₀ 1 = 1 / 4 := by
    rw [eventTime_succ, h0]; simp [eventTime]
  have hE2 : K₀.eventTime p₀ 2 = 3 / 8 := by
    rw [eventTime_succ, hE1, h1]; norm_num
  refine ⟨hE1, hE2, ?_⟩
  rw [eventTime_succ, hE2, h2]; norm_num

/-- **The constructed path at four times**, read off the jumps: `(1, 1)` before `1/4`, `(0, 2)`
on `[1/4, 3/8)`, `(0, 1)` on `[3/8, 7/8)` and `(0, 0)` afterwards. -/
theorem sirPath_values :
    sirPath 2 2 2 x₀ e₁ e₂ (1 / 8) = (1, 1) ∧ sirPath 2 2 2 x₀ e₁ e₂ (1 / 3) = (0, 2) ∧
      sirPath 2 2 2 x₀ e₁ e₂ (1 / 2) = (0, 1) ∧ sirPath 2 2 2 x₀ e₁ e₂ 1 = (0, 0) := by
  obtain ⟨hE1, hE2, hE3⟩ := eventTimes
  have hdur := sir_dur_nonneg (β := 2) (γ := 2) (by norm_num) (by norm_num) x₀_le e₁_pos e₂_pos
  have key := fun {m : ℕ} (hm : m ≤ 3) {t : ℝ} (h₁ : K₀.eventTime p₀ m ≤ t)
    (h₂ : m < 3 → t < K₀.eventTime p₀ (m + 1)) =>
    realPath_eq (K := K₀) x₀ (initClock e₁ e₂) active_lt_three totalRate_three hdur hm h₁ h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := key (m := 0) (t := 1 / 8) (by norm_num) (by simp [eventTime])
      (fun _ => by rw [hE1]; norm_num)
    simpa [sirPath, x₀] using this
  · have := key (m := 1) (t := 1 / 3) (by norm_num) (by rw [hE1]; norm_num)
      (fun _ => by rw [hE2]; norm_num)
    rw [config_one] at this
    simpa [sirPath] using this
  · have := key (m := 2) (t := 1 / 2) (by norm_num) (by rw [hE2]; norm_num)
      (fun _ => by rw [hE3]; norm_num)
    rw [config_two] at this
    simpa [sirPath] using this
  · have := key (m := 3) (t := 1) le_rfl (by rw [hE3]; norm_num) (fun h => absurd h (lt_irrefl 3))
    rw [config_three] at this
    simpa [sirPath] using this

/-- The concrete outcome is an instance of the existence theorem: the constructed counts solve
the time-change equations, and at time `1/2` they are `S = 0`, `I = 1`, `R = 1`. -/
example : IsChainPath 2 2 2 (clockCount e₁) (clockCount e₂) (sirS 2 2 2 x₀ e₁ e₂)
      (sirI 2 2 2 x₀ e₁ e₂) (sirR 2 2 2 x₀ e₁ e₂) ∧
    sirS 2 2 2 x₀ e₁ e₂ (1 / 2) = 0 ∧ sirI 2 2 2 x₀ e₁ e₂ (1 / 2) = 1 ∧
      sirR 2 2 2 x₀ e₁ e₂ (1 / 2) = 1 := by
  have h := sirPath_values.2.2.1
  refine ⟨isChainPath_sir (by norm_num) (by norm_num) x₀_le e₁_pos e₂_pos, ?_, ?_, ?_⟩
  · simp only [sirS, h]; rfl
  · simp only [sirI, h]; rfl
  · simp only [sirR, sirS, sirI, h]; rfl

/-! ### A non-trivial instance of the logistic test's `hchain`

The logistic test (`MathlibExtTest.Biology.Epidemiology.StochasticSIRKurtz`) takes as a
hypothesis `hchain`: a family of chains, driven by unit Poisson processes, with `β = 1`,
`γ = 0` and initial counts `(N - ⌊N/2⌋, ⌊N/2⌋, 0)`. The constructed chain driven by the
canonical clocks satisfies it, so Kurtz's limit holds for a genuine chain. The logistic
solution below repeats the one of that test, whose declarations are private to its module. -/

/-- Logistic susceptible fraction `s(t) = 1 / (1 + e^t)`. -/
noncomputable def sL (t : ℝ) : ℝ := 1 / (1 + exp t)

/-- Logistic infective fraction `i(t) = e^t / (1 + e^t)`. -/
noncomputable def iL (t : ℝ) : ℝ := exp t / (1 + exp t)

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

theorem tendsto_half_div : Tendsto (fun N : ℕ => ((N / 2 : ℕ) : ℝ) / N) atTop (𝓝 (1 / 2)) := by
  have hlo : Tendsto (fun N : ℕ => (1 / 2 : ℝ) - (1 / 2) / N) atTop (𝓝 (1 / 2)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have h : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by
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

/-- The initial state `(N - ⌊N/2⌋, ⌊N/2⌋)`. -/
def halfState (N : ℕ) : SIRState N := (⟨N - N / 2, by omega⟩, ⟨N / 2, by omega⟩)

theorem halfState_le (N : ℕ) : ((halfState N).1 : ℕ) + (halfState N).2 ≤ N := by
  simp only [halfState]; omega

/-- **The logistic test's `hchain`, satisfied by the constructed chain**: driven by the two
coordinate clocks of `clockLaw` (independent unit Poisson processes), the constructed counts
started at `(N - ⌊N/2⌋, ⌊N/2⌋, 0)` solve the time-change equations with `β = 1`, `γ = 0`,
almost surely, for every `N`. -/
theorem logistic_hchain : ∀ N, ∀ᵐ ω ∂clockLaw,
    IsChainPath 1 0 N (fun u => clockCount ω.1 u) (fun u => clockCount ω.2 u)
      (sirS 1 0 N (halfState N) ω.1 ω.2) (sirI 1 0 N (halfState N) ω.1 ω.2)
      (sirR 1 0 N (halfState N) ω.1 ω.2) :=
  fun N => ae_isChainPath_sir zero_le_one le_rfl (halfState_le N)

/-- **Kurtz's limit for the constructed chain**: the expected infective fraction of the
constructed logistic chain at time `1` converges to `i(1) = e / (1 + e)`. No chain is assumed:
all hypotheses of `tendsto_integral_infected` are discharged. -/
theorem tendsto_mean_infected_constructed :
    Tendsto (fun N : ℕ => ∫ ω, (sirI 1 0 N (halfState N) ω.1 ω.2 1 : ℝ) / N ∂clockLaw) atTop
      (𝓝 (exp 1 / (1 + exp 1))) := by
  have hs0 : sL 0 = 1 / 2 := by norm_num [sL]
  have hi0 : iL 0 = 1 / 2 := by norm_num [iL]
  have hinit₀ : ∀ N, ∀ᵐ ω ∂clockLaw, sirPath 1 0 N (halfState N) ω.1 ω.2 0 = halfState N :=
    fun N => by
      filter_upwards [ae_clockLaw_pos] with ω hω
      exact sirPath_zero zero_le_one le_rfl (halfState_le N) hω.1 hω.2
  have hS₀ : ∀ N, ∀ᵐ ω ∂clockLaw, sirS 1 0 N (halfState N) ω.1 ω.2 0 = N - N / 2 := fun N => by
    filter_upwards [hinit₀ N] with ω hω
    simp only [sirS]; rw [hω]; rfl
  have hI₀ : ∀ N, ∀ᵐ ω ∂clockLaw, sirI 1 0 N (halfState N) ω.1 ω.2 0 = N / 2 := fun N => by
    filter_upwards [hinit₀ N] with ω hω
    simp only [sirI]; rw [hω]; rfl
  have hR₀ : ∀ N, ∀ᵐ ω ∂clockLaw, sirR 1 0 N (halfState N) ω.1 ω.2 0 = 0 := fun N => by
    filter_upwards [hinit₀ N] with ω hω
    simp only [sirR, sirS, sirI]; rw [hω]
    simp only [halfState]
    omega
  have hinit : ∀ δ, 0 < δ → Tendsto (fun N => clockLaw {ω | δ ≤ deviation N
      (sirS 1 0 N (halfState N) ω.1 ω.2) (sirI 1 0 N (halfState N) ω.1 ω.2)
      (sirR 1 0 N (halfState N) ω.1 ω.2) sL iL (fun _ => 0) 0}) atTop (𝓝 0) := by
    intro δ hδ
    refine tendsto_measure_deviation_zero_of_initial (S₀ := fun N => N - N / 2)
      (I₀ := fun N => N / 2) (R₀ := fun _ => 0) hS₀ hI₀ hR₀ ?_ ?_ ?_ hδ
    · rw [hs0]; exact tendsto_sub_half_div
    · rw [hi0]; exact tendsto_half_div
    · simp
  have hmeas : ∀ N, Measurable fun ω : (ℕ → ℝ) × (ℕ → ℝ) => sirI 1 0 N (halfState N) ω.1 ω.2 1 :=
    fun N => (measurable_of_countable (fun x : SIRState N => (x.2 : ℕ))).comp
      (measurable_sirPath (halfState N) 1)
  have hsum : sL 0 + iL 0 + (fun _ : ℝ => (0 : ℝ)) 0 = 1 := by rw [hs0, hi0]; norm_num
  have h := tendsto_integral_infected (μ := clockLaw) (Y₁ := fun _ u ω => clockCount ω.1 u)
    (Y₂ := fun _ u ω => clockCount ω.2 u) (S := fun N ω => sirS 1 0 N (halfState N) ω.1 ω.2)
    (I := fun N ω => sirI 1 0 N (halfState N) ω.1 ω.2)
    (R := fun N ω => sirR 1 0 N (halfState N) ω.1 ω.2) (s := sL) (i := iL) (r := fun _ => 0)
    (t := 1) zero_le_one le_rfl
    (fun _ => isPoissonProcess_clockCount_fst) (fun _ => isPoissonProcess_clockCount_snd)
    logistic_hchain logistic_isSolution (by rw [hs0]; norm_num) (by rw [hi0]; norm_num) le_rfl
    hsum hinit zero_le_one hmeas
  exact h

/-! ### Dependent clocks: existence holds, law identification is not claimed -/

/-- **Existence with dependent clocks**: driving both channels by the *same* unit Poisson clock,
the constructed counts still solve the time-change equations almost surely (existence is
pathwise and does not use independence). -/
theorem ae_isChainPath_sameClock {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {N : ℕ} {x : SIRState N}
    (hx : (x.1 : ℕ) + x.2 ≤ N) :
    ∀ᵐ e ∂(Measure.infinitePi fun _ : ℕ => expMeasure 1),
      IsChainPath β γ N (clockCount e) (clockCount e) (sirS β γ N x e e) (sirI β γ N x e e)
        (sirR β γ N x e e) := by
  filter_upwards [ae_pos_infinitePi] with e he
  exact isChainPath_sir hβ hγ hx he he

/-- With the same clock for both channels, `β = 2`, `γ = 1`, `N = 2`, started at `(1, 1)`, both
rates are `1` and both residual clocks are `e 0`: every outcome makes the first jump a tie,
infection and recovery at once, from `(1, 1)` to `(0, 1)`. -/
theorem sameClock_first_jump (e : ℕ → ℝ) :
    ((sirChannels 2 1 2).config 1 (((1, 1) : SIRState 2), initClock e e)).1 = (0, 1) := by
  simp [config, step, next, sirChannels, initClock, totalRate]

/-- The jump chain never makes that transition: its jump-matrix entry from `(1, 1)` to `(0, 1)`
is `0`. -/
theorem jumpMatrix_sameClock_target :
    ctmcJumpMatrix (sirChannels 2 1 2).rateMatrix ((1, 1) : SIRState 2) (0, 1) = 0 := by
  rw [(sirChannels_isValid (by norm_num) (by norm_num) 2).ctmcJumpMatrix_eq
    (by norm_num [sirChannels, totalRate])]
  simp [sirChannels]

/-- **The shared-clock first jump is a null event for the jump chain**: under the input law of
the jump-chain construction, the first jump from `(1, 1)` goes to `(0, 1)` with probability `0`,
while the shared-clock chain makes that jump on every outcome (`sameClock_first_jump`). -/
theorem ctmcInputMeasure_first_jump_sameClock_target :
    ctmcInputMeasure (sirChannels_isValid (β := 2) (γ := 1) (by norm_num) (by norm_num)
      2).isRateMatrix {ω | ctmcJumpChain ((1, 1) : SIRState 2) ω 1 = (0, 1)} = 0 := by
  set hQ := (sirChannels_isValid (β := 2) (γ := 1) (by norm_num) (by norm_num) 2).isRateMatrix
  have hA : MeasurableSet {g : (SIRState 2 → SIRState 2) × ℝ | g.1 (1, 1) = (0, 1)} :=
    measurableSet_eq_fun ((measurable_pi_apply _).comp measurable_fst) measurable_const
  have hset : {ω | ctmcJumpChain ((1, 1) : SIRState 2) ω 1 = (0, 1)} =
      (fun ω : ℕ → (SIRState 2 → SIRState 2) × ℝ => ω 0) ⁻¹'
        {g : (SIRState 2 → SIRState 2) × ℝ | g.1 (1, 1) = (0, 1)} := rfl
  rw [hset, ← Measure.map_apply (measurable_pi_apply 0) hA, ctmcInputMeasure,
    Measure.infinitePi_map_eval, ctmcStepMeasure]
  have hprod : {g : (SIRState 2 → SIRState 2) × ℝ | g.1 (1, 1) = (0, 1)} =
      {ξ : SIRState 2 → SIRState 2 | ξ (1, 1) = (0, 1)} ×ˢ univ := by
    ext g; simp
  rw [hprod, Measure.prod_prod, measure_univ, mul_one,
    show {ξ : SIRState 2 → SIRState 2 | ξ (1, 1) = (0, 1)} =
      Function.eval ((1, 1) : SIRState 2) ⁻¹' ({((0, 1) : SIRState 2)} : Set (SIRState 2))
      from rfl,
    ← Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _), Measure.pi_map_eval]
  simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), IsRateMatrix.ctmcJumpPMF,
    jumpMatrix_sameClock_target]

end MathlibExtTest.Biology.Epidemiology.StochasticSIRChain
