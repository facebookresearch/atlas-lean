/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Epidemiology.StochasticSEIRVital
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-! Tests for Kurtz's law of large numbers for the stochastic SEIR epidemic with vital dynamics:

* the channel intensities computed from `rate` at concrete states: the incidence is
  `β S I / N`, the birth rate `μ N` does not depend on the state, and at `μ = 0` births and deaths
  vanish;
* the reaction network computed from the definitions of `StochasticCRNLLN`: the mass-action
  propensities are the chain's rates, the jump sizes sum to `11`, and the mass-action field is
  the `SEIRVital` vector field;
* a concrete chain path with vital dynamics (`μ = 1`): one removed individual dies and one
  susceptible is born at time `1`, checked against the time-change equations from the
  definitions; its population and the bound of `total_le` on it, recomputed;
* non-vacuity: the full hypothesis bundle of Kurtz's theorem (attained-time and supremum forms)
  is satisfied by genuine unit Poisson processes (exponential interarrivals on an infinite
  product space) and the disease-free chain without vital dynamics (`μ = 0`);
* the ODE hypotheses of the endemic corollary are satisfiable: `R₀ = 2 > 1` for
  `β = 4, σ = 1, γ = 0, μ = 1`, and a solution from a positive initial point exists.

Existence of chain paths for `μ > 0` driven by Poisson processes is not proved (only the single
deterministic path above), so the theorems are exercised at `μ > 0` only through their ODE
hypotheses.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal

namespace MathlibExtTest.Biology.Epidemiology.StochasticSEIRVital

open MathlibExt.Biology.Dynamics
open MathlibExt.Biology.Epidemiology
open MathlibExt.Biology.Epidemiology.StochasticSEIRVital

/-! ### Channel intensities, computed from the definitions -/

/-- Incidence `β S I / N` at `β = 2`, `N = 10`, `S = 6`, `I = 3`: `2 · 6 · 3 / 10 = 18 / 5`. -/
example : rate 2 1 1 1 10 (fun _ => 6) (fun _ => 0) (fun _ => 3) (fun _ => 0) .infection 0 =
    18 / 5 := by
  norm_num [rate, scaledRate]

/-- The birth rate is `μ N = 5` at `μ = 1/2`, `N = 10`, whatever the state (here empty). -/
example : rate 0 0 0 (1 / 2) 10 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) .birth 7 =
    5 := by
  norm_num [rate, scaledRate]

/-- Deaths of infectives at rate `μ I = 3 / 2` for `μ = 1/2`, `I = 3`, `N = 10`. -/
example : rate 0 0 0 (1 / 2) 10 (fun _ => 0) (fun _ => 0) (fun _ => 3) (fun _ => 0) .deathI 7 =
    3 / 2 := by
  norm_num [rate, scaledRate]

/-- Without vital dynamics (`μ = 0`) the birth and death channels are silent. -/
example (β σ γ s e i r : ℝ) :
    scaledRate β σ γ 0 s e i r .birth = 0 ∧ scaledRate β σ γ 0 s e i r .deathS = 0 ∧
      scaledRate β σ γ 0 s e i r .deathE = 0 ∧ scaledRate β σ γ 0 s e i r .deathI = 0 ∧
      scaledRate β σ γ 0 s e i r .deathR = 0 := by
  simp [scaledRate]

/-- The rate bound at `β = σ = γ = μ = 1`, `K = 1` is `1 + 1 + 3 = 5`, and the infection
intensity at the corner `s = i = 1` is `1 ≤ 5`. -/
example : rateBound 1 1 1 1 1 = 5 ∧ scaledRate 1 1 1 1 1 1 1 1 .infection = 1 := by
  norm_num [rateBound, scaledRate]

/-! ### The reaction network, computed from the definitions -/

/-- The mass-action incidence at `β = 2`, `N = 10`, `S = 6`, `I = 3` is
`N β S I / N² = 10 · 2 · 6 · 3 / 100 = 18 / 5`, the chain's `β S I / N`. -/
example : StochasticCRNLLN.massActionPropensity network (rateConst 2 1 1 1) 10 .infection
    (vec4 6 0 3 0) = 18 / 5 := by
  norm_num [StochasticCRNLLN.massActionPropensity, SystemsBiology.propensity, prod_compartment,
    sum_compartment, network, networkSrc, vec4, rateConst,
    ComplexBalanced.ReactionNetwork.propensity]

/-- The mass-action birth propensity at `μ = 1/2`, `N = 10` is `μ N = 5`, in the empty state. -/
example : StochasticCRNLLN.massActionPropensity network (rateConst 0 0 0 (1 / 2)) 10 .birth
    (vec4 0 0 0 0) = 5 := by
  norm_num [StochasticCRNLLN.massActionPropensity, SystemsBiology.propensity, prod_compartment,
    sum_compartment, network, networkSrc, vec4, rateConst,
    ComplexBalanced.ReactionNetwork.propensity]

/-- The jump sizes `‖ζ_c‖₁` are `1, 2, 2, 2, 1, 1, 1, 1`, summing to `11`. -/
example : StochasticCRNLLN.stoichNorm network = 11 := by
  norm_num [StochasticCRNLLN.stoichNorm, StochasticCRNLLN.l1Norm, StochasticCRNLLN.reactionVector,
    sum_channel, sum_compartment, network, networkSrc, networkProd, vec4]

/-- The `S`-component of the mass-action field at `(1/2, 1/4, 1/4, 0)` for `β = 4`, `σ = 1`,
`γ = 0`, `μ = 1` is `μ - β s i - μ s = 1 - 1/2 - 1/2 = 0`. -/
example : network.massActionField (rateConst 4 1 0 1) (vec4 (1 / 2) (1 / 4) (1 / 4) 0) .S = 0 := by
  norm_num [ComplexBalanced.ReactionNetwork.massActionField, sum_channel, prod_compartment,
    network, networkSrc, networkProd, vec4, rateConst]

/-! ### A concrete chain path with vital dynamics -/

/-- The susceptible count: born at time `1`. -/
noncomputable def birthS : ℝ → ℕ := fun t => if t < 1 then 0 else 1

/-- The removed count: dies at time `1`. -/
noncomputable def deathRpath : ℝ → ℕ := fun t => if t < 1 then 1 else 0

/-- A counting path with a unit jump at `1`. -/
noncomputable def jumpAtOne : ℝ≥0 → ℕ := fun u => if u < 1 then 0 else 1

/-- The driving paths: the birth and removed-death channels jump when their clock reaches `1`;
the other channels never jump. -/
noncomputable def clocks : Channel → ℝ≥0 → ℕ
  | .birth => jumpAtOne
  | .deathR => jumpAtOne
  | _ => fun _ => 0

private theorem measurable_ite_one (a b : ℕ) :
    Measurable (fun t : ℝ => if t < 1 then a else b) :=
  Measurable.ite measurableSet_Iio measurable_const measurable_const

/-- `∫₀ᵗ (if x < 1 then 1 else 0) = min t 1` for `t ≥ 0`. -/
theorem integral_deathRpath {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in (0 : ℝ)..t, (deathRpath x : ℝ) = min t 1 := by
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun x => (deathRpath x : ℝ)) volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun ?_ (ae_of_all _ fun x => ?_)
    · exact (measurable_from_nat.comp (measurable_ite_one 1 0)).aestronglyMeasurable
    · simp only [deathRpath]
      split_ifs <;> simp
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [ae_iff]
    simp
  have hle : ∀ {c : ℝ}, 0 ≤ c → c ≤ 1 → ∫ x in (0 : ℝ)..c, (deathRpath x : ℝ) = c := by
    intro c hc0 hc1
    have : ∫ x in (0 : ℝ)..c, (deathRpath x : ℝ) = ∫ x in (0 : ℝ)..c, (1 : ℝ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hne] with x hx1 hx
      rw [uIoc_of_le hc0] at hx
      have : x < 1 := lt_of_le_of_ne (hx.2.trans hc1) hx1
      simp [deathRpath, this]
    rw [this]
    simp
  rcases le_or_gt t 1 with h1 | h1
  · rw [min_eq_left h1, hle ht h1]
  · rw [min_eq_right h1.le, ← intervalIntegral.integral_add_adjacent_intervals (hii 0 1)
      (hii 1 t), hle zero_le_one le_rfl]
    have : ∫ x in (1 : ℝ)..t, (deathRpath x : ℝ) = ∫ x in (1 : ℝ)..t, (0 : ℝ) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [uIcc_of_le h1.le] at hx
      simp [deathRpath, not_lt.2 hx.1]
    rw [this]
    simp

/-- The removed-death clock of the path is `min t 1`. -/
theorem clock_deathR {t : ℝ} (ht : 0 ≤ t) :
    clock 0 0 0 1 1 birthS (fun _ => 0) (fun _ => 0) deathRpath .deathR t =
      Real.toNNReal (min t 1) := by
  unfold clock
  rw [← integral_deathRpath ht]
  congr 2
  funext x
  simp [rate, scaledRate]

/-- The birth clock of the path is `N μ t = t`, computed from the definition. -/
theorem clock_birth_path (t : ℝ) :
    clock 0 0 0 1 1 birthS (fun _ => 0) (fun _ => 0) deathRpath .birth t = Real.toNNReal t := by
  unfold clock
  simp [rate, scaledRate]

/-- `jumpAtOne (toNNReal t)` is `0` before time `1` and `1` from then on, for `t ≥ 0`. -/
theorem jumpAtOne_toNNReal {t : ℝ} : jumpAtOne (Real.toNNReal t) = if t < 1 then 0 else 1 := by
  unfold jumpAtOne
  by_cases h : t < 1
  · have : Real.toNNReal t < 1 := by rw [Real.toNNReal_lt_one]; exact h
    simp [h, this]
  · have : ¬ Real.toNNReal t < 1 := by rw [Real.toNNReal_lt_one]; exact h
    simp [h, this]

/-- **A chain path with vital dynamics** (non-vacuity of `IsChainPath` at `μ = 1`): scale
`N = 1`, no transmission (`β = σ = γ = 0`), one removed individual at time `0`. The birth clock
`t` and the removed-death clock `min t 1` both reach the jump of their counting path at time
`1`: a susceptible is born and the removed individual dies. -/
theorem vital_isChainPath :
    IsChainPath 0 0 0 1 1 clocks birthS (fun _ => 0) (fun _ => 0) deathRpath where
  measurable_susceptible := measurable_ite_one 0 1
  measurable_exposed := measurable_const
  measurable_infected := measurable_const
  measurable_removed := measurable_ite_one 1 0
  susceptible_eq t _ := by
    rw [clock_birth_path]
    simp only [clocks, jumpAtOne_toNNReal, birthS]
    split_ifs <;> simp_all
  exposed_eq t _ := by simp [clocks]
  infected_eq t _ := by simp [clocks]
  removed_eq t ht := by
    rw [clock_deathR ht]
    simp only [clocks, jumpAtOne_toNNReal, deathRpath]
    rcases lt_or_ge t 1 with h | h
    · simp [h, min_eq_left h.le]
    · simp [not_lt.2 h, min_eq_right h]

/-- The population of the path, computed directly: `1` before and after the simultaneous birth
and death at time `1`. -/
example : (birthS (1 / 2) + deathRpath (1 / 2) : ℕ) = 1 ∧ (birthS 2 + deathRpath 2 : ℕ) = 1 := by
  norm_num [birthS, deathRpath]

/-- The instance of `total_le` on the path at `t = 2`, recomputed from the definitions: the
population is `1` and the bound is the initial `1` plus the one birth, `1 ≤ 1 + 1`. -/
example : ((birthS 2 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + deathRpath 2 = 1 ∧
    (birthS 0 : ℝ) + ((0 : ℕ) : ℝ) + ((0 : ℕ) : ℝ) + deathRpath 0 +
      clocks .birth (clock 0 0 0 1 1 birthS (fun _ => 0) (fun _ => 0) deathRpath .birth 2) =
        1 + 1 := by
  rw [clock_birth_path]
  norm_num [birthS, deathRpath, clocks, jumpAtOne_toNNReal, jumpAtOne]

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

/-- Every clock of the disease-free chain `(N, 0, 0, 0)` without vital dynamics is `0`. -/
theorem clock_diseaseFree (β σ γ : ℝ) (N : ℕ) (c : Channel) (t : ℝ) :
    clock β σ γ 0 N (fun _ => N) (fun _ => 0) (fun _ => 0) (fun _ => 0) c t = 0 := by
  cases c <;> simp [clock, rate, scaledRate]

/-- The disease-free chain `(N, 0, 0, 0)` without vital dynamics is a chain path for any clocks
starting at `0`. -/
theorem diseaseFree_isChainPath (β σ γ : ℝ) (N : ℕ) {y : Channel → ℝ≥0 → ℕ}
    (hy : ∀ c, y c 0 = 0) :
    IsChainPath β σ γ 0 N y (fun _ => N) (fun _ => 0) (fun _ => 0) (fun _ => 0) where
  measurable_susceptible := measurable_const
  measurable_exposed := measurable_const
  measurable_infected := measurable_const
  measurable_removed := measurable_const
  susceptible_eq t _ := by simp [clock_diseaseFree, hy]
  exposed_eq t _ := by simp [clock_diseaseFree, hy]
  infected_eq t _ := by simp [clock_diseaseFree, hy]
  removed_eq t _ := by simp [clock_diseaseFree, hy]

/-- The disease-free equilibrium `(1, 0, 0, 0)` solves the ODE without vital dynamics. -/
theorem diseaseFree_isSolution (β σ γ : ℝ) :
    SEIRVital.IsSolution β σ γ 0 1 (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨fun t _ => by simpa using hasDerivAt_const t (1 : ℝ),
    fun t _ => by simpa using hasDerivAt_const t (0 : ℝ),
    fun t _ => by simpa using hasDerivAt_const t (0 : ℝ),
    fun t _ => by simpa using hasDerivAt_const t (0 : ℝ)⟩

/-- The scaled initial state of the disease-free chain converges to `(1, 0, 0, 0)`: for `N > 0`
its deviation at time `0` is `|N / N - 1| = 0`, so the event is empty. -/
theorem diseaseFree_init {δ : ℝ} (hδ : 0 < δ) :
    haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
    Tendsto (fun N : ℕ => Measure.infinitePi (fun _ : ℕ => expMeasure 1)
      {_ω | δ ≤ deviation N (fun _ => N) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) 0}) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have h0 : deviation N (fun _ => N) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 1)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 = 0 := by
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    simp [deviation, div_self hN']
  have hδ' : ¬ δ ≤ 0 := not_le.2 hδ
  simp [h0, hδ']

/-- **All hypotheses of `tendsto_measure_deviation` are satisfiable** by genuine unit Poisson
processes: on the product of exponential laws, the coordinate Poisson process drives every
channel of the disease-free chain without vital dynamics, whose limit is `(1, 0, 0, 0)`. -/
example (β σ γ : ℝ) (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ) (T ε : ℝ) (hε : 0 < ε) :
    haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
    Tendsto (fun N : ℕ => Measure.infinitePi (fun _ : ℕ => expMeasure 1)
      {ω | ∃ t ∈ Icc 0 T, ε ≤ deviation N (fun _ => N) (fun _ => 0) (fun _ => 0) (fun _ => 0)
        (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) t}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have hY := isPoissonProcess_expCount
  refine tendsto_measure_deviation (Y := fun _ _ => _) (S := fun N _ _ => N)
    (E := fun _ _ _ => 0) (I := fun _ _ _ => 0) (R := fun _ _ _ => 0) hβ hσ hγ le_rfl
    (fun _ _ => hY) (fun N => ?_) (diseaseFree_isSolution β σ γ) (fun δ hδ => diseaseFree_init hδ)
    T hε
  filter_upwards [hY.ae_zero] with ω hω
  exact diseaseFree_isChainPath β σ γ N fun _ => hω

/-- The supremum form `tendsto_measure_iSup_deviation` under the same genuine Poisson clocks and
disease-free chain. -/
example (β σ γ : ℝ) (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ) (T ε : ℝ) (hε : 0 < ε) :
    haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
    Tendsto (fun N : ℕ => Measure.infinitePi (fun _ : ℕ => expMeasure 1)
      {_ω | ENNReal.ofReal ε ≤ ⨆ t ∈ Icc 0 T, ENNReal.ofReal (deviation N (fun _ => N)
        (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0)
        (fun _ => 0) t)}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have hY := isPoissonProcess_expCount
  refine tendsto_measure_iSup_deviation (Y := fun _ _ => _) (S := fun N _ _ => N)
    (E := fun _ _ _ => 0) (I := fun _ _ _ => 0) (R := fun _ _ _ => 0) hβ hσ hγ le_rfl
    (fun _ _ => hY) (fun N => ?_) (diseaseFree_isSolution β σ γ) (fun δ hδ => diseaseFree_init hδ)
    T hε
  filter_upwards [hY.ae_zero] with ω hω
  exact diseaseFree_isChainPath β σ γ N fun _ => hω

/-! ### The ODE hypotheses of the endemic corollary are satisfiable -/

/-- `R₀ = β σ / ((μ + σ) (μ + γ)) = 4 / 2 = 2 > 1` at `β = 4`, `σ = 1`, `γ = 0`, `μ = 1`. -/
theorem R0_example : SEIRVital.R0 4 1 0 1 = 2 := by norm_num [SEIRVital.R0]

/-- An ODE solution at scale `1` from the positive initial point `(1/2, 1/4, 1/4, 0)` exists for
these parameters, so `hode`, `hs0`, `he0`, `hi0` and `hR` of
`eventually_tendsto_measure_endemic` hold together.
Its Poisson-process and chain hypotheses (`hY`, `hchain`) are never met together here, only the
ODE ones: chain existence for `μ > 0` is standard and out of scope. -/
example : ∃ s e i r : ℝ → ℝ, SEIRVital.IsSolution 4 1 0 1 1 s e i r ∧ 0 < s 0 ∧ 0 < e 0 ∧
    0 < i 0 ∧ 1 < SEIRVital.R0 4 1 0 1 := by
  obtain ⟨s, e, i, r, h, hs, he, hi, -, -, -⟩ := SEIRVital.exists_isSolution (β := 4) (σ := 1)
    (γ := 0) (μ := 1) (N := 1) (S₀ := 1 / 2)
    (E₀ := 1 / 4) (I₀ := 1 / 4) (R₀ := 0) (by norm_num) one_pos le_rfl one_pos one_pos
    (by norm_num) (by norm_num) (by norm_num) le_rfl
  exact ⟨s, e, i, r, h, by rw [hs]; norm_num, by rw [he]; norm_num, by rw [hi]; norm_num,
    by rw [R0_example]; norm_num⟩

end MathlibExtTest.Biology.Epidemiology.StochasticSEIRVital
