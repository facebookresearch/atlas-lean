/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.StochasticCRNLLN
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-! Tests for Kurtz's law of large numbers for stochastic reaction networks:

* reaction vectors, `stoichNorm` and stochastic mass-action propensities computed from the
  definitions: for dimerization `2X → ∅` at `N = 10`, `z = 5`, the propensity is `10 · 5 · 4 / 10²
  = 2` while the macroscopic rate gives `N β(z / N) = 5 / 2` (the `O(1)` gap in `λ`, `O(1 / N)` in
  `λ / N`, that `abs_massActionPropensity_div_sub_le` controls), and one molecule cannot dimerize;
* a chain path computed from the definition: the immigration process `∅ → X` with
  `X(t) = y(N κ t)` satisfies the time-change equation for every nondecreasing `y` with `y(0) = 0`;
* the small-`N` case `N = 1`, where the deviation at `t = 1/2` is at least `1/2` on every path, so
  no limit statement is claimed at fixed `N`;
* non-vacuity: the full hypothesis bundles of `tendsto_measure_deviation_massAction` and
  `tendsto_measure_deviation_of_eq` are satisfied by the immigration network driven by a genuine
  unit Poisson process (exponential interarrivals on an infinite product space); the conclusion is
  the functional law of large numbers `Y(N κ t) / N → κ t` for the Poisson process.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal

namespace MathlibExtTest.Biology.Dynamics.StochasticCRNLLN

open MathlibExt.Biology.Dynamics.ComplexBalanced
open MathlibExt.Biology.Dynamics.StochasticCRNNonExplosion
open MathlibExt.Biology.Dynamics.StochasticCRNLLN
open MathlibExt.Biology.Dynamics.SystemsBiology (propensity)

/-! ### Reaction vectors and mass-action propensities, from the definitions -/

/-- The birth–death network on one species: reaction `0` is `∅ → X`, reaction `1` is `X → ∅`. -/
def birthDeath : ReactionNetwork Unit (Fin 2) where
  src r _ := if r = 0 then 0 else 1
  prod r _ := if r = 0 then 1 else 0

example : reactionVector birthDeath 0 () = 1 ∧ reactionVector birthDeath 1 () = -1 := by
  norm_num [reactionVector, birthDeath]

example : stoichNorm birthDeath = 2 := by
  norm_num [stoichNorm, l1Norm, reactionVector, birthDeath, Fin.sum_univ_two]

/-- Dimerization `2X → ∅`. -/
def dimer : ReactionNetwork Unit Unit where
  src _ _ := 2
  prod _ _ := 0

/-- At `N = 10` and `z = 5` with `κ = 1`: `λ = 10 · (5 · 4) / 10² = 2`, while the macroscopic rate
gives `N β(z / N) = 10 · (1/2)² = 5/2`. -/
example : massActionPropensity dimer (fun _ => 1) 10 () (fun _ => 5) = 2 ∧
    (10 : ℝ) * dimer.rate (fun _ => 1) (scaled 10 fun _ => 5) () = 5 / 2 := by
  have h : Nat.descFactorial 5 2 = 20 := rfl
  constructor
  · norm_num [massActionPropensity, propensity, dimer, h]
  · norm_num [ReactionNetwork.rate, scaled, dimer]

/-- One molecule cannot dimerize: the propensity vanishes, as `propensity_eq_zero` requires. -/
example : massActionPropensity dimer (fun _ => 1) 10 () (fun _ => 1) = 0 := by
  have h : Nat.descFactorial 1 2 = 0 := rfl
  norm_num [massActionPropensity, propensity, dimer, h]

/-- At `N = 1` the stochastic mass-action propensity is `SystemsBiology.propensity`: for
dimerization with `κ = 3` at `z = 4` both are `3 · 4 · 3 = 36`, computed from the definitions. -/
example : massActionPropensity dimer (fun _ => 3) 1 () (fun _ => 4) = 36 ∧
    propensity dimer (fun _ => 3) () (fun _ => 4) = 36 := by
  have h : Nat.descFactorial 4 2 = 12 := rfl
  constructor
  · norm_num [massActionPropensity, propensity, dimer, h]
  · norm_num [propensity, dimer, h]

example :
    massActionPropensity dimer (fun _ => 3) 1 = propensity dimer (fun _ => 3) :=
  massActionPropensity_one dimer _

/-! ### The immigration chain, from the definition -/

/-- Immigration `∅ → X`. -/
def immig : ReactionNetwork Unit Unit where
  src _ _ := 0
  prod _ _ := 1

/-- The mass-action propensity of immigration is the constant `N κ`. -/
theorem massActionPropensity_immig (κ : ℝ) (N : ℕ) (r : Unit) (z : Unit → ℕ) :
    massActionPropensity immig (fun _ => κ) N r z = N * κ := by
  simp [massActionPropensity, propensity, immig]

/-- The immigration path `X(t) = y(N κ t)`. -/
noncomputable def immigPath (κ : ℝ) (N : ℕ) (y : ℝ≥0 → ℕ) : ℝ → Unit → ℕ :=
  fun t _ => y (Real.toNNReal (N * κ * t))

/-- **A chain path, from the definition** (non-vacuity of `IsChainPath`): for every
nondecreasing counting path `y` with `y(0) = 0`, the immigration path `X(t) = y(N κ t)` solves
the time-change equation of the mass-action immigration network. -/
theorem immigPath_isChainPath {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ) {y : ℝ≥0 → ℕ} (hy0 : y 0 = 0)
    (hy : Monotone y) :
    IsChainPath (massAction immig (fun _ => κ) (fun _ => hκ) N) (fun _ => y) (immigPath κ N y)
    where
  measurable_coord _ := by
    have hmono : Monotone fun t : ℝ => (y (Real.toNNReal (N * κ * t)) : ℝ) := fun a b hab =>
      Nat.cast_le.2 (hy (Real.toNNReal_le_toNNReal
        (mul_le_mul_of_nonneg_left hab (by positivity))))
    have := Measurable.nat_floor hmono.measurable
    simpa [immigPath] using this
  intervalIntegrable_propensity _ _ := by
    simp only [massAction, massActionPropensity_immig]
    exact intervalIntegrable_const
  coord_eq t _ i := by
    have hclock : ∀ r, clock (massAction immig (fun _ => κ) (fun _ => hκ) N) r (immigPath κ N y)
        t = Real.toNNReal (N * κ * t) := by
      intro r
      simp only [clock, massAction, massActionPropensity_immig, intervalIntegral.integral_const,
        smul_eq_mul, sub_zero]
      congr 1
      ring
    have hζ : ∀ r,
        reactionVector (massAction immig (fun _ => κ) (fun _ => hκ) N).network r i = 1 := by
      intro r
      simp [massAction, reactionVector, immig]
    rw [Fintype.sum_unique, hclock, hζ]
    simp [immigPath, hy0]

/-! ### Small `N`: no limit is claimed -/

/-- **At `N = 1` the scaled chain is far from the mean-field solution.** For `κ = 1`, the count at
time `1/2` is a natural number while `x(1/2) = 1/2`, so the deviation is at least `1/2` on every
path. Kurtz's theorem is a statement about `N → ∞` only. -/
example (y : ℝ≥0 → ℕ) : 1 / 2 ≤ deviation 1 (immigPath 1 1 y) (fun t _ => t) (1 / 2) := by
  unfold deviation l1Norm scaled immigPath
  simp only [Finset.univ_unique, Finset.sum_singleton, Pi.sub_apply, Nat.cast_one, div_one]
  generalize y _ = n
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    norm_num
  · have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 h
    rw [abs_of_nonneg (by linarith)]
    linarith

/-! ### Non-vacuity of Kurtz's theorem with a genuine Poisson process -/

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

/-- The unit Poisson process on the product of exponential laws. -/
noncomputable abbrev expCount : ℝ≥0 → (ℕ → ℝ) → ℕ :=
  PoissonProcess.count fun (i : ℕ) (ω : ℕ → ℝ) => ω i

/-- The deterministic immigration path `x(t) = κ t` and its initial condition. -/
theorem tendsto_scaled_zero (κ : ℝ) :
    Tendsto (fun N : ℕ => scaled N fun _ : Unit => 0) atTop
      (𝓝 ((fun t (_ : Unit) => κ * t) 0)) := by
  have : (fun N : ℕ => scaled N fun _ : Unit => 0) = fun _ => (fun t (_ : Unit) => κ * t) 0 := by
    funext N i
    simp [scaled]
  rw [this]
  exact tendsto_const_nhds

/-- **All hypotheses of `tendsto_measure_deviation_massAction` are satisfiable**: the mass-action
immigration network driven by the coordinate Poisson process has the mean-field limit
`x(t) = κ t`, and the theorem yields the functional law of large numbers for the Poisson process,
`P(∃ t ∈ [0, T], |Y(N κ t) / N - κ t| ≥ ε) → 0`. -/
example {κ : ℝ} (hκ : 0 ≤ κ) (T ε : ℝ) (hε : 0 < ε) :
    haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
    Tendsto (fun N : ℕ => Measure.infinitePi (fun _ : ℕ => expMeasure 1)
      {ω | ∃ t ∈ Icc 0 T, ε ≤ deviation N (immigPath κ N fun u => expCount u ω)
        (fun t _ => κ * t) t}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have hY := isPoissonProcess_expCount
  refine tendsto_measure_deviation_massAction immig (κ := fun _ => κ) (fun _ => hκ)
    (Y := fun _ _ => expCount) (X := fun N ω => immigPath κ N fun u => expCount u ω)
    (fun _ _ => hY) (fun N => ?_) (fun t _ _ => ?_) (fun δ hδ => ?_) T hε
  · filter_upwards [hY.ae_zero, hY.ae_monotone] with ω h0 hm
    exact immigPath_isChainPath hκ N h0 hm
  · simpa [ReactionNetwork.massActionField, immig] using (hasDerivAt_id t).const_mul κ
  · refine tendsto_measure_deviation_zero_of_initial (z₀ := fun _ _ => 0) (fun N => ?_)
      (tendsto_scaled_zero κ) hδ
    filter_upwards [hY.ae_zero] with ω h0
    funext i
    simp [immigPath, h0]

/-- **All hypotheses of `tendsto_measure_deviation_of_eq` are satisfiable**: the immigration
network is exactly density dependent, `λ^N(z) = N κ = N β(z / N)` with the constant macroscopic
rate `β = κ`. -/
example {κ : ℝ} (hκ : 0 ≤ κ) (T ε : ℝ) (hε : 0 < ε) :
    haveI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
    Tendsto (fun N : ℕ => Measure.infinitePi (fun _ : ℕ => expMeasure 1)
      {ω | ∃ t ∈ Icc 0 T, ε ≤ deviation N (immigPath κ N fun u => expCount u ω)
        (fun t _ => κ * t) t}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  have hY := isPoissonProcess_expCount
  refine tendsto_measure_deviation_of_eq (G := immig)
    (C := massAction immig (fun _ => κ) (fun _ => hκ)) (β := fun _ _ => κ)
    (Y := fun _ _ => expCount) (X := fun N ω => immigPath κ N fun u => expCount u ω)
    (fun _ => rfl) (fun _ => (LipschitzWith.const κ).locallyLipschitz)
    (fun N _ r z => massActionPropensity_immig κ N r z) (fun _ _ => hY) (fun N => ?_)
    ⟨fun t _ _ => ?_⟩ (fun δ hδ => ?_) T hε
  · filter_upwards [hY.ae_zero, hY.ae_monotone] with ω h0 hm
    exact immigPath_isChainPath hκ N h0 hm
  · simpa [reactionVector, immig] using (hasDerivAt_id t).const_mul κ
  · refine tendsto_measure_deviation_zero_of_initial (z₀ := fun _ _ => 0) (fun N => ?_)
      (tendsto_scaled_zero κ) hδ
    filter_upwards [hY.ae_zero] with ω h0
    funext i
    simp [immigPath, h0]

end MathlibExtTest.Biology.Dynamics.StochasticCRNLLN
