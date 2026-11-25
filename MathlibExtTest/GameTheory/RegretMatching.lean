/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.RegretMatching

/-! # Tests for regret matching

Regret-matching probabilities in Chicken after one round, the Main Theorem instantiated for
Chicken, and a degenerate game (two players, zero costs, constant play on a one-point space) in
which every hypothesis of the theorem is discharged.
-/

open MeasureTheory Filter Topology
open MathlibExt.GameTheory.RegretMatchingWanted
open MathlibExt.GameTheory.CorrelatedEquilibrium
open MathlibExt.GameTheory.NoRegretDynamics (empirical)
open MathlibExt.GameTheory.BlackwellApproachabilityWanted (historySigma)

namespace MathlibExtTest.GameTheory.RegretMatching

/-- Every cost of Chicken is at most `6` in absolute value. -/
theorem abs_chickenCost_le (i : Fin 2) (s : Fin 2 → Fin 2) : |chickenCost i s| ≤ 6 := by
  have h : ∀ a b : Fin 2, |-(![![(5 : ℝ), 3], ![6, 0]] a b)| ≤ 6 := by
    intro a b
    fin_cases a <;> fin_cases b <;> norm_num
  exact h _ _

/-- After one round of (leave, leave) in Chicken, player `0` regrets not having stayed by `1`
(staying would have paid `6` instead of `5`), so with `μ = 13` it switches to staying with
probability `1 / 13`. -/
example : regretMatching chickenCost 13 (fun _ : Fin 1 => ![0, 0]) 0 1 = 1 / 13 := by
  simp [regretMatching, condRegret, switchGain, chickenCost]
  norm_num

/-- ... and repeats leaving with the remaining probability `12 / 13`. -/
example : regretMatching chickenCost 13 (fun _ : Fin 1 => ![0, 0]) 0 0 = 12 / 13 := by
  simp [regretMatching, condRegret, switchGain, chickenCost]
  norm_num

/-- After one round of (stay, leave), player `0` (who stayed and paid the best payoff `6`) has
no regret, so it stays with probability `1`. -/
example : regretMatching chickenCost 13 (fun _ : Fin 1 => ![1, 0]) 0 1 = 1 := by
  simp [regretMatching, condRegret, switchGain, chickenCost]
  norm_num

/-- The set of correlated equilibria of Chicken, the target of the theorem, contains Aumann's
correlated equilibrium. -/
example : chickenCE ∈ {ψ | IsCorrelatedEq chickenCost ψ 0} := chickenCE_isCorrelatedEq

/-- **Regret matching in Chicken.** With costs bounded by `M = 6` and `μ = 13 > 2 · 6 · (2 − 1)`,
if both players use regret matching, the empirical distributions of play converge almost surely to
the set of correlated equilibria. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → Fin 2 → Fin 2) (hX : ∀ t s, MeasurableSet {ω | X t ω = s})
    (hlaw : ∀ t s,
      P[{ω | X (t + 1) ω = s}.indicator (fun _ => (1 : ℝ)) | historySigma X t] =ᵐ[P]
        fun ω => ∏ i, regretMatching chickenCost 13 (fun k : Fin (t + 1) => X k ω) i (s i)) :
    ∀ᵐ ω ∂P, Tendsto (fun T : ℕ => Metric.infDist
      (empirical (fun k : Fin (T + 1) => X k ω)) {ψ | IsCorrelatedEq chickenCost ψ 0}) atTop
      (𝓝 0) :=
  regretMatching_tendsto_correlatedEq chickenCost abs_chickenCost_le
    (fun _ => by norm_num) X hX hlaw

/-- Zero costs for two players with two actions each. -/
def zeroCost : Fin 2 → (Fin 2 → Fin 2) → ℝ := fun _ _ => 0

/-- Constant play of the profile `(0, 0)` on the one-point space. -/
def constPlay : ℕ → Unit → Fin 2 → Fin 2 := fun _ _ _ => 0

/-- Constant play is regret matching for zero costs (with `μ = 1`): no regret is ever positive,
so each player repeats its last action with probability `1`. -/
theorem condExp_constPlay (t : ℕ) (s : Fin 2 → Fin 2) :
    (Measure.dirac () : Measure Unit)[{ω | constPlay (t + 1) ω = s}.indicator (fun _ => (1 : ℝ)) |
      historySigma constPlay t] =ᵐ[Measure.dirac ()]
      fun ω => ∏ i, regretMatching zeroCost 1 (fun k : Fin (t + 1) => constPlay k ω) i (s i) := by
  have hm : historySigma constPlay t ≤ (inferInstance : MeasurableSpace Unit) := fun _ _ =>
    MeasurableSet.of_discrete
  rw [condExp_of_stronglyMeasurable hm (stronglyMeasurable_const' fun _ _ => rfl)
    ((integrable_const (1 : ℝ)).indicator MeasurableSet.of_discrete)]
  refine Filter.Eventually.of_forall fun ω => ?_
  by_cases hs : s = fun _ => 0
  · subst hs
    rw [Set.indicator_of_mem (show constPlay (t + 1) ω = fun _ => 0 from rfl)]
    simp [regretMatching, condRegret, switchGain, constPlay, zeroCost]
  · have : ∃ i, s i ≠ 0 := by
      by_contra h
      push Not at h
      exact hs (funext h)
    obtain ⟨i, hi⟩ := this
    have hns : ω ∉ {ω | constPlay (t + 1) ω = s} := fun h => hs h.symm
    rw [Set.indicator_of_notMem hns]
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    simp [regretMatching, condRegret, switchGain, hi, constPlay, zeroCost]

/-- **A fully discharged instance.** In the zero-cost game with `M = 0` and `μ = 1`, constant play
on the one-point probability space satisfies every hypothesis of the theorem. -/
example : ∀ᵐ ω ∂(Measure.dirac () : Measure Unit), Tendsto (fun T : ℕ => Metric.infDist
      (empirical (fun k : Fin (T + 1) => constPlay k ω)) {ψ | IsCorrelatedEq zeroCost ψ 0}) atTop
      (𝓝 0) :=
  regretMatching_tendsto_correlatedEq (M := 0) (μ := 1) zeroCost (fun _ _ => by simp [zeroCost])
    (fun _ => by simp) constPlay (fun _ _ => MeasurableSet.of_discrete) condExp_constPlay

end MathlibExtTest.GameTheory.RegretMatching
