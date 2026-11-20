/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.HeatTransfer.HeatExchangers

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.HeatTransfer.HeatExchangers`

Two parallel-flow exchangers with `Ch = 3 kW/K`, `Cc = 3/2 kW/K`, `L = 2 m`, `Thi = 360 K` and
`Tci = 300 K`:

* `UA = log 2 kW/K`: outlets `350 K` and `320 K`, end differences `60` and `30`, logarithmic mean
  `30 / log 2`, and `UA ΔT_lm = 30 kW`, the heat lost by the hot stream;
* `UA = 0`: no exchange, and the logarithmic mean of the equal end differences takes its
  equal-difference branch instead of the junk value of `0 / log 1`.

The solution predicate only sees the exchanger: the `UA = log 2` closed forms replaced by `0` for
`x < 0` still solve the exchanger equations.

A counterflow exchanger with equal capacity rates `Ch = Cc = 1 kW/K`, `UA = 2 kW/K`, `L = 1 m`,
`Thi = 600 K` and `Tci = 300 K` has the solution `Th(x) = 600 - 200 x`, `Tc(x) = 500 - 200 x`:

* uniqueness identifies it with the closed form, whose boundary constant is `100`;
* the bounds hold with crossing outlets, `Th_out = 400 < Tc_out = 500`;
* both streams carry `200 kW` by the counterflow balance and by the equal-capacity duty, and the
  difference is the constant `100 K`.

With `UA = 0` both duties vanish; with unequal capacity rates `Ch = 2`, `Cc = 1` the boundary
constant takes its textbook form and the hot stream stays above the cold one; and the parallel-flow
closed form above, which has the parallel-flow sign, violates the counterflow balance.

Effectiveness: the counterflow fixture has `Cr = 1`, `NTU = 2` and `ε_c = 2 / 3`, the
equal-capacity branch where the general formula is `0 / 0`, with duty `200 kW`, above the
parallel-flow `(1 - e^{-4}) / 2`; the first parallel-flow fixture has `Cr = 1 / 2`, `ε_p = 1 / 3`
and duty `30 kW`, and a counterflow exchanger with the same data carries between `30` and `90 kW`.
-/

@[expose] public section

namespace PhyslibExtTest.HeatTransfer.HeatExchangers

open _root_.HeatTransfer.HeatExchangers

/-- `UA > 0` with unequal inlets, in kW/K, m and K: `Ch = 3`, `Cc = 3 / 2`, `L = 2`,
`UA = log 2 ≈ 0.693` (so `K = log 2 / 2` and `UA (1 / Ch + 1 / Cc) = log 2`), `Thi = 360`,
`Tci = 300`. The outlets are `Th(L) = 350` and `Tc(L) = 320`; the end differences `60` and `30`
have logarithmic mean `30 / log 2`, and `UA ΔT_lm = 30 kW = Ch (Thi - Th(L))`. -/
lemma fixture_parallel_unequal :
    parallelHotTemp 3 (3 / 2) (Real.log 2 / 2) 360 300 2 = 350 ∧
      parallelColdTemp 3 (3 / 2) (Real.log 2 / 2) 360 300 2 = 320 ∧
      logMeanTempDiff (360 - 300) (350 - 320) = 30 / Real.log 2 ∧
      Real.log 2 * logMeanTempDiff (360 - 300) (350 - 320) = 3 * (360 - 350) := by
  have hr : parallelDecayRate 3 (3 / 2) (Real.log 2 / 2) * 2 = Real.log 2 := by
    unfold parallelDecayRate
    field_simp
    ring
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hexp : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log h2pos]
    norm_num
  have e1 : (360 : ℝ) - 300 = 60 := by norm_num
  have e2 : (350 : ℝ) - 320 = 30 := by norm_num
  have h3 : logMeanTempDiff (360 - 300) (350 - 320) = 30 / Real.log 2 := by
    unfold logMeanTempDiff
    simp only [e1, e2]
    norm_num
  have h12 : (1 : ℝ) < 2 := by norm_num
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos h12)
  refine ⟨?_, ?_, h3, ?_⟩
  · unfold parallelHotTemp
    rw [hr, hexp]
    norm_num
  · unfold parallelColdTemp
    rw [hr, hexp]
    norm_num
  · rw [h3]
    field_simp
    ring

/-- `UA = 0` gives no exchange: with `K = 0` both streams keep their inlet temperatures
`360 K` and `300 K`, and the logarithmic mean of the equal end differences takes the
equal-difference branch `60`, while the unguarded formula `(Δ - Δ) / log (Δ / Δ)` divides by
`log 1 = 0` and returns Lean's junk value `0`. -/
lemma fixture_parallel_no_exchange :
    (∀ x, parallelHotTemp 3 (3 / 2) 0 360 300 x = 360 ∧
      parallelColdTemp 3 (3 / 2) 0 360 300 x = 300) ∧
      logMeanTempDiff (360 - 300) (360 - 300) = 60 ∧
      ((360 : ℝ) - 300 - (360 - 300)) / Real.log ((360 - 300) / (360 - 300)) = 0 := by
  have hr : ∀ x, parallelDecayRate 3 (3 / 2) 0 * x = 0 := by
    intro x
    unfold parallelDecayRate
    simp only [zero_mul]
  refine ⟨fun x => ?_, ?_, ?_⟩
  · unfold parallelHotTemp
    unfold parallelColdTemp
    rw [hr x]
    constructor <;> simp only [neg_zero, Real.exp_zero, sub_self, mul_zero, sub_zero, add_zero]
  · unfold logMeanTempDiff
    norm_num
  · have h0 : ((360 : ℝ) - 300 - (360 - 300)) = 0 := by norm_num
    rw [h0]
    exact zero_div _

/-- The solution predicate only sees `[0, L]`: the closed forms replaced by `0` for `x < 0`, which
jump at the inlet, still solve the exchanger equations, so uniqueness covers them. -/
example : IsParallelFlowSolution 3 (3 / 2) (Real.log 2 / 2) 2 360 300
    (fun x => if x < 0 then 0 else parallelHotTemp 3 (3 / 2) (Real.log 2 / 2) 360 300 x)
    (fun x => if x < 0 then 0 else parallelColdTemp 3 (3 / 2) (Real.log 2 / 2) 360 300 x) := by
  obtain ⟨h0, h1, h2⟩ := isParallelFlowSolution_closedForm (Ch := 3) (Cc := 3 / 2)
    (by norm_num) (by norm_num) (Real.log 2 / 2) 2 360 300
  have hnot : ∀ y ∈ Set.Icc (0 : ℝ) 2, ¬ y < 0 := fun y hy => not_lt.mpr hy.1
  refine ⟨by simpa using h0, by simpa using h1, fun x hx => ?_⟩
  obtain ⟨hh, hc⟩ := h2 x hx
  simp only [hnot x hx, ite_false]
  exact ⟨hh.congr (fun y hy => by simp [hnot y hy]) (by simp [hnot x hx]),
    hc.congr (fun y hy => by simp [hnot y hy]) (by simp [hnot x hx])⟩

/-! ## Counterflow exchangers -/

/-- Equal capacity rates with a temperature cross, in kW/K, kW, m and K: `Ch = Cc = 1`, `UA = 2`,
`L = 1` (so `K = UA / L = 2`), `Thi = 600`, `Tci = 300`. The pair `Th(x) = 600 - 200 x`,
`Tc(x) = 500 - 200 x` solves the counterflow problem; its outlets cross,
`Th_out = 400 < Tc_out = 500`; the difference is `100 = (Thi - Tci) / (1 + UA / C)` at every `x`;
and the duty `Ch (Thi - Th_out) = 200 = UA (Thi - Tci) / (1 + UA / C)` is nonzero. -/
lemma fixture_counterflow_cross :
    IsCounterflowSolution 1 1 (2 / 1) 1 600 300 (fun x => 600 - 200 * x)
        (fun x => 500 - 200 * x) ∧
      (600 : ℝ) - 200 * 1 < 500 - 200 * 0 ∧
      (∀ x : ℝ, (600 - 200 * x) - (500 - 200 * x) = (600 - 300) / (1 + 2 / 1 : ℝ)) ∧
      (1 : ℝ) * (600 - (600 - 200 * 1)) = 2 * (600 - 300) / (1 + 2 / 1) ∧
      (2 : ℝ) * (600 - 300) / (1 + 2 / 1) ≠ 0 := by
  refine ⟨⟨?_, ?_, ?_⟩, by norm_num, ?_, by norm_num, by norm_num⟩
  · change (600 : ℝ) - 200 * 0 = 600
    norm_num
  · change (500 : ℝ) - 200 * 1 = 300
    norm_num
  · intro x _
    have hval : (-200 : ℝ) = -(2 / 1) * ((600 - 200 * x) - (500 - 200 * x)) := by
      ring
    constructor
    · have h2 : HasDerivAt (fun y : ℝ => 200 * y) 200 x :=
        ((hasDerivAt_id' x).const_mul 200).congr_deriv (by ring)
      have hsub : HasDerivAt (fun y : ℝ => 600 - 200 * y) (-200) x :=
        h2.const_sub 600
      have hmul : HasDerivAt (fun y : ℝ => (1 : ℝ) * (600 - 200 * y)) (1 * -200) x :=
        hsub.const_mul 1
      have hderiv : HasDerivAt (fun y : ℝ => (1 : ℝ) * (600 - 200 * y)) (-200) x :=
        hmul.congr_deriv (by ring)
      exact hderiv.hasDerivWithinAt.congr_deriv hval
    · have h2 : HasDerivAt (fun y : ℝ => 200 * y) 200 x :=
        ((hasDerivAt_id' x).const_mul 200).congr_deriv (by ring)
      have hsub : HasDerivAt (fun y : ℝ => 500 - 200 * y) (-200) x :=
        h2.const_sub 500
      have hmul : HasDerivAt (fun y : ℝ => (1 : ℝ) * (500 - 200 * y)) (1 * -200) x :=
        hsub.const_mul 1
      have hderiv : HasDerivAt (fun y : ℝ => (1 : ℝ) * (500 - 200 * y)) (-200) x :=
        hmul.congr_deriv (by ring)
      exact hderiv.hasDerivWithinAt.congr_deriv hval
  · intro x
    have h100 : ((600 - 300) / (1 + 2 / 1 : ℝ)) = 100 := by norm_num
    linear_combination -h100

/-- Uniqueness identifies the fixture pair with the closed form on `[0, 1]`; at `x = 0` the
closed-form difference `D₀ exp (-s · 0)` then gives the boundary constant `D₀ = 100`. -/
example : (∀ x ∈ Set.Icc (0 : ℝ) 1,
      (600 - 200 * x : ℝ) = counterflowHotTemp 1 1 (2 / 1) 1 600 300 x ∧
        (500 - 200 * x : ℝ) = counterflowColdTemp 1 1 (2 / 1) 1 600 300 x) ∧
      counterflowInletDiff 1 1 (2 / 1) 1 600 300 = 100 := by
  have h := fixture_counterflow_cross.1.eq_closedForm one_pos one_pos (by norm_num)
  refine ⟨h, ?_⟩
  obtain ⟨h0, h1⟩ := h 0 ⟨le_rfl, zero_le_one⟩
  have hd := counterflowHotTemp_sub_counterflowColdTemp 1 1 (2 / 1) 1 600 300 0
  rw [← h0, ← h1] at hd
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hd
  linarith

/-- The bounds at the fixture: the hot stream stays above the cold one,
`Tci = 300 ≤ Tc x ≤ Tc_out = 500 < Thi = 600` and `Tci = 300 < Th_out = 400 ≤ Th x ≤ Thi = 600`;
the outlets cross (`400 < 500`), which the bounds allow. -/
example : (∀ x ∈ Set.Icc (0 : ℝ) 1, (500 - 200 * x : ℝ) < 600 - 200 * x) ∧
    (500 - 200 * 0 : ℝ) < 600 ∧ (300 : ℝ) < 600 - 200 * 1 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, (300 : ℝ) ≤ 500 - 200 * x ∧ 500 - 200 * x ≤ 500 - 200 * 0) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, (600 - 200 * 1 : ℝ) ≤ 600 - 200 * x ∧ 600 - 200 * x ≤ 600) := by
  have h := fixture_counterflow_cross.1
  obtain ⟨hc0, hc⟩ := h.cold_bounds one_pos one_pos (by norm_num) zero_le_one (by norm_num)
  obtain ⟨hhL, hh⟩ := h.hot_bounds one_pos one_pos (by norm_num) zero_le_one (by norm_num)
  exact ⟨h.cold_lt_hot one_pos one_pos (by norm_num) (by norm_num), hc0, hhL, hc, hh⟩

/-- The counterflow balance at the fixture outlet: the hot stream loses `1 · (600 - 400) = 200`
and the cold stream gains `1 · (500 - 300) = 200`. -/
example : (1 : ℝ) * (600 - (600 - 200 * 1)) = 1 * ((500 - 200 * 0) - (500 - 200 * 1)) :=
  fixture_counterflow_cross.1.heat_balance 1 ⟨zero_le_one, le_rfl⟩

/-- The equal-capacity lemmas at the fixture: the difference is the constant
`300 / (1 + 2 / 1) = 100`, and both stream heats are `2 · 300 / 3 = 200`. -/
example : (∀ x ∈ Set.Icc (0 : ℝ) 1, (600 - 200 * x : ℝ) - (500 - 200 * x) = 100) ∧
    (1 : ℝ) * (600 - (600 - 200 * 1)) = 200 ∧ (1 : ℝ) * ((500 - 200 * 0) - 300) = 200 := by
  have h := fixture_counterflow_cross.1
  obtain ⟨hQh, hQc⟩ := h.equalCapacity_heat one_pos (by norm_num) one_pos
  exact ⟨fun x hx => (h.equalCapacity_sub_const one_pos (by norm_num) one_pos x hx).trans
    (by norm_num), hQh.trans (by norm_num), hQc.trans (by norm_num)⟩

/-- No exchange (`UA = 0`): the closed form solves the problem with `K = 0 / 1`, and by the
equal-capacity lemma both stream heats vanish. -/
example : (1 : ℝ) * (600 - counterflowHotTemp 1 1 (0 / 1) 1 600 300 1) = 0 ∧
    (1 : ℝ) * (counterflowColdTemp 1 1 (0 / 1) 1 600 300 0 - 300) = 0 := by
  have h := isCounterflowSolution_closedForm (Ch := 1) (Cc := 1) one_pos one_pos
    (by norm_num : (0 : ℝ) ≤ 0 / 1) zero_le_one 600 300
  obtain ⟨hh, hc⟩ := h.equalCapacity_heat one_pos le_rfl one_pos
  exact ⟨hh.trans (by norm_num), hc.trans (by norm_num)⟩

/-- Unequal capacity rates `Ch = 2`, `Cc = 1`, `K = 1`, `L = 1` (so `s = -1 / 2`): the boundary
constant takes the textbook form `(Cc - Ch) (Thi - Tci) / (Cc - Ch exp (-s L))`, here
`-300 / (1 - 2 exp (1 / 2))`, and along the closed form the hot stream stays above the cold one. -/
example : counterflowInletDiff 2 1 1 1 600 300 = -300 / (1 - 2 * Real.exp (1 / 2)) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      counterflowColdTemp 2 1 1 1 600 300 x < counterflowHotTemp 2 1 1 1 600 300 x := by
  have hs : counterflowRate 2 1 1 * 1 = -(1 / 2) := by
    unfold counterflowRate
    norm_num
  refine ⟨?_, (isCounterflowSolution_closedForm (Ch := 2) (Cc := 1) two_pos one_pos zero_le_one
    zero_le_one 600 300).cold_lt_hot two_pos one_pos zero_le_one (by norm_num)⟩
  rw [counterflowInletDiff_eq_of_ne two_pos one_pos zero_le_one zero_le_one (by norm_num), hs]
  norm_num

/-- The parallel-flow sign violates counterflow accounting: the parallel-flow closed form with
`UA = log 2` solves the equations with the parallel-flow sign, and its hot temperature drops from
`360` to `350`, so the counterflow port balance `Ch (Th 0 - Th L) = Cc (Tc 0 - Tc L)` fails. -/
example : 3 * (parallelHotTemp 3 (3 / 2) (Real.log 2 / 2) 360 300 0 -
      parallelHotTemp 3 (3 / 2) (Real.log 2 / 2) 360 300 2) ≠
    3 / 2 * (parallelColdTemp 3 (3 / 2) (Real.log 2 / 2) 360 300 0 -
      parallelColdTemp 3 (3 / 2) (Real.log 2 / 2) 360 300 2) := by
  obtain ⟨h0, -, hpar⟩ := isParallelFlowSolution_closedForm (Ch := 3) (Cc := 3 / 2)
    (by norm_num) (by norm_num) (Real.log 2 / 2) 2 360 300
  refine parallelSign_violates_counterflow_balance (by norm_num) (by norm_num) hpar ?_
  rw [fixture_parallel_unequal.1, h0]
  norm_num

/-! ## Effectiveness -/

/-- **Equal capacity rates.** `Ch = Cc = 1`, `UA = 2`, `L = 1`, `Thi = 600`, `Tci = 300`
(`Cr = 1`, `NTU = 2`): the `Cr = 1` branch gives `ε_c = 2 / 3` and the duty `200`, while
`ε_p = (1 - e^{-4}) / 2 < 2 / 3`. -/
lemma effectiveness_fixture_equal {Th Tc : ℝ → ℝ}
    (h : IsCounterflowSolution 1 1 (2 / 1) 1 600 300 Th Tc) :
    capacityRatio 1 1 = 1 ∧ counterflowEffectiveness (transferUnits 2 1 1) 1 = 2 / 3 ∧
      1 * (600 - Th 1) = 200 ∧ parallelEffectiveness 2 1 < 2 / 3 := by
  have hQ := (h.heat_eq_effectiveness (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have hCr : capacityRatio 1 1 = 1 := by norm_num [capacityRatio]
  have hε : counterflowEffectiveness (transferUnits 2 1 1) 1 = 2 / 3 := by
    norm_num [counterflowEffectiveness, transferUnits]
  rw [hCr, hε] at hQ
  refine ⟨hCr, hε, by rw [hQ]; norm_num, ?_⟩
  unfold parallelEffectiveness
  have hx : (-(2 * (1 + 1)) : ℝ) = -4 := by norm_num
  rw [hx, div_lt_iff₀ (by norm_num)]
  linarith [Real.exp_pos (-4)]

/-- **Unequal capacity rates.** `Ch = 3`, `Cc = 3 / 2` (`Cr = 1 / 2`), `UA = log 2`, `L = 2`,
`Thi = 360`, `Tci = 300`: `ε_p = 1 / 3` and the parallel-flow duty is `30`; a counterflow
exchanger with the same data carries at least `30` and at most `Cmin (Thi - Tci) = 90`. -/
lemma effectiveness_fixture_unequal {Thp Tcp Thc Tcc : ℝ → ℝ}
    (hp : IsParallelFlowSolution 3 (3 / 2) (Real.log 2 / 2) 2 360 300 Thp Tcp)
    (hc : IsCounterflowSolution 3 (3 / 2) (Real.log 2 / 2) 2 360 300 Thc Tcc) :
    capacityRatio 3 (3 / 2) = 1 / 2 ∧
      parallelEffectiveness (transferUnits (Real.log 2) 3 (3 / 2)) (1 / 2) = 1 / 3 ∧
      3 * (360 - Thp 2) = 30 ∧ 30 ≤ 3 * (360 - Thc 2) ∧ 3 * (360 - Thc 2) ≤ 90 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCr : capacityRatio 3 (3 / 2) = 1 / 2 := by norm_num [capacityRatio]
  have hmin : min (3 : ℝ) (3 / 2) = 3 / 2 := by norm_num
  have hεp : parallelEffectiveness (transferUnits (Real.log 2) 3 (3 / 2)) (1 / 2) = 1 / 3 := by
    unfold parallelEffectiveness transferUnits
    rw [hmin]
    have hx : Real.log 2 / (3 / 2) * (1 + 1 / 2) = Real.log 2 := by ring
    rw [hx, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hQp := (hp.heat_eq_effectiveness (by norm_num) (by norm_num) (by norm_num)).1
  rw [hCr, hεp, hmin] at hQp
  have hQc := (hc.heat_eq_effectiveness (by norm_num) (by norm_num) hlog.le (by norm_num)).1
  rw [hCr, hmin] at hQc
  have hN : 0 ≤ transferUnits (Real.log 2) 3 (3 / 2) := by
    unfold transferUnits
    rw [hmin]
    exact div_nonneg hlog.le (by norm_num)
  have hcmp := parallelEffectiveness_le_counterflowEffectiveness hN
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [hεp] at hcmp
  have hbd := (counterflowEffectiveness_bounds hN (by norm_num : (1 / 2 : ℝ) ≤ 1)).2
  refine ⟨hCr, hεp, by rw [hQp]; norm_num, ?_, ?_⟩
  · rw [hQc]
    nlinarith
  · rw [hQc]
    nlinarith

/-- The stream data of both fixtures give the effectiveness domain: `Cr = 1` for `Ch = Cc = 1`,
and `0 < Cr ≠ 1` for `Ch = 3`, `Cc = 3 / 2`, whose `NTU` is nonnegative for `UA = log 2`. -/
example : capacityRatio 1 1 = 1 ∧ 0 < capacityRatio 3 (3 / 2) ∧ capacityRatio 3 (3 / 2) ≠ 1 ∧
    0 ≤ transferUnits (Real.log 2) 3 (3 / 2) := by
  obtain ⟨-, -, h1, -⟩ := capacityRatio_domain (Ch := 1) (Cc := 1) (UA := 2) one_pos one_pos
    (by norm_num)
  obtain ⟨hpos, -, hne, hN⟩ := capacityRatio_domain (Ch := 3) (Cc := 3 / 2) (UA := Real.log 2)
    (by norm_num) (by norm_num) (Real.log_nonneg (by norm_num))
  exact ⟨h1.mpr rfl, hpos, fun h => absurd (hne.mp h) (by norm_num), hN⟩

/-- The parallel-flow effectiveness of the equal-capacity data, `(1 - e^{-4}) / 2`, lies in
`[0, 1]`. -/
example : 0 ≤ parallelEffectiveness 2 1 ∧ parallelEffectiveness 2 1 ≤ 1 :=
  parallelEffectiveness_bounds (by norm_num) (by norm_num)

/-- At `Cr = 1` and `NTU = 2` the general counterflow formula is `0 / 0`, which Lean evaluates to
`0`, while the effectiveness takes its equal-capacity value `2 / 3`. -/
example : (1 - Real.exp (-(2 * (1 - 1)))) / (1 - 1 * Real.exp (-(2 * (1 - 1)))) = (0 : ℝ) ∧
    counterflowEffectiveness 2 1 = 2 / 3 := by
  obtain ⟨h0, h1, -⟩ := counterflowEffectiveness_one_substitution (NTU := 2) (by norm_num)
  exact ⟨h0, h1.trans (by norm_num)⟩

end PhyslibExtTest.HeatTransfer.HeatExchangers
