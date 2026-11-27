/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SplitConformal
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Probability.Statistics.SplitConformal

namespace MathlibExtTest.Probability.Statistics.SplitConformal

/-! ### Order statistic: multiplicity, off-by-one and the `⊤` branch -/

/-- Ties are counted with multiplicity: the second smallest of `(0, 0, 1)` is `0`. A quantile
of the set of distinct values `{0, 1}` would give `1` here. -/
example : orderStatistic ![(0 : ℝ), 0, 1] 2 = (0 : ℝ) := by
  rw [orderStatistic_eq_coe_iff (by norm_num)]
  simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- The third smallest of `(0, 0, 1)` is `1`. -/
example : orderStatistic ![(0 : ℝ), 0, 1] 3 = (1 : ℝ) := by
  rw [orderStatistic_eq_coe_iff (by norm_num)]
  simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- Past the number of values the order statistic is `⊤`. -/
example : orderStatistic ![(0 : ℝ), 0, 1] 4 = ⊤ :=
  (orderStatistic_eq_top_iff _ (by norm_num)).2 (by simp)

/-! ### The threshold: `n = 0`, `k = n + 1` and the rank `k` -/

/-- With no calibration score (`n = 0`) the threshold is `⊤` and the test score is covered. -/
example (ω : Fin 1 → ℝ) : splitConformalThreshold 1 ω = ⊤ :=
  (orderStatistic_eq_top_iff _ le_rfl).2 (by simp)

/-- The `+∞` branch: `k = n + 1` always gives the threshold `⊤`. -/
example (n : ℕ) (ω : Fin (n + 1) → ℝ) : splitConformalThreshold (n + 1) ω = ⊤ :=
  (orderStatistic_eq_top_iff _ (by omega)).2 (by simp)

/-- Off-by-one at an exact grid point: `α = 1/4`, `n + 1 = 4` gives `k = 3`, not `4`. -/
example : ⌈(1 - (1 / 4 : ℝ)) * (3 + 1)⌉₊ = 3 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-- Off the grid: `α = 1/10`, `n + 1 = 4` gives `k = 4 = n + 1`, hence the `⊤` branch. -/
example : ⌈(1 - (1 / 10 : ℝ)) * (3 + 1)⌉₊ = 4 := by
  rw [Nat.ceil_eq_iff (by norm_num)]
  norm_num

/-! ### Coverage equivalence with ties -/

/-- A test score equal to the threshold is covered: calibration `(0, 0, 1)`, test `0`, `k = 2`.
Only strictly smaller calibration scores count, so `L = 0`. -/
example : ((![(0 : ℝ), 0, 1, 0] (Fin.last 3) : ℝ) : WithTop ℝ) ≤
    splitConformalThreshold 2 ![(0 : ℝ), 0, 1, 0] := by
  rw [coe_le_splitConformalThreshold_iff (by norm_num), strictLowerCount]
  simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- Calibration `(0, 0, 1)`, test `1/2`, `k = 2`: the threshold is `0` and `L = 2`, so the test
score is not covered. -/
example : ¬ (((![(0 : ℝ), 0, 1, 1 / 2] (Fin.last 3) : ℝ) : WithTop ℝ) ≤
    splitConformalThreshold 2 ![(0 : ℝ), 0, 1, 1 / 2]) := by
  rw [coe_le_splitConformalThreshold_iff (by norm_num), strictLowerCount]
  simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- The same vector at `α = 1/4` (`k = 3`): the p-value `(4 - 2) / 4 = 1/2` exceeds `α`, and the
test score is covered by the third smallest calibration score `1`. -/
example : ((![(0 : ℝ), 0, 1, 1 / 2] (Fin.last 3) : ℝ) : WithTop ℝ) ≤
    splitConformalThreshold ⌈(1 - (1 / 4 : ℝ)) * ((3 : ℕ) + 1)⌉₊ ![(0 : ℝ), 0, 1, 1 / 2] := by
  rw [coe_le_splitConformalThreshold_iff_lt_permutationPValue (by norm_num),
    permutationPValue_eval_last, strictLowerCount]
  simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- All scores equal: `L = 0` and the permutation p-value is `1`. -/
example (n : ℕ) : permutationPValue (Equiv.Perm (Fin (n + 1)))
    (fun ω : Fin (n + 1) → ℝ => ω (Fin.last n)) (fun _ => 0) = 1 := by
  rw [permutationPValue_eval_last, strictLowerCount]
  simp only [lt_self_iff_false, Finset.filter_false, Finset.card_empty, Nat.cast_zero, sub_zero]
  exact div_self (by positivity)

/-! ### Direction of the coordinate action -/

/-- `(σ • ω) i = ω (σ⁻¹ i)`: with the rotation `0 ↦ 1 ↦ 2 ↦ 0`, the entry at `1` of `σ • ω` is
`ω 0`, whereas `(ω ∘ σ) 1 = ω 2`. -/
example (a b c : ℝ) : (finRotate 3 • ![a, b, c]) 1 = a ∧ (![a, b, c] ∘ finRotate 3) 1 = c := by
  rw [coordinatePermAction_smul_apply]
  constructor
  · have : (finRotate 3)⁻¹ 1 = 0 := by decide
    rw [this]
    rfl
  · have : finRotate 3 1 = 2 := by decide
    simp [this]

/-! ### Non-vacuity of the coverage theorem -/

/-- A point mass at a constant vector is a coordinate-permutation invariant probability law (an
all-ties case); the coverage theorem applies to it. -/
example (n : ℕ) :
    ENNReal.ofReal (1 - 1 / 10) ≤ Measure.dirac (fun _ : Fin (n + 1) => (0 : ℝ))
      {ω | (ω (Fin.last n) : WithTop ℝ) ≤
        splitConformalThreshold ⌈(1 - 1 / 10 : ℝ) * (n + 1)⌉₊ ω} := by
  refine ofReal_one_sub_le_measure_coe_le_splitConformalThreshold _ (fun σ => ?_)
    (by norm_num) (by norm_num)
  rw [Measure.map_dirac' (f := fun ω : Fin (n + 1) → ℝ => ω ∘ σ)
    (Measurable.of_eval fun i => by exact measurable_pi_apply (σ i))]
  rfl

/-- The derived endpoint `α = 0` (outside the recorded range `0 < α < 1`): `k = n + 1`, the
threshold is `⊤`, and the coverage bound is `1`. -/
example (n : ℕ) (μ : Measure (Fin (n + 1) → ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ σ : Equiv.Perm (Fin (n + 1)), μ.map (fun ω => ω ∘ σ) = μ) :
    1 ≤ μ {ω | (ω (Fin.last n) : WithTop ℝ) ≤
      splitConformalThreshold ⌈(1 - 0 : ℝ) * (n + 1)⌉₊ ω} := by
  simpa using ofReal_one_sub_le_measure_coe_le_splitConformalThreshold μ hμ le_rfl one_pos

/-! ### Axioms -/

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.coe_le_orderStatistic_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms coe_le_orderStatistic_iff

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.orderStatistic_eq_coe_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms orderStatistic_eq_coe_iff

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.orderStatistic_eq_top_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms orderStatistic_eq_top_iff

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.coordinatePermAction_smul_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms coordinatePermAction_smul_apply

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.smulInvariantMeasure_of_map_comp_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms smulInvariantMeasure_of_map_comp_eq

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.coe_le_splitConformalThreshold_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms coe_le_splitConformalThreshold_iff

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.permutationPValue_eval_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms permutationPValue_eval_last

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.strictLowerCount_lt_ceil_iff_lt_permutationPValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms strictLowerCount_lt_ceil_iff_lt_permutationPValue

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.coe_le_splitConformalThreshold_iff_lt_permutationPValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms coe_le_splitConformalThreshold_iff_lt_permutationPValue

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.ofReal_ceil_div_le_measure_coe_le_splitConformalThreshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ofReal_ceil_div_le_measure_coe_le_splitConformalThreshold

/--
info: 'MathlibExt.Probability.Statistics.SplitConformal.ofReal_one_sub_le_measure_coe_le_splitConformalThreshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ofReal_one_sub_le_measure_coe_le_splitConformalThreshold

end MathlibExtTest.Probability.Statistics.SplitConformal
