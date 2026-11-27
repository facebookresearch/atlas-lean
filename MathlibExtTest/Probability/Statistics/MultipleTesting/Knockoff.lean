/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Knockoff
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

@[expose] public section

open MeasureTheory ProbabilityTheory Finset MathlibExt.Probability.Statistics.MultipleTesting
  MathlibExt.Probability.Statistics.MultipleTesting.Knockoff

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Knockoff

/-! ### A worked example

`W = (3, 2, -1, 1/2)` and `q = 1/2`. For knockoff+ the ratio
`(1 + #{W ≤ -t}) / #{W ≥ t}` is `1` at `t = 3`, `1/2` at `t = 2`, `1` at `t = 1` and `2/3` at
`t = 1/2`, so the threshold is `2` and knockoff+ selects `{0, 1}`. For knockoff (no `+1`) the
ratio at `t = 1/2` is already `1/3`, so the threshold is `1/2` and knockoff selects `{0, 1, 3}`. -/

/-- The knockoff+ threshold of the example is `2`, the only qualifying `|W_j|`. -/
theorem knockoffPlus_threshold_example :
    knockoffThreshold 1 (1 / 2) ![(3 : ℝ), 2, -1, 1 / 2] = ((2 : ℝ) : WithTop ℝ) := by
  have : (univ.filter fun j : Fin 4 => ![(3 : ℝ), 2, -1, 1 / 2] j ≠ 0 ∧
      ((1 : ℕ) + (univ.filter fun i => ![(3 : ℝ), 2, -1, 1 / 2] i ≤
        -|![(3 : ℝ), 2, -1, 1 / 2] j|).card : ℝ) /
        max ((univ.filter fun i => |![(3 : ℝ), 2, -1, 1 / 2] j| ≤
          ![(3 : ℝ), 2, -1, 1 / 2] i).card : ℝ) 1 ≤ 1 / 2) = {1} := by
    ext j
    fin_cases j <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num
  rw [knockoffThreshold, this]
  simp

/-- Knockoff+ selects `{0, 1}` in the example. -/
example : knockoffSelection 1 (1 / 2) ![(3 : ℝ), 2, -1, 1 / 2] = {0, 1} := by
  ext j
  simp only [knockoffSelection, knockoffPlus_threshold_example, Finset.mem_filter,
    Finset.mem_univ, true_and, WithTop.coe_le_coe, Finset.mem_insert, Finset.mem_singleton]
  fin_cases j <;> norm_num

/-- The knockoff threshold (offset `0`) of the example is `1/2`. -/
theorem knockoff_threshold_example :
    knockoffThreshold 0 (1 / 2) ![(3 : ℝ), 2, -1, 1 / 2] = ((1 / 2 : ℝ) : WithTop ℝ) := by
  have : (univ.filter fun j : Fin 4 => ![(3 : ℝ), 2, -1, 1 / 2] j ≠ 0 ∧
      ((0 : ℕ) + (univ.filter fun i => ![(3 : ℝ), 2, -1, 1 / 2] i ≤
        -|![(3 : ℝ), 2, -1, 1 / 2] j|).card : ℝ) /
        max ((univ.filter fun i => |![(3 : ℝ), 2, -1, 1 / 2] j| ≤
          ![(3 : ℝ), 2, -1, 1 / 2] i).card : ℝ) 1 ≤ 1 / 2) = {0, 1, 2, 3} := by
    ext j
    fin_cases j <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Finset.card_filter, Fin.sum_univ_succ,
      Fin.sum_univ_zero] <;> norm_num
  rw [knockoffThreshold, this]
  simp
  norm_num

/-- Knockoff selects `{0, 1, 3}`: strictly more than knockoff+, consistent with
`knockoffSelection_one_subset_zero`. -/
example : knockoffSelection 0 (1 / 2) ![(3 : ℝ), 2, -1, 1 / 2] = {0, 1, 3} := by
  ext j
  simp only [knockoffSelection, knockoff_threshold_example, Finset.mem_filter,
    Finset.mem_univ, true_and, WithTop.coe_le_coe, Finset.mem_insert, Finset.mem_singleton]
  fin_cases j <;> norm_num

/-- The FDP bound at the knockoff+ threshold, with nulls `H0 = {1, 2}`. -/
example :
    falseDiscoveryProportion {1, 2} (knockoffSelection 1 (1 / 2) ![(3 : ℝ), 2, -1, 1 / 2]) ≤
      1 / 2 * ((knockoffSelection 1 (1 / 2) ![(3 : ℝ), 2, -1, 1 / 2] ∩ {1, 2}).card : ℝ) /
        (1 + (({1, 2} : Finset (Fin 4)).filter fun j => ![(3 : ℝ), 2, -1, 1 / 2] j ≤ -2).card) :=
  falseDiscoveryProportion_knockoffSelection_one_le knockoffPlus_threshold_example _

/-! ### Degenerate cases -/

/-- All statistics zero: no threshold, nothing selected. -/
example (c : ℕ) (q : ℝ) (p : ℕ) : knockoffThreshold c q (0 : Fin p → ℝ) = ⊤ := by
  simp [knockoffThreshold]

/-- `q = 0`: knockoff+ never selects anything, since its ratio is always positive. -/
example (p : ℕ) (W : Fin p → ℝ) : knockoffSelection 1 0 W = ∅ := by
  ext j
  simp only [Finset.notMem_empty, iff_false]
  intro hj
  have hpos := pos_of_mem_knockoffSelection hj
  simp only [knockoffSelection, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  induction h : knockoffThreshold 1 0 W with
  | top => rw [h] at hj; exact absurd hj (by simp)
  | coe t =>
    have := knockoffThreshold_ratio_le h
    have hD : (0 : ℝ) < max ((knockoffSelection 1 0 W).card : ℝ) 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hnum : (0 : ℝ) < (1 : ℕ) + ((univ.filter fun i => W i ≤ -t).card : ℝ) := by
      push_cast; positivity
    exact absurd this (not_le.2 (div_pos hnum hD))

/-- The sign-flip hypothesis of the knockoff FDR theorems is satisfiable: constant statistics
`W = 0` under a Dirac measure. -/
example (p : ℕ) (H0 : Finset (Fin p)) :
    ∀ S ⊆ H0, (Measure.dirac (0 : ℝ)).map (fun _ => flipSigns S (0 : Fin p → ℝ)) =
      (Measure.dirac (0 : ℝ)).map (fun _ => (0 : Fin p → ℝ)) := by
  intro S _
  congr 1
  funext _ j
  simp [flipSigns]

/-- A non-degenerate witness of the sign-flip hypothesis: i.i.d. standard Gaussian statistics
`W = id`, with every coordinate allowed to be null. Flipping the signs of any set of coordinates
preserves the product law, since each coordinate's law is symmetric. -/
example (p : ℕ) (H0 : Finset (Fin p)) :
    ∀ S ⊆ H0, (Measure.pi fun _ : Fin p => gaussianReal 0 1).map (fun ω => flipSigns S (id ω)) =
      (Measure.pi fun _ : Fin p => gaussianReal 0 1).map id := by
  intro S _
  have hf : (fun ω : Fin p → ℝ => flipSigns S (id ω)) =
      fun ω j => (if j ∈ S then (fun x : ℝ => -x) else id) (ω j) := by
    funext ω j; by_cases h : j ∈ S <;> simp [flipSigns, h]
  rw [hf, Measure.map_id, Measure.pi_map_pi (fun j => by
    by_cases h : j ∈ S <;> simp [h] <;> fun_prop)]
  congr 1; funext j
  by_cases h : j ∈ S
  · simp [h, gaussianReal_map_neg]
  · simp [h]

end MathlibExtTest.Probability.Statistics.MultipleTesting.Knockoff
