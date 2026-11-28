/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.MultipleTesting.KnockoffFDR

/-!
# Tests for knockoff and knockoff+ FDR control

A fair sign on one null statistic gives a nontrivial example with tied magnitudes
and a zero statistic.
-/

open MeasureTheory
open MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Probability.Statistics.MultipleTesting.Knockoff
open MathlibExt.Probability.KnockoffFDRWanted

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.KnockoffFDR

private noncomputable def statistics (b : Bool) : Fin 3 → ℝ :=
  if b then ![1, 1, 0] else ![-1, 1, 0]

-- The tie at magnitude one is included in the threshold counts all at once.
example : knockoffSelection 1 (1 / 2) (statistics true) = {0, 1} := by
  have ht : knockoffThreshold 1 (1 / 2) (statistics true) = ((1 : ℝ) : WithTop ℝ) := by
    have hc : (Finset.univ.filter fun j : Fin 3 => statistics true j ≠ 0 ∧
        ((1 : ℕ) + (Finset.univ.filter fun i => statistics true i ≤
          -|statistics true j|).card : ℝ) /
          max ((Finset.univ.filter fun i => |statistics true j| ≤ statistics true i).card : ℝ)
            1 ≤ (1 / 2 : ℝ)) = {0, 1} := by
      ext j
      fin_cases j <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
        norm_num [statistics]
    rw [knockoffThreshold, hc]
    norm_num [statistics]
  ext j
  simp only [knockoffSelection, ht, Finset.mem_filter, Finset.mem_univ, true_and,
    WithTop.coe_le_coe, Finset.mem_insert, Finset.mem_singleton]
  fin_cases j <;> norm_num [statistics]

example : knockoffSelection 1 (1 / 2) (statistics false) = ∅ := by
  have ht : knockoffThreshold 1 (1 / 2) (statistics false) = ⊤ := by
    unfold knockoffThreshold
    have hc : (Finset.univ.filter fun j : Fin 3 => statistics false j ≠ 0 ∧
        ((1 : ℕ) + (Finset.univ.filter fun i => statistics false i ≤
          -|statistics false j|).card : ℝ) /
          max ((Finset.univ.filter fun i => |statistics false j| ≤ statistics false i).card : ℝ)
            1 ≤ (1 / 2 : ℝ)) = ∅ := by
      ext j
      fin_cases j <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num [statistics]
    rw [hc, Finset.inf_empty]
  ext j
  simp only [knockoffSelection, ht, Finset.mem_filter, Finset.mem_univ, true_and,
    WithTop.top_le_iff, WithTop.coe_ne_top, Finset.notMem_empty]

-- Knockoff at level `1/2` selects the null `0` and the non-null `1` when the coin shows `true`.
private theorem knockoffSelection_zero_half_true :
    knockoffSelection 0 (1 / 2) (statistics true) = {0, 1} := by
  have ht : knockoffThreshold 0 (1 / 2) (statistics true) = ((1 : ℝ) : WithTop ℝ) := by
    have hc : (Finset.univ.filter fun j : Fin 3 => statistics true j ≠ 0 ∧
        ((0 : ℕ) + (Finset.univ.filter fun i => statistics true i ≤
          -|statistics true j|).card : ℝ) /
          max ((Finset.univ.filter fun i => |statistics true j| ≤ statistics true i).card : ℝ)
            1 ≤ (1 / 2 : ℝ)) = {0, 1} := by
      ext j
      fin_cases j <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
        norm_num [statistics]
    rw [knockoffThreshold, hc]
    norm_num [statistics]
  ext j
  simp only [knockoffSelection, ht, Finset.mem_filter, Finset.mem_univ, true_and,
    WithTop.coe_le_coe, Finset.mem_insert, Finset.mem_singleton]
  fin_cases j <;> norm_num [statistics]

-- When the coin shows `false`, knockoff at level `1/2` selects nothing.
private theorem knockoffSelection_zero_half_false :
    knockoffSelection 0 (1 / 2) (statistics false) = ∅ := by
  have ht : knockoffThreshold 0 (1 / 2) (statistics false) = ⊤ := by
    unfold knockoffThreshold
    have hc : (Finset.univ.filter fun j : Fin 3 => statistics false j ≠ 0 ∧
        ((0 : ℕ) + (Finset.univ.filter fun i => statistics false i ≤
          -|statistics false j|).card : ℝ) /
          max ((Finset.univ.filter fun i => |statistics false j| ≤ statistics false i).card : ℝ)
            1 ≤ (1 / 2 : ℝ)) = ∅ := by
      ext j
      fin_cases j <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        Finset.card_filter, Fin.sum_univ_succ, Fin.sum_univ_zero] <;> norm_num [statistics]
    rw [hc, Finset.inf_empty]
  ext j
  simp only [knockoffSelection, ht, Finset.mem_filter, Finset.mem_univ, true_and,
    WithTop.top_le_iff, WithTop.coe_ne_top, Finset.notMem_empty]

private noncomputable def fairCoin : Measure Bool :=
  (1 / 2 : ENNReal) • (Measure.dirac true + Measure.dirac false)

private instance isProbabilityMeasure_fairCoin : IsProbabilityMeasure fairCoin := ⟨by
  simp only [fairCoin, smul_apply, add_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, div_eq_mul_inv, one_mul]
  rw [show (1 : ENNReal) + 1 = 2 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

private theorem measurable_statistics : Measurable statistics := measurable_of_countable _

-- Flipping the sign of the null statistic `0` swaps the two outcomes of the fair coin.
private theorem map_flipSigns_statistics : ∀ S ⊆ ({0} : Finset (Fin 3)),
    fairCoin.map (fun b => flipSigns S (statistics b)) = fairCoin.map statistics := by
  intro S hS
  rcases Finset.subset_singleton_iff.mp hS with rfl | rfl
  · rfl
  have hswap : (fun b => flipSigns {0} (statistics b)) = fun b => statistics (!b) := by
    funext b i
    cases b <;> fin_cases i <;> norm_num [statistics, flipSigns]
  have hm := measurable_statistics
  have hn : Measurable fun b => statistics (!b) := measurable_of_countable _
  rw [hswap, fairCoin, Measure.map_smul _ hn.aemeasurable, Measure.map_smul _ hm.aemeasurable,
    Measure.map_add _ _ hn, Measure.map_add _ _ hm]
  simp only [Measure.map_dirac' hn, Measure.map_dirac' hm, Bool.not_true, Bool.not_false]
  rw [add_comm]

example :
    ∫ b, falseDiscoveryProportion {0} (knockoffSelection 1 (1 / 2) (statistics b)) ∂fairCoin ≤
      1 / 2 :=
  integral_falseDiscoveryProportion_knockoffSelection_one_le fairCoin
    measurable_statistics {0} map_flipSigns_statistics (by norm_num) (by norm_num)

example :
    ∫ b, ((knockoffSelection 0 (1 / 2) (statistics b) ∩ {0}).card : ℝ) /
        ((knockoffSelection 0 (1 / 2) (statistics b)).card + (1 / 2 : ℝ)⁻¹) ∂fairCoin ≤
      1 / 2 :=
  integral_card_inter_div_knockoffSelection_zero_le fairCoin
    measurable_statistics {0} map_flipSigns_statistics (by norm_num) (by norm_num)

-- The bound is not attained here: the expected ratio is `(1/2) · 1/(2 + 2) + (1/2) · 0 = 1/8`.
example :
    ∫ b, ((knockoffSelection 0 (1 / 2) (statistics b) ∩ {0}).card : ℝ) /
        ((knockoffSelection 0 (1 / 2) (statistics b)).card + (1 / 2 : ℝ)⁻¹) ∂fairCoin =
      1 / 8 := by
  rw [fairCoin, integral_smul_measure, integral_add_measure Integrable.of_finite
    Integrable.of_finite, integral_dirac, integral_dirac, knockoffSelection_zero_half_true,
    knockoffSelection_zero_half_false]
  norm_num

end MathlibExtTest.Probability.Statistics.MultipleTesting.KnockoffFDR
