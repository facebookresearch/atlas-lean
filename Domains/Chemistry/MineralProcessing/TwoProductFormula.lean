/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Ring

/-!
# Two-product mass balances

Conservation of total mass and of one component determines the concentrate yield from
three assays when the product grades differ. The recovery divides the component flow
in the concentrate by that in the feed.
-/

namespace Domains.Chemistry.MineralProcessing.TwoProductFormula

/-- The grade `f` is between the concentrate grade `c` and the tailings grade `t`, since
it is a mass-weighted average. If the product grades differ, the balances determine
concentrate yield; they also determine recovery when the feed grade is positive. If the
product grades coincide, all three grades agree and every nonnegative split of the feed
satisfies both balances.

The interval hypotheses for grades express their meaning as mass fractions. The mass
and component balances are those of University of Alaska Fairbanks, *AMIT 135: Mill
Operations*, Lesson 2, “Circuit Mass Balancing.” -/
public theorem two_product_formula (F C T f c t : ℝ) (hF : 0 < F) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (_hf : 0 ≤ f ∧ f ≤ 1) (_hc : 0 ≤ c ∧ c ≤ 1) (_ht : 0 ≤ t ∧ t ≤ 1)
    (hmass : F = C + T) (hcomponent : F * f = C * c + T * t) :
    min c t ≤ f ∧ f ≤ max c t ∧
    (c ≠ t → C / F = (f - t) / (c - t) ∧
      (0 < f → C * c / (F * f) = c * (f - t) / (f * (c - t)))) ∧
    (c = t → f = c ∧ f = t ∧ ∀ x : ℝ, 0 ≤ x → x ≤ F →
      0 ≤ F - x ∧ F = x + (F - x) ∧ F * f = x * c + (F - x) * t) := by
  have hlo : min c t ≤ f := by
    apply (mul_le_mul_iff_of_pos_left hF).mp
    rw [hcomponent, hmass, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hT)
  have hhi : f ≤ max c t := by
    apply (mul_le_mul_iff_of_pos_left hF).mp
    rw [hcomponent, hmass, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hC)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hT)
  refine ⟨hlo, hhi, ?_, ?_⟩
  · intro hct
    have hbalance : F * (f - t) = C * (c - t) := by
      calc
        F * (f - t) = F * f - F * t := mul_sub _ _ _
        _ = C * (c - t) := by
          rw [hcomponent, hmass]
          ring
    have hyield : C / F = (f - t) / (c - t) := by
      apply (div_eq_div_iff (ne_of_gt hF) (sub_ne_zero.mpr hct)).2
      calc
        C * (c - t) = F * (f - t) := hbalance.symm
        _ = (f - t) * F := mul_comm _ _
    refine ⟨hyield, ?_⟩
    intro _hf_pos
    calc
      C * c / (F * f) = C / F * (c / f) := (div_mul_div_comm _ _ _ _).symm
      _ = c * (f - t) / (f * (c - t)) := by
        rw [hyield, div_mul_div_comm, mul_comm (f - t) c, mul_comm (c - t) f]
  · intro hct
    have hfc : f = c := le_antisymm (by simpa [← hct] using hhi) (by simpa [← hct] using hlo)
    refine ⟨hfc, hfc.trans hct, ?_⟩
    intro x _hx0 hxF
    refine ⟨sub_nonneg.mpr hxF, by ring, ?_⟩
    rw [hfc, ← hct]
    ring

end Domains.Chemistry.MineralProcessing.TwoProductFormula
