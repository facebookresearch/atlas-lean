/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Code.FK.PcUpperUncond
import Code.BeffaraDC.SelfDualValue

namespace StatMech

namespace BeffaraDC

open StatMech.FK












theorem mem_subcritical_of_lt_selfDualPoint {q : ℝ} (hq : 1 ≤ q) {p : ℝ}
    (hp0 : 0 < p) (hp_sd : p < selfDualPoint q)
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < selfDualPoint q → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0) :
    p ∈ fkSubcriticalSet 2 q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  
  have hsd1 : selfDualPoint q < 1 := (selfDualPoint_mem_Ioo hq0).2
  have hp1 : p < 1 := hp_sd.trans hsd1
  refine ⟨hp0, hp1, hq0, ?_⟩
  exact hNoPercBelow p hp0 hp1 hp_sd






theorem selfDualPoint_subcritical_le_fkPc {q : ℝ} (hq : 1 ≤ q)
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < selfDualPoint q → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0) :
    selfDualPoint q ≤ fkPc 2 q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  
  refine le_of_forall_lt_imp_le_of_dense (fun p hp => ?_)
  
  rcases le_or_gt p 0 with hp0 | hp0
  · 
    exact hp0.trans (fkPc_pos (by norm_num) hq).le
  · 
    have hmem : p ∈ fkSubcriticalSet 2 q :=
      mem_subcritical_of_lt_selfDualPoint hq hp0 hp hNoPercBelow
    exact le_csSup (fkSubcriticalSet_bddAbove' 2 q) hmem













theorem fkPc_le_selfDualPoint {q : ℝ} (hq : 1 ≤ q)
    (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      selfDualPoint q < r → 0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q)) :
    fkPc 2 q ≤ selfDualPoint q := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  
  refine csSup_le (fkSubcriticalSet_nonempty hq) (fun r hr => ?_)
  
  obtain ⟨hr0, hr1, _hq0, hzero⟩ := hr
  by_contra hcon
  
  push Not at hcon
  have hθ : 0 < fkTheta 2 hr0 hr1 hq0 (q := q) := hPercAbove r hr0 hr1 hcon
  exact (not_mem_fkSubcriticalSet_of_fkTheta_pos hr0 hr1 hq0 hθ)
    ⟨hr0, hr1, hq0, hzero⟩













theorem fkPc_eq_selfDualPoint {q : ℝ} (hq : 1 ≤ q)
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < selfDualPoint q → fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0)
    (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      selfDualPoint q < r → 0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q)) :
    fkPc 2 q = selfDualPoint q :=
  le_antisymm (fkPc_le_selfDualPoint hq hPercAbove)
    (selfDualPoint_subcritical_le_fkPc hq hNoPercBelow)







theorem beffaraDC_critical_point {q : ℝ} (hq : 1 ≤ q)
    (hNoPercBelow : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      r < Real.sqrt q / (1 + Real.sqrt q) →
        fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q) = 0)
    (hPercAbove : ∀ (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1),
      Real.sqrt q / (1 + Real.sqrt q) < r →
        0 < fkTheta 2 hr0 hr1 (zero_lt_one.trans_le hq) (q := q)) :
    fkPc 2 q = Real.sqrt q / (1 + Real.sqrt q) := by
  
  have hval : selfDualPoint q = Real.sqrt q / (1 + Real.sqrt q) := rfl
  rw [← hval] at hNoPercBelow hPercAbove ⊢
  exact fkPc_eq_selfDualPoint hq hNoPercBelow hPercAbove

end BeffaraDC

end StatMech
