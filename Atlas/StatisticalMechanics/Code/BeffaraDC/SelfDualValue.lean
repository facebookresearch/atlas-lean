/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































import Mathlib

open Real

namespace StatMech

namespace BeffaraDC






noncomputable def dualParam (p q : ℝ) : ℝ := (1 - p) * q / ((1 - p) * q + p)





noncomputable def selfDualPoint (q : ℝ) : ℝ := Real.sqrt q / (1 + Real.sqrt q)





theorem dualDen_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < (1 - p) * q + p := by
  have : 0 < (1 - p) * q := mul_pos (by linarith) hq
  linarith


theorem dualParam_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < dualParam p q := by
  unfold dualParam
  exact div_pos (mul_pos (by linarith) hq) (dualDen_pos hp hp1 hq)


theorem dualParam_lt_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    dualParam p q < 1 := by
  unfold dualParam
  rw [div_lt_one (dualDen_pos hp hp1 hq)]
  linarith


theorem dualParam_mem_Ioo {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    dualParam p q ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨dualParam_pos hp hp1 hq, dualParam_lt_one hp hp1 hq⟩






theorem dualParam_product_eq {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (dualParam p q) * p / ((1 - dualParam p q) * (1 - p)) = q := by
  have hden := dualDen_pos hp hp1 hq
  have hdenne : ((1 - p) * q + p) ≠ 0 := ne_of_gt hden
  have hpne : p ≠ 0 := ne_of_gt hp
  have h1pne : (1 - p) ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have h1md : 1 - dualParam p q = p / ((1 - p) * q + p) := by
    unfold dualParam; field_simp; ring
  rw [h1md]
  unfold dualParam
  rw [div_eq_iff (mul_ne_zero (div_ne_zero hpne hdenne) h1pne)]
  field_simp





theorem dualParam_fixed_iff {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    dualParam p q = p ↔ p ^ 2 = q * (1 - p) ^ 2 := by
  have hden := dualDen_pos hp hp1 hq
  unfold dualParam
  rw [div_eq_iff (ne_of_gt hden)]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]


theorem selfDualPoint_mem_Ioo {q : ℝ} (hq : 0 < q) :
    selfDualPoint q ∈ Set.Ioo (0 : ℝ) 1 := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  refine ⟨by unfold selfDualPoint; positivity, ?_⟩
  unfold selfDualPoint
  rw [div_lt_one (by positivity)]
  linarith


theorem selfDualPoint_sq {q : ℝ} (hq : 0 < q) :
    (selfDualPoint q) ^ 2 = q * (1 - selfDualPoint q) ^ 2 := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  set s := Real.sqrt q with hsdef
  have h1s : (0 : ℝ) < 1 + s := by linarith
  unfold selfDualPoint
  rw [← hsdef, ← hsq]
  field_simp
  ring




theorem selfDualPoint_is_fixed {q : ℝ} (hq : 0 < q) :
    dualParam (selfDualPoint q) q = selfDualPoint q := by
  obtain ⟨hp0, hp1⟩ := selfDualPoint_mem_Ioo hq
  rw [dualParam_fixed_iff hp0 hp1 hq]
  exact selfDualPoint_sq hq





theorem selfDualPoint_unique {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hfix : dualParam p q = p) : p = selfDualPoint q := by
  have heq : p ^ 2 = q * (1 - p) ^ 2 := (dualParam_fixed_iff hp hp1 hq).mp hfix
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  set s := Real.sqrt q with hsdef
  have hpos : 0 < s * (1 - p) := mul_pos hs (by linarith)
  
  have hpeq : p = s * (1 - p) := by
    nlinarith [heq, hsq, hpos, hp, sq_nonneg (p - s * (1 - p)),
      sq_nonneg (p + s * (1 - p))]
  
  have h1s : (0 : ℝ) < 1 + s := by linarith
  rw [selfDualPoint, ← hsdef, eq_div_iff (ne_of_gt h1s)]
  nlinarith [hpeq]

end BeffaraDC

end StatMech
