/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.NPVIRR
import Mathlib.Tactic.NormNum

/-!
# Tests for NPV and IRR

The project `(-100, 110)` has IRR `1/10`: its NPV at `0` is `10 > 0` and at `1/5` it is not
positive. The project `(-1, 0, 4)` has IRR `1`, and its NPV at `1/2` is `7/9 > 0`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.NPVIRR

open MathlibExt.Economics.Finance

-- Test (1): `c 0 = -100`, `c 1 = 110`, `N = 1`, IRR `1/10`.
private theorem test1_e0 : (if (0:ℕ) = 0 then (-100:ℝ) else (110:ℝ)) = -100 := by simp

private theorem test1_e1 : (if (1:ℕ) = 0 then (-100:ℝ) else (110:ℝ)) = 110 := by
  simp [show (1:ℕ) ≠ 0 from one_ne_zero]

private theorem test1_hnn : ∀ k ∈ Finset.Icc 1 1,
    0 ≤ (fun k => if k = 0 then (-100:ℝ) else (110:ℝ)) k := by
  intro k hk
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
  have hk1 : k = 1 := by omega
  subst hk1
  dsimp only
  rw [test1_e1]
  norm_num

private theorem test1_hpos : ∃ k ∈ Finset.Icc 1 1,
    0 < (fun k => if k = 0 then (-100:ℝ) else (110:ℝ)) k :=
  ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩, by dsimp only; rw [test1_e1]; norm_num⟩

private theorem test1_irr : IsIRR (fun k => if k = 0 then (-100:ℝ) else (110:ℝ)) 1 (1/10 : ℝ) := by
  refine ⟨by norm_num, ?_⟩
  unfold npv presentValue discountFactor
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  dsimp only
  rw [test1_e0, test1_e1]
  norm_num

example : npv (fun k => if k = 0 then (-100:ℝ) else (110:ℝ)) 1 0 = 10 := by
  unfold npv presentValue discountFactor
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  dsimp only
  rw [test1_e0, test1_e1]
  norm_num

example : 0 < npv (fun k => if k = 0 then (-100:ℝ) else (110:ℝ)) 1 0 :=
  (npv_pos_iff_lt_irr test1_hnn test1_hpos test1_irr (by norm_num)).mpr (by norm_num)

example : ¬ 0 < npv (fun k => if k = 0 then (-100:ℝ) else (110:ℝ)) 1 (1/5 : ℝ) :=
  mt (npv_pos_iff_lt_irr test1_hnn test1_hpos test1_irr (by norm_num)).mp (by norm_num)

-- Test (2): `c 0 = -1`, `c 2 = 4`, else `0`, `N = 2`, IRR `1`.
private theorem test2_e0 : (if (0:ℕ) = 0 then (-1:ℝ) else if (0:ℕ) = 2 then (4:ℝ) else 0) = -1 := by
  simp

private theorem test2_e1 : (if (1:ℕ) = 0 then (-1:ℝ) else if (1:ℕ) = 2 then (4:ℝ) else 0) = 0 := by
  simp [show (1:ℕ) ≠ 0 from one_ne_zero, show (1:ℕ) ≠ 2 by norm_num]

private theorem test2_e2 : (if (2:ℕ) = 0 then (-1:ℝ) else if (2:ℕ) = 2 then (4:ℝ) else 0) = 4 := by
  simp [show (2:ℕ) ≠ 0 by norm_num]

private theorem range2_eq : Finset.range 2 = Finset.range (1 + 1) := rfl

private theorem test2_hnn : ∀ k ∈ Finset.Icc 1 2,
    0 ≤ (fun k => if k = 0 then (-1:ℝ) else if k = 2 then (4:ℝ) else 0) k := by
  have c1 : (0:ℝ) ≤ (fun k => if k = 0 then (-1:ℝ) else if k = 2 then (4:ℝ) else 0) 1 := by
    dsimp only
    rw [test2_e1]
  have c2 : (0:ℝ) ≤ (fun k => if k = 0 then (-1:ℝ) else if k = 2 then (4:ℝ) else 0) 2 := by
    dsimp only
    rw [test2_e2]
    norm_num
  intro k hk
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with rfl | rfl
  · exact c1
  · exact c2

private theorem test2_hpos : ∃ k ∈ Finset.Icc 1 2,
    0 < (fun k => if k = 0 then (-1:ℝ) else if k = 2 then (4:ℝ) else 0) k :=
  ⟨2, Finset.mem_Icc.mpr ⟨by norm_num, le_rfl⟩, by dsimp only; rw [test2_e2]; norm_num⟩

private theorem test2_irr : IsIRR (fun k => if k = 0 then (-1:ℝ) else if k = 2 then (4:ℝ) else 0) 2 1 := by
  refine ⟨by norm_num, ?_⟩
  unfold npv presentValue discountFactor
  rw [Finset.sum_range_succ, range2_eq, Finset.sum_range_succ, Finset.sum_range_one]
  dsimp only
  rw [test2_e0, test2_e1, test2_e2]
  norm_num

example : npv (fun k => if k = 0 then (-1:ℝ) else if k = 2 then (4:ℝ) else 0) 2 (1/2 : ℝ) = 7/9 := by
  unfold npv presentValue discountFactor
  rw [Finset.sum_range_succ, range2_eq, Finset.sum_range_succ, Finset.sum_range_one]
  dsimp only
  rw [test2_e0, test2_e1, test2_e2]
  norm_num

example : 0 < npv (fun k => if k = 0 then (-1:ℝ) else if k = 2 then (4:ℝ) else 0) 2 (1/2 : ℝ) :=
  (npv_pos_iff_lt_irr test2_hnn test2_hpos test2_irr (by norm_num)).mpr (by norm_num)

end MathlibExtTest.Economics.Finance.NPVIRR
