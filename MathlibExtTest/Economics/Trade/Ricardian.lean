/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Trade.Ricardian
import Mathlib.Tactic

/-! Examples and checks for `MathlibExt.Economics.Trade.Ricardian` (Atlas AP01.T01). -/

namespace MathlibExtTest.Economics.Trade.Ricardian

open MathlibExt.Economics.Ricardian

def H : Country where
  a₁ := 1
  a₂ := 2
  L := 10
  a₁_pos := by norm_num
  a₂_pos := by norm_num
  L_pos := by norm_num

def F : Country where
  a₁ := 3
  a₂ := 2
  L := 12
  a₁_pos := by norm_num
  a₂_pos := by norm_num
  L_pos := by norm_num

theorem test_mem : (1:ℝ) ∈ Set.Ioo (autarkyPrice H) (autarkyPrice F) := by
  have hH : autarkyPrice H = (1:ℝ) / 2 := rfl
  have hF : autarkyPrice F = (3:ℝ) / 2 := rfl
  rw [Set.mem_Ioo, hH, hF]
  norm_num

theorem test_gains :
    autarkySet H ⊂ specializeGood1Set H 1 ∧ autarkySet F ⊂ specializeGood2Set F 1 :=
  mutual_gains_of_mem_Ioo H F test_mem

theorem test_boundary : ¬ autarkySet H ⊂ specializeGood1Set H (1/2) := by
  have hH : autarkyPrice H = (1:ℝ) / 2 := rfl
  rw [autarkySet_ssubset_specializeGood1Set_iff H (show (0:ℝ) < 1/2 by norm_num), hH]
  norm_num

end MathlibExtTest.Economics.Trade.Ricardian
