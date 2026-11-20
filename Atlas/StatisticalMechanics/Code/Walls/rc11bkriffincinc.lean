/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































import Code.Walls.rc10core

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace







open Classical in








theorem rc11_deficitIncInc_of_bkr (h : rc10_BKRSetFamily) : rc10_DeficitBridgeIncInc := by
  intro n A B hA hB
  
  rw [rc5_deficit, rc10_card_box_eq A B hA hB, rc10_card_reflInter_eq A B]
  
  have hbkr := h n (eventFamily A) (eventFamily B) (rc10_isUpperSet_eventFamily hA)
    (rc10_isUpperSet_eventFamily hB)
  have hcast : (#(rc10_boxSupp (eventFamily A) (eventFamily B)) : ℤ)
      ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by exact_mod_cast hbkr
  omega

open Classical in










theorem rc11_bkr_of_deficitIncInc (h : rc10_DeficitBridgeIncInc) : rc10_BKRSetFamily := by
  intro n 𝒜 ℬ h𝒜 hℬ
  set A := familyEvent 𝒜 with hA
  set B := familyEvent ℬ with hB
  
  have hAinc : IsIncreasing A := by
    intro ω ω' hωω' hω
    simp only [hA, mem_familyEvent] at hω ⊢
    exact h𝒜 (Finset.coe_subset.mpr (cfgSupport_subset_of_le hωω')) hω
  have hBinc : IsIncreasing B := by
    intro ω ω' hωω' hω
    simp only [hB, mem_familyEvent] at hω ⊢
    exact hℬ (Finset.coe_subset.mpr (cfgSupport_subset_of_le hωω')) hω
  
  have hdef := h n A B hAinc hBinc
  
  have hEA : eventFamily A = 𝒜 := rc10_eventFamily_familyEvent 𝒜
  have hEB : eventFamily B = ℬ := rc10_eventFamily_familyEvent ℬ
  
  rw [rc5_deficit, rc10_card_box_eq A B hAinc hBinc, rc10_card_reflInter_eq A B, hEA, hEB] at hdef
  have hcast : (#(rc10_boxSupp 𝒜 ℬ) : ℤ) ≤ #(rc10_reflInter 𝒜 ℬ) := by linarith [hdef]
  exact_mod_cast hcast






theorem rc11_bkr_iff_deficitIncInc : rc10_BKRSetFamily ↔ rc10_DeficitBridgeIncInc :=
  ⟨rc11_deficitIncInc_of_bkr, rc11_bkr_of_deficitIncInc⟩







open Classical in



theorem rc11_deficit_incInc_one (A B : Set (ConfigSpace (Fin 1)))
    (_ : IsIncreasing A) (_ : IsIncreasing B) : rc5_deficit A B ≤ 0 :=
  rc9_deficit_one A B

end StatMech.Walls
