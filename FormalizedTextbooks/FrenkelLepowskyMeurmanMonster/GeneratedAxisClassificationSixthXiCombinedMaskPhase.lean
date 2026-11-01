/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFastMaskPhase

/-! Combining the two genuine cocycle sums retains the complete original scalar phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Selected central and cocycle phases add in their literal characteristic-two coordinates. -/
theorem generatedSixth_Q_selected_phase_add (c d : Fin 24 → ZMod 2)
    (p q : Fin 24 → Fin 24 → ZMod 2) (v : Fin 24 → ZMod 2)
    (l : List (Fin 24)) :
    generatedSixthQSelectedPhase (fun i => c i + d i) (fun i j => p i j + q i j) v l =
      generatedSixthQSelectedPhase c p v l + generatedSixthQSelectedPhase d q v l := by
  induction l with
  | nil => simp [generatedSixthQSelectedPhase]
  | cons i l ih =>
    have hs : (l.map (fun j => if v j = 0 then 0 else p i j + q i j)).sum =
        (l.map (fun j => if v j = 0 then 0 else p i j)).sum +
        (l.map (fun j => if v j = 0 then 0 else q i j)).sum := by
      rw [← List.sum_map_add]
      apply congrArg List.sum
      apply List.map_congr_left
      intro j _
      split <;> simp_all
    by_cases hi : v i = 0
    · simp [generatedSixthQSelectedPhase, hi, ih]
    · simp only [generatedSixthQSelectedPhase, hi, ite_false, ih, hs]
      ring

/-- The row XOR includes the original input cocycle and the full image cocycle. -/
def generatedSixthXiCombinedPairRows (i : Fin 24) : ℕ :=
  Nat.xor (generatedSixthXiInputPairRows i) (generatedSixthXiCoordinatePairMasks i)

/-- A single selected sum retains all genuine central bits and both ordered cocycles. -/
def generatedSixthXiCombinedMaskPhase (n : ℕ) : ZMod 2 :=
  generatedSixthXiMaskParity (generatedSixthXiSelectedMaskPhase
    generatedSixthXiCoordinateCentralMask generatedSixthXiCombinedPairRows n (List.finRange 24))

/-- The combined scalar evaluator is exactly the original complete Xi phase. -/
theorem generatedSixth_xi_combined_mask_phase (n : ℕ) :
    generatedSixthXiCombinedMaskPhase n = generatedSixthXiFastMaskPhase n := by
  have hp (i j : Fin 24) :
      (if (generatedSixthXiCombinedPairRows i).testBit j.val then (1 : ZMod 2) else 0) =
        (if (generatedSixthXiInputPairRows i).testBit j.val then 1 else 0) +
        (if (generatedSixthXiCoordinatePairMasks i).testBit j.val then 1 else 0) :=
    congrFun (monsterCo1GeometryBinaryMaskDecode_xor (n := 24)
      (generatedSixthXiInputPairRows i) (generatedSixthXiCoordinatePairMasks i)) j
  rw [generatedSixthXiCombinedMaskPhase, generatedSixthXiFastMaskPhase,
    generatedSixth_xi_mask_parity_xor, generatedSixth_xi_selected_mask_phase,
    generatedSixth_xi_selected_mask_phase, generatedSixth_xi_selected_mask_phase]
  simp_rw [hp]
  have h := generatedSixth_Q_selected_phase_add (fun _ => 0)
    (fun i => if generatedSixthXiCoordinateCentralMask.testBit i.val then 1 else 0)
    (fun i j => if (generatedSixthXiInputPairRows i).testBit j.val then 1 else 0)
    (fun i j => if (generatedSixthXiCoordinatePairMasks i).testBit j.val then 1 else 0)
    (monsterCo1GeometryBinaryMaskDecode n) (List.finRange 24)
  simpa using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
