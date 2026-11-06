/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Norton V transport of the entire eleventh spin factor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhSpinData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SpinSupportData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01InverseSupported

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The entire signed spin factor after the next literal Norton V, including all zeros. -/
def monsterNortonLine01EleventhVSpinVector : NortonUIntegerVector :=
  fun n => if monsterNortonLine01EleventhSpinSupport (monsterNortonBitXor n 1038) then -1 else 0

private theorem xor_cancel (n : Fin 4096) :
    monsterNortonBitXor (monsterNortonBitXor n 1038) 1038 = n := by
  apply Fin.ext
  simp [monsterNortonBitXor, Nat.xor_assoc]

private theorem phase_coefficient (p : Fin 32) :
    nortonUIntegerSign (spinPhase y555NortonVQ (golayLabelCoefficients
      (monsterNortonBitXor (monsterNortonLine01EleventhSpinLabel p) 1038))) *
        monsterNortonLine01EleventhSpinCoefficient p = -1 := by
  revert p
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Transport the concrete actual phase before comparing the sparse packet coordinates.
/-- The sparse signed packet is the actual Norton V spin action with its full central phase. -/
theorem monsterNortonLine01EleventhVSpin_actual :
    nortonUIntegerQ y555NortonVQ monsterNortonLine01EleventhSpinVector =
      monsterNortonLine01EleventhVSpinVector := by
  funext n
  simp only [nortonUIntegerQ, monsterNortonLine01SpinSupport_v_translation,
    ← monsterNortonBitXor_coeff, nortonUIntegerLabel_coeff]
  unfold monsterNortonLine01EleventhSpinVector monsterNortonLine01EleventhVSpinVector
  by_cases hs : monsterNortonLine01EleventhSpinSupport (monsterNortonBitXor n 1038)
  · rw [ite_eq_left hs, ite_eq_left hs]
    have he : monsterNortonLine01EleventhSpinLabel
        (monsterNortonLine01EleventhSpinLookup (monsterNortonBitXor n 1038)) =
          monsterNortonBitXor n 1038 := hs
    have hx := congrArg (fun m => monsterNortonBitXor m 1038) he
    rw [xor_cancel] at hx
    conv_lhs => arg 1; rw [← hx]
    exact phase_coefficient _
  · rw [ite_eq_right hs, ite_eq_right hs, mul_zero]

private theorem translated_input (p : Fin 32) :
    monsterNortonLine01CompactInputSupport
      (monsterNortonBitXor (monsterNortonLine01EleventhSpinLabel p) 1038) := by
  revert p
  decide +kernel

/-- This particular V packet lies entirely in the proved inverse input catalogue. -/
theorem monsterNortonLine01EleventhVSpin_input_zero (n : Fin 4096)
    (hn : ¬ monsterNortonLine01CompactInputSupport n) :
    monsterNortonLine01EleventhVSpinVector n = 0 := by
  have hs : ¬ monsterNortonLine01EleventhSpinSupport (monsterNortonBitXor n 1038) := by
    intro hs
    have he : monsterNortonLine01EleventhSpinLabel
        (monsterNortonLine01EleventhSpinLookup (monsterNortonBitXor n 1038)) =
          monsterNortonBitXor n 1038 := hs
    have h := translated_input (monsterNortonLine01EleventhSpinLookup
      (monsterNortonBitXor n 1038))
    rw [he, xor_cancel] at h
    exact hn h
  exact ite_eq_right hs

/-- The actual inverse image has no coordinates outside the proved output catalogue. -/
theorem monsterNortonLine01EleventhVSpin_inverse_zero (n : Fin 4096)
    (hn : ¬ monsterNortonLine01CompactOutputSupport n) :
    monsterNortonUCompactInverseNumerator monsterNortonLine01EleventhVSpinVector n = 0 := by
  exact monsterNortonLine01CompactInverse_supported _
    monsterNortonLine01EleventhVSpin_input_zero n hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
