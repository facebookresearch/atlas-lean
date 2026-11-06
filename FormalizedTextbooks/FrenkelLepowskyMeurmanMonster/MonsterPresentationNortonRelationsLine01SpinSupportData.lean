/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite exact spin-label support certificates for the actual first-line word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactBitwiseLabels

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual 128-label output support after Norton v translation. -/
def monsterNortonLine01SpinSupport (n : Fin 4096) : Prop :=
  monsterNortonLine01CompactOutputSupport (monsterNortonBitXor n 1038)

instance (n : Fin 4096) : Decidable (monsterNortonLine01SpinSupport n) :=
  inferInstanceAs (Decidable (monsterNortonLine01CompactOutputSupport _))

/-- The genuine Norton v spin translation is the exact source label 1038. -/
theorem monsterNortonLine01SpinSupport_v_translation :
    spinTranslation y555NortonVQ = golayLabelCoefficients 1038 := by
  decide +kernel

/-- Both low/high representatives have exactly the same membership in the reached spin support. -/
theorem monsterNortonLine01SpinSupport_low_high (n : Fin 4096) :
    (monsterNortonLine01SpinSupport n ↔ monsterNortonLine01SpinSupport
      ⟨n.val % 2048, by omega⟩) ∧
    (monsterNortonLine01SpinSupport n ↔ monsterNortonLine01SpinSupport
      ⟨n.val % 2048 + 2048, by omega⟩) := by
  revert n
  decide +kernel

/-- Every reached odd-short source code lies in both low/high halves of the tensor spin support. -/
theorem monsterNortonLine01OddSource_spinSupport (a : Fin 64) (k : Fin 16)
    (h : monsterNortonLine01ShortInverseIsOctad a = false) :
    monsterNortonLine01SpinSupport
      ⟨(monsterNortonLine01ShortInverseOddCode a k).val, by omega⟩ ∧
    monsterNortonLine01SpinSupport
      ⟨(monsterNortonLine01ShortInverseOddCode a k).val + 2048, by omega⟩ := by
  revert a k h
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
