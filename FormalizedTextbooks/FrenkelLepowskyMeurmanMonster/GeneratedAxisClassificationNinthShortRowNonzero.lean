/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortCount

/-! An original pair-mask certificate and the genuine octad nonvanishing theorem give a compact
nonzero predicate for every chronological source row. This predicate retains the actual original
numerator and can be used for later finite family counts. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Candidate nonzero bits for the552 original signed-pair numerators. -/
def generatedNinthShortRowPairNonzeroMask : ℕ :=
  0x780f0f8781e43c03c01e087840f000f00078041e00bc3fffc3ffde1ffe787ff8 +
    2 ^ 256 * 0xf8781e43c03c01e087840f000f00078041e00bc3fffc3ffde1ffe787ff84bfde +
    2 ^ 512 * 0x4bfde780f0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Check the552 original integer pair numerators against their displayed nonzero bits.
private theorem pair_mask_actual : ∀ n : Fin 552,
    generatedNinthShortRowPairNonzeroMask.testBit n.val = true ↔
      generatedFifthFinalPairNumerator (⟨n.val / 276, by omega⟩ : Fin 2)
        (generatedNinthCoordinatePairData (⟨n.val % 276, by omega⟩ : Fin 276)).1
        (generatedNinthCoordinatePairData (⟨n.val % 276, by omega⟩ : Fin 276)).2 ≠ 0 := by
  decide +kernel

/-- The compact nonzero predicate at each original chronological source address. -/
def generatedNinthShortRowNonzero (k : Fin 4136) : Bool :=
  if k.val < 552 then generatedNinthShortRowPairNonzeroMask.testBit k.val else true

/-- The compact predicate equals nonvanishing of the genuine original signed numerator. -/
theorem generatedNinth_short_row_nonzero_actual (k : Fin 4136) :
    generatedNinthShortRowNonzero k = true ↔
      generatedNinthOriginalShortNumerator (generatedNinthShortRowSource k) ≠ 0 := by
  unfold generatedNinthShortRowNonzero
  split_ifs with h
  · have hk : generatedNinthShortRowSource k = Sum.inl
        ((⟨k.val / 276, by omega⟩ : Fin 2), (⟨k.val % 276, by omega⟩ : Fin 276)) := by
      unfold generatedNinthShortRowSource
      split
      · rfl
      · omega
    rw [hk]
    simpa only [generatedNinthOriginalShortNumerator, generatedNinth_coordinate_pair_actual]
      using pair_mask_actual (⟨k.val, h⟩ : Fin 552)
  · have hk : generatedNinthShortRowSource k = Sum.inr
        ((⟨(k.val - 552) / 64, by omega⟩ : Fin 56),
          (⟨(k.val - 552) % 64, by omega⟩ : Fin 64)) := by
      unfold generatedNinthShortRowSource
      split
      · omega
      · rfl
    rw [hk]
    exact ⟨fun _ => generatedNinth_original_octad_numerator_ne_zero _ _, fun _ => rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
