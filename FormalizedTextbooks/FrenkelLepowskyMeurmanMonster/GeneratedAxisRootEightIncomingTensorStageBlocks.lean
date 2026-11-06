/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightTensorBlockFourier

/-! Each original incoming packed stage selects its complete fixed row before finite replay. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original signed incoming coefficient read within one complete source row. -/
def generatedRootEightIncomingTensorStageBlock (s : Fin 5) (r : Fin 8)
    (b : Fin 16) (u : Fin 256) : ℤ :=
  (((generatedRootEightIncomingTensorStageWords s r
    ⟨b.val / 2, by omega⟩ ⟨8 * (b.val % 2) + u.val / 32, by omega⟩).shiftRight
      (6 * (u.val % 32)) % 64 : ℕ) : ℤ) - 16

/-- The exact block lookup retains every original signed slot and its complete source row. -/
theorem generatedRootEight_incoming_tensor_stage_block (s : Fin 5) (r : Fin 8)
    (b : Fin 16) (u : Fin 256) :
    generatedRootEightIncomingTensorStageInteger s r
      (generatedNinthLowerSpinTensorBlockIndex b u) =
        generatedRootEightIncomingTensorStageBlock s r b u := by
  have hb : (b.val * 256 + u.val) / 512 = b.val / 2 := by omega
  have hw : (b.val * 256 + u.val) / 32 % 16 =
      8 * (b.val % 2) + u.val / 32 := by omega
  have hu : (b.val * 256 + u.val) % 32 = u.val % 32 := by omega
  dsimp only [generatedRootEightIncomingTensorStageInteger,
    generatedRootEightIncomingTensorStageBlock, generatedNinthLowerSpinTensorBlockIndex]
  simp only [hb, hw, hu]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
