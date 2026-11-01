/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightTensorBlockFourier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalTensorCircuitData

/-! Each full canonical stage selects its original complete packed row before finite replay. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original signed canonical coefficient read within one complete source row. -/
def generatedRootEightCanonicalTensorStageBlock (s : Fin 5) (i : Fin 24)
    (b : Fin 16) (u : Fin 256) : ℤ :=
  (((generatedRootEightCanonicalTensorStageWords s i b
    ⟨u.val / 16, by omega⟩).shiftRight
      (12 * (u.val % 16)) % 4096 : ℕ) : ℤ) - 2048

/-- The exact fixed-row lookup retains all signed original canonical coordinates. -/
theorem generatedRootEight_canonical_tensor_stage_block (s : Fin 5) (i : Fin 24)
    (b : Fin 16) (u : Fin 256) :
    generatedRootEightCanonicalTensorStageInteger s i
      (generatedNinthLowerSpinTensorBlockIndex b u) =
        generatedRootEightCanonicalTensorStageBlock s i b u := by
  have hb : (b.val * 256 + u.val) / 256 = b.val := by omega
  have hw : (b.val * 256 + u.val) / 16 % 16 = u.val / 16 := by omega
  have hu : (b.val * 256 + u.val) % 16 = u.val % 16 := by omega
  dsimp only [generatedRootEightCanonicalTensorStageInteger,
    generatedRootEightCanonicalTensorStageBlock, generatedNinthLowerSpinTensorBlockIndex]
  simp only [hb, hw, hu]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
