/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiWordCacheSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSparseFastTensor

/-! Every original Gaussian term and preferred correction remains in the complete cached tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Four original physical columns with both complete signed C caches and all Gaussian terms. -/
def generatedSixthXiCachedRawTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ a : Fin 4, generatedSixthXiPhysicalWeight i a *
    generatedSixthXiCachedSpinInteger
      (fun m => generatedSixthTensorFastExecutable m (generatedSixthXiPhysicalColumn i a)) n

/-- The unchanged original Q correction acts on the complete cached tensor. -/
def generatedSixthXiCachedTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  nortonUIntegerSign (if (monsterCo1GeometryBinaryMaskDot 12 135 n.val).testBit 0 then
      1 else 0) *
    generatedSixthXiCachedRawTensor (generatedSixthSpinLabelXor n 538) i

/-- The complete cached tensor equals the original signed fast numerator at every actual address. -/
theorem generatedSixth_xi_cached_tensor (n : Fin 4096) (i : Fin 24) :
    generatedSixthXiCachedTensor n i = generatedSixthXiSparseFastTensor n i := by
  simp only [generatedSixthXiCachedTensor, generatedSixthXiCachedRawTensor,
    generatedSixth_xi_cached_spin_integer, generatedSixthXiSparseFastTensor,
    generatedSixthXiSparseFastRawTensor]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
