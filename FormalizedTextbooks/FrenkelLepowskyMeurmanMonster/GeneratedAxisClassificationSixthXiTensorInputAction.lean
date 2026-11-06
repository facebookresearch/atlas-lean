/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorInputSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiLiteralTensor

/-! Checked input integers speed the original signed Gaussian without changing any term. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original physical column retains all signed C and Gaussian contributions. -/
def generatedSixthXiInputCachedRawTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ a : Fin 4, generatedSixthXiPhysicalWeight i a *
    generatedSixthXiLiteralSpinInteger
      (fun m => generatedSixthXiTensorInput m (generatedSixthXiPhysicalColumn i a)) n

/-- The actual Q correction acts on the complete checked Gaussian numerator. -/
def generatedSixthXiInputCachedTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  nortonUIntegerSign (if (monsterCo1GeometryBinaryMaskDot 12 135 n.val).testBit 0 then
      1 else 0) *
    generatedSixthXiInputCachedRawTensor (generatedSixthSpinLabelXor n 538) i

/-- The checked input cache preserves the complete original tensor operator and all phases. -/
theorem generatedSixth_xi_input_cached_tensor (n : Fin 4096) (i : Fin 24) :
    generatedSixthXiInputCachedTensor n i = generatedSixthXiCachedTensor n i := by
  rw [← generatedSixth_xi_literal_tensor]
  simp only [generatedSixthXiInputCachedTensor, generatedSixthXiInputCachedRawTensor,
    generatedSixthXiLiteralTensor, generatedSixthXiLiteralRawTensor,
    generatedSixth_xi_tensor_input]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
