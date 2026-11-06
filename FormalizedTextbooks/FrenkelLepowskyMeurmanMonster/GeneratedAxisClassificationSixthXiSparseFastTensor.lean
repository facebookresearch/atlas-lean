/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthTensorFastExecutable
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSparseTensor

/-! Caching only a proved weight sign retains every original Gaussian term and preferred
correction. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original signed Gaussian term remains in each of the four physical columns. -/
def generatedSixthXiSparseFastRawTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ a : Fin 4, generatedSixthXiPhysicalWeight i a *
    generatedSixthXiFastSpinInteger
      (fun m => generatedSixthTensorFastExecutable m (generatedSixthXiPhysicalColumn i a)) n

/-- The unchanged actual Q correction acts on the complete faster tensor numerator. -/
def generatedSixthXiSparseFastTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  nortonUIntegerSign (if (monsterCo1GeometryBinaryMaskDot 12 135 n.val).testBit 0 then
      1 else 0) *
    generatedSixthXiSparseFastRawTensor (generatedSixthSpinLabelXor n 538) i

/-- The complete original corrected-Xi integer tensor is unchanged at every address. -/
theorem generatedSixth_xi_sparse_fast_numerator (n : Fin 4096) (i : Fin 24) :
    generatedSixthXiSparseFastTensor n i = generatedSixthXiSparseTensor n i := by
  simp only [generatedSixthXiSparseFastTensor, generatedSixthXiSparseFastRawTensor,
    generatedSixth_tensor_fast_executable, generatedSixthXiSparseTensor,
    generatedSixthXiSparseRawTensor]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
