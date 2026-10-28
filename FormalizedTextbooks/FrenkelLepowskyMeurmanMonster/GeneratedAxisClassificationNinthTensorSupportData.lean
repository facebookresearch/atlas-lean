/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpinInteger

/-! Thirteen actual spin labels detect every affine sign character.
Their occurrence in the original ninth tensor requires a separate coordinate certificate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Original spin labels selected for affine sign detection. -/
def generatedNinthTensorSupportLabels : Fin 13 → Fin 4096 :=
  ![0, 3, 4, 9, 16, 32, 40, 68, 128, 256, 513, 1028, 2048]

/-- The affine evaluation matrix has its constant column followed by twelve spin coordinates. -/
def generatedNinthTensorSupportAffine : Matrix (Fin 13) (Fin 13) (ZMod 2) :=
  fun i j => golayBooleanCast ((1 + 2 * (generatedNinthTensorSupportLabels i).val).testBit j.val)

/-- Exact row encodings of the inverse of the affine evaluation matrix. -/
def generatedNinthTensorSupportInverseRows : Fin 13 → ℕ :=
  ![1, 105, 106, 5, 96, 17, 33, 132, 257, 513, 1128, 2052, 4097]

/-- Decode the actual thirteen-dimensional affine inverse. -/
def generatedNinthTensorSupportInverse : Matrix (Fin 13) (Fin 13) (ZMod 2) :=
  fun i j => golayBooleanCast ((generatedNinthTensorSupportInverseRows i).testBit j.val)

/-- The finite inverse is checked by genuine matrix multiplication over the binary field. -/
theorem generatedNinth_tensor_support_inverse :
    generatedNinthTensorSupportInverse * generatedNinthTensorSupportAffine = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
