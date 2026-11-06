/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPhysicalSupport

/-! An exact four-column evaluator retains the complete original conjugated-Xi tensor action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Four physical columns, each retaining every original signed Gaussian spin term. -/
def generatedSixthXiSparseRawTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ a : Fin 4, generatedSixthXiPhysicalWeight i a *
    generatedSixthXiFastSpinInteger
      (fun m => generatedSixthTensorExecutable m (generatedSixthXiPhysicalColumn i a)) n

/-- The actual preferred Q correction acts on the complete four-column numerator. -/
def generatedSixthXiSparseTensor (n : Fin 4096) (i : Fin 24) : ℤ :=
  nortonUIntegerSign (if (monsterCo1GeometryBinaryMaskDot 12 135 n.val).testBit 0 then
      1 else 0) *
    generatedSixthXiSparseRawTensor (generatedSixthSpinLabelXor n 538) i

/-- Four physical columns equal all twenty-four original columns for every spin address. -/
theorem generatedSixth_xi_sparse_raw (n : Fin 4096) (i : Fin 24) :
    generatedSixthXiSparseRawTensor n i = generatedSixthXiFastRawTensor n i := by
  exact (generatedSixth_xi_physical_sum i
    (fun j => generatedSixthXiFastSpinInteger (fun m => generatedSixthTensorExecutable m j) n)).symm

/-- The exact sparse evaluator is the complete original preferred signed tensor numerator. -/
theorem generatedSixth_xi_sparse_numerator (n : Fin 4096) (i : Fin 24) :
    generatedSixthXiSparseTensor n i = generatedSixthXiTensorInteger n i := by
  rw [generatedSixthXiSparseTensor, generatedSixth_xi_sparse_raw]
  exact generatedSixth_xi_fast_tensor_numerator n i

/-- The unmodified actual corrected-Xi tensor action has the sparse integer evaluator. -/
theorem generatedSixth_xi_sparse_tensor (n : Fin 4096) (i : Fin 24) :
    localTensorRepresentation (generatedSixthCorrectedGenerator 4)
      (griessConwayEncode generatedSixthAxis).2.2 (golayLabelCoefficients n) i =
      (generatedSixthXiSparseTensor n i : ℝ) / (512 * Real.sqrt 2) := by
  rw [generatedSixth_xi_sparse_numerator]
  exact generatedSixth_xi_corrected_tensor_integer n i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
