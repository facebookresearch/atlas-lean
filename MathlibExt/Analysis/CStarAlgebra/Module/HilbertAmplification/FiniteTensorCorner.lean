/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.FiniteMatrixTensor

/-!
# Actual finite-frame corners of arbitrary raw compact tensors

Extract the original coefficient-valued entries of a raw tensor, then use
the actual finite matrix tensor map. On pure tensors this is the literal
finite rank-one compression of the compact factor. These linear maps are
needed to extend the finite-corner norm computation to every raw tensor;
they use no completed model or norm-comparison certificate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct BigOperators CStarAlgebra

namespace CStarModule.HilbertAmplification

universe uH uA uI

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type uI}
variable (v : ι → H) (A : Type uA) [NonUnitalCStarAlgebra A]

/-- The original tensor matrix coefficients, collected in their actual source matrix. -/
noncomputable def tensorFrameMatrixLinear :
    A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier →ₗ[ℂ] CStarMatrix ι ι A where
  toFun z := CStarMatrix.ofMatrix fun i j => tensorMatrixCoefficient H A (v j) (v i) z
  map_add' z w := by
    apply CStarMatrix.ext
    intro i j
    rw [CStarMatrix.add_apply]
    rw [CStarMatrix.ofMatrix_apply (m := ι) (n := ι) (A := A)
      (M := fun r c => tensorMatrixCoefficient H A (v c) (v r) (z + w)) (i := i)]
    rw [CStarMatrix.ofMatrix_apply (m := ι) (n := ι) (A := A)
      (M := fun r c => tensorMatrixCoefficient H A (v c) (v r) z) (i := i)]
    rw [CStarMatrix.ofMatrix_apply (m := ι) (n := ι) (A := A)
      (M := fun r c => tensorMatrixCoefficient H A (v c) (v r) w) (i := i)]
    exact (tensorMatrixCoefficient H A (v j) (v i)).map_add z w
  map_smul' c z := by
    apply CStarMatrix.ext
    intro i j
    rw [CStarMatrix.smul_apply, RingHom.id_apply]
    rw [CStarMatrix.ofMatrix_apply (m := ι) (n := ι) (A := A)
      (M := fun r d => tensorMatrixCoefficient H A (v d) (v r) (c • z)) (i := i)]
    rw [CStarMatrix.ofMatrix_apply (m := ι) (n := ι) (A := A)
      (M := fun r d => tensorMatrixCoefficient H A (v d) (v r) z) (i := i)]
    exact (tensorMatrixCoefficient H A (v j) (v i)).map_smul c z

/-- Each extracted matrix entry is the original full-H coefficient of the raw tensor. -/
theorem tensorFrameMatrixLinear_apply
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) (i j : ι) :
    tensorFrameMatrixLinear v A z i j = tensorMatrixCoefficient H A (v j) (v i) z := rfl

variable [Fintype ι]

/-- The actual finite-frame raw tensor compression, with its linear structure. -/
noncomputable def finiteTensorCorner :
    A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier →ₗ[ℂ]
      A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
  (finiteMatrixTensorLinear v A).comp (tensorFrameMatrixLinear v A)

/-- The corner is the literal sum of extracted entries tensor original rank-one operators. -/
theorem finiteTensorCorner_apply
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    finiteTensorCorner v A z =
      ∑ i, ∑ j, tensorMatrixCoefficient H A (v j) (v i) z ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j) := rfl

/-- An orthonormal corner is the image of its actual matrix under the constructed star hom. -/
theorem finiteTensorCorner_eq_finiteMatrixTensorHom (hv : Orthonormal ℂ v)
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    finiteTensorCorner v A z = finiteMatrixTensorHom v hv A (tensorFrameMatrixLinear v A z) := rfl

/-- On each pure tensor, the compact factor has its actual finite rank-one compression. -/
theorem finiteTensorCorner_tmul (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    finiteTensorCorner v A (a ⊗ₜ[ℂ] T) =
      a ⊗ₜ[ℂ] (∑ i, ∑ j,
        inner ℂ (v i) ((T : H →L[ℂ] H) (v j)) • hilbertCompactRankOne H (v i) (v j)) := by
  simp only [finiteTensorCorner_apply, tensorMatrixCoefficient_tmul,
    compactOperatorMatrixCoefficient_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]

end CStarModule.HilbertAmplification
