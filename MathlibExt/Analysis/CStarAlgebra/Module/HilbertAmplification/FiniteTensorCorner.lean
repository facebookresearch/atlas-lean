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
# Finite-frame compression of compact tensors

For a complex Hilbert space `H`, nonunital C-star algebra `A` and indexed family `v : I → H`, a
tensor `z ∈ A ⊗_ℂ K(H)` has matrix entries `C_v(z)_(i,j) = tensorMatrixCoefficient H A (v j) (v
i) z`. When `I` is finite, define its corner by `P_v z = ∑ i,j, C_v(z)_(i,j) ⊗ θ_(v i,v j)`.

On a pure tensor `a⊗T`, this is `a ⊗ (∑ i,j, ⟪v i,T(v j)⟫_ℂ • θ_(v i,v j))`. For orthonormal
`v`, it factors through the finite-frame matrix star homomorphism. The matrix-entry map itself
permits arbitrary index types.
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

/-- **Matrix entries of an algebraic compact tensor.** For an indexed family `v : I → H`, the
complex-linear map `C_v` has entries `C_v(z)_(i,j) = tensorMatrixCoefficient H A (v j) (v i)
z`; finiteness of `I` is not required for this map. -/
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

/-- **Entry formula for the frame matrix.** `tensorFrameMatrixLinear v A z i j =
tensorMatrixCoefficient H A (v j) (v i) z`. -/
theorem tensorFrameMatrixLinear_apply
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) (i j : ι) :
    tensorFrameMatrixLinear v A z i j = tensorMatrixCoefficient H A (v j) (v i) z := rfl

variable [Fintype ι]

/-- **Finite-frame tensor corner.** For a finite family `v`, define the complex-linear corner `P_v
z = ∑ i,j, C_v(z)_(i,j) ⊗ θ_(v i,v j)` in `A ⊗_ℂ K(H)`. -/
noncomputable def finiteTensorCorner :
    A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier →ₗ[ℂ]
      A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
  (finiteMatrixTensorLinear v A).comp (tensorFrameMatrixLinear v A)

/-- **Formula for the tensor corner.** `finiteTensorCorner v A z` is the sum of
`tensorMatrixCoefficient H A (v j) (v i) z ⊗ θ_(v i,v j)` over the finite frame. -/
theorem finiteTensorCorner_apply
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    finiteTensorCorner v A z =
      ∑ i, ∑ j, tensorMatrixCoefficient H A (v j) (v i) z ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j) := rfl

/-- **Factorization through an orthonormal matrix frame.** For orthonormal `v`,
`finiteTensorCorner v A z = finiteMatrixTensorHom v hv A (tensorFrameMatrixLinear v A z)`. -/
theorem finiteTensorCorner_eq_finiteMatrixTensorHom (hv : Orthonormal ℂ v)
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    finiteTensorCorner v A z = finiteMatrixTensorHom v hv A (tensorFrameMatrixLinear v A z) := rfl

/-- **Finite corner of a pure compact tensor.** `P_v(a⊗T) = a ⊗ (∑ i,j, inner ℂ (v i) (T (v j)) •
θ_(v i,v j))` for a finite family `v`. -/
theorem finiteTensorCorner_tmul (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    finiteTensorCorner v A (a ⊗ₜ[ℂ] T) =
      a ⊗ₜ[ℂ] (∑ i, ∑ j,
        inner ℂ (v i) ((T : H →L[ℂ] H) (v j)) • hilbertCompactRankOne H (v i) (v j)) := by
  simp only [finiteTensorCorner_apply, tensorMatrixCoefficient_tmul,
    compactOperatorMatrixCoefficient_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]

end CStarModule.HilbertAmplification
