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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.MatrixCoefficients
public import MathlibExt.Algebra.Star.StarAlgHom
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Finite matrix frames in algebraic compact tensors

For a complex Hilbert space `H`, nonunital C-star algebra `A` and finite family `v : I → H`,
define `Φ_v(M) = ∑ i, ∑ j, M i j ⊗ θ_(v i,v j)` in `A ⊗_ℂ K(H)`. This is complex-linear for
every finite family.

If `v` is orthonormal, its rank-one operators obey the matrix-unit laws, so `Φ_v` is a nonunital
star-algebra homomorphism. The tensor coefficient at input `v j` and test vector `v i` recovers
`M i j`, making the map injective. An empty finite index type is allowed.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators CStarAlgebra TensorProduct

namespace CStarModule.HilbertAmplification

universe uH uA uI

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type uI} [Fintype ι]
variable (v : ι → H) (hv : Orthonormal ℂ v)

open scoped Classical in
omit [Fintype ι] in
include hv in
/-- **Matrix-unit multiplication for an orthonormal frame.** If `v : I → H` is orthonormal, `θ_(v
i,v j) θ_(v k,v l)` is `θ_(v i,v l)` when `j = k` and zero otherwise. -/
theorem hilbertCompactRankOne_frame_mul (i j k l : ι) :
    hilbertCompactRankOne H (v i) (v j) * hilbertCompactRankOne H (v k) (v l) =
      if j = k then hilbertCompactRankOne H (v i) (v l) else 0 := by
  rw [hilbertCompactRankOne_mul, (orthonormal_iff_ite.mp hv) j k]
  split_ifs <;> simp only [one_smul, zero_smul]

variable (A : Type uA) [NonUnitalCStarAlgebra A]

/-- **Finite matrix-entry tensor map.** For a finite family `v : I → H`, the complex-linear map
from `CStarMatrix I I A` to `A ⊗_ℂ K(H)` sends `M` to `∑ i, ∑ j, M i j ⊗ θ_(v i,v j)`. -/
noncomputable def finiteMatrixTensorLinear :
    CStarMatrix ι ι A →ₗ[ℂ] A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier where
  toFun M := ∑ i, ∑ j, M i j ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j)
  map_add' M N := by
    simp only [CStarMatrix.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [RingHom.id_apply, CStarMatrix.smul_apply, Finset.smul_sum,
      TensorProduct.smul_tmul']

/-- **Formula for the finite matrix tensor map.** `finiteMatrixTensorLinear v A M = ∑ i, ∑ j, M i
j ⊗ hilbertCompactRankOne H (v i) (v j)`. -/
theorem finiteMatrixTensorLinear_apply (M : CStarMatrix ι ι A) :
    finiteMatrixTensorLinear v A M =
      ∑ i, ∑ j, M i j ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j) := rfl

open scoped Classical in
omit [Fintype ι] in
include hv in
/-- **Product of elementary frame tensors.** For an orthonormal frame, `(a⊗θ_(v i,v j)) (b⊗θ_(v
k,v l))` equals `(a*b)⊗θ_(v i,v l)` when `j=k` and zero otherwise. -/
theorem finiteMatrixTensor_summand_mul (a b : A) (i j k l : ι) :
    (a ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j)) *
        (b ⊗ₜ[ℂ] hilbertCompactRankOne H (v k) (v l)) =
      if j = k then (a * b) ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v l) else 0 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, hilbertCompactRankOne_frame_mul v hv]
  split_ifs <;> simp only [TensorProduct.tmul_zero]

include hv in
/-- **Multiplication of finite matrix tensors.** For an orthonormal frame, `Φ_v(M*N) =
Φ_v(M)*Φ_v(N)`. -/
theorem finiteMatrixTensorLinear_mul (M N : CStarMatrix ι ι A) :
    finiteMatrixTensorLinear v A (M * N) =
      finiteMatrixTensorLinear v A M * finiteMatrixTensorLinear v A N := by
  classical
  symm
  change (∑ i, ∑ j, M i j ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j)) *
      (∑ k, ∑ l, N k l ⊗ₜ[ℂ] hilbertCompactRankOne H (v k) (v l)) = _
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        (M i j ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j)) *
          (N k l ⊗ₜ[ℂ] hilbertCompactRankOne H (v k) (v l)) := by
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        if j = k then (M i j * N k l) ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v l) else 0 := by
      simp only [finiteMatrixTensor_summand_mul v hv A]
    _ = ∑ i, ∑ j, ∑ l, ∑ k,
        if j = k then (M i j * N k l) ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v l) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ l, (M i j * N j l) ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v l) := by
      simp
    _ = ∑ i, ∑ l, ∑ j, (M i j * N j l) ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v l) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = finiteMatrixTensorLinear v A (M * N) := by
      simp only [finiteMatrixTensorLinear_apply, CStarMatrix.mul_apply, TensorProduct.sum_tmul]

/-- **Adjoints of finite matrix tensors.**
For an orthonormal frame, `Φ_v(star M) = star (Φ_v M)`. -/
theorem finiteMatrixTensorLinear_star (M : CStarMatrix ι ι A) :
    finiteMatrixTensorLinear v A (star M) = star (finiteMatrixTensorLinear v A M) := by
  simp only [finiteMatrixTensorLinear_apply, CStarMatrix.star_apply,
    star_sum, TensorProduct.star_tmul, hilbertCompactRankOne_star]
  exact Finset.sum_comm

include hv in
/-- **Recovery of finite matrix entries.** For an orthonormal frame, `tensorMatrixCoefficient H A
(v j) (v i) (finiteMatrixTensorLinear v A M) = M i j`. -/
theorem tensorMatrixCoefficient_finiteMatrixTensor (M : CStarMatrix ι ι A) (i j : ι) :
    tensorMatrixCoefficient H A (v j) (v i) (finiteMatrixTensorLinear v A M) = M i j := by
  classical
  have hi := orthonormal_iff_ite.mp hv
  simp only [finiteMatrixTensorLinear_apply, map_sum, tensorMatrixCoefficient_tmul,
    compactOperatorMatrixCoefficient_apply, hilbertCompactRankOne_coe,
    InnerProductSpace.rankOne_apply, inner_smul_right, hi]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
    ite_smul, one_smul, zero_smul]
  simp [eq_comm]

include hv in
/-- **Injectivity of the finite frame tensor map.** For an orthonormal finite family,
`finiteMatrixTensorLinear v A` is injective; this also holds for the empty frame. -/
theorem finiteMatrixTensorLinear_injective : Function.Injective (finiteMatrixTensorLinear v A) := by
  intro M N h
  apply CStarMatrix.ext
  intro i j
  have hc := congrArg (tensorMatrixCoefficient H A (v j) (v i)) h
  simpa only [tensorMatrixCoefficient_finiteMatrixTensor v hv A] using hc

/-- **Star homomorphism of a finite matrix frame.** For an orthonormal finite family `v`, the map
`M ↦ ∑ i,j, M i j ⊗ θ_(v i,v j)` is a nonunital complex star-algebra homomorphism into `A ⊗_ℂ
K(H)`. -/
noncomputable def finiteMatrixTensorHom :
    CStarMatrix ι ι A →⋆ₙₐ[ℂ] A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
  NonUnitalStarAlgHom.ofLinearMap (finiteMatrixTensorLinear v A)
    (finiteMatrixTensorLinear_mul v hv A) (finiteMatrixTensorLinear_star v A)

/-- **Value of the finite frame star homomorphism.** `finiteMatrixTensorHom v hv A M = ∑ i, ∑ j, M
i j ⊗ hilbertCompactRankOne H (v i) (v j)`. -/
theorem finiteMatrixTensorHom_apply (M : CStarMatrix ι ι A) :
    finiteMatrixTensorHom v hv A M =
      ∑ i, ∑ j, M i j ⊗ₜ[ℂ] hilbertCompactRankOne H (v i) (v j) := rfl

/-- **Injective finite frame star homomorphism.** The homomorphism determined by an orthonormal
finite family is injective, including an empty index type. -/
theorem finiteMatrixTensorHom_injective : Function.Injective (finiteMatrixTensorHom v hv A) :=
  finiteMatrixTensorLinear_injective v hv A

end CStarModule.HilbertAmplification
