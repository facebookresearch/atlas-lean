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

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.Algebra.Algebra.Tower

/-!
# Tensor–Hom comparison through a surjective scalar map

Let S be a commutative R-algebra with surjective algebra map. Compatible R,S-actions on M,J,U
identify R-linear maps M→J with S-linear maps and identify the R- and S-balanced tensor
products. These coordinate comparisons retain their pure-tensor values.

If the Hom domain M is finitely generated and projective over S, the S-linear contraction
comparison transports to an R-linear equivalence Hom_R(M,J)⊗_R U≅Hom_R(M,J⊗_R U). Its forward
map is χ(f⊗u)(m)=f(m)⊗_R u. All ring and carrier universes are independent; finite projectivity
is required on M, while J,U are arbitrary compatible modules.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

namespace TensorProduct

universe uR uS uM uJ uU

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type uM} {J : Type uJ} {U : Type uU}
  [AddCommGroup M] [AddCommGroup J] [AddCommGroup U]
  [Module R M] [Module R J] [Module R U]
  [Module S M] [Module S J] [Module S U]
  [IsScalarTower R S M] [IsScalarTower R S J] [IsScalarTower R S U]

/-- Let S be a commutative R-algebra with surjective algebra map, and let all R,S-module actions
below be compatible scalar towers. The ring and module carrier universes are independent. Let
M,J,U be R,S-modules. This is the R-linear equivalence Hom_R(M,J)⊗_R U≅Hom_S(M,J)⊗_S U. R-linear
maps are S-linear by surjectivity and the compatible actions, and the tensor quotient changes
from R- to S-balancing. No finite-projectivity assumption is used. -/
def rTensorHomScalarInputEquiv
    (h : Function.Surjective (algebraMap R S)) :
    (M →ₗ[R] J) ⊗[R] U ≃ₗ[R] (M →ₗ[S] J) ⊗[S] U := by
  letI : CompatibleSMul R S (M →ₗ[S] J) U :=
    CompatibleSMul.of_algebraMap_surjective (M := M →ₗ[S] J) (N := U) h
  let eHom : (M →ₗ[R] J) ≃ₗ[R] M →ₗ[S] J :=
    LinearMap.extendScalarsOfSurjectiveEquiv h
  exact TensorProduct.congr eHom (LinearEquiv.refl R U) ≪≫ₗ
    TensorProduct.equivOfCompatibleSMul S R R (M →ₗ[S] J) U

/-- Let S be a commutative R-algebra with surjective algebra map, and let all R,S-module actions
below be compatible scalar towers. The ring and module carrier universes are independent. Let
M,J,U be R,S-modules. This R-linear equivalence Hom_S(M,J⊗_S U)≅Hom_R(M,J⊗_R U) first restricts
the map's scalar structure and then applies the canonical balancing equivalence J⊗_S U≅J⊗_R U to
each value. -/
def rTensorHomScalarOutputEquiv
    (h : Function.Surjective (algebraMap R S)) :
    (M →ₗ[S] J ⊗[S] U) ≃ₗ[R] M →ₗ[R] J ⊗[R] U := by
  letI : CompatibleSMul R S J U :=
    CompatibleSMul.of_algebraMap_surjective (M := J) (N := U) h
  let eTensor : J ⊗[S] U ≃ₗ[R] J ⊗[R] U :=
    TensorProduct.equivOfCompatibleSMul R S R J U
  exact (LinearMap.extendScalarsOfSurjectiveEquiv
    (R := R) (S := S) (M := M) (N := J ⊗[S] U) h).symm ≪≫ₗ
      (LinearEquiv.refl R M).arrowCongr eTensor

/-- Let S be a commutative R-algebra with surjective algebra map, and let all R,S-module actions
below be compatible scalar towers. The ring and module carrier universes are independent. Let
M,J,U be R,S-modules. If M is finitely generated projective over S, there is an R-linear
equivalence Hom_R(M,J)⊗_R U≅Hom_R(M,J⊗_R U). It is the input scalar comparison, S-linear
finite-projective contraction and output scalar comparison, with the R-linear contraction as
forward map. -/
def rTensorHomEquivOfSurjectiveScalars
    [Module.Projective S M] [Module.Finite S M]
    (h : Function.Surjective (algebraMap R S)) :
    (M →ₗ[R] J) ⊗[R] U ≃ₗ[R] M →ₗ[R] J ⊗[R] U :=
  rTensorHomScalarInputEquiv h ≪≫ₗ
    (_root_.rTensorHomEquivHomRTensor S M J U).restrictScalars R ≪≫ₗ
      rTensorHomScalarOutputEquiv h

/-- Let S be a commutative R-algebra with surjective algebra map, and let all R,S-module actions
below be compatible scalar towers. The ring and module carrier universes are independent. Let
M,J,U be R,S-modules. Assume M is finitely generated projective over S. For f∈Hom_R(M,J), u∈U
and m∈M, the equivalence sends f⊗_R u to the map with value f(m)⊗_R u at m. -/
theorem rTensorHomEquivOfSurjectiveScalars_tmul
    [Module.Projective S M] [Module.Finite S M]
    (h : Function.Surjective (algebraMap R S)) (f : M →ₗ[R] J) (u : U) (m : M) :
    rTensorHomEquivOfSurjectiveScalars (M := M) (J := J) (U := U) h (f ⊗ₜ[R] u) m =
      f m ⊗ₜ[R] u := by
  simp [rTensorHomEquivOfSurjectiveScalars, rTensorHomScalarInputEquiv,
    rTensorHomScalarOutputEquiv, TensorProduct.congr_tmul,
    _root_.rTensorHomEquivHomRTensor_apply, TensorProduct.rTensorHomToHomRTensor_apply,
    TensorProduct.equivOfCompatibleSMul, LinearEquiv.arrowCongr,
    LinearMap.extendScalarsOfSurjectiveEquiv]

/-- Let S be a commutative R-algebra with surjective algebra map, and let all R,S-module actions
below be compatible scalar towers. The ring and module carrier universes are independent. Let
M,J,U be R,S-modules. When M is finitely generated projective over S, the forward linear map of
Hom_R(M,J)⊗_R U≅Hom_R(M,J⊗_R U) is χ_R, characterized by χ_R(f⊗u)(m)=f(m)⊗_R u. The scalar
transports preserve this precise comparison. -/
theorem rTensorHomEquivOfSurjectiveScalars_toLinearMap
    [Module.Projective S M] [Module.Finite S M]
    (h : Function.Surjective (algebraMap R S)) :
    (rTensorHomEquivOfSurjectiveScalars (M := M) (J := J) (U := U) h).toLinearMap =
      TensorProduct.rTensorHomToHomRTensor (.id R) M J U := by
  apply TensorProduct.ext'
  intro f u
  apply LinearMap.ext
  intro m
  change rTensorHomEquivOfSurjectiveScalars (M := M) (J := J) (U := U) h
      (f ⊗ₜ[R] u) m = TensorProduct.rTensorHomToHomRTensor (.id R) M J U (f ⊗ₜ[R] u) m
  rw [rTensorHomEquivOfSurjectiveScalars_tmul, TensorProduct.rTensorHomToHomRTensor_apply]

end TensorProduct
