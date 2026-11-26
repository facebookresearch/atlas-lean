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

public import MathlibExt.LinearAlgebra.TensorProduct.HomFiniteFactor
public import MathlibExt.LinearAlgebra.TensorProduct.SurjectiveScalarHom

/-!
# Hom–tensor comparison through a scalar quotient

Let R,S be commutative rings with surjective algebra map R→S, and P,N,U S-modules with
compatible restricted R-actions. Assume U is finitely generated projective over S; P and N are
otherwise arbitrary. The R-linear map C_R:Hom_R(P,N)⊗_R U→Hom_R(P,N⊗_R U), C_R(f⊗u)(p)=f(p)⊗u,
is an isomorphism.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace TensorProduct

universe uR uS uP uN uU

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
  {P : Type uP} {N : Type uN} {U : Type uU}
  [AddCommGroup P] [AddCommGroup N] [AddCommGroup U]
  [Module R P] [Module R N] [Module R U]
  [Module S P] [Module S N] [Module S U]
  [IsScalarTower R S P] [IsScalarTower R S N] [IsScalarTower R S U]

/-- **Hom–tensor equivalence for projectivity over quotient scalars.**

Let R,S be commutative rings with surjective algebra map R→S, and P,N,U S-modules with
compatible restricted R-actions. Assume U is finitely generated projective over S; P and N are
otherwise arbitrary. The equivalence homTensorFiniteFactorEquivOfSurjectiveScalars identifies
Hom_R(P,N)⊗_R U with Hom_R(P,N⊗_R U), by (f⊗u)(p)↦f(p)⊗u.
-/
def homTensorFiniteFactorEquivOfSurjectiveScalars
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) :
    (P →ₗ[R] N) ⊗[R] U ≃ₗ[R] P →ₗ[R] N ⊗[R] U :=
  rTensorHomScalarInputEquiv h ≪≫ₗ
    (homTensorFiniteFactorEquiv S P N U).restrictScalars R ≪≫ₗ
      rTensorHomScalarOutputEquiv h

/-- **Pure tensor evaluation in the scalar-quotient Hom equivalence.**

Let R,S be commutative rings with surjective algebra map R→S, and P,N,U S-modules with
compatible restricted R-actions. Assume U is finitely generated projective over S; P and N are
otherwise arbitrary. For R-linear f:P→N, u∈U and p∈P,
homTensorFiniteFactorEquivOfSurjectiveScalars(f⊗_Ru)(p)=f(p)⊗_Ru.
-/
theorem homTensorFiniteFactorEquivOfSurjectiveScalars_tmul
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) (f : P →ₗ[R] N) (u : U) (p : P) :
    homTensorFiniteFactorEquivOfSurjectiveScalars (P := P) (N := N) (U := U) h
        (f ⊗ₜ[R] u) p = f p ⊗ₜ[R] u := by
  simp [homTensorFiniteFactorEquivOfSurjectiveScalars, homTensorFiniteFactorEquiv,
    rTensorHomScalarInputEquiv, rTensorHomScalarOutputEquiv,
    TensorProduct.congr_tmul, TensorProduct.rTensorHomToHomRTensor_apply,
    TensorProduct.equivOfCompatibleSMul, LinearEquiv.arrowCongr,
    LinearMap.extendScalarsOfSurjectiveEquiv]

/-- **Forward map of the scalar-quotient Hom–tensor equivalence.**

Let R,S be commutative rings with surjective algebra map R→S, and P,N,U S-modules with
compatible restricted R-actions. Assume U is finitely generated projective over S; P and N are
otherwise arbitrary. The R-linear map of homTensorFiniteFactorEquivOfSurjectiveScalars equals
rTensorHomToHomRTensor(.id R) P N U, with pure values f⊗u↦(p↦f(p)⊗u).
-/
theorem homTensorFiniteFactorEquivOfSurjectiveScalars_toLinearMap
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) :
    (homTensorFiniteFactorEquivOfSurjectiveScalars (P := P) (N := N) (U := U) h).toLinearMap =
      rTensorHomToHomRTensor (.id R) P N U := by
  apply TensorProduct.ext'
  intro f u
  apply LinearMap.ext
  intro p
  change homTensorFiniteFactorEquivOfSurjectiveScalars (P := P) (N := N) (U := U) h
      (f ⊗ₜ[R] u) p = rTensorHomToHomRTensor (.id R) P N U (f ⊗ₜ[R] u) p
  rw [homTensorFiniteFactorEquivOfSurjectiveScalars_tmul,
    TensorProduct.rTensorHomToHomRTensor_apply]

end TensorProduct
