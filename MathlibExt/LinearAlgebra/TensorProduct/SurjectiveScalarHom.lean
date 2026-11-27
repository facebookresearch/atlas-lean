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
# Tensor–Hom scalar change through a quotient

Let R,S be commutative rings with surjective algebra map R→S, and M,J,U S-modules with
compatible restricted R-actions. Scalar restriction identifies R-linear and S-linear Hom
spaces and R/S tensor products. If M is finitely generated projective over S,
Hom_R(M,J)⊗_RU≃Hom_R(M,J⊗_RU) by f⊗u↦(m↦f(m)⊗u).
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

/-- **Surjective scalars give tensor scalar compatibility.**

Let R,S be commutative rings with surjective algebra map R→S, and M,J,U S-modules with
compatible restricted R-actions. For s∈S,m∈M,j∈J, (s•m)⊗_Rj=m⊗_R(s•j), so CompatibleSMul R S M
J holds.
-/
theorem compatibleSMul_of_surjective_algebraMap
    (h : Function.Surjective (algebraMap R S)) : CompatibleSMul R S M J where
  smul_tmul s m j := by
    obtain ⟨r, rfl⟩ := h s
    simpa only [algebraMap_smul] using (TensorProduct.smul_tmul (R := R) r m j)

/-- **Scalar-change equivalence on the input Hom tensor.**

Let R,S be commutative rings with surjective algebra map R→S, and M,J,U S-modules with
compatible restricted R-actions. The R-linear equivalence rTensorHomScalarInputEquiv
identifies Hom_R(M,J)⊗_RU with Hom_S(M,J)⊗_SU, preserving f⊗u.
-/
def rTensorHomScalarInputEquiv
    (h : Function.Surjective (algebraMap R S)) :
    (M →ₗ[R] J) ⊗[R] U ≃ₗ[R] (M →ₗ[S] J) ⊗[S] U := by
  letI : CompatibleSMul R S (M →ₗ[S] J) U :=
    compatibleSMul_of_surjective_algebraMap (M := M →ₗ[S] J) (J := U) h
  let eHom : (M →ₗ[R] J) ≃ₗ[R] M →ₗ[S] J :=
    LinearMap.extendScalarsOfSurjectiveEquiv h
  exact TensorProduct.congr eHom (LinearEquiv.refl R U) ≪≫ₗ
    TensorProduct.equivOfCompatibleSMul S R R (M →ₗ[S] J) U

/-- **Scalar-change equivalence on the output Hom space.**

Let R,S be commutative rings with surjective algebra map R→S, and M,J,U S-modules with
compatible restricted R-actions. The R-linear equivalence rTensorHomScalarOutputEquiv
identifies Hom_S(M,J⊗_SU) with Hom_R(M,J⊗_RU), using the pure-preserving tensor scalar
comparison.
-/
def rTensorHomScalarOutputEquiv
    (h : Function.Surjective (algebraMap R S)) :
    (M →ₗ[S] J ⊗[S] U) ≃ₗ[R] M →ₗ[R] J ⊗[R] U := by
  letI : CompatibleSMul R S J U :=
    compatibleSMul_of_surjective_algebraMap (M := J) (J := U) h
  let eTensor : J ⊗[S] U ≃ₗ[R] J ⊗[R] U :=
    TensorProduct.equivOfCompatibleSMul R S R J U
  exact (LinearMap.extendScalarsOfSurjectiveEquiv
    (R := R) (S := S) (M := M) (N := J ⊗[S] U) h).symm ≪≫ₗ
      (LinearEquiv.refl R M).arrowCongr eTensor

/-- **Tensor–Hom equivalence for projectivity over quotient scalars.**

Let R,S be commutative rings with surjective algebra map R→S, and M,J,U S-modules with
compatible restricted R-actions. If M is finitely generated projective over S,
rTensorHomEquivOfSurjectiveScalars:Hom_R(M,J)⊗_RU≃ₗ[R]Hom_R(M,J⊗_RU) sends f⊗u to m↦f(m)⊗u.
-/
def rTensorHomEquivOfSurjectiveScalars
    [Module.Projective S M] [Module.Finite S M]
    (h : Function.Surjective (algebraMap R S)) :
    (M →ₗ[R] J) ⊗[R] U ≃ₗ[R] M →ₗ[R] J ⊗[R] U :=
  rTensorHomScalarInputEquiv h ≪≫ₗ
    (_root_.rTensorHomEquivHomRTensor S M J U).restrictScalars R ≪≫ₗ
      rTensorHomScalarOutputEquiv h

/-- **Pure tensor evaluation in the quotient-scalar tensor–Hom equivalence.**

Let R,S be commutative rings with surjective algebra map R→S, and M,J,U S-modules with
compatible restricted R-actions. If M is finitely generated projective over S, then
rTensorHomEquivOfSurjectiveScalars(f⊗_Ru)(m)=f(m)⊗_Ru.
-/
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

/-- **Forward map of the quotient-scalar tensor–Hom equivalence.**

Let R,S be commutative rings with surjective algebra map R→S, and M,J,U S-modules with
compatible restricted R-actions. For M finitely generated projective over S, the forward map
is rTensorHomToHomRTensor(.id R) M J U, the evaluation f⊗u↦(m↦f(m)⊗u).
-/
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
