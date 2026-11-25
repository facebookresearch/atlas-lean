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
# Actual finite tensor–Hom transport along a surjective scalar map

Native scalar extension identifies the original linear maps, and native
compatible-scalar tensor equivalences retain every original pure tensor.
The only finite-projective contraction is the existing native equivalence.
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

/-- A surjective actual scalar map proves compatibility on the original R tensor. -/
theorem compatibleSMul_of_surjective_algebraMap
    (h : Function.Surjective (algebraMap R S)) : CompatibleSMul R S M J where
  smul_tmul s m j := by
    obtain ⟨r, rfl⟩ := h s
    simpa only [algebraMap_smul] using (TensorProduct.smul_tmul (R := R) r m j)

/-- Original scalar/input tensor coordinates; no finite-projectivity premise is used. -/
def rTensorHomScalarInputEquiv
    (h : Function.Surjective (algebraMap R S)) :
    (M →ₗ[R] J) ⊗[R] U ≃ₗ[R] (M →ₗ[S] J) ⊗[S] U := by
  letI : CompatibleSMul R S (M →ₗ[S] J) U :=
    compatibleSMul_of_surjective_algebraMap (M := M →ₗ[S] J) (J := U) h
  let eHom : (M →ₗ[R] J) ≃ₗ[R] M →ₗ[S] J :=
    LinearMap.extendScalarsOfSurjectiveEquiv h
  exact TensorProduct.congr eHom (LinearEquiv.refl R U) ≪≫ₗ
    TensorProduct.equivOfCompatibleSMul S R R (M →ₗ[S] J) U

/-- Original scalar/output Hom coordinates, retaining every original underlying function. -/
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

/-- The actual native coefficient transports followed by the existing S contraction.
The original construction is factored through the same unchanged scalar coordinates. -/
def rTensorHomEquivOfSurjectiveScalars
    [Module.Projective S M] [Module.Finite S M]
    (h : Function.Surjective (algebraMap R S)) :
    (M →ₗ[R] J) ⊗[R] U ≃ₗ[R] M →ₗ[R] J ⊗[R] U :=
  rTensorHomScalarInputEquiv h ≪≫ₗ
    (_root_.rTensorHomEquivHomRTensor S M J U).restrictScalars R ≪≫ₗ
      rTensorHomScalarOutputEquiv h

/-- The transport retains the canonical original R-linear evaluation on every pure tensor. -/
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

/-- The forward linear map is the exact original R coefficient map, independent of
the quotient/transport used to earn its inverse. -/
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
