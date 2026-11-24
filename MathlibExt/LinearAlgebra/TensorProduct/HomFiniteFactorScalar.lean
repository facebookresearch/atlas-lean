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
# Original scalar transport for a finite-projective tensor factor

The unchanged scalar coordinate factors transport the coefficient equivalence
earned from the actual finite-free retraction of the tensor factor. The first
Hom source is arbitrary, and the hom is the original R coefficient map.
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

/-- Original scalar/input/output Isos surround the actual finite-factor
coefficient equivalence. No finite-projectivity of the Hom source is required. -/
def homTensorFiniteFactorEquivOfSurjectiveScalars
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) :
    (P →ₗ[R] N) ⊗[R] U ≃ₗ[R] P →ₗ[R] N ⊗[R] U :=
  rTensorHomScalarInputEquiv h ≪≫ₗ
    (homTensorFiniteFactorEquiv S P N U).restrictScalars R ≪≫ₗ
      rTensorHomScalarOutputEquiv h

/-- Every original pure tensor retains its actual coefficient evaluation. -/
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

/-- The source map is exactly the original R coefficient comparison, with the
scalar quotient and its actual inverse completely internal to the construction. -/
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
