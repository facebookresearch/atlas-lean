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

public import MathlibExt.LinearAlgebra.TensorProduct.PiFiniteFactor
public import MathlibExt.LinearAlgebra.TensorProduct.SurjectiveScalarHom

/-!
# Scalar transport for product tensor comparisons

Compatible-scalar tensor coordinates transport the finite-projective
factor comparison, preserving pure tensors and product projections.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace TensorProduct

universe uR uS uI uN uU

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type uI} {U : Type uU} [AddCommGroup U] [Module R U] [Module S U]
  [IsScalarTower R S U] (N : ι → Type uN)
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, Module S (N i)]
  [∀ i, IsScalarTower R S (N i)]

/-- All scalar tensor coordinates and the original finite-factor product map
are constructed internally from the actual surjective scalar action. -/
def piRightFiniteFactorOfSurjectiveScalars
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) :
    U ⊗[R] (∀ i, N i) ≃ₗ[R] ∀ i, U ⊗[R] N i := by
  letI : CompatibleSMul R S U (∀ i, N i) :=
    compatibleSMul_of_surjective_algebraMap (M := U) (J := ∀ i, N i) h
  letI (i : ι) : CompatibleSMul R S U (N i) :=
    compatibleSMul_of_surjective_algebraMap (M := U) (J := N i) h
  exact TensorProduct.equivOfCompatibleSMul S R R U (∀ i, N i) ≪≫ₗ
    (piRightFiniteFactor S N U).restrictScalars R ≪≫ₗ
      LinearEquiv.piCongrRight (fun i => TensorProduct.equivOfCompatibleSMul R S R U (N i))

/-- Every original pure tensor retains every original product coordinate. -/
theorem piRightFiniteFactorOfSurjectiveScalars_tmul
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) (u : U) (x : ∀ i, N i) (i : ι) :
    piRightFiniteFactorOfSurjectiveScalars N h (u ⊗ₜ[R] x) i = u ⊗ₜ[R] x i := by
  simp [piRightFiniteFactorOfSurjectiveScalars, piRightFiniteFactor,
    TensorProduct.equivOfCompatibleSMul, TensorProduct.piRightHom_tmul]

/-- The original R product comparison is the exact forward map. -/
theorem piRightFiniteFactorOfSurjectiveScalars_toLinearMap
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) :
    (piRightFiniteFactorOfSurjectiveScalars N h).toLinearMap = piRightHom R R U N := by
  apply TensorProduct.ext'
  intro u x
  funext i
  change piRightFiniteFactorOfSurjectiveScalars N h (u ⊗ₜ[R] x) i =
    piRightHom R R U N (u ⊗ₜ[R] x) i
  rw [piRightFiniteFactorOfSurjectiveScalars_tmul, piRightHom_tmul]

end TensorProduct
