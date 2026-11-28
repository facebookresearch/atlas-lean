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
# Arbitrary product tensor comparisons under a scalar surjection

Let R→S be a surjective algebra map of commutative rings. Let U and every member N_i of an
arbitrary product family be compatible R,S-modules. If U is finitely generated projective over
S, scalar balancing transports the product comparison over S to the R-linear equivalence
U⊗_R(∏_iN_i)≅∏_i(U⊗_RN_i).

Its forward map is the canonical componentwise tensor map, sending u⊗x to i↦u⊗x_i. The family
and index may be infinite. The S-actions on U and the family are part of the hypotheses, and all
ring, index and carrier universes are independent.
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

/-- Let S be a commutative R-algebra with surjective algebra map, and let all R,S-module actions
below be compatible scalar towers. The ring, module and index universes are independent. Let U
and the family N_i be compatible R,S-modules and U finitely generated projective over S. This is
the R-linear equivalence U⊗_R(∏_iN_i)≅∏_i(U⊗_RN_i). It compares R- and S-balancing on the input
and outputs and applies the finite-factor product equivalence over S. -/
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

/-- Let S be a commutative R-algebra with surjective algebra map, and let all R,S-module actions
below be compatible scalar towers. The ring, module and index universes are independent. For
compatible R,S-modules U,N_i with U finitely generated projective over S, the product
equivalence satisfies e(u⊗_R x)_i=u⊗_R x_i for every u∈U, family x and index i. The formula
includes arbitrary product indices. -/
theorem piRightFiniteFactorOfSurjectiveScalars_tmul
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) (u : U) (x : ∀ i, N i) (i : ι) :
    piRightFiniteFactorOfSurjectiveScalars N h (u ⊗ₜ[R] x) i = u ⊗ₜ[R] x i := by
  simp [piRightFiniteFactorOfSurjectiveScalars, piRightFiniteFactor,
    TensorProduct.equivOfCompatibleSMul, TensorProduct.piRightHom_tmul]

/-- Let S be a commutative R-algebra with surjective algebra map, and let all R,S-module actions
below be compatible scalar towers. The ring, module and index universes are independent. For U
finitely generated projective over S and an arbitrary compatible R,S-module family N_i, the
underlying R-linear map of U⊗_R(∏_iN_i)≅∏_i(U⊗_RN_i) is π_R, with π_R(u⊗x)_i=u⊗x_i. -/
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
