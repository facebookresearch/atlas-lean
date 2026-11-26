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
# Product tensor comparison through a scalar quotient

Let R,S be commutative rings with a surjective algebra map R→S, U and all N_i S-modules with
compatible restricted R-actions, and U finitely generated projective over S. The product index
I is arbitrary. The R-linear map Π_R:U⊗_R(∏iN_i)→∏i(U⊗_RN_i), u⊗x↦(i↦u⊗x_i), is an
isomorphism.
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

/-- **Product tensor equivalence for finite projectivity over quotient scalars.**

Let R,S be commutative rings with a surjective algebra map R→S, U and all N_i S-modules with
compatible restricted R-actions, and U finitely generated projective over S. The product index
I is arbitrary. The equivalence
piRightFiniteFactorOfSurjectiveScalars:U⊗_R(∏iN_i)≃ₗ[R]∏i(U⊗_RN_i) has pure tensor value
u⊗x↦(i↦u⊗x_i).
-/
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

/-- **Pure tensor coordinates of the scalar-quotient product equivalence.**

Let R,S be commutative rings with a surjective algebra map R→S, U and all N_i S-modules with
compatible restricted R-actions, and U finitely generated projective over S. The product index
I is arbitrary. For u∈U, x∈∏iN_i and i∈I, piRightFiniteFactorOfSurjectiveScalars(u⊗_R
x)(i)=u⊗_R x_i.
-/
theorem piRightFiniteFactorOfSurjectiveScalars_tmul
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) (u : U) (x : ∀ i, N i) (i : ι) :
    piRightFiniteFactorOfSurjectiveScalars N h (u ⊗ₜ[R] x) i = u ⊗ₜ[R] x i := by
  simp [piRightFiniteFactorOfSurjectiveScalars, piRightFiniteFactor,
    TensorProduct.equivOfCompatibleSMul, TensorProduct.piRightHom_tmul]

/-- **Forward map of the scalar-quotient product equivalence.**

Let R,S be commutative rings with a surjective algebra map R→S, U and all N_i S-modules with
compatible restricted R-actions, and U finitely generated projective over S. The product index
I is arbitrary. The linear map of piRightFiniteFactorOfSurjectiveScalars equals piRightHom R R
U N, the product-coordinate comparison u⊗x↦(i↦u⊗x_i).
-/
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
