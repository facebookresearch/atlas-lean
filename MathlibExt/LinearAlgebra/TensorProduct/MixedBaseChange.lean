/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Mixed base change over integer tensor products

Two independent coefficient rings act through their inclusions in the
integer tensor product. Cancelling both scalar extensions gives the
integer tensor of the coefficient modules.
The construction uses tensor pushouts; flatness and freeness are not
required.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace TensorProduct.AlgebraTensorModule

universe u v w z
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]
variable (M : Type w) (N : Type z) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] SMulCommClass.of_commMonoid

local notation "T" => R ⊗[ℤ] S
local notation "L" => T ⊗[R] M
local notation "Q" => T ⊗[S] N

local instance mixedBaseChangeSwappedPushout : Algebra.IsPushout ℤ S R T :=
  (inferInstance : Algebra.IsPushout ℤ R S T).symm

local instance mixedBaseChangeIntTower (P : Type*) [AddCommGroup P] [Module T P] :
    IsScalarTower ℤ T P := AddCommGroup.intIsScalarTower

private def mixedCancelRight : L ⊗[T] Q ≃ₗ[T] L ⊗[S] N :=
  (TensorProduct.isBaseChange S N T).tensorEquiv L

private def mixedCancelLeft : L ⊗[S] N ≃ₗ[S] N ⊗[ℤ] M :=
  (TensorProduct.congr (Algebra.IsPushout.cancelBaseChange ℤ S R T M) (LinearEquiv.refl S N)).trans
    ((TensorProduct.comm S (S ⊗[ℤ] M) N).trans (cancelBaseChange ℤ S S N M))

/-- The mixed scalar extensions cancel to the original integer tensor of the modules. -/
@[no_expose]
def mixedBaseChangeEquiv : L ⊗[T] Q ≃ₗ[ℤ] M ⊗[ℤ] N :=
  ((mixedCancelRight R S M N).restrictScalars ℤ).trans
    (((mixedCancelLeft R S M N).restrictScalars ℤ).trans (TensorProduct.comm ℤ N M))

private theorem mixedCancelRight_symm_tmul (x : L) (n : N) :
    (mixedCancelRight R S M N).symm (x ⊗ₜ[S] n) = x ⊗ₜ[T] ((1 : T) ⊗ₜ[S] n) := by
  unfold mixedCancelRight IsBaseChange.tensorEquiv
  rw [LinearEquiv.symm_trans_apply, cancelBaseChange_symm_tmul, LinearEquiv.symm_lTensor,
    LinearEquiv.symm_symm, LinearEquiv.lTensor_tmul, IsBaseChange.equiv_tmul, one_smul]
  rfl

private theorem mixedCancelLeft_symm_tmul (m : M) (n : N) :
    (mixedCancelLeft R S M N).symm (n ⊗ₜ[ℤ] m) = ((1 : T) ⊗ₜ[R] m) ⊗ₜ[S] n := by
  unfold mixedCancelLeft
  simp only [LinearEquiv.symm_trans_apply]
  rw [cancelBaseChange_symm_tmul, TensorProduct.comm_symm, TensorProduct.comm_tmul,
    TensorProduct.congr_symm, TensorProduct.congr_tmul,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one]

/-- The inverse retains the literal original tensor, inserting only the two unit coefficients. -/
theorem mixedBaseChangeEquiv_symm_tmul (m : M) (n : N) :
    (mixedBaseChangeEquiv R S M N).symm (m ⊗ₜ[ℤ] n) =
      ((1 : T) ⊗ₜ[R] m) ⊗ₜ[T] ((1 : T) ⊗ₜ[S] n) := by
  unfold mixedBaseChangeEquiv
  simp only [LinearEquiv.symm_trans_apply]
  change (mixedCancelRight R S M N).symm
    ((mixedCancelLeft R S M N).symm ((TensorProduct.comm ℤ N M).symm (m ⊗ₜ[ℤ] n))) = _
  rw [TensorProduct.comm_symm, TensorProduct.comm_tmul, mixedCancelLeft_symm_tmul,
    mixedCancelRight_symm_tmul]

/-- The canonical unit tensors recover the original module tensor. -/
theorem mixedBaseChangeEquiv_unit_tmul (m : M) (n : N) :
    mixedBaseChangeEquiv R S M N
      (((1 : T) ⊗ₜ[R] m) ⊗ₜ[T] ((1 : T) ⊗ₜ[S] n)) = m ⊗ₜ[ℤ] n := by
  rw [← mixedBaseChangeEquiv_symm_tmul, LinearEquiv.apply_symm_apply]

end TensorProduct.AlgebraTensorModule
