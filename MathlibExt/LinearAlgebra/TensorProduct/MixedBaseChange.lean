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
# Mixed base change across two independent coefficient rings

Let R,S be commutative rings, M an R-module and N an S-module, with independently sized
carriers. Set T=R⊗_ℤS, L=T⊗_R M and Q=T⊗_S N, using the canonical coefficient inclusions into
T. The ℤ-linear equivalence θ:L⊗_TQ≃M⊗_ℤN sends (1_T⊗_Rm)⊗_T(1_T⊗_Sn) to m⊗_ℤn, with inverse
inserting the two unit coefficients.
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

/-- **Cancellation of mixed tensor scalar extensions.**

Let R,S be commutative rings, M an R-module and N an S-module, with independently sized
carriers. Set T=R⊗_ℤS, L=T⊗_R M and Q=T⊗_S N, using the canonical coefficient inclusions into
T. The equivalence mixedBaseChangeEquiv R S M N:(T⊗_RM)⊗_T(T⊗_SN)≃ₗ[ℤ]M⊗_ℤN has inverse
m⊗n↦(1_T⊗m)⊗(1_T⊗n).
-/
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

/-- **Inverse mixed-base-change value on a pure tensor.**

Let R,S be commutative rings, M an R-module and N an S-module, with independently sized
carriers. Set T=R⊗_ℤS, L=T⊗_R M and Q=T⊗_S N, using the canonical coefficient inclusions into
T. For m∈M and n∈N, (mixedBaseChangeEquiv R S M N)⁻¹(m⊗_ℤn)=(1_T⊗_Rm)⊗_T(1_T⊗_Sn).
-/
theorem mixedBaseChangeEquiv_symm_tmul (m : M) (n : N) :
    (mixedBaseChangeEquiv R S M N).symm (m ⊗ₜ[ℤ] n) =
      ((1 : T) ⊗ₜ[R] m) ⊗ₜ[T] ((1 : T) ⊗ₜ[S] n) := by
  unfold mixedBaseChangeEquiv
  simp only [LinearEquiv.symm_trans_apply]
  change (mixedCancelRight R S M N).symm
    ((mixedCancelLeft R S M N).symm ((TensorProduct.comm ℤ N M).symm (m ⊗ₜ[ℤ] n))) = _
  rw [TensorProduct.comm_symm, TensorProduct.comm_tmul, mixedCancelLeft_symm_tmul,
    mixedCancelRight_symm_tmul]

/-- **Unit tensor value of the mixed-base-change equivalence.**

Let R,S be commutative rings, M an R-module and N an S-module, with independently sized
carriers. Set T=R⊗_ℤS, L=T⊗_R M and Q=T⊗_S N, using the canonical coefficient inclusions into
T. For m∈M and n∈N, mixedBaseChangeEquiv R S M N ((1_T⊗_Rm)⊗_T(1_T⊗_Sn))=m⊗_ℤn.
-/
theorem mixedBaseChangeEquiv_unit_tmul (m : M) (n : N) :
    mixedBaseChangeEquiv R S M N
      (((1 : T) ⊗ₜ[R] m) ⊗ₜ[T] ((1 : T) ⊗ₜ[S] n)) = m ⊗ₜ[ℤ] n := by
  rw [← mixedBaseChangeEquiv_symm_tmul, LinearEquiv.apply_symm_apply]

end TensorProduct.AlgebraTensorModule
