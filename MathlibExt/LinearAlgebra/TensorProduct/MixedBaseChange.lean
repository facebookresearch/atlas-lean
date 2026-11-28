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
# Mixed coefficient extension through an integer tensor ring

Let R,S be commutative rings and M,N modules over R,S respectively, with independent ring and
carrier universes. Put T=R⊗_ℤS. The two scalar extensions L=T⊗_R M and Q=T⊗_S N tensor over T to
an abelian group canonically isomorphic to M⊗_ℤN.

The inverse sends m⊗n to (1⊗_R m)⊗_T(1⊗_S n), and the forward map recovers m⊗n from those
unit-coefficient tensors. The equivalence is ℤ-linear and uses the symmetric tensor-ring pushout
and compatible integer scalar towers; flatness and freeness are not hypotheses.
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

/-- For commutative rings R,S in independent universes, T=R⊗_ℤS is the scalar pushout of ℤ→S and ℤ→R
as well as of ℤ→R and ℤ→S. The two inclusions satisfy the tensor-ring universal property after
exchanging the coefficient rings. -/
local instance mixedBaseChangeSwappedPushout : Algebra.IsPushout ℤ S R T :=
  (inferInstance : Algebra.IsPushout ℤ R S T).symm

/-- Let R,S be commutative rings, T=R⊗_ℤS and P any T-module with an additive commutative group
structure. Its integer and T-actions form the scalar tower ℤ→T→P. Integer multiplication agrees
with the action of the integer scalar cast in T, independently of the carrier universes. -/
local instance mixedBaseChangeIntTower (P : Type*) [AddCommGroup P] [Module T P] :
    IsScalarTower ℤ T P := AddCommGroup.intIsScalarTower

private def mixedCancelRight : L ⊗[T] Q ≃ₗ[T] L ⊗[S] N :=
  (TensorProduct.isBaseChange S N T).tensorEquiv L

private def mixedCancelLeft : L ⊗[S] N ≃ₗ[S] N ⊗[ℤ] M :=
  (TensorProduct.congr (Algebra.IsPushout.cancelBaseChange ℤ S R T M) (LinearEquiv.refl S N)).trans
    ((TensorProduct.comm S (S ⊗[ℤ] M) N).trans (cancelBaseChange ℤ S S N M))

/-- Let R,S be commutative rings in independent universes u,v, M an R-module in w and N an S-module
in z. Put T=R⊗_ℤS, L=T⊗_R M and Q=T⊗_S N using the two tensor-ring inclusions. This is the
ℤ-linear equivalence L⊗_T Q≅M⊗_ℤN. It cancels both scalar extensions through the tensor pushout
T without any flatness condition. -/
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
    LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one]

/-- Let R,S be commutative rings in independent universes u,v, M an R-module in w and N an S-module
in z. Put T=R⊗_ℤS, L=T⊗_R M and Q=T⊗_S N using the two tensor-ring inclusions. For m∈M,n∈N, the
inverse of e:L⊗_T Q≅M⊗_ℤN satisfies e^{-1}(m⊗_ℤ n)=(1⊗_R m)⊗_T(1⊗_S n). The factor order is
retained. -/
theorem mixedBaseChangeEquiv_symm_tmul (m : M) (n : N) :
    (mixedBaseChangeEquiv R S M N).symm (m ⊗ₜ[ℤ] n) =
      ((1 : T) ⊗ₜ[R] m) ⊗ₜ[T] ((1 : T) ⊗ₜ[S] n) := by
  unfold mixedBaseChangeEquiv
  simp only [LinearEquiv.symm_trans_apply]
  change (mixedCancelRight R S M N).symm
    ((mixedCancelLeft R S M N).symm ((TensorProduct.comm ℤ N M).symm (m ⊗ₜ[ℤ] n))) = _
  rw [TensorProduct.comm_symm, TensorProduct.comm_tmul, mixedCancelLeft_symm_tmul,
    mixedCancelRight_symm_tmul]

/-- Let R,S be commutative rings in independent universes u,v, M an R-module in w and N an S-module
in z. Put T=R⊗_ℤS, L=T⊗_R M and Q=T⊗_S N using the two tensor-ring inclusions. For m∈M,n∈N,
e((1⊗_R m)⊗_T(1⊗_S n))=m⊗_ℤn. This gives the forward map's value on the canonical
unit-coefficient tensor. -/
theorem mixedBaseChangeEquiv_unit_tmul (m : M) (n : N) :
    mixedBaseChangeEquiv R S M N
      (((1 : T) ⊗ₜ[R] m) ⊗ₜ[T] ((1 : T) ⊗ₜ[S] n)) = m ⊗ₜ[ℤ] n := by
  rw [← mixedBaseChangeEquiv_symm_tmul, LinearEquiv.apply_symm_apply]

end TensorProduct.AlgebraTensorModule
