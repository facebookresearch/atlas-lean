/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.ULift

@[expose] public section
noncomputable section
set_option autoImplicit false
universe v w p q s
open TensorProduct

namespace ScalarRestriction

variable (ell : ℕ) (M : Type v) (N : Type w)
  [AddCommGroup M] [AddCommGroup N]
  [Module (ULift.{s} (ZMod ell)) M] [Module (ULift.{s} (ZMod ell)) N]

/-- **Integer balancing is compatible with lifted residue scalars.**

Let ℓ∈ℕ, L=ULift(ZMod ℓ) a universe-lifted copy of the residue ring, and M,N L-modules. With
their integer scalar actions, (a•m)⊗_ℤn=m⊗_ℤ(a•n) for every a∈L. This is CompatibleSMul ℤ L M
N, including ℓ=0.
-/
theorem liftedZModIntegerCompatibleSMul :
    TensorProduct.CompatibleSMul ℤ (ULift.{s} (ZMod ell)) M N := by
  refine ⟨?_⟩
  intro a m n
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective a.down
  have ha : (z : ULift.{s} (ZMod ell)) = a := by
    apply ULift.ext
    exact hz
  rw [← ha, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  exact TensorProduct.smul_tmul z m n

/-- **Lifted residue-ring tensor equals the integer tensor.**

Let ℓ∈ℕ, L=ULift(ZMod ℓ) and M,N L-modules. The ℤ-linear equivalence
liftedZModIntegerTensorEquiv:M⊗_LN≃ₗ[ℤ]M⊗_ℤN preserves m⊗n.
-/
def liftedZModIntegerTensorEquiv :
    M ⊗[ULift.{s} (ZMod ell)] N ≃ₗ[ℤ] M ⊗[ℤ] N := by
  let : TensorProduct.CompatibleSMul ℤ (ULift.{s} (ZMod ell)) M N :=
    liftedZModIntegerCompatibleSMul ell M N
  exact TensorProduct.equivOfCompatibleSMul ℤ (ULift.{s} (ZMod ell)) ℤ M N

@[simp]
theorem liftedZModIntegerTensorEquiv_tmul (m : M) (n : N) :
    liftedZModIntegerTensorEquiv ell M N (m ⊗ₜ[ULift.{s} (ZMod ell)] n) =
      m ⊗ₜ[ℤ] n := rfl

@[simp]
theorem liftedZModIntegerTensorEquiv_symm_tmul (m : M) (n : N) :
    (liftedZModIntegerTensorEquiv ell M N).symm (m ⊗ₜ[ℤ] n) =
      m ⊗ₜ[ULift.{s} (ZMod ell)] n := rfl

variable {M N} {P : Type p} {Q : Type q}
  [AddCommGroup P] [AddCommGroup Q]
  [Module (ULift.{s} (ZMod ell)) P] [Module (ULift.{s} (ZMod ell)) Q]

/-- **Naturality of the lifted-residue integer tensor comparison.**

Let ℓ∈ℕ, L=ULift(ZMod ℓ), M,N,P,Q L-modules and f:M→P,g:N→Q L-linear. For Θ the
pure-preserving equivalence between L and integer tensors, (f⊗_ℤg)∘Θ_(M,N)=Θ_(P,Q)∘(f⊗_Lg).
-/
theorem liftedZModIntegerTensorEquiv_naturality
    (f : M →ₗ[ULift.{s} (ZMod ell)] P) (g : N →ₗ[ULift.{s} (ZMod ell)] Q) :
    (TensorProduct.map (f.restrictScalars ℤ) (g.restrictScalars ℤ)).comp
        (liftedZModIntegerTensorEquiv ell M N).toLinearMap =
      (liftedZModIntegerTensorEquiv ell P Q).toLinearMap.comp
        ((TensorProduct.map f g).restrictScalars ℤ) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add x y hx hy =>
      let lhsMap : M ⊗[ULift.{s} (ZMod ell)] N →ₗ[ℤ] P ⊗[ℤ] Q :=
        (TensorProduct.map (f.restrictScalars ℤ) (g.restrictScalars ℤ)).comp
          (liftedZModIntegerTensorEquiv ell M N).toLinearMap
      let rhsMap : M ⊗[ULift.{s} (ZMod ell)] N →ₗ[ℤ] P ⊗[ℤ] Q :=
        (liftedZModIntegerTensorEquiv ell P Q).toLinearMap.comp
          ((TensorProduct.map f g).restrictScalars ℤ)
      have hx' : lhsMap x = rhsMap x := hx
      have hy' : lhsMap y = rhsMap y := hy
      exact (lhsMap.map_add x y).trans
        ((congrArg₂ (· + ·) hx' hy').trans (rhsMap.map_add x y).symm)

end ScalarRestriction
