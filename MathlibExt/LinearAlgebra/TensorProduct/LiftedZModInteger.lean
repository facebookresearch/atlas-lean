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

/-!
# Tensoring over a lifted residue ring agrees with integer tensoring

Let ℓ∈ℕ and E be a copy of ZMod(ℓ) in an arbitrary lift universe s. For E-modules M,N with
independent carrier universes, every scalar of E is represented by an integer. Consequently the
balancing relation over ℤ already gives the balancing relation over E.

The resulting ℤ-linear equivalence M⊗_E N≅M⊗_ℤ N is identity on pure tensors in both directions
and natural in both E-linear factor maps. The modulus may be zero, where ZMod(0)=ℤ.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe v w p q s
open TensorProduct

namespace ScalarRestriction

variable (ell : ℕ) (M : Type v) (N : Type w)
  [AddCommGroup M] [AddCommGroup N]
  [Module (ULift.{s} (ZMod ell)) M] [Module (ULift.{s} (ZMod ell)) N]

/-- Let ℓ∈ℕ, E a copy of ZMod(ℓ) placed in universe s, and M,N additive groups with E-module
structures in independent carrier universes v,w. For every e∈E and m∈M,n∈N, the ℤ-tensor product
satisfies (e•m)⊗n=m⊗(e•n). Each e is an integer cast, and its action agrees with integer
multiplication. The modulus ℓ may be zero. -/
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

/-- Let ℓ∈ℕ, E a copy of ZMod(ℓ) placed in universe s, and M,N additive groups with E-module
structures in independent carrier universes v,w. This is the ℤ-linear equivalence M⊗_E N≅M⊗_ℤ N
induced by equality of their balancing relations. Forward and inverse maps send each pure tensor
m⊗n to the same pair of factors. -/
def liftedZModIntegerTensorEquiv :
    M ⊗[ULift.{s} (ZMod ell)] N ≃ₗ[ℤ] M ⊗[ℤ] N := by
  let : TensorProduct.CompatibleSMul ℤ (ULift.{s} (ZMod ell)) M N :=
    liftedZModIntegerCompatibleSMul ell M N
  exact TensorProduct.equivOfCompatibleSMul ℤ (ULift.{s} (ZMod ell)) ℤ M N

/-- Let ℓ∈ℕ, E a copy of ZMod(ℓ) placed in universe s, and M,N additive groups with E-module
structures in independent carrier universes v,w. For m∈M,n∈N, the forward map e:M⊗_E N≅M⊗_ℤ N
satisfies e(m⊗_E n)=m⊗_ℤ n. The factor elements and their carrier universes are retained. -/
@[simp]
theorem liftedZModIntegerTensorEquiv_tmul (m : M) (n : N) :
    liftedZModIntegerTensorEquiv ell M N (m ⊗ₜ[ULift.{s} (ZMod ell)] n) =
      m ⊗ₜ[ℤ] n := rfl

/-- Let ℓ∈ℕ, E a copy of ZMod(ℓ) placed in universe s, and M,N additive groups with E-module
structures in independent carrier universes v,w. For m∈M,n∈N, the inverse of e:M⊗_E N≅M⊗_ℤ N
satisfies e^{-1}(m⊗_ℤ n)=m⊗_E n. The formula includes all moduli and lift heights. -/
@[simp]
theorem liftedZModIntegerTensorEquiv_symm_tmul (m : M) (n : N) :
    (liftedZModIntegerTensorEquiv ell M N).symm (m ⊗ₜ[ℤ] n) =
      m ⊗ₜ[ULift.{s} (ZMod ell)] n := rfl

variable {M N} {P : Type p} {Q : Type q}
  [AddCommGroup P] [AddCommGroup Q]
  [Module (ULift.{s} (ZMod ell)) P] [Module (ULift.{s} (ZMod ell)) Q]

/-- Let ℓ∈ℕ, E a copy of ZMod(ℓ) placed in universe s, and M,N additive groups with E-module
structures in independent carrier universes v,w. Let P,Q be E-modules in further independent
universes and f:M→P,g:N→Q E-linear maps. For the canonical comparisons e_{M,N},e_{P,Q},
(f|_ℤ⊗g|_ℤ)∘e_{M,N}=e_{P,Q}∘(f⊗_E g), as ℤ-linear maps. Thus tensor comparison is natural in
both factors. -/
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
