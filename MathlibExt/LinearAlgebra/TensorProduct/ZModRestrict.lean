/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Residue-ring tensors and integer tensors

Let n∈ℕ and M,N be ZMod n-modules, regarded as integer modules on their additive groups. For
n=0, ZMod 0=ℤ. Let Θ:M⊗_ℤN≃ₗ[ℤ]M⊗_(ZMod n)N be the comparison preserving pure tensors. The
equivalence and inverse retain the pure value m⊗n. The integer tensor is n-torsion, which
supplies its residue scalar action.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u v

namespace TensorProduct

variable (n : ℕ) (M : Type u) (N : Type v)
variable [AddCommGroup M] [AddCommGroup N]
variable [Module (ZMod n) M] [Module (ZMod n) N]

omit [Module (ZMod n) N] in
/-- **Residue torsion in an integer tensor with one torsion factor.**

Let n∈ℕ, M a ZMod n-module and N any additive commutative group. Then n•z=0 for every z∈M⊗_ℤN;
no residue-ring module action on N is needed.
-/
theorem intTensor_nsmul_eq_zero (z : TensorProduct ℤ M N) : n • z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [← Nat.cast_smul_eq_nsmul ℤ, TensorProduct.smul_tmul']
      rw [Nat.cast_smul_eq_nsmul]
      rw [ZModModule.char_nsmul_eq_zero, zero_tmul]
  | add x y hx hy =>
      rw [nsmul_add, hx, hy, add_zero]

/-- **Integer-linear map to a residue-ring tensor.**

Let n∈ℕ and M,N be ZMod n-modules, regarded as integer modules on their additive groups. For
n=0, ZMod 0=ℤ. Let Θ:M⊗_ℤN≃ₗ[ℤ]M⊗_(ZMod n)N be the comparison preserving pure tensors. The map
intToZMod:M⊗_ℤN→ₗ[ℤ]M⊗_(ZMod n)N sends m⊗n′ to the same pure tensor.
-/
noncomputable def intToZMod :
    TensorProduct ℤ M N →ₗ[ℤ] TensorProduct (ZMod n) M N := by
  let inner (x : M) : N →+ TensorProduct (ZMod n) M N :=
    { toFun := fun y => x ⊗ₜ[ZMod n] y
      map_zero' := by simp
      map_add' := by intro y z; rw [tmul_add] }
  let outer : M →+ (N →ₗ[ℤ] TensorProduct (ZMod n) M N) :=
    { toFun := fun x => (inner x).toIntLinearMap
      map_zero' := by
        apply LinearMap.ext
        intro y
        simp [inner]
      map_add' := fun x y => by
        apply LinearMap.ext
        intro z
        simp [inner, add_tmul] }
  exact TensorProduct.lift outer.toIntLinearMap

@[simp]
theorem intToZMod_tmul (x : M) (y : N) :
    intToZMod n M N (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ZMod n] y :=
  rfl

/-- **Residue-linear map back to the integer tensor.**

Let n∈ℕ and M,N be ZMod n-modules, regarded as integer modules on their additive groups. For
n=0, ZMod 0=ℤ. Let Θ:M⊗_ℤN≃ₗ[ℤ]M⊗_(ZMod n)N be the comparison preserving pure tensors. The map
zmodToInt:M⊗_(ZMod n)N→ₗ[ZMod n]M⊗_ℤN preserves pure tensors, with the target carrying its
induced n-torsion scalar structure.
-/
noncomputable def zmodToInt :
    TensorProduct (ZMod n) M N →ₗ[ZMod n] TensorProduct ℤ M N := by
  let inner (x : M) : N →+ TensorProduct ℤ M N :=
    { toFun := fun y => x ⊗ₜ[ℤ] y
      map_zero' := by simp
      map_add' := by intro y z; rw [tmul_add] }
  let outer : M →+ (N →ₗ[ZMod n] TensorProduct ℤ M N) :=
    { toFun := fun x => (inner x).toZModLinearMap n
      map_zero' := by
        apply LinearMap.ext
        intro y
        simp [inner]
      map_add' := fun x y => by
        apply LinearMap.ext
        intro z
        simp [inner, add_tmul] }
  exact TensorProduct.lift (outer.toZModLinearMap n)

@[simp]
theorem zmodToInt_tmul (x : M) (y : N) :
    zmodToInt n M N (x ⊗ₜ[ZMod n] y) = x ⊗ₜ[ℤ] y :=
  by simp [zmodToInt]

/-- **Integer-linear residue-to-integer tensor map.**

Let n∈ℕ and M,N be ZMod n-modules, regarded as integer modules on their additive groups. For
n=0, ZMod 0=ℤ. Let Θ:M⊗_ℤN≃ₗ[ℤ]M⊗_(ZMod n)N be the comparison preserving pure tensors. The map
zmodToIntLinear is the integer-linear form of the pure-preserving inverse comparison.
-/
noncomputable def zmodToIntLinear :
    TensorProduct (ZMod n) M N →ₗ[ℤ] TensorProduct ℤ M N :=
  (zmodToInt n M N).toAddMonoidHom.toIntLinearMap

@[simp]
theorem zmodToIntLinear_tmul (x : M) (y : N) :
    zmodToIntLinear n M N (x ⊗ₜ[ZMod n] y) = x ⊗ₜ[ℤ] y := by
  change zmodToInt n M N (x ⊗ₜ[ZMod n] y) = _
  rw [zmodToInt_tmul]

variable [iM : Module ℤ M] [iN : Module ℤ N]

/-- **Canonical equivalence of integer and residue tensors.**

Let n∈ℕ and M,N be ZMod n-modules, regarded as integer modules on their additive groups. For
n=0, ZMod 0=ℤ. Let Θ:M⊗_ℤN≃ₗ[ℤ]M⊗_(ZMod n)N be the comparison preserving pure tensors. This
pure-preserving equivalence is zmodRestrictIntEquiv n M N.
-/
noncomputable def zmodRestrictIntEquiv :
    TensorProduct ℤ M N ≃ₗ[ℤ] TensorProduct (ZMod n) M N := by
  cases Subsingleton.elim iM (AddCommGroup.toIntModule (M := M))
  cases Subsingleton.elim iN (AddCommGroup.toIntModule (M := N))
  exact {
    __ := intToZMod n M N
    invFun := zmodToIntLinear n M N
    left_inv z := by
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
          change zmodToIntLinear n M N
            (intToZMod n M N (x ⊗ₜ[ℤ] y)) = _
          rw [intToZMod_tmul, zmodToIntLinear_tmul]
      | add x y hx hy =>
          change zmodToIntLinear n M N
            (intToZMod n M N (x + y)) = _
          rw [map_add, map_add]
          exact congrArg₂ (fun a b => a + b) hx hy
    right_inv z := by
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
          change intToZMod n M N
            (zmodToIntLinear n M N (x ⊗ₜ[ZMod n] y)) = _
          rw [zmodToIntLinear_tmul, intToZMod_tmul]
      | add x y hx hy =>
          change intToZMod n M N
            (zmodToIntLinear n M N (x + y)) = _
          rw [map_add, map_add]
          exact congrArg₂ (fun a b => a + b) hx hy }

@[simp]
theorem zmodRestrictIntEquiv_apply_tmul (x : M) (y : N) :
    zmodRestrictIntEquiv n M N (x ⊗ₜ[ℤ] y) =
      x ⊗ₜ[ZMod n] y :=
  by
    cases Subsingleton.elim iM (AddCommGroup.toIntModule (M := M))
    cases Subsingleton.elim iN (AddCommGroup.toIntModule (M := N))
    rfl

@[simp]
theorem zmodRestrictIntEquiv_symm_apply_tmul (x : M) (y : N) :
    (zmodRestrictIntEquiv n M N).symm (x ⊗ₜ[ZMod n] y) =
      x ⊗ₜ[ℤ] y :=
  by
    cases Subsingleton.elim iM (AddCommGroup.toIntModule (M := M))
    cases Subsingleton.elim iN (AddCommGroup.toIntModule (M := N))
    exact zmodToIntLinear_tmul n M N x y

end TensorProduct
