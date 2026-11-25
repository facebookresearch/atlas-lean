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
# Tensor products after restricting `ZMod n`-modules to `ℤ`

For `ZMod n`-modules `M` and `N`, the tensor product of their underlying
abelian groups over `ℤ` is canonically isomorphic to `M ⊗[ZMod n] N` after
forgetting its scalar structure to `ℤ`.  The construction uses only the
universal properties and the fact that the integral tensor product is
`n`-torsion.

The canonical equivalence accepts the actual stored integer module
structures. Their equality with the canonical integer action is the stock
uniqueness theorem, so this extension retains the same tensor comparison.

The statement includes `n = 0`, where `ZMod 0 = ℤ`.
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
/-- The integral tensor product of two `ZMod n`-modules is `n`-torsion. -/
theorem intTensor_nsmul_eq_zero (z : TensorProduct ℤ M N) : n • z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [← Nat.cast_smul_eq_nsmul ℤ, TensorProduct.smul_tmul']
      rw [Nat.cast_smul_eq_nsmul]
      rw [ZModModule.char_nsmul_eq_zero, zero_tmul]
  | add x y hx hy =>
      rw [nsmul_add, hx, hy, add_zero]

/-- Canonical integral-linear map from the tensor product over `ℤ` to the
tensor product over `ZMod n`. -/
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

/-- Canonical `ZMod n`-linear map back to the integral tensor product,
equipped with its canonical `n`-torsion module structure. -/
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

/-- The `ℤ`-linear form of `zmodToInt`, forgetting its `ZMod n` scalar
structure. -/
noncomputable def zmodToIntLinear :
    TensorProduct (ZMod n) M N →ₗ[ℤ] TensorProduct ℤ M N :=
  (zmodToInt n M N).toAddMonoidHom.toIntLinearMap

@[simp]
theorem zmodToIntLinear_tmul (x : M) (y : N) :
    zmodToIntLinear n M N (x ⊗ₜ[ZMod n] y) = x ⊗ₜ[ℤ] y := by
  change zmodToInt n M N (x ⊗ₜ[ZMod n] y) = _
  rw [zmodToInt_tmul]

variable [iM : Module ℤ M] [iN : Module ℤ N]

/-- Canonical comparison between tensoring two `ZMod n`-modules over `ℤ`
and tensoring them over `ZMod n`, with the latter restricted to `ℤ`. -/
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
