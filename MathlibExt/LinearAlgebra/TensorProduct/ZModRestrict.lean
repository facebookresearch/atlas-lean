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
# Integer tensor products of residue-ring modules

For a ZMod(n)-module M and any additive commutative group N, the integer tensor M⊗_ℤN is
annihilated by n. If N is also a ZMod(n)-module, the canonical maps M⊗_ℤN→M⊗_{ZMod(n)}N and back
retain every pure tensor and are inverse ℤ-linear maps.

The reverse map is also ZMod(n)-linear when the integer tensor carries its canonical
residue-module action from n-annihilation. The equivalence allows specified integer-module
structures on M,N: uniqueness of the integer action on an additive group identifies them with
repeated addition. Carrier universes are independent, and n=0 is included with ZMod(0)=ℤ.
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
/-- Let n∈ℕ, M a ZMod(n)-module and N any additive commutative group, with independent carrier
universes. For every z∈M⊗_ℤN, n•z=0. Only M needs the residue-module structure; moving repeated
addition into M proves the tensor vanishing. -/
theorem intTensor_nsmul_eq_zero (z : TensorProduct ℤ M N) : n • z = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      rw [← Nat.cast_smul_eq_nsmul ℤ, TensorProduct.smul_tmul']
      rw [Nat.cast_smul_eq_nsmul]
      rw [ZModModule.char_nsmul_eq_zero, zero_tmul]
  | add x y hx hy =>
      rw [nsmul_add, hx, hy, add_zero]

/-- Let n∈ℕ and M,N be ZMod(n)-modules with additive commutative group structures and independent
carrier universes u,v. This ℤ-linear map M⊗_ℤN→M⊗_{ZMod(n)}N sends m⊗_ℤ x to m⊗_{ZMod(n)}x. It
is induced by the bilinear residue tensor map on the underlying additive groups. -/
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

/-- Let n∈ℕ and M,N be ZMod(n)-modules with additive commutative group structures and independent
carrier universes u,v. For m∈M,x∈N, the forward map satisfies f(m⊗_ℤx)=m⊗_{ZMod(n)}x. The same
factor elements are used in the two balanced tensor quotients. -/
@[simp]
theorem intToZMod_tmul (x : M) (y : N) :
    intToZMod n M N (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ZMod n] y :=
  rfl

/-- Let n∈ℕ and M,N be ZMod(n)-modules with additive commutative group structures and independent
carrier universes u,v. Equip M⊗_ℤN with the canonical ZMod(n)-action provided by n-annihilation.
This ZMod(n)-linear map M⊗_{ZMod(n)}N→M⊗_ℤN sends each pure tensor to the integer pure tensor
with the same factors. -/
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

/-- Let n∈ℕ and M,N be ZMod(n)-modules with additive commutative group structures and independent
carrier universes u,v. For m∈M,x∈N, the canonical reverse map sends m⊗_{ZMod(n)}x to m⊗_ℤx. Its
target carries the residue action arising from modulus annihilation. -/
@[simp]
theorem zmodToInt_tmul (x : M) (y : N) :
    zmodToInt n M N (x ⊗ₜ[ZMod n] y) = x ⊗ₜ[ℤ] y :=
  by simp [zmodToInt]

/-- Let n∈ℕ and M,N be ZMod(n)-modules with additive commutative group structures and independent
carrier universes u,v. Forgetting the residue scalar structure on the canonical reverse map
gives this ℤ-linear map M⊗_{ZMod(n)}N→M⊗_ℤN. It has the same additive map and pure-tensor
values. -/
noncomputable def zmodToIntLinear :
    TensorProduct (ZMod n) M N →ₗ[ℤ] TensorProduct ℤ M N :=
  (zmodToInt n M N).toAddMonoidHom.toIntLinearMap

/-- Let n∈ℕ and M,N be ZMod(n)-modules with additive commutative group structures and independent
carrier universes u,v. For m∈M,x∈N, the integer-linear reverse map satisfies
g(m⊗_{ZMod(n)}x)=m⊗_ℤx. The formula retains the factors and their carrier universes. -/
@[simp]
theorem zmodToIntLinear_tmul (x : M) (y : N) :
    zmodToIntLinear n M N (x ⊗ₜ[ZMod n] y) = x ⊗ₜ[ℤ] y := by
  change zmodToInt n M N (x ⊗ₜ[ZMod n] y) = _
  rw [zmodToInt_tmul]

variable [iM : Module ℤ M] [iN : Module ℤ N]

/-- Let n∈ℕ and M,N be ZMod(n)-modules with additive commutative group structures and independent
carrier universes u,v. Allow given integer-module structures on M,N. This ℤ-linear equivalence
M⊗_ℤN≅M⊗_{ZMod(n)}N uses those structures, identified by uniqueness with the canonical integer
actions. Its forward and inverse maps preserve pure tensors, and the modulus may be zero. -/
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

/-- Let n∈ℕ and M,N be ZMod(n)-modules with additive commutative group structures and independent
carrier universes u,v. With any given integer-module structures, the equivalence
e:M⊗_ℤN≅M⊗_{ZMod(n)}N satisfies e(m⊗_ℤx)=m⊗_{ZMod(n)}x for all m,x. Uniqueness of integer scalar
action gives the same comparison. -/
@[simp]
theorem zmodRestrictIntEquiv_apply_tmul (x : M) (y : N) :
    zmodRestrictIntEquiv n M N (x ⊗ₜ[ℤ] y) =
      x ⊗ₜ[ZMod n] y :=
  by
    cases Subsingleton.elim iM (AddCommGroup.toIntModule (M := M))
    cases Subsingleton.elim iN (AddCommGroup.toIntModule (M := N))
    rfl

/-- Let n∈ℕ and M,N be ZMod(n)-modules with additive commutative group structures and independent
carrier universes u,v. With the given integer-module structures, e^{-1}(m⊗_{ZMod(n)}x)=m⊗_ℤx.
This is the inverse formula of the canonical residue-restriction tensor equivalence, including
n=0. -/
@[simp]
theorem zmodRestrictIntEquiv_symm_apply_tmul (x : M) (y : N) :
    (zmodRestrictIntEquiv n M N).symm (x ⊗ₜ[ZMod n] y) =
      x ⊗ₜ[ℤ] y :=
  by
    cases Subsingleton.elim iM (AddCommGroup.toIntModule (M := M))
    cases Subsingleton.elim iN (AddCommGroup.toIntModule (M := N))
    exact zmodToIntLinear_tmul n M N x y

end TensorProduct
