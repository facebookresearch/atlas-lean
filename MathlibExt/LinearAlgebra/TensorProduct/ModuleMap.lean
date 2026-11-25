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

public import Mathlib.Algebra.Module.Bimodule
public import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Maps for the native tensor-product module action

The module structures are the native `TensorProduct.Algebra.module` values
computed from the original two scalar actions. A ground-linear equivariant
map is linear for their tensor product, and a tensor-product-linear map is
linear for each original action. No module structure is supplied as data.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u a b m n p

namespace TensorProduct.Algebra

variable {k : Type u} [CommSemiring k]
  {A : Type a} {B : Type b} [Semiring A] [Semiring B]
  [Algebra k A] [Algebra k B]
  {M : Type m} {N : Type n}
  [AddCommMonoid M] [AddCommMonoid N]
  [Module k M] [Module k N]
  [Module A M] [Module A N] [Module B M] [Module B N]
  [IsScalarTower k A M] [IsScalarTower k A N]
  [IsScalarTower k B M] [IsScalarTower k B N]
  [SMulCommClass A B M] [SMulCommClass A B N]

/-- Package the original equivariant ground map over the native tensor scalars. -/
def ofLinearMap (f : M →ₗ[k] N)
    (hA : ∀ (a : A) (x : M), f (a • x) = a • f x)
    (hB : ∀ (b : B) (x : M), f (b • x) = b • f x) :
    letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
    letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
    M →ₗ[A ⊗[k] B] N := by
  letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
  letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro z x
  change f (z • x) = z • f x
  induction z using TensorProduct.inductionOn with
  | tmul a b => rw [smul_def, smul_def, hA, hB]
  | add z w hz hw => rw [add_smul, f.map_add, hz, hw, add_smul]

@[simp]
theorem ofLinearMap_apply (f : M →ₗ[k] N) (hA hB) (x : M) :
    ofLinearMap (k := k) (A := A) (B := B) f hA hB x = f x := rfl

/-- A tensor-module morphism preserves the original first scalar action. -/
def toLeftLinearMap
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
      M →ₗ[A ⊗[k] B] N) : M →ₗ[A] N := by
  letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
  letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro a x
  simpa only [RingHom.id_apply, smul_def, one_smul] using f.map_smul (a ⊗ₜ[k] (1 : B)) x

/-- A tensor-module morphism preserves the original second scalar action. -/
def toRightLinearMap
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
      M →ₗ[A ⊗[k] B] N) : M →ₗ[B] N := by
  letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
  letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro b x
  simpa only [RingHom.id_apply, smul_def, one_smul] using f.map_smul ((1 : A) ⊗ₜ[k] b) x

@[simp]
theorem toLeftLinearMap_apply
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
      M →ₗ[A ⊗[k] B] N) (x : M) : toLeftLinearMap f x = f x := rfl

@[simp]
theorem toRightLinearMap_apply
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
      M →ₗ[A ⊗[k] B] N) (x : M) : toRightLinearMap f x = f x := rfl

/-- Returning through the first action retains the original ground dictionary. -/
@[simp]
theorem toLeftLinearMap_ofLinearMap (f : M →ₗ[k] N) (hA hB) :
    (toLeftLinearMap (k := k) (A := A) (B := B)
      (ofLinearMap (k := k) (A := A) (B := B) f hA hB)).restrictScalars k = f := by
  apply LinearMap.ext
  intro x
  rfl

/-- Returning through the second action also retains the same ground map. -/
@[simp]
theorem toRightLinearMap_ofLinearMap (f : M →ₗ[k] N) (hA hB) :
    (toRightLinearMap (k := k) (A := A) (B := B)
      (ofLinearMap (k := k) (A := A) (B := B) f hA hB)).restrictScalars k = f := by
  apply LinearMap.ext
  intro x
  rfl

end TensorProduct.Algebra
