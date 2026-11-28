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
# Maps for commuting tensor-scalar actions

Let k be a commutative semiring and A,B semiring k-algebras, not necessarily commutative.
Compatible commuting A- and B-actions on a k-semimodule M give an A⊗_kB-module action
(a⊗b)•x=a•(b•x).

A k-linear map preserving both endpoint actions is linear over A⊗_kB. Conversely tensor
linearity restricts along a↦a⊗1 and b↦1⊗b to linearity for each action. The conversions retain
the same functions, and restricting either endpoint map back to k recovers the given k-linear
map. Scalar and carrier universes are independent.
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

/-- Let k be a commutative semiring, A,B possibly noncommutative semiring k-algebras, and M,N
additive commutative monoids with compatible k,A,B-module structures. Assume the A- and
B-actions commute on both modules. All scalar and carrier universes are independent. For
k-linear f:M→N with f(a•x)=a•f(x) and f(b•x)=b•f(x), this is the A⊗_kB-linear map with function
f for the action (a⊗b)•x=a•(b•x). -/
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

/-- Let k be a commutative semiring, A,B possibly noncommutative semiring k-algebras, and M,N
additive commutative monoids with compatible k,A,B-module structures. Assume the A- and
B-actions commute on both modules. All scalar and carrier universes are independent. If f is
k-linear and preserves the A- and B-actions, its constructed A⊗_kB-linear map sends x to f(x)
for every x∈M. -/
@[simp]
theorem ofLinearMap_apply (f : M →ₗ[k] N) (hA hB) (x : M) :
    ofLinearMap (k := k) (A := A) (B := B) f hA hB x = f x := rfl

/-- Let k be a commutative semiring, A,B possibly noncommutative semiring k-algebras, and M,N
additive commutative monoids with compatible k,A,B-module structures. Assume the A- and
B-actions commute on both modules. All scalar and carrier universes are independent. An
A⊗_kB-linear f:M→N for the derived tensor actions gives an A-linear map with the same function.
Equivariance at a⊗1 gives f(a•x)=a•f(x). -/
def toLeftLinearMap
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
      M →ₗ[A ⊗[k] B] N) : M →ₗ[A] N := by
  letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
  letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro a x
  simpa only [RingHom.id_apply, smul_def, one_smul] using f.map_smul (a ⊗ₜ[k] (1 : B)) x

/-- Let k be a commutative semiring, A,B possibly noncommutative semiring k-algebras, and M,N
additive commutative monoids with compatible k,A,B-module structures. Assume the A- and
B-actions commute on both modules. All scalar and carrier universes are independent. An
A⊗_kB-linear f:M→N gives a B-linear map with the same function. The tensor scalar 1⊗b supplies
f(b•x)=b•f(x). -/
def toRightLinearMap
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
      M →ₗ[A ⊗[k] B] N) : M →ₗ[B] N := by
  letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
  letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
  refine { toFun := f, map_add' := f.map_add, map_smul' := ?_ }
  intro b x
  simpa only [RingHom.id_apply, smul_def, one_smul] using f.map_smul ((1 : A) ⊗ₜ[k] b) x

/-- Let k be a commutative semiring, A,B possibly noncommutative semiring k-algebras, and M,N
additive commutative monoids with compatible k,A,B-module structures. Assume the A- and
B-actions commute on both modules. All scalar and carrier universes are independent. For
tensor-linear f and x∈M, the restricted A-linear map has value f(x). It uses the given endpoint
actions. -/
@[simp]
theorem toLeftLinearMap_apply
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
      M →ₗ[A ⊗[k] B] N) (x : M) : toLeftLinearMap f x = f x := rfl

/-- Let k be a commutative semiring, A,B possibly noncommutative semiring k-algebras, and M,N
additive commutative monoids with compatible k,A,B-module structures. Assume the A- and
B-actions commute on both modules. All scalar and carrier universes are independent. For
tensor-linear f and x∈M, the restricted B-linear map has value f(x), on the same carriers. -/
@[simp]
theorem toRightLinearMap_apply
    (f : letI : Module (A ⊗[k] B) M := TensorProduct.Algebra.module
      letI : Module (A ⊗[k] B) N := TensorProduct.Algebra.module
      M →ₗ[A ⊗[k] B] N) (x : M) : toRightLinearMap f x = f x := rfl

/-- Let k be a commutative semiring, A,B possibly noncommutative semiring k-algebras, and M,N
additive commutative monoids with compatible k,A,B-module structures. Assume the A- and
B-actions commute on both modules. All scalar and carrier universes are independent. For
k-linear f preserving both actions, construct its tensor-linear map, restrict to A, then
restrict scalars along k→A. The resulting k-linear map is f. -/
@[simp]
theorem toLeftLinearMap_ofLinearMap (f : M →ₗ[k] N) (hA hB) :
    (toLeftLinearMap (k := k) (A := A) (B := B)
      (ofLinearMap (k := k) (A := A) (B := B) f hA hB)).restrictScalars k = f := by
  apply LinearMap.ext
  intro x
  rfl

/-- Let k be a commutative semiring, A,B possibly noncommutative semiring k-algebras, and M,N
additive commutative monoids with compatible k,A,B-module structures. Assume the A- and
B-actions commute on both modules. All scalar and carrier universes are independent. For
k-linear f preserving both actions, construct its tensor-linear map, restrict to B, then
restrict scalars along k→B. The resulting k-linear map equals f. -/
@[simp]
theorem toRightLinearMap_ofLinearMap (f : M →ₗ[k] N) (hA hB) :
    (toRightLinearMap (k := k) (A := A) (B := B)
      (ofLinearMap (k := k) (A := A) (B := B) f hA hB)).restrictScalars k = f := by
  apply LinearMap.ext
  intro x
  rfl

end TensorProduct.Algebra
