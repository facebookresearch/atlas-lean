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

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.Algebra.Algebra.NonUnitalSubalgebra

/-!
# The augmentation kernel of a tensor algebra

Let R be a commutative semiring and V an R-module whose additive structure
is a commutative monoid, with independent ring and module universes.
The tensor algebra T_R(V) has an augmentation ε : T_R(V) → R characterized
by ε(ι(v)) = 0 and ε(r) = r on the scalar summand.

The nonunital tensor algebra here is ker ε as a nonunital R-subalgebra of
T_R(V), with addition, scalar multiplication and multiplication inherited
from T_R(V). The linear inclusion V → ker ε sends v to its tensor generator.
The kernel contains a scalar r only when r = 0, and excludes 1 when R
is nontrivial.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe uR uV

namespace TensorAlgebra

variable (R : Type uR) [CommSemiring R]
variable (V : Type uV) [AddCommMonoid V] [Module R V]

/-- For a commutative semiring R and an R-module V with additive
commutative monoid structure, this is the nonunital R-subalgebra ker ε
of the tensor algebra T_R(V), where ε sends every generator ι(v) to zero
and is the identity on the scalar copy of R. -/
def augmentationKernel : NonUnitalSubalgebra R (TensorAlgebra R V) :=
  NonUnitalSubalgebra.comap (TensorAlgebra.algebraMapInv.toNonUnitalAlgHom)
    (⊥ : NonUnitalSubalgebra R R)

/-- For a commutative semiring R, an R-module V with additive
commutative monoid structure, and x ∈ T_R(V), membership in the
augmentation kernel is equivalent to ε(x) = 0, where
ε : T_R(V) → R is the augmentation killing V. -/
@[simp]
theorem mem_augmentationKernel (x : TensorAlgebra R V) :
    x ∈ augmentationKernel R V ↔ TensorAlgebra.algebraMapInv x = 0 :=
  NonUnitalAlgebra.mem_bot

/-- For a commutative semiring R, an R-module V with additive
commutative monoid structure, and v ∈ V, the tensor generator ι(v)
has zero augmentation: ε(ι(v)) = 0. -/
@[simp]
theorem algebraMapInv_ι (v : V) :
    TensorAlgebra.algebraMapInv (TensorAlgebra.ι R v) = 0 := by
  simp only [TensorAlgebra.algebraMapInv, TensorAlgebra.lift_ι_apply, LinearMap.zero_apply]

/-- For a commutative semiring R, an R-module V with additive
commutative monoid structure, and v ∈ V, the degree-one tensor
generator ι(v) belongs to ker(ε : T_R(V) → R). -/
theorem ι_mem_augmentationKernel (v : V) :
    TensorAlgebra.ι R v ∈ augmentationKernel R V :=
  (mem_augmentationKernel R V _).2 (algebraMapInv_ι R V v)

/-- For a commutative semiring R, an R-module V with additive
commutative monoid structure, and r ∈ R, the scalar tensor r · 1
belongs to ker(ε : T_R(V) → R) if and only if r = 0.
This uses that the augmentation restricts to the identity on R. -/
theorem algebraMap_mem_augmentationKernel_iff (r : R) :
    algebraMap R (TensorAlgebra R V) r ∈ augmentationKernel R V ↔ r = 0 := by
  rw [mem_augmentationKernel, TensorAlgebra.algebraMap_leftInverse V r]

/-- For a nontrivial commutative semiring R and an R-module V with
additive commutative monoid structure, the tensor-algebra unit 1
does not belong to ker(ε : T_R(V) → R), since ε(1) = 1 ≠ 0. -/
theorem one_not_mem_augmentationKernel [Nontrivial R] :
    (1 : TensorAlgebra R V) ∉ augmentationKernel R V := by
  rw [mem_augmentationKernel]
  simpa only [map_one] using (one_ne_zero : (1 : R) ≠ 0)

end TensorAlgebra

/-- For a commutative semiring R and an R-module V with additive
commutative monoid structure, NonUnitalTensorAlgebra R V is the carrier
of ker(ε : T_R(V) → R). Its nonunital semiring and R-module operations
are inherited from the tensor algebra. R and V may have independent universes. -/
abbrev NonUnitalTensorAlgebra (R : Type uR) (V : Type uV)
    [CommSemiring R] [AddCommMonoid V] [Module R V] :=
  ↥(TensorAlgebra.augmentationKernel R V)

namespace NonUnitalTensorAlgebra

variable (R : Type uR) [CommSemiring R]
variable (V : Type uV) [AddCommMonoid V] [Module R V]

/-- For a commutative semiring R and an R-module V with additive
commutative monoid structure, this is the nonunital R-algebra
homomorphism ker(ε : T_R(V) → R) → T_R(V) given by inclusion.
It preserves addition, R-scalars and multiplication. -/
def inclusion : NonUnitalTensorAlgebra R V →ₙₐ[R] TensorAlgebra R V :=
  NonUnitalSubalgebraClass.subtype (TensorAlgebra.augmentationKernel R V)

@[simp]
theorem inclusion_apply (x : NonUnitalTensorAlgebra R V) : inclusion R V x = x.1 := rfl

theorem inclusion_injective : Function.Injective (inclusion R V) := Subtype.val_injective

/-- For a commutative semiring R, an R-module V with additive
commutative monoid structure, and x ∈ NonUnitalTensorAlgebra R V,
its image in T_R(V) has augmentation zero. -/
@[simp]
theorem algebraMapInv_inclusion (x : NonUnitalTensorAlgebra R V) :
    TensorAlgebra.algebraMapInv (x : TensorAlgebra R V) = 0 :=
  (TensorAlgebra.mem_augmentationKernel R V _).1 x.property

/-- For a commutative semiring R and an R-module V with additive
commutative monoid structure, this R-linear map
V → NonUnitalTensorAlgebra R V sends v to the tensor generator ι(v),
regarded as an element of the augmentation kernel. -/
def ι : V →ₗ[R] NonUnitalTensorAlgebra R V :=
  (TensorAlgebra.ι R).codRestrict (TensorAlgebra.augmentationKernel R V).toSubmodule
    (TensorAlgebra.ι_mem_augmentationKernel R V)

@[simp]
theorem inclusion_ι (v : V) :
    (ι R V v : TensorAlgebra R V) = TensorAlgebra.ι R v := rfl

theorem ι_injective : Function.Injective (ι R V) := by
  intro v w h
  exact (TensorAlgebra.ι_inj R v w).1 (congrArg (inclusion R V) h)

/-- For a commutative semiring R, an R-module V with additive
commutative monoid structure, and x, y ∈ NonUnitalTensorAlgebra R V,
inclusion into T_R(V) satisfies inclusion(xy) = inclusion(x) inclusion(y).
Thus the kernel uses the tensor algebra's multiplication in the same order. -/
theorem inclusion_mul (x y : NonUnitalTensorAlgebra R V) :
    inclusion R V (x * y) = inclusion R V x * inclusion R V y :=
  (inclusion R V).map_mul x y

end NonUnitalTensorAlgebra
