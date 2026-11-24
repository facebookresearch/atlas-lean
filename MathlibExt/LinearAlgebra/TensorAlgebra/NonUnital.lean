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
# The actual augmentation kernel of the tensor algebra

The existing scalar retraction is the augmentation sending vector generators
to zero. Its genuine kernel inherits the original tensor multiplication and
has the original degree-one linear inclusion. These are the strict carrier
prerequisites for the positive tensor-power and universal nonunital maps.
Those further identifications and maps are separate constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe uR uV

namespace TensorAlgebra

variable (R : Type uR) [CommSemiring R]
variable (V : Type uV) [AddCommMonoid V] [Module R V]

/-- The genuine scalar-zero kernel of the existing tensor augmentation. -/
def augmentationKernel : NonUnitalSubalgebra R (TensorAlgebra R V) :=
  NonUnitalSubalgebra.comap (TensorAlgebra.algebraMapInv.toNonUnitalAlgHom)
    (⊥ : NonUnitalSubalgebra R R)

/-- Membership uses the actual scalar component, with no chosen degree model. -/
@[simp]
theorem mem_augmentationKernel (x : TensorAlgebra R V) :
    x ∈ augmentationKernel R V ↔ TensorAlgebra.algebraMapInv x = 0 :=
  NonUnitalAlgebra.mem_bot

/-- The original vector generators have zero augmentation. -/
@[simp]
theorem algebraMapInv_ι (v : V) :
    TensorAlgebra.algebraMapInv (TensorAlgebra.ι R v) = 0 := by
  simp only [TensorAlgebra.algebraMapInv, TensorAlgebra.lift_ι_apply, LinearMap.zero_apply]

/-- Every original vector belongs to the genuine augmentation kernel. -/
theorem ι_mem_augmentationKernel (v : V) :
    TensorAlgebra.ι R v ∈ augmentationKernel R V :=
  (mem_augmentationKernel R V _).2 (algebraMapInv_ι R V v)

/-- The augmentation kernel meets the original scalar summand only at zero. -/
theorem algebraMap_mem_augmentationKernel_iff (r : R) :
    algebraMap R (TensorAlgebra R V) r ∈ augmentationKernel R V ↔ r = 0 := by
  rw [mem_augmentationKernel, TensorAlgebra.algebraMap_leftInverse V r]

/-- Over nonzero scalars, the scalar unit is absent from the positive carrier. -/
theorem one_not_mem_augmentationKernel [Nontrivial R] :
    (1 : TensorAlgebra R V) ∉ augmentationKernel R V := by
  rw [mem_augmentationKernel]
  simpa only [map_one] using (one_ne_zero : (1 : R) ≠ 0)

end TensorAlgebra

/-- The nonunital tensor carrier is the actual augmentation kernel. -/
abbrev NonUnitalTensorAlgebra (R : Type uR) (V : Type uV)
    [CommSemiring R] [AddCommMonoid V] [Module R V] :=
  ↥(TensorAlgebra.augmentationKernel R V)

namespace NonUnitalTensorAlgebra

variable (R : Type uR) [CommSemiring R]
variable (V : Type uV) [AddCommMonoid V] [Module R V]

/-- Include the original nonunital carrier in its actual unital tensor algebra. -/
def inclusion : NonUnitalTensorAlgebra R V →ₙₐ[R] TensorAlgebra R V :=
  NonUnitalSubalgebraClass.subtype (TensorAlgebra.augmentationKernel R V)

@[simp]
theorem inclusion_apply (x : NonUnitalTensorAlgebra R V) : inclusion R V x = x.1 := rfl

theorem inclusion_injective : Function.Injective (inclusion R V) := Subtype.val_injective

/-- The actual included tensor has zero scalar augmentation. -/
@[simp]
theorem algebraMapInv_inclusion (x : NonUnitalTensorAlgebra R V) :
    TensorAlgebra.algebraMapInv (x : TensorAlgebra R V) = 0 :=
  (TensorAlgebra.mem_augmentationKernel R V _).1 x.property

/-- The degree-one inclusion has the original vector generator as its literal value. -/
def ι : V →ₗ[R] NonUnitalTensorAlgebra R V :=
  (TensorAlgebra.ι R).codRestrict (TensorAlgebra.augmentationKernel R V).toSubmodule
    (TensorAlgebra.ι_mem_augmentationKernel R V)

@[simp]
theorem inclusion_ι (v : V) :
    (ι R V v : TensorAlgebra R V) = TensorAlgebra.ι R v := rfl

theorem ι_injective : Function.Injective (ι R V) := by
  intro v w h
  exact (TensorAlgebra.ι_inj R v w).1 (congrArg (inclusion R V) h)

/-- The original tensor multiplication is unchanged by the literal inclusion. -/
theorem inclusion_mul (x y : NonUnitalTensorAlgebra R V) :
    inclusion R V (x * y) = inclusion R V x * inclusion R V y :=
  (inclusion R V).map_mul x y

end NonUnitalTensorAlgebra
