/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.Triangulated.GrothendieckGroup

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open MathlibExt.CategoryTheory.TriangulatedGrothendieck
open scoped ZeroObject

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

-- The zero object has class zero, and a shift by one negates the class.
example : classOf C (0 : C) = 0 := classOf_zero

example (X : C) : classOf C (X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) = classOf C X := by
  rw [classOf_shift_one, classOf_shift_one, neg_neg]

-- Direct sums: the split triangle `X → X ⊞ Y → Y → X⟦1⟧` gives additivity.
example (X Y : C) : classOf C (X ⊞ Y) = classOf C X + classOf C Y :=
  classOf_triangle (binaryBiproductTriangle_distinguished X Y)

-- An additive invariant descends to `K0` and is computed on classes.
example {G : Type*} [AddCommGroup G] (a : AdditiveInvariant (C := C) G) (X : C) :
    a.desc (classOf C X) = a.value X :=
  a.desc_classOf X

-- The zero invariant descends to a map vanishing on every class.
example (X : C) : (⟨fun _ ↦ (0 : ℤ), fun _ ↦ rfl, fun _ _ ↦ by simp⟩ :
    AdditiveInvariant (C := C) ℤ).desc (classOf C X) = 0 :=
  AdditiveInvariant.desc_classOf _ X
