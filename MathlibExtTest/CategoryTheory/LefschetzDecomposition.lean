/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.LefschetzDecomposition

/-! # Tests for Lefschetz morphisms

The zeroth power of a degree-two morphism is the identity, the next power composes with it, and
cohomology objects lie in the heart.
-/

namespace MathlibExtTest.CategoryTheory.LefschetzDecomposition

open _root_.CategoryTheory _root_.CategoryTheory.Triangulated
open _root_.MathlibExt.CategoryTheory.LefschetzDecomposition

universe v u

section Iterates

variable {C : Type u} [Category.{v} C] [HasShift C ℤ] {K : C} (η : K ⟶ K⟦(2 : ℤ)⟧)

example : lefschetzPower η 0 = ShiftedHom.mk₀ _ (by simp) (𝟙 K) := rfl

example (i : ℕ) :
    lefschetzPower η (i + 1) = ShiftedHom.comp (lefschetzPower η i) η (by omega) := rfl

end Iterates

section Cohomology

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ (j : ℤ), (shiftFunctor C j).Additive] [Pretriangulated C] [IsTriangulated C]

example (t : TStructure C) (j : ℤ) (K : C) : t.heart ((cohomologyFunctor t j).obj K) :=
  cohomologyFunctor_obj_mem_heart t j K

/-- Hard Lefschetz asks that every Lefschetz morphism be an isomorphism. -/
example (t : TStructure C) {K : C} (η : K ⟶ K⟦(2 : ℤ)⟧) (h : HasHardLefschetz t η) (i : ℕ) :
    IsIso (lefschetzMorphism t η i) := h i

end Cohomology

end MathlibExtTest.CategoryTheory.LefschetzDecomposition
