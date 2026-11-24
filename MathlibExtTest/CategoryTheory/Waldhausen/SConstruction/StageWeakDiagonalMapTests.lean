/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalMap

/-!
# Weak-stage diagonal-map consumer tests

Focused same-universe checks for the public `stageWeakDiagonalMap`: its
degree-2 component is the diagonal of the weak-stage nerve map, and its action
on degree-zero `mk₀` and degree-one `mk₁` simplices is induced by the
weak-stage map. No identity/composition restatements.

Nonclaims: no realization, additivity, π₀/K₀ identification, G-theory,
spectra, or Q/S comparison.
-/

open CategoryTheory Limits Simplicial
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalMapTests

variable (C : Type u) [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u) [Category.{v} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D

/-- Degree-2 component is the diagonal of the weak-stage nerve map.

Protects against an index/flip/wide-category mismatch where the diagonal
confuses outer and inner degrees or reindexes through the wrong category. -/
example :
    (stageWeakDiagonalMap C D F).app (Opposite.op ⦋2⦌) =
      ((stageWeakNerveMap C D F).app (Opposite.op ⦋2⦌)).app
        (Opposite.op ⦋2⦌) := rfl

/-- Action on a degree-zero `mk₀` simplex is `mk₀` of the mapped object.

Protects against an object-action mismatch where the diagonal map sends
zero-simplices through the wrong degree or forgets the weak-stage map. -/
example (X : StageWeakCategory C 0) :
    (stageWeakDiagonalMap C D F).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀ ((mapStageWeak C D F 0).obj X) :=
  stageWeakDiagonalMap_app_mk₀ C D F X

/-- Action on a degree-one `mk₁` simplex maps its weak-stage arrow.

Protects the computation used to transport canonical object edges through an
exact-functor diagonal map. -/
example {X Y : StageWeakCategory C 1} (φ : X ⟶ Y) :
    (stageWeakDiagonalMap C D F).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ φ) =
      ComposableArrows.mk₁ ((mapStageWeak C D F 1).map φ) :=
  stageWeakDiagonalMap_app_mk₁ C D F φ

/-- Mapped degree-zero vertex is `mk₀` of the mapped weak-stage zero.

Protects against wiring the diagonal map to the wrong degree or forgetting the
weak-stage map on the zero object. -/
example :
    (stageWeakDiagonalMap C D F).app (Opposite.op ⦋0⦌)
      (stageWeakDiagonalZeroVertex C) =
      ComposableArrows.mk₀ ((mapStageWeak C D F 0).obj ⟨stageZero C⟩) :=
  stageWeakDiagonalMap_zeroVertex C D F

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalMapTests
