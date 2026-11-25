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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwoExtraction

/-!
# Stage-two extraction consumer tests

Focused public-API checks for actual `stageTwoExtraction`: object legs recover
the central horiz/vert maps and morphism apps recover the interval components
encoding the two naturality squares with correct orientation. No helper API,
equivalence, reindexing, simplicial object, nerve, realization, K/G-theory,
or Q/S comparison.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageTwoExtractionTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Extraction object legs recover the central horiz/vert maps. -/
example (A : Stage C 2) :
    ComposableArrows.map' ((CofiberSequenceCategory.forget C).obj
      ((stageTwoExtraction C).obj A)) 0 1 =
      A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)) ∧
    ComposableArrows.map' ((CofiberSequenceCategory.forget C).obj
      ((stageTwoExtraction C).obj A)) 1 2 =
      A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)) :=
  ⟨stageTwoExtraction_map'_zero_one C A, stageTwoExtraction_map'_one_two C A⟩

/-- Extraction morphism apps recover interval components for both squares. -/
example {A B : Stage C 2} (φ : A ⟶ B) :
    ComposableArrows.app' ((CofiberSequenceCategory.forget C).map
      ((stageTwoExtraction C).map φ)) 0 =
      φ.hom.app (interval (0 : Fin 3) 1 (by decide)) ∧
    ComposableArrows.app' ((CofiberSequenceCategory.forget C).map
      ((stageTwoExtraction C).map φ)) 1 =
      φ.hom.app (interval (0 : Fin 3) 2 (by decide)) ∧
    ComposableArrows.app' ((CofiberSequenceCategory.forget C).map
      ((stageTwoExtraction C).map φ)) 2 =
      φ.hom.app (interval (1 : Fin 3) 2 (by decide)) :=
  ⟨stageTwoExtraction_app_zero C φ, stageTwoExtraction_app_one C φ,
    stageTwoExtraction_app_two C φ⟩

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageTwoExtractionTests
