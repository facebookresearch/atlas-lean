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

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakCategory
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZero

/-!
# Stage weak-equivalence category consumer tests

Focused public checks for `StageWeakCategory` and `reindexStageWeak`: degree-zero stage
object identity with `Stage`, faithful inclusion object and map behavior,
restriction along a face map, and strict identity with contravariant composition.
No simplicial object, nerve, realization, or comparison content.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakCategoryTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Degree-zero stage object projects to the Stage zero fixture, also through inclusion. -/
noncomputable example :
    (⟨stageZero C⟩ : StageWeakCategory C 0).obj = stageZero C ∧
      (stageWeakInclusion C 0).obj ⟨stageZero C⟩ = stageZero C :=
  ⟨rfl, stageWeakInclusion_obj C 0 _⟩

/-- Faithful inclusion preserves maps and is faithful. -/
example (n : ℕ) (X Y : StageWeakCategory C n) (φ : X ⟶ Y) :
    (stageWeakInclusion C n).map φ = φ.hom ∧ (stageWeakInclusion C n).Faithful :=
  ⟨stageWeakInclusion_map C n φ, inferInstance⟩

/-- Restriction along the face map computes through `reindexStage`. -/
example (X Y : StageWeakCategory C 1) (φ : X ⟶ Y) :
    (reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).obj X =
        ⟨(reindexStage (SimplexCategory.δ (0 : Fin 2))).obj X.obj⟩ ∧
      (reindexStageWeak C (SimplexCategory.δ (0 : Fin 2))).map φ =
        ⟨(reindexStage (SimplexCategory.δ (0 : Fin 2))).map φ.hom,
          stageWeak_of_reindexStage C (SimplexCategory.δ (0 : Fin 2))
            φ.hom φ.property⟩ :=
  ⟨reindexStageWeak_obj C _ X, reindexStageWeak_map C _ φ⟩

/-- Identity and contravariant composition hold strictly. -/
example (a b c : SimplexCategory) (f : a ⟶ b) (g : b ⟶ c) :
    reindexStageWeak C (𝟙 a) = 𝟭 (StageWeakCategory C a.len) ∧
      reindexStageWeak C (f ≫ g) = reindexStageWeak C g ⋙ reindexStageWeak C f :=
  ⟨reindexStageWeak_id C a, reindexStageWeak_comp C f g⟩

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakCategoryTests
