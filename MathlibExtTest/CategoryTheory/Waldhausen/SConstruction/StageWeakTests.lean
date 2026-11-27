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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeak
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Pointwise stage weak-equivalence consumer tests

Downstream checks for `stageWeak`/`IsStageWeak`/`mem_stageWeak`,
`stageWeak_respectsIso`, and `stageWeak_of_reindexStage`: pointwise membership,
identity/composition closure, iso transport, and preservation under a nonidentity
simplex map. No `WideSubcategory` bundle, nerve, realization, or K/G-theory content.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Membership in `stageWeak` is pointwise weak equivalence. -/
example (n : ℕ) (X Y : Stage C n) (f : X ⟶ Y) :
    IsStageWeak C n f ↔ ∀ a, IsWeakEquivalence ((eval C n a).map f) :=
  mem_stageWeak C n

/-- Identity and composition closure for `stageWeak`. -/
example (n : ℕ) (X Y Z : Stage C n) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : stageWeak C n f) (hg : stageWeak C n g) :
    stageWeak C n (𝟙 X) ∧ stageWeak C n (f ≫ g) :=
  ⟨MorphismProperty.id_mem _ _, MorphismProperty.comp_mem _ _ _ hf hg⟩

/-- Iso transport for `stageWeak` via `stageWeak_respectsIso`. -/
example (n : ℕ) (X Y Z W : Stage C n) (e₁ : X ⟶ Y) [IsIso e₁] (f : Y ⟶ Z)
    (hf : stageWeak C n f) (e₂ : Z ⟶ W) [IsIso e₂] :
    stageWeak C n (e₁ ≫ f) ∧ stageWeak C n (f ≫ e₂) :=
  ⟨MorphismProperty.RespectsIso.precomp _ e₁ f hf,
    MorphismProperty.RespectsIso.postcomp _ e₂ f hf⟩

/-- Reindexing along a nonidentity constant simplex map preserves `stageWeak`
(domain and codomain differ, hence the map is nonidentity). -/
example (X Y : Stage C 1) (φ : X ⟶ Y) (h : stageWeak C 1 φ) :
    stageWeak C 0
      ((reindexStage
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0)).map φ) :=
  stageWeak_of_reindexStage C
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1) 0) φ h

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageWeakTests
