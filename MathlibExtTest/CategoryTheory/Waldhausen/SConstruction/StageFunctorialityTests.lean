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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageFunctoriality
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageNatIso
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Exact-stage functoriality consumer tests

Focused generic checks for `mapStage`/`mapStageWeak`: postcomposition
evaluation, reindex commutation along a face map, weak restriction
projection, and inclusion commutation; plus `StageNatIso`
coverage via `mapStageNatIso`/`mapStageWeakNatIso` including heterogeneous
natural-isomorphism transport. No concrete category, no new
instance, no nerve, realization, or K/G-theory content.
-/

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageFunctorialityTests

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]
variable (E : Type u₃) [Category.{v₃} E] [Preadditive E] [Limits.HasZeroObject E]
  [HasBinaryBiproducts E] [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]
/- Second exact functor `C ⥤ D` for heterogeneous `StageNatIso` tests.
Named `H` to avoid shadowing the existing `G : D ⥤ E`; `e : F ≅ H` is the
heterogeneous natural-isomorphism input. -/
variable (H : C ⥤ D) [H.Additive] [Functor.IsExact H]
variable (e : F ≅ H)

local instance : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
local instance : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E

/-- Postcomposed stage evaluates through `F`: a variance check that fails if
`mapStage` does not postcompose objects and maps. -/
example (n : ℕ) (X Y : Stage C n) (φ : X ⟶ Y) (a : Ar n) :
    (eval D n a).obj ((mapStage C D F n).obj X) = F.obj ((eval C n a).obj X) ∧
      (eval D n a).map ((mapStage C D F n).map φ) =
        F.map ((eval C n a).map φ) :=
  ⟨rfl, rfl⟩

/-- Postcomposition commutes with reindexing along a nonidentity face map. -/
example :
    (reindexStage (C := C) (SimplexCategory.δ (0 : Fin 2)) ⋙ mapStage C D F 0) =
      (mapStage C D F 1 ⋙
        reindexStage (C := D) (SimplexCategory.δ (0 : Fin 2))) :=
  mapStage_reindex C D F _

/-- Weak restriction projects through `mapStage`: a restriction check that fails
if `mapStageWeak` does not restrict `mapStage` on objects and maps. -/
example (n : ℕ) (X Y : StageWeakCategory C n) (φ : X ⟶ Y) :
    (stageWeakInclusion D n).obj ((mapStageWeak C D F n).obj X) =
        (mapStage C D F n).obj X.obj ∧
      (stageWeakInclusion D n).map ((mapStageWeak C D F n).map φ) =
        (mapStage C D F n).map φ.hom :=
  ⟨rfl, rfl⟩

/-- Inclusion commutes with exact-stage functoriality as functors. -/
example (n : ℕ) :
    mapStageWeak C D F n ⋙ stageWeakInclusion D n =
      stageWeakInclusion C n ⋙ mapStage C D F n :=
  mapStageWeak_inclusion C D F n

/-- Identity and composition-agreement for `mapStage` seen on `eval`
components: the identity functor leaves every evaluation unchanged, and the
composite functor agrees componentwise with staged postcomposition. -/
example (n : ℕ) (X Y : Stage C n) (φ : X ⟶ Y) (a : Ar n) :
    (eval C n a).obj ((mapStage C C (𝟭 C) n).obj X) = (eval C n a).obj X ∧
      (eval C n a).map ((mapStage C C (𝟭 C) n).map φ) = (eval C n a).map φ ∧
        (eval E n a).obj ((mapStage C E (F ⋙ G) n).obj X) =
          (eval E n a).obj
            ((mapStage D E G n).obj ((mapStage C D F n).obj X)) ∧
        (eval E n a).map ((mapStage C E (F ⋙ G) n).map φ) =
          (eval E n a).map
            ((mapStage D E G n).map ((mapStage C D F n).map φ)) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Identity and composition-agreement for `mapStageWeak` seen through the
weak inclusion: the identity leaves every included component unchanged, and
the composite agrees componentwise with staged restriction. -/
example (n : ℕ) (X Y : StageWeakCategory C n) (φ : X ⟶ Y) :
    (stageWeakInclusion C n).obj ((mapStageWeak C C (𝟭 C) n).obj X) =
        (stageWeakInclusion C n).obj X ∧
      (stageWeakInclusion C n).map ((mapStageWeak C C (𝟭 C) n).map φ) =
        (stageWeakInclusion C n).map φ ∧
        (stageWeakInclusion E n).obj ((mapStageWeak C E (F ⋙ G) n).obj X) =
          (stageWeakInclusion E n).obj
            ((mapStageWeak D E G n).obj ((mapStageWeak C D F n).obj X)) ∧
        (stageWeakInclusion E n).map ((mapStageWeak C E (F ⋙ G) n).map φ) =
          (stageWeakInclusion E n).map
            ((mapStageWeak D E G n).map ((mapStageWeak C D F n).map φ)) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Natural-iso transport hom component evaluates through the identity: the
`Iso.refl` stage iso acts as the identity at each `Ar n` object. -/
example (n : ℕ) (X : Stage C n) (a : Ar n) :
    (eval C n a).map
      (((mapStageNatIso C C (𝟭 C) (𝟭 C) (Iso.refl (𝟭 C)) n).hom).app X) =
      𝟙 ((eval C n a).obj X) :=
  rfl

/-- Natural-iso transport inv component orientation: the inverse projection
likewise acts as the identity at each `Ar n` object. -/
example (n : ℕ) (X : Stage C n) (a : Ar n) :
    (eval C n a).map
      (((mapStageNatIso C C (𝟭 C) (𝟭 C) (Iso.refl (𝟭 C)) n).inv).app X) =
      𝟙 ((eval C n a).obj X) :=
  rfl

/-- Weak natural-iso transport lies over the stage iso: both hom and inv
projections agree with the underlying `mapStageNatIso` components. -/
example (n : ℕ) (X : StageWeakCategory C n) :
    (stageWeakInclusion C n).map
        (((mapStageWeakNatIso C C (𝟭 C) (𝟭 C) (Iso.refl (𝟭 C)) n).hom).app X) =
        ((mapStageNatIso C C (𝟭 C) (𝟭 C) (Iso.refl (𝟭 C)) n).hom).app X.obj ∧
      (stageWeakInclusion C n).map
        (((mapStageWeakNatIso C C (𝟭 C) (𝟭 C) (Iso.refl (𝟭 C)) n).inv).app X) =
        ((mapStageNatIso C C (𝟭 C) (𝟭 C) (Iso.refl (𝟭 C)) n).inv).app X.obj :=
  ⟨rfl, rfl⟩

/-- Heterogeneous natural-iso transport hom component: the stage iso over
`e : F ≅ H` evaluates through `e.hom` at each `Ar n` object. -/
example (n : ℕ) (X : Stage C n) (a : Ar n) :
    (eval D n a).map
      (((mapStageNatIso C D F H e n).hom).app X) =
      e.hom.app ((eval C n a).obj X) :=
  rfl

/-- Heterogeneous natural-iso transport inv component orientation. -/
example (n : ℕ) (X : Stage C n) (a : Ar n) :
    (eval D n a).map
      (((mapStageNatIso C D F H e n).inv).app X) =
      e.inv.app ((eval C n a).obj X) :=
  rfl

/-- Heterogeneous weak transport lies over the stage iso. -/
example (n : ℕ) (X : StageWeakCategory C n) :
    (stageWeakInclusion D n).map
        (((mapStageWeakNatIso C D F H e n).hom).app X) =
        ((mapStageNatIso C D F H e n).hom).app X.obj ∧
      (stageWeakInclusion D n).map
        (((mapStageWeakNatIso C D F H e n).inv).app X) =
        ((mapStageNatIso C D F H e n).inv).app X.obj :=
  ⟨rfl, rfl⟩

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageFunctorialityTests
