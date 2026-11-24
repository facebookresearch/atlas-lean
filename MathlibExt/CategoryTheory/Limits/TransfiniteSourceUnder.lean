/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The SAME transfinite composition lifted under its original source

The native bottom isomorphism supplies the complete original root maps
and actual under-source diagram. The SAME terminal cocone and original
factorization equation give its genuine full under-category colimit.
Category objects, Homs and stage indices have independent universes;
no universe restriction is imposed on any later cell occurrence family.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.TransfiniteCompositionOfShape
variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : C} {f : X ⟶ Y} (c : TransfiniteCompositionOfShape J f)

/-- The SAME original source-to-stage map through the genuine native bottom isomorphism. -/
def sourceMapToStage (j : J) : X ⟶ c.F.obj j :=
  c.isoBot.inv ≫ c.F.map (homOfLE bot_le)

/-- All original stage maps retain the complete source equation. -/
theorem sourceMapToStage_map {j k : J} (g : j ⟶ k) :
    sourceMapToStage c j ≫ c.F.map g = sourceMapToStage c k := by
  change (c.isoBot.inv ≫ c.F.map (homOfLE bot_le)) ≫ c.F.map g =
    c.isoBot.inv ≫ c.F.map (homOfLE bot_le)
  rw [Category.assoc, ← c.F.map_comp]
  rfl

/-- The SAME original root maps form the actual natural transformation into every full stage. -/
def sourceStageMap : (Functor.const J).obj X ⟶ c.F where
  app := sourceMapToStage c
  naturality _j _k g := (Category.id_comp _).trans (sourceMapToStage_map c g).symm

/-- Lift the entire SAME original stage diagram under its actual original source. -/
def sourceUnderDiagram : J ⥤ Under X := Under.lift c.F (sourceStageMap c)

/-- Every original terminal cocone leg retains the SAME full original composite map. -/
theorem sourceMapToStage_incl (j : J) :
    sourceMapToStage c j ≫ c.incl.app j = f := by
  change (c.isoBot.inv ≫ c.F.map (homOfLE bot_le)) ≫ c.incl.app j = f
  rw [Category.assoc, (Cocone.mk Y c.incl).w (homOfLE bot_le)]
  exact c.fac

/-- The SAME whole original terminal cocone with its actual maps lifted under the original
source. -/
def sourceUnderCocone : Cocone (sourceUnderDiagram c) :=
  Under.liftCocone c.F (sourceStageMap c) (Cocone.mk Y c.incl) f (sourceMapToStage_incl c)

/-- The SAME original native terminal universal property proves the full actual under-source
colimit. -/
def sourceUnderIsColimit : IsColimit (sourceUnderCocone c) :=
  Under.isColimitLiftCocone c.F (sourceStageMap c) (Cocone.mk Y c.incl) f
    (sourceMapToStage_incl c) c.isColimit

/-- The actual original first under-source map is a genuine isomorphism, in every
independent stage universe. -/
instance sourceUnderDiagram_bot_isIso : IsIso ((sourceUnderDiagram c).obj ⊥).hom := by
  change IsIso (c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : J) ≤ ⊥)))
  have h : homOfLE (bot_le : (⊥ : J) ≤ ⊥) = 𝟙 (⊥ : J) := Subsingleton.elim _ _
  rw [h, Functor.map_id, Category.comp_id]
  exact c.isoBot.isIso_inv

end CategoryTheory.TransfiniteCompositionOfShape
