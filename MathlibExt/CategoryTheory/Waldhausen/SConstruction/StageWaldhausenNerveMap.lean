/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenFunctoriality
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonal
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.SimplicialStageWeak

/-!
# Simplicial weak-Stage maps for Waldhausen-exact functors

An explicitly Waldhausen-exact functor induces compatible maps of weak Stage
categories, their nerves, and their simplicial diagonals.  The simplicial
objects must live in the same object and hom universes; the underlying
finite-degree `mapStageWeak` remains available in mixed universes.

This file asserts no realization weak equivalence, Approximation theorem,
comma contraction, K-space comparison, or spectrum result.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace CategoryTheory.Functor.IsWaldhausenExact

variable {C D E : Type u}
  [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [WaldhausenCategoryWithoutGluing C] [WaldhausenCategoryWithoutGluing D]
      [WaldhausenCategoryWithoutGluing E]
variable {F : C ⥤ D} {G : D ⥤ E}

open Waldhausen.SConstruction

/-- The simplicial map on weak Stage categories induced by an explicitly
Waldhausen-exact functor. -/
def simplicialStageMapWeak (hF : F.IsWaldhausenExact) :
    simplicialStageWeak C ⟶ simplicialStageWeak D where
  app a := (hF.mapStageWeak a.unop.len).toCatHom
  naturality {a b} f := by
    apply Cat.ext
    exact hF.mapStageWeak_reindex f.unop

@[simp]
theorem simplicialStageMapWeak_app (hF : F.IsWaldhausenExact)
    (a : SimplexCategoryᵒᵖ) :
    hF.simplicialStageMapWeak.app a =
      (hF.mapStageWeak a.unop.len).toCatHom :=
  rfl

@[simp]
theorem simplicialStageMapWeak_id :
    (Functor.IsWaldhausenExact.id (C := C)).simplicialStageMapWeak =
      𝟙 (simplicialStageWeak C) := by
  ext a
  exact mapStageWeak_id C a.unop.len

@[simp]
theorem simplicialStageMapWeak_comp
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) :
    (hF.comp hG).simplicialStageMapWeak =
      hF.simplicialStageMapWeak ≫ hG.simplicialStageMapWeak := by
  ext a
  exact hF.mapStageWeak_comp hG a.unop.len

/-- The induced map between the simplicial nerves of weak Stage categories. -/
def stageWeakNerveMap (hF : F.IsWaldhausenExact) :
    stageWeakNerve C ⟶ stageWeakNerve D :=
  Functor.whiskerRight hF.simplicialStageMapWeak nerveFunctor

@[simp]
theorem stageWeakNerveMap_app (hF : F.IsWaldhausenExact)
    (a : SimplexCategoryᵒᵖ) :
    hF.stageWeakNerveMap.app a =
      nerveFunctor.map (hF.mapStageWeak a.unop.len).toCatHom :=
  rfl

/-- The induced map between weak-Stage simplicial diagonals. -/
def stageWeakDiagonalMap (hF : F.IsWaldhausenExact) :
    stageWeakDiagonal C ⟶ stageWeakDiagonal D :=
  SSet.simplicialDiagonalFunctor.map hF.stageWeakNerveMap

end CategoryTheory.Functor.IsWaldhausenExact

end
