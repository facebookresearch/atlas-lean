/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceScalarDiagram

/-!
# Whole original flagged-nerve source naturality

Every original source simplicial map retains the same whole necklace,
all supplied coefficient flags, and the actual original endpoint images.
The complete scalar/source square and original nerve diagram maps
commute.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

variable {K L M : SSet.{u}} {x y : K _⦋0⦌} {q r : SimplexCategoryᵒᵖ}

/-- The entire original input map under the same source map, retaining all original flags. -/
def sourceObject (f : K ⟶ L) (T : Object K x y q) :
    Object L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) q where
  necklace := T.necklace
  input := T.input ≫ f
  source_eq :=
    ((congrArg SSet.yonedaEquiv (Category.assoc T.necklace.source T.input f).symm).trans
      (SSet.yonedaEquiv_comp (T.necklace.source ≫ T.input) f)).trans
        (congrArg (f.app (op ⦋0⦌)) T.source_eq)
  target_eq :=
    ((congrArg SSet.yonedaEquiv (Category.assoc T.necklace.target T.input f).symm).trans
      (SSet.yonedaEquiv_comp (T.necklace.target ≫ T.input) f)).trans
        (congrArg (f.app (op ⦋0⦌)) T.target_eq)
  coefficient := T.coefficient
  joints := T.joints

/-- The same whole original flagged map under the original source simplicial map. -/
def sourceHom (f : K ⟶ L) {T U : Object K x y q} (g : T ⟶ U) :
    sourceObject f T ⟶ sourceObject f U where
  necklaceMap := g.necklaceMap
  over := (Category.assoc g.necklaceMap.map U.input f).symm.trans
    (congrArg (fun a => a ≫ f) g.over)
  flags := g.flags

/-- The original source functor on the entire original flagged category. -/
def sourceFunctor (f : K ⟶ L) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Object K x y q ⥤ Object L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) q where
  obj := sourceObject f
  map := sourceHom f
  map_id _T := Hom.ext rfl
  map_comp _g _h := Hom.ext rfl

/-- The complete original source identity is the actual flagged-category identity. -/
theorem sourceFunctor_id (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    sourceFunctor (𝟙 K) x y q = 𝟭 (Object K x y q) := rfl

/-- The complete original source composition follows the same two original input maps. -/
theorem sourceFunctor_comp (f : K ⟶ L) (g : L ⟶ M) (x y : K _⦋0⦌)
    (q : SimplexCategoryᵒᵖ) :
    sourceFunctor (f ≫ g) x y q =
      sourceFunctor f x y q ⋙
        sourceFunctor g (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) q := rfl

/-- Every original scalar operator commutes with the complete same original source functor. -/
theorem scalar_source (f : K ⟶ L) (x y : K _⦋0⦌) (θ : q ⟶ r) :
    scalarFunctor K x y θ ⋙ sourceFunctor f x y r =
      sourceFunctor f x y q ⋙
        scalarFunctor L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) θ := rfl

/-- The same original source map on the entire original bisimplicial flagged nerve. -/
def sourceNerveDiagramMap (f : K ⟶ L) (x y : K _⦋0⦌) :
    scalarNerveDiagram K x y ⟶
      scalarNerveDiagram L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) where
  app q := nerveMap (sourceFunctor f x y q)
  naturality q r θ := by
    have h := congrArg (fun F : Object K x y q ⥤
        Object L (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) r => nerveMap F)
      (scalar_source f x y θ)
    exact h

/-- The complete original source map retains the same native necklace. -/
theorem sourceObject_necklace (f : K ⟶ L) (T : Object K x y q) :
    (sourceObject f T).necklace = T.necklace := rfl

/-- The complete original source map retains the literal original input composition. -/
theorem sourceObject_input (f : K ⟶ L) (T : Object K x y q) :
    (sourceObject f T).input = T.input ≫ f := rfl

/-- The complete original source map retains every original coefficient flag unchanged. -/
theorem sourceObject_coefficient (f : K ⟶ L) (T : Object K x y q) :
    (sourceObject f T).coefficient = T.coefficient := rfl

/-- The original source map on the scalar diagram is the same whole original functor nerve map. -/
theorem sourceNerveDiagramMap_app (f : K ⟶ L) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (sourceNerveDiagramMap f x y).app q = nerveMap (sourceFunctor f x y q) := rfl

/-- The complete original source identity is the same nerve-diagram identity. -/
theorem sourceNerveDiagramMap_id (K : SSet.{u}) (x y : K _⦋0⦌) :
    sourceNerveDiagramMap (𝟙 K) x y = 𝟙 (scalarNerveDiagram K x y) := rfl

/-- The complete original source composition is the same composition of whole nerve-diagram maps. -/
theorem sourceNerveDiagramMap_comp (f : K ⟶ L) (g : L ⟶ M) (x y : K _⦋0⦌) :
    sourceNerveDiagramMap (f ≫ g) x y =
      sourceNerveDiagramMap f x y ≫
        sourceNerveDiagramMap g (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y) := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
