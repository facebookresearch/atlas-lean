/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Unit data assembled from the raw completion and baseline replacement constructions.
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCompletionRaw
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkBaselineReplacement
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalObjectComponentEssentialSurjectivity
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero
import Mathlib.CategoryTheory.Whiskering

/-!
# Coaugmentation of the diagonal power construction

The coefficient-power diagonal defines a functorial construction followed by baseline
replacement. Its coaugmentation is the raw diagonal unit followed by the baseline unit, its
targets are Reedy fibrant, and its components induce surjections on simplicial components in
every outer degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Cartesian

namespace SimplicialSpace.RezkCompletionData

/-- Native functorial assembly of the SAME original coefficient powers, flip and diagonal. -/
def rawFunctor : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  (MonoidalClosed.internalHom (C := SimplicialSpace.{u})).flip ⋙
    (Functor.whiskeringLeft SimplexCategoryᵒᵖ SimplicialSpaceᵒᵖ SimplicialSpace).obj
      RezkCompletionRaw.coefficient.op ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SimplicialSpace
      (SimplicialObject SSet)).obj forget ⋙
    flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ SSet ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ (SimplicialObject SSet) SSet).obj
      SSet.simplicialDiagonalFunctor ⋙ ofSimplicialObject

/-- Every original object is the exact previously constructed raw diagonal. -/
theorem rawFunctor_obj (W : SimplicialSpace.{u}) :
    rawFunctor.obj W = RezkCompletionRaw.rawCompletion W := rfl

/-- Every original map is the exact previously constructed whole raw diagonal map. -/
theorem rawFunctor_map {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    rawFunctor.map f = RezkCompletionRaw.rawCompletionMap f := rfl

/-- Apply the ONE fixed unlocalized baseline replacement to the SAME raw diagonal functor. -/
def completion : SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  rawFunctor ⋙ RezkBaselineReplacement.replacement

/-- The completion coaugmentation is the literal original raw unit followed by its baseline unit. -/
def unit : 𝟭 SimplicialSpace.{u} ⟶ completion where
  app W := RezkCompletionRaw.rawCompletionUnit W ≫
    RezkBaselineReplacement.unit.app (RezkCompletionRaw.rawCompletion W)
  naturality W V f := by
    change f ≫ (RezkCompletionRaw.rawCompletionUnit V ≫
      RezkBaselineReplacement.unit.app (RezkCompletionRaw.rawCompletion V)) =
      (RezkCompletionRaw.rawCompletionUnit W ≫
        RezkBaselineReplacement.unit.app (RezkCompletionRaw.rawCompletion W)) ≫
          RezkBaselineReplacement.replacement.map (RezkCompletionRaw.rawCompletionMap f)
    rw [← Category.assoc, RezkCompletionRaw.rawCompletionUnit_naturality,
      Category.assoc, RezkBaselineReplacement.unit_naturality, ← Category.assoc]

/-- The original composite unit is retained as an actual equation on every W. -/
theorem unit_app (W : SimplicialSpace.{u}) :
    unit.app W = RezkCompletionRaw.rawCompletionUnit W ≫
      RezkBaselineReplacement.unit.app (RezkCompletionRaw.rawCompletion W) := rfl

/-- Naturality includes every original map, rather than a selected coefficient vertex. -/
theorem unit_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    f ≫ unit.app V = unit.app W ≫ completion.map f := unit.naturality f

/-- The actual unlocalized terminal factorization makes the SAME target Reedy fibrant. -/
theorem completion_fibrant (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant (completion.obj W) :=
  RezkBaselineReplacement.replacement_fibrant (RezkCompletionRaw.rawCompletion W)

/-- ALL original outer rows have component coverage, including zero and empty endpoints.
No Segal, completeness, mapping-fibre or whole-raw weak-equivalence premise is supplied. -/
theorem unit_components_surjective (W : SimplicialSpace.{u}) (n : ℕ) :
    Function.Surjective (SSet.mapπ₀ ((unit.app W).hom.app (op ⦋n⦌))) := by
  let uN := (RezkCompletionRaw.rawCompletionUnit W).hom.app (op ⦋n⦌)
  let rhoN := (RezkBaselineReplacement.unit.app
    (RezkCompletionRaw.rawCompletion W)).hom.app (op ⦋n⦌)
  have hu : Function.Surjective (SSet.mapπ₀ uN) :=
    SSet.mapPiZero_surjective_of_surjective_vertices uN
      (RezkCompletionRaw.rawCompletionUnit_innerZero_bijective W (op ⦋n⦌)).2
  have hrho : Function.Bijective (SSet.mapπ₀ rhoN) :=
    SSet.realizationWeakEquivalences.bijective_mapπ₀
      (RezkBaselineReplacement.unit_components (RezkCompletionRaw.rawCompletion W) n).2
  change Function.Surjective (SSet.mapπ₀ (uN ≫ rhoN))
  intro q
  obtain ⟨b, hb⟩ := hrho.2 q
  obtain ⟨a, ha⟩ := hu b
  refine ⟨a, ?_⟩
  rw [SSet.mapπ₀_comp_apply, ha, hb]

end SimplicialSpace.RezkCompletionData
