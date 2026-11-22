/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.CardinalSubarrowPresentation
import MathlibExt.CategoryTheory.Subfunctor.TransfiniteUnion
import Mathlib.CategoryTheory.Limits.Comma

/-!
# Colimits of original bounded subarrow chains

The cocone and its universal property use the literal original endpoint
unions. Its two inclusion components preserve every original site, simplex
and point. Only the final point-bound theorem needs regularity of the bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits
open SimplicialPresheaf.KanWeakInterpolation

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D]
  {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)
  {J : Type u} [LinearOrder J] (γ : Cardinal.{u})
  (a : J → cardinalSubarrowIndex f γ) (ha : Monotone a)

/-- The actual whole-Arrow cocone to the original indexed union. -/
def cardinalSubarrowChainCocone :
    Cocone (ha.functor ⋙ cardinalSubarrowDiagram f γ) where
  pt := Subdiagram.arrow f (Subdiagram.indexedUnion f (fun j => (a j).val))
  ι :=
    { app j := Subdiagram.map f
        (Subdiagram.le_indexedUnion f (fun j => (a j).val) j)
      naturality := by
        intro j k h
        ext d n x <;> rfl }

/-- Every cocone leg is the literal original subdiagram inclusion square. -/
theorem cardinalSubarrowChainCocone_ι (j : J) :
    (cardinalSubarrowChainCocone f γ a ha).ι.app j =
      Subdiagram.map f (Subdiagram.le_indexedUnion f (fun j => (a j).val) j) := rfl

/-- The source leg keeps the same point at the same original site and degree. -/
theorem cardinalSubarrowChainCocone_left_val (j : J) (d : Dᵒᵖ)
    (n : SimplexCategoryᵒᵖ)
    (x : (((ha.functor ⋙ cardinalSubarrowDiagram f γ).obj j).left.obj d).obj n) :
    ((((cardinalSubarrowChainCocone f γ a ha).ι.app j).left.app d).app n x).val =
      x.val := rfl

/-- The target leg keeps the same point at the same original site and degree. -/
theorem cardinalSubarrowChainCocone_right_val (j : J) (d : Dᵒᵖ)
    (n : SimplexCategoryᵒᵖ)
    (x : (((ha.functor ⋙ cardinalSubarrowDiagram f γ).obj j).right.obj d).obj n) :
    ((((cardinalSubarrowChainCocone f γ a ha).ι.app j).right.app d).app n x).val =
      x.val := rfl

/-- Public pointwise subfunctor union colimits give the original source colimit. -/
def cardinalSubarrowChainLeftIsColimit :
    IsColimit (Arrow.leftFunc.mapCocone (cardinalSubarrowChainCocone f γ a ha)) := by
  apply evaluationJointlyReflectsColimits
  intro d
  let U : J → Subfunctor (X.obj d) := fun j => ((a j).val.row d).left (f.app d)
  have hU : Monotone U := fun _ _ h => (ha h d).1
  change IsColimit (Subfunctor.chainUnionCocone U hU)
  exact Subfunctor.isColimitChainUnionCocone U hU

/-- Public pointwise subfunctor union colimits give the original target colimit. -/
def cardinalSubarrowChainRightIsColimit :
    IsColimit (Arrow.rightFunc.mapCocone (cardinalSubarrowChainCocone f γ a ha)) := by
  apply evaluationJointlyReflectsColimits
  intro d
  let U : J → Subfunctor (Y.obj d) := fun j => ((a j).val.row d).right (f.app d)
  have hU : Monotone U := fun _ _ h => (ha h d).2
  change IsColimit (Subfunctor.chainUnionCocone U hU)
  exact Subfunctor.isColimitChainUnionCocone U hU

/-- Native Arrow reflection gives the whole original colimit and descendant square. -/
def cardinalSubarrowChainIsColimit :
    IsColimit (cardinalSubarrowChainCocone f γ a ha) :=
  Comma.fstSndJointlyReflectColimit
    (cardinalSubarrowChainLeftIsColimit f γ a ha)
    (cardinalSubarrowChainRightIsColimit f γ a ha)

omit [LinearOrder J] in
/-- A genuinely small indexed family bounds both original union endpoint point types. -/
theorem cardinalSubarrowChainUnion_pointBound [Fact γ.IsRegular]
    (hJ : HasCardinalLT J γ) :
    HasCardinalLT
        (originalTotalPoints
          (Subdiagram.arrow f (Subdiagram.indexedUnion f (fun j => (a j).val))).left) γ ∧
      HasCardinalLT
        (originalTotalPoints
          (Subdiagram.arrow f (Subdiagram.indexedUnion f (fun j => (a j).val))).right) γ := by
  let : Small.{u} J := hJ.small
  let U := cardinalSubarrowUnion f γ a hJ
  have hU : U.val = Subdiagram.indexedUnion f (fun j => (a j).val) := by
    change Subdiagram.indexedUnion f
      (fun j : Shrink.{u} J => (a ((equivShrink.{u} J).symm j)).val) =
        Subdiagram.indexedUnion f (fun j => (a j).val)
    apply Subdiagram.ext
    funext d
    apply Subtype.ext
    apply Prod.ext
    · change (⨆ j : Shrink.{u} J,
          ((a ((equivShrink.{u} J).symm j)).val.row d).left (f.app d)) =
        ⨆ j : J, ((a j).val.row d).left (f.app d)
      exact (equivShrink.{u} J).symm.iSup_comp
        (g := fun j : J => (((a j).val.row d).left (f.app d) : (X.obj d).Subcomplex))
    · change (⨆ j : Shrink.{u} J,
          ((a ((equivShrink.{u} J).symm j)).val.row d).right (f.app d)) =
        ⨆ j : J, ((a j).val.row d).right (f.app d)
      exact (equivShrink.{u} J).symm.iSup_comp
        (g := fun j : J => (((a j).val.row d).right (f.app d) : (Y.obj d).Subcomplex))
  rw [← hU]
  exact U.property

end SimplicialPresheaf
