/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceFlankingMaps

/-!
# The genuine original flanking functor and inclusion

The same complete native construction preserves actual original
identities and compositions. Its inclusion into the original flagged
necklace is a genuine natural transformation over the same input.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Flanking

open OriginalBead.TerminalFlag

variable {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- Original flanking retains the entire actual identity map. -/
theorem map_id (T : Object K x y q) : map (𝟙 T) = 𝟙 (object T) := by
  apply Hom.ext
  apply SSet.OriginalNecklace.Morphism.ext
  ext i : 3
  apply (embedding T.coefficient).injective
  exact Operators.vertexMap_image (𝟙 T : T ⟶ T).necklaceMap.operator
    (𝟙 T : T ⟶ T).necklaceMap.source (𝟙 T : T ⟶ T).necklaceMap.target
    T.coefficient T.coefficient (𝟙 T : T ⟶ T).flags i

/-- Original flanking retains the whole actual composition, at every selected original vertex. -/
theorem map_comp {T U V : Object K x y q} (f : T ⟶ U) (g : U ⟶ V) :
    map (f ≫ g) = map f ≫ map g := by
  apply Hom.ext
  apply SSet.OriginalNecklace.Morphism.ext
  ext i : 3
  apply (embedding V.coefficient).injective
  calc
    embedding V.coefficient ((selectedOperator (f ≫ g)).toOrderHom i) =
        (f ≫ g).necklaceMap.operator.toOrderHom (embedding T.coefficient i) :=
      Operators.vertexMap_image (f ≫ g).necklaceMap.operator
        (f ≫ g).necklaceMap.source (f ≫ g).necklaceMap.target
        T.coefficient V.coefficient (f ≫ g).flags i
    _ = g.necklaceMap.operator.toOrderHom
        (f.necklaceMap.operator.toOrderHom (embedding T.coefficient i)) := rfl
    _ = g.necklaceMap.operator.toOrderHom
        (embedding U.coefficient ((selectedOperator f).toOrderHom i)) :=
      congrArg g.necklaceMap.operator.toOrderHom
        (Operators.vertexMap_image f.necklaceMap.operator
          f.necklaceMap.source f.necklaceMap.target T.coefficient U.coefficient f.flags i).symm
    _ = embedding V.coefficient
        ((selectedOperator g).toOrderHom ((selectedOperator f).toOrderHom i)) :=
      (Operators.vertexMap_image g.necklaceMap.operator
        g.necklaceMap.source g.necklaceMap.target U.coefficient V.coefficient g.flags
        ((selectedOperator f).toOrderHom i)).symm

/-- The actual original flanking functor on the entire original fixed-scalar category. -/
def functor (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Object K x y q ⥤ Object K x y q where
  obj := object
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The original native subnecklace inclusion is natural for every entire original flagged map. -/
def inclusionTransformation (K : SSet.{u}) (x y : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    functor K x y q ⟶ 𝟭 (Object K x y q) where
  app := inclusion
  naturality _T _U f := inclusion_naturality f

/-- Every actual object of the original flanking functor is flanked by its same original flags. -/
theorem functor_obj_isFlanked (T : Object K x y q) :
    IsFlanked ((functor K x y q).obj T) := object_isFlanked T

/-- The same entire native inclusion is the original natural-transformation component. -/
theorem inclusionTransformation_app (T : Object K x y q) :
    (inclusionTransformation K x y q).app T = inclusion T := rfl

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Flanking
