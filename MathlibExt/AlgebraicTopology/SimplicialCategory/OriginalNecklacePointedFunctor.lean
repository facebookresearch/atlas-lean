/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceJoyalInclusion
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceInputSourceFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHomFunctor

/-!
# The full original native necklace pointed functor

The same two original native vertices form the literal boundary map.
Every original native map and every original input over the supplied
source retain their entire simplicial maps and both endpoint equations.
No coefficient, fibrancy or weak outcome restricts this functor.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

open OriginalNecklaceHom SSet.OriginalNecklace

/-- Every same whole original native map is pointed at its actual original source and target vertices. -/
def pointedNativeMap {T U : Data} (f : T ⟶ U) :
    SSet.OriginalNecklace.pointedObject.{u} T ⟶ SSet.OriginalNecklace.pointedObject.{u} U :=
  Under.homMk f.map
    ((SSet.boundaryOneMap_naturality f.map (OriginalNecklaceHom.sourceVertex T)
      (OriginalNecklaceHom.targetVertex T)).trans
        (congrArg₂ SSet.boundaryOneMap (nativeMap_source f) (nativeMap_target f)))

/-- The full original native necklace functor to the same original endpoint-fixed category. -/
def pointedNativeFunctor : Data ⥤ OriginalPointed.Category.{u} where
  obj := SSet.OriginalNecklace.pointedObject
  map := pointedNativeMap
  map_id T := by
    apply Under.UnderMorphism.ext
    exact Morphism.map_id T
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact Morphism.map_comp f g

/-- The whole original native input with the same exact two endpoint boundary equations. -/
def pointedInputMap {K : SSet.{u}} {x y : K _⦋0⦌} (T : Object K x y) :
    SSet.OriginalNecklace.pointedObject.{u} T.necklace ⟶ Under.mk (SSet.boundaryOneMap x y) :=
  Under.homMk T.input
    ((SSet.boundaryOneMap_naturality T.input (OriginalNecklaceHom.sourceVertex T.necklace)
      (OriginalNecklaceHom.targetVertex T.necklace)).trans
        (congrArg₂ SSet.boundaryOneMap
          ((SSet.yonedaEquiv_comp T.necklace.source T.input).symm.trans T.source_eq)
          ((SSet.yonedaEquiv_comp T.necklace.target T.input).symm.trans T.target_eq)))

/-- The full original native inputs form their same original pointed Over category functor. -/
def pointedInputFunctor (K : SSet.{u}) (x y : K _⦋0⦌) :
    Object K x y ⥤ Over (Under.mk (SSet.boundaryOneMap x y)) where
  obj T := Over.mk (pointedInputMap T)
  map {T U} f := Over.homMk (pointedNativeMap f.necklaceMap) (Under.UnderMorphism.ext f.over)
  map_id T := by
    apply Over.OverMorphism.ext
    exact pointedNativeFunctor.map_id T.necklace
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact pointedNativeFunctor.map_comp f.necklaceMap g.necklaceMap

/-- Every same full original pointed-input object retains the literal original input simplicial map. -/
theorem pointedInputFunctor_input (K : SSet.{u}) (x y : K _⦋0⦌) (T : Object K x y) :
    (((pointedInputFunctor K x y).obj T).hom).right = T.input := rfl

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
