/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklacePointedFunctor

/-!
# All original pointed native maps are precisely the original necklace arrows

The same full original endpoint maps are read from the actual one-boundary
faces. The existing canonical native map recognition gives the inverse
of every full pointed Hom map, retaining the whole original simplex map.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

open OriginalNecklaceHom SSet.OriginalNecklace

private theorem pointedNative_source {T U : Data}
    (g : SSet.OriginalNecklace.pointedObject.{u} T ⟶ SSet.OriginalNecklace.pointedObject.{u} U) :
    T.source ≫ g.right = U.source := by
  have h := congrArg (fun f => SSet.boundary.ι (1 : Fin 2) ≫ f) (Under.w g)
  have hs : SSet.const (OriginalNecklaceHom.sourceVertex T) ≫ g.right =
      SSet.const (OriginalNecklaceHom.sourceVertex U) :=
    (congrArg (fun f => f ≫ g.right) (SSet.boundary_ι_one_boundaryOneMap
      (OriginalNecklaceHom.sourceVertex T) (OriginalNecklaceHom.targetVertex T))).symm.trans
      ((Category.assoc _ _ _).trans
        (h.trans (SSet.boundary_ι_one_boundaryOneMap
          (OriginalNecklaceHom.sourceVertex U) (OriginalNecklaceHom.targetVertex U))))
  exact (congrArg (fun f => f ≫ g.right)
    ((SSet.yonedaEquiv_symm_zero (OriginalNecklaceHom.sourceVertex T)).symm.trans
      (Equiv.symm_apply_apply SSet.yonedaEquiv T.source))).symm.trans
        (hs.trans
          ((SSet.yonedaEquiv_symm_zero (OriginalNecklaceHom.sourceVertex U)).symm.trans
            (Equiv.symm_apply_apply SSet.yonedaEquiv U.source)))

private theorem pointedNative_target {T U : Data}
    (g : SSet.OriginalNecklace.pointedObject.{u} T ⟶ SSet.OriginalNecklace.pointedObject.{u} U) :
    T.target ≫ g.right = U.target := by
  have h := congrArg (fun f => SSet.boundary.ι (0 : Fin 2) ≫ f) (Under.w g)
  have hs : SSet.const (OriginalNecklaceHom.targetVertex T) ≫ g.right =
      SSet.const (OriginalNecklaceHom.targetVertex U) :=
    (congrArg (fun f => f ≫ g.right) (SSet.boundary_ι_zero_boundaryOneMap
      (OriginalNecklaceHom.sourceVertex T) (OriginalNecklaceHom.targetVertex T))).symm.trans
      ((Category.assoc _ _ _).trans
        (h.trans (SSet.boundary_ι_zero_boundaryOneMap
          (OriginalNecklaceHom.sourceVertex U) (OriginalNecklaceHom.targetVertex U))))
  exact (congrArg (fun f => f ≫ g.right)
    ((SSet.yonedaEquiv_symm_zero (OriginalNecklaceHom.targetVertex T)).symm.trans
      (Equiv.symm_apply_apply SSet.yonedaEquiv T.target))).symm.trans
        (hs.trans
          ((SSet.yonedaEquiv_symm_zero (OriginalNecklaceHom.targetVertex U)).symm.trans
            (Equiv.symm_apply_apply SSet.yonedaEquiv U.target)))

/-- The full original pointed necklace functor is genuinely fully faithful on all original arrows. -/
def pointedNativeFullyFaithful : pointedNativeFunctor.{u}.FullyFaithful where
  preimage g := Morphism.ofMap g.right (pointedNative_source g) (pointedNative_target g)
  map_preimage g :=
    Under.UnderMorphism.ext (Morphism.ofMap_map g.right (pointedNative_source g) (pointedNative_target g))
  preimage_map g := Morphism.map_injective
    (Morphism.ofMap_map g.map (pointedNative_source (pointedNativeMap g)) (pointedNative_target (pointedNativeMap g)))

/-- Every same original native input arrow retains its entire actual pointed Over map injectively. -/
def pointedInputFullyFaithful (K : SSet.{u}) (x y : K _⦋0⦌) :
    (pointedInputFunctor K x y).FullyFaithful where
  preimage g :=
    { necklaceMap := pointedNativeFullyFaithful.preimage g.left
      over := (congrArg (fun f => f ≫ _) (Morphism.ofMap_map g.left.right
        (pointedNative_source g.left) (pointedNative_target g.left))).trans
          (congrArg Under.Hom.right (Over.w g)) }
  map_preimage g := by
    apply Over.OverMorphism.ext
    exact pointedNativeFullyFaithful.map_preimage g.left
  preimage_map g := Hom.ext (pointedNativeFullyFaithful.preimage_map g.necklaceMap)

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
