/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedFibrantGadgets
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedReplacementOver

/-!
# Full original gadget inputs over the same original pointed target

Every full original pointed gadget map to the target is retained.
The canonical original replacement and an actual target unit retraction
produce the original full input replacement functor. Both natural unit
comparisons preserve the exact original input triangles and all maps.
-/

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The full original gadget inclusion retains every complete original pointed object and map. -/
def gadgetInclusion : MappingGadgets.{u} ⥤ Category.{u} := ObjectProperty.ι _

/-- The full original fibrant-gadget inclusion into the original pointed category. -/
def fibrantGadgetFullInclusion : FibrantMappingGadgets.{u} ⥤ Category.{u} :=
  fibrantGadgetInclusion ⋙ gadgetInclusion

/-- Every full original fibrant gadget input is its same original gadget input. -/
def fibrantInputInclusion (K : Category.{u}) :
    CostructuredArrow fibrantGadgetFullInclusion K ⥤ CostructuredArrow gadgetInclusion K :=
  CostructuredArrow.pre fibrantGadgetInclusion gadgetInclusion K

/-- The same actual canonical replacement of every original full gadget input. -/
def gadgetInputReplacement (K : Category.{u}) (r : replacementFunctor.obj K ⟶ K) :
    CostructuredArrow gadgetInclusion K ⥤ CostructuredArrow fibrantGadgetFullInclusion K where
  obj X := CostructuredArrow.mk (Y := gadgetReplacementFunctor.obj X.left)
    (replacementFunctor.map X.hom ≫ r)
  map {X Y} f := CostructuredArrow.homMk (gadgetReplacementFunctor.map f.left) (by
    change replacementFunctor.map f.left.hom ≫ (replacementFunctor.map Y.hom ≫ r) =
      replacementFunctor.map X.hom ≫ r
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ r) ((replacementFunctor.map_comp f.left.hom Y.hom).symm.trans
        (congrArg replacementFunctor.map (CostructuredArrow.w f)))))
  map_id X := by
    apply CostructuredArrow.hom_ext
    exact gadgetReplacementFunctor.map_id X.left
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact gadgetReplacementFunctor.map_comp f.left g.left

/-- The same original unit gives a full natural transformation on the original gadget inputs over the same target. -/
def gadgetInputReplacementUnit (K : Category.{u}) (r : replacementFunctor.obj K ⟶ K)
    (hr : replacementUnit.app K ≫ r = 𝟙 K) :
    𝟭 (CostructuredArrow gadgetInclusion K) ⟶ gadgetInputReplacement K r ⋙ fibrantInputInclusion K where
  app X := CostructuredArrow.homMk (gadgetReplacementUnit.app X.left) (by
    change replacementUnit.app X.left.obj ≫ (replacementFunctor.map X.hom ≫ r) = X.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ r) (replacementUnit.naturality X.hom).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun f => X.hom ≫ f) hr).trans (Category.comp_id _)))))
  naturality X Y f := by
    apply CostructuredArrow.hom_ext
    exact gadgetReplacementUnit.naturality f.left

end CategoryTheory.CoherentRealization.OriginalPointed
