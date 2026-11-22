/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedMappingGadgets
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceCommaInput

/-!
# Every same full original native necklace is a genuine mapping gadget

The actual original native inclusion is categorical weak by the full
first-crossing pairing. Both original endpoints read back to the same
ordinal simplex. This legitimate source comparison supplies both
independent actual gadget point properties without assuming the raw
right-Q comparison.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalNecklaceInput

open SSet.OriginalNecklace

/-- The same whole original native necklace gives genuine ordinal source data with its original endpoints. -/
def nativeOrdinalComparison (T : Data) : OriginalPointed.OrdinalComparison (pointedNativeFunctor.{u}.obj T) where
  dimension := T.dimension
  map := (complex T.joints).ι
  categorical := inclusion_categoricalEquivalence T
  source := by
    have h : OriginalPointed.source (pointedNativeFunctor.{u}.obj T) = T.source :=
      (SSet.boundary_ι_one_boundaryOneMap _ _).trans
        ((SSet.yonedaEquiv_symm_zero _).symm.trans (Equiv.symm_apply_apply SSet.yonedaEquiv T.source))
    exact (congrArg (fun f => f ≫ (complex T.joints).ι) h).trans (vertexMap_ι T.joints 0)
  target := by
    have h : OriginalPointed.target (pointedNativeFunctor.{u}.obj T) = T.target :=
      (SSet.boundary_ι_zero_boundaryOneMap _ _).trans
        ((SSet.yonedaEquiv_symm_zero _).symm.trans (Equiv.symm_apply_apply SSet.yonedaEquiv T.target))
    exact (congrArg (fun f => f ≫ (complex T.joints).ι) h).trans (vertexMap_ι T.joints (Fin.last T.dimension))

/-- Every same full original native necklace belongs to the actual independent mapping-gadget class. -/
theorem native_mappingGadget (T : Data) : OriginalPointed.mappingGadgetProperty (pointedNativeFunctor.{u}.obj T) :=
  OriginalPointed.mappingGadgetProperty_of_ordinal _ (nativeOrdinalComparison T)

/-- The full original native necklace functor into the genuine full original pointed mapping-gadget category. -/
def nativeGadgetFunctor : Data ⥤ OriginalPointed.MappingGadgets.{u} where
  obj T := ⟨pointedNativeFunctor.obj T, native_mappingGadget T⟩
  map f := ObjectProperty.homMk (pointedNativeFunctor.map f)
  map_id T := by
    apply ObjectProperty.hom_ext
    exact pointedNativeFunctor.map_id T
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact pointedNativeFunctor.map_comp f g

end CategoryTheory.CoherentRealization.OriginalNecklaceInput
