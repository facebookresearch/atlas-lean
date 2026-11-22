/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedGadgetReplacement
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceMappingGadgets

/-!
# The same full original fibrant gadget category

The full subcategory keeps precisely actual quasicategory carriers
among the original mapping gadgets. The same canonical original
replacement functor and original unit define the fibrant replacement
and both full natural comparisons. No source maps or Homs are discarded.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- Actual original quasicategory carriers among the same full original gadgets. -/
def fibrantGadgetProperty (X : MappingGadgets.{u}) : Prop := SSet.Quasicategory X.obj.right

/-- The same full original fibrant mapping gadgets, retaining all full original pointed arrows. -/
abbrev FibrantMappingGadgets := ObjectProperty.FullSubcategory fibrantGadgetProperty.{u}

/-- The full original inclusion of genuine fibrant gadgets into the same original gadget category. -/
def fibrantGadgetInclusion : FibrantMappingGadgets.{u} ⥤ MappingGadgets.{u} :=
  ObjectProperty.ι _

/-- The same actual canonical original replacement gives a functor to genuinely fibrant original gadgets. -/
def gadgetReplacementFunctor : MappingGadgets.{u} ⥤ FibrantMappingGadgets.{u} where
  obj X := ⟨⟨replacementFunctor.obj X.obj, mappingGadgetProperty_replacement X.obj X.property⟩,
    replacement_quasicategory X.obj⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk (replacementFunctor.map f.hom))
  map_id X := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact replacementFunctor.map_id X.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact replacementFunctor.map_comp f.hom g.hom

/-- The same complete original unit gives the full natural original gadget replacement comparison. -/
def gadgetReplacementUnit : 𝟭 MappingGadgets.{u} ⟶ gadgetReplacementFunctor ⋙ fibrantGadgetInclusion where
  app X := ObjectProperty.homMk (replacementUnit.app X.obj)
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    exact replacementUnit.naturality f.hom

/-- The same original unit retains the full natural comparison on the genuine fibrant subcategory as well. -/
def fibrantGadgetReplacementUnit : 𝟭 FibrantMappingGadgets.{u} ⟶ fibrantGadgetInclusion ⋙ gadgetReplacementFunctor where
  app X := ObjectProperty.homMk (ObjectProperty.homMk (replacementUnit.app X.obj.obj))
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact replacementUnit.naturality f.hom.hom

end CategoryTheory.CoherentRealization.OriginalPointed
