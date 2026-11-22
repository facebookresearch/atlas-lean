/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedOrdinalRawPoint
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedOrdinalReplacementPoint
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontReedyBothPoints
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalNecklaceInputNervePoint

/-!
# The original independent pointed mapping gadget properties

The full original pointed objects carry two separate actual point-map
properties: their SAME raw coherent endpoint Hom, and the SAME right
mapping object of their canonical original quasicategory replacement.
Neither property assumes the desired original raw comparison. Every
actual ordinal-source object is admitted by the proved original maps.
The original native necklaces and actual generated Reedy degrees keep
all their full original objects and morphisms.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalPointed

/-- The actual original right-mapping object of the same full pointed replacement. -/
def replacementRightMapping (X : Category.{u}) : SSet.{u} :=
  SSet.mappingSpaceRight (replacementFunctor.obj X).right (source (replacementFunctor.obj X))
    (target (replacementFunctor.obj X))

/-- The two independent actual original point-map properties defining the full original mapping-gadget category. -/
def mappingGadgetProperty (X : Category.{u}) : Prop :=
  SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (homObject X)) ∧
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from (replacementRightMapping X))

/-- The full original pointed mapping gadget category, retaining every full pointed arrow. -/
abbrev MappingGadgets := ObjectProperty.FullSubcategory mappingGadgetProperty.{u}

/-- Legitimate genuine ordinal source geometry supplies both independent actual original gadget point properties. -/
theorem mappingGadgetProperty_of_ordinal (X : Category.{u}) (h : OrdinalComparison X) : mappingGadgetProperty X :=
  ⟨ordinalComparison_rawPoint_weak X h, ordinalReplacementRightMapping_point_weak X h⟩

/-- The same original full actual Reedy degrees belong to the independent original mapping-gadget class. -/
theorem reedyDegree_mappingGadget (n : SimplexCategory) :
    mappingGadgetProperty (OriginalFixedFrontContraction.rawReedyDegree.{u} n) :=
  mappingGadgetProperty_of_ordinal _ (OriginalFixedFrontContraction.rawReedyOrdinalComparison n)

end CategoryTheory.CoherentRealization.OriginalPointed
