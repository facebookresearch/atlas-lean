/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentEquivalenceCoreHoms

/-!
# The actual original component-equivalence core enrichment and inclusion

The SAME original individual objects carry the full original selected
Hom subcomplexes. All enriched laws descend through their actual monic
inclusions and original coefficient equalities. The full original core
inclusion is an actual enriched functor fixing every original object and
retaining every original selected Hom simplex. No weak outcome follows
from this construction alone.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore

variable (C : Carrier.{u})

/-- The actual full original component-equivalence core enrichment, on the SAME individual objects. -/
@[instance_reducible]
def enrichment : EnrichedCategory SSet.{u} C where
  Hom := hom C
  id := idMap C
  comp := compMap C
  id_comp x y := by
    ext q a
    apply Subtype.ext
    exact congr($(e_id_comp SSet.{u} x y).app q a.val)
  comp_id x y := by
    ext q a
    apply Subtype.ext
    exact congr($(e_comp_id SSet.{u} x y).app q a.val)
  assoc x y z t := by
    ext q a
    apply Subtype.ext
    exact congr($(e_assoc SSet.{u} x y z t).app q (a.1.val, a.2.1.val, a.2.2.val))

/-- The SAME full original core carrier keeps exactly its individual original object type. -/
def object : Carrier.{u} := by
  let _ : EnrichedCategory SSet.{u} C := enrichment C
  exact SimplicialEnrichment.of C

/-- Its actual full original Hom is exactly the same selected original Hom subcomplex. -/
theorem object_hom (x y : object C) : (x ⟶[SSet.{u}] y) = hom C x y := rfl

/-- The entire actual original core inclusion retains all individual objects and full Hom inclusion maps. -/
def inclusion : object C ⟶ C where
  obj x := x
  map := inclusionHom C
  map_id := idMap_inclusion C
  map_comp := compMap_inclusion C

/-- Every SAME individual original object is literally retained by the actual full core inclusion. -/
theorem inclusion_obj (x : object C) : (inclusion C).obj x = x := rfl

/-- Every full original scalar coefficient of the actual core inclusion is the SAME selected simplex, with all
operators retained. -/
theorem inclusion_apply (q : SimplexCategoryᵒᵖ) (x y : object C) (a : (x ⟶[SSet.{u}] y).obj q) :
    ((inclusion C).map x y).app q a = a.val := rfl

/-- The SAME entire original core Hom inclusion is monic at every original ordered pair. -/
instance inclusionHom_mono (x y : object C) : Mono ((inclusion C).map x y) :=
  inferInstanceAs (Mono (homSubcomplex C x y).ι)

end CategoryTheory.SimplicialEnrichment.ComponentEquivalenceCore
