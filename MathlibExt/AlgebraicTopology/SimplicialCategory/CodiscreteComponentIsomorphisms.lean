/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CodiscreteEnrichment
import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategory

/-!
# Actual original component isomorphisms in the unit-Hom enrichment

The supplied original individual objects have the same whole unit Homs.
Their original unit vertices give both component-isomorphism maps and
both exact inverse identities. Objects are not replaced by components.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CodiscreteComponentIsomorphisms

private theorem unit_components : Subsingleton (SSet.π₀ (𝟙_ SSet.{u})) := by
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective b
  cases x
  cases y
  rfl

/-- Both original unit vertices form an actual isomorphism between the SAME supplied original objects. -/
def iso (O : Type u) (x y : CodiscreteEnrichment.object O) :
    ComponentCategory.objectOf.{u} (CodiscreteEnrichment.object O) x ≅
      ComponentCategory.objectOf.{u} (CodiscreteEnrichment.object O) y where
  hom := ComponentCategory.arrowOf (CodiscreteEnrichment.object O) PUnit.unit
  inv := ComponentCategory.arrowOf (CodiscreteEnrichment.object O) PUnit.unit
  hom_inv_id := @Subsingleton.elim (SSet.π₀ (𝟙_ SSet.{u})) unit_components _ _
  inv_hom_id := @Subsingleton.elim (SSet.π₀ (𝟙_ SSet.{u})) unit_components _ _

/-- The original component isomorphism retains its literal original unit Hom vertex. -/
theorem iso_hom (O : Type u) (x y : CodiscreteEnrichment.object O) :
    (iso O x y).hom = ComponentCategory.arrowOf (CodiscreteEnrichment.object O) PUnit.unit := rfl

/-- Its inverse retains the SAME literal original unit Hom vertex at the reversed original pair. -/
theorem iso_inv (O : Type u) (x y : CodiscreteEnrichment.object O) :
    (iso O x y).inv = ComponentCategory.arrowOf (CodiscreteEnrichment.object O) PUnit.unit := rfl

end CategoryTheory.SimplicialEnrichment.CodiscreteComponentIsomorphisms
