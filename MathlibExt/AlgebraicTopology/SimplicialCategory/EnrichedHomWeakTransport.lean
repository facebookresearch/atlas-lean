/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomComponentAction

/-!
# Actual original Hom weakness along component isomorphisms

Choose original unit-Hom representatives of the SAME original component
isomorphism and its inverse. The genuine full Hom component functor
retains both inverse equations in the full scalar internal Homs. Those
actual equations give realization weakness of both SAME original Hom
action maps, with no Kan or desired weak-comparison premise.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomWeakTransport
open ComponentCategory EnrichedHomVertexActions EnrichedHomComponentAction
attribute [local instance] scalarEnrichment scalarOrdinaryEnrichment

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- An original unit-Hom representative of the SAME original component-isomorphism forward arrow. -/
def forwardUnit {x y : C} (e : objectOf.{u} C x ≅ objectOf.{u} C y) :
    𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y) :=
  (SSet.unitHomEquiv _).symm
    (Classical.choose (SSet.π₀.mk_surjective (X := (x ⟶[SSet.{u}] y)) e.hom))

/-- An original unit-Hom representative of that SAME original inverse component arrow. -/
def inverseUnit {x y : C} (e : objectOf.{u} C x ≅ objectOf.{u} C y) :
    𝟙_ SSet.{u} ⟶ (y ⟶[SSet.{u}] x) :=
  (SSet.unitHomEquiv _).symm
    (Classical.choose (SSet.π₀.mk_surjective (X := (y ⟶[SSet.{u}] x)) e.inv))

/-- The actual forward representative has exactly the SAME original component class. -/
theorem forwardUnit_class {x y : C} (e : objectOf.{u} C x ≅ objectOf.{u} C y) :
    arrowOf C (SSet.unitHomEquiv _ (forwardUnit e)) = e.hom := by
  change SSet.π₀.mk (SSet.unitHomEquiv _ (forwardUnit e)) = e.hom
  simpa only [forwardUnit, Equiv.apply_symm_apply] using
    Classical.choose_spec (SSet.π₀.mk_surjective (X := (x ⟶[SSet.{u}] y)) e.hom)

/-- The actual inverse representative has exactly the SAME original inverse component class. -/
theorem inverseUnit_class {x y : C} (e : objectOf.{u} C x ≅ objectOf.{u} C y) :
    arrowOf C (SSet.unitHomEquiv _ (inverseUnit e)) = e.inv := by
  change SSet.π₀.mk (SSet.unitHomEquiv _ (inverseUnit e)) = e.inv
  simpa only [inverseUnit, Equiv.apply_symm_apply] using
    Classical.choose_spec (SSet.π₀.mk_surjective (X := (y ⟶[SSet.{u}] x)) e.inv)

/-- Any supplied SAME original unit-Hom representatives of a component isomorphism act weakly on the full original
Homs. -/
theorem post_weak_of_component_iso_representatives (z : C) {x y : C}
    (e : objectOf.{u} C x ≅ objectOf.{u} C y)
    (A : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) (B : 𝟙_ SSet.{u} ⟶ (y ⟶[SSet.{u}] x))
    (hA : arrowOf C (SSet.unitHomEquiv _ A) = e.hom)
    (hB : arrowOf C (SSet.unitHomEquiv _ B) = e.inv) :
    SSet.realizationWeakEquivalences (post z A) ∧ SSet.realizationWeakEquivalences (post z B) := by
  let P := postFunctor z
  let V := vertexFunctor SSet.{u}
  let f := post z A
  let g := post z B
  have hf : V.map f = P.map e.hom :=
    (postFunctor_vertex z A).symm.trans (congrArg (fun a => P.map a) hA)
  have hg : V.map g = P.map e.inv :=
    (postFunctor_vertex z B).symm.trans (congrArg (fun a => P.map a) hB)
  have hX : SSet.π₀.mk (SSet.ihomVertexEquiv _ _ (f ≫ g)) =
      SSet.π₀.mk (SSet.ihomVertexEquiv _ _ (𝟙 (z ⟶[SSet.{u}] x))) := by
    change V.map (f ≫ g) = V.map (𝟙 (z ⟶[SSet.{u}] x))
    exact (V.map_comp f g).trans
      ((congrArg₂ (fun a b => @CategoryStruct.comp (objects.{u} SSet.{u}) _
        (V.obj (z ⟶[SSet.{u}] x)) (V.obj (z ⟶[SSet.{u}] y)) (V.obj (z ⟶[SSet.{u}] x)) a b) hf hg).trans
        ((P.map_comp e.hom e.inv).symm.trans
          ((congrArg (fun a => P.map a) e.hom_inv_id).trans
            ((P.map_id (objectOf.{u} C x)).trans (V.map_id (z ⟶[SSet.{u}] x)).symm))))
  have hY : SSet.π₀.mk (SSet.ihomVertexEquiv _ _ (g ≫ f)) =
      SSet.π₀.mk (SSet.ihomVertexEquiv _ _ (𝟙 (z ⟶[SSet.{u}] y))) := by
    change V.map (g ≫ f) = V.map (𝟙 (z ⟶[SSet.{u}] y))
    exact (V.map_comp g f).trans
      ((congrArg₂ (fun a b => @CategoryStruct.comp (objects.{u} SSet.{u}) _
        (V.obj (z ⟶[SSet.{u}] y)) (V.obj (z ⟶[SSet.{u}] x)) (V.obj (z ⟶[SSet.{u}] y)) a b) hg hf).trans
        ((P.map_comp e.inv e.hom).symm.trans
          ((congrArg (fun a => P.map a) e.inv_hom_id).trans
            ((P.map_id (objectOf.{u} C y)).trans (V.map_id (z ⟶[SSet.{u}] y)).symm))))
  exact SSet.realizationWeakEquivalences_both_of_ihom_inverse f g hX hY

/-- Both SAME selected original postcomposition Hom actions are weak from the actual original component isomorphism. -/
theorem post_weak_of_component_iso (z : C) {x y : C} (e : objectOf.{u} C x ≅ objectOf.{u} C y) :
    SSet.realizationWeakEquivalences (post z (forwardUnit e)) ∧
      SSet.realizationWeakEquivalences (post z (inverseUnit e)) :=
  post_weak_of_component_iso_representatives z e (forwardUnit e) (inverseUnit e)
    (forwardUnit_class e) (inverseUnit_class e)

end CategoryTheory.SimplicialEnrichment.EnrichedHomWeakTransport
