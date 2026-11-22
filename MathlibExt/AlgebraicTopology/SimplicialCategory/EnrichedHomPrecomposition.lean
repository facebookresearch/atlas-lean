/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomWeakTransport
import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentOpposite

/-!
# The same original precomposition Hom action is weak on component isomorphisms

The actual opposite enrichment reverses the entire original Hom data.
Its proved component functor transports the same original isomorphism
and both actual unit-Hom representatives. The full opposite post action
is the SAME original precomposition formula, including its original
composition and unitors. The actual scalar inverse proof therefore
gives weakness of both full original precomposition maps, with no Kan
condition or assumed weak outcome.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory BraidedCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomPrecomposition
open ComponentCategory EnrichedHomVertexActions EnrichedHomWeakTransport

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- The SAME full original precomposition action, read through the entire actual opposite enrichment. -/
def pre (z : C) {x y : C} (f : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    (y ⟶[SSet.{u}] z) ⟶ (x ⟶[SSet.{u}] z) :=
  post (C := Cᵒᵖ) (op z) (x := op y) (y := op x) f

/-- This whole opposite action is literally the original composition by the SAME supplied original unit-Hom map. -/
theorem pre_original_formula (z : C) {x y : C} (f : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    pre z f = (λ_ (y ⟶[SSet.{u}] z)).inv ≫ f ▷ (y ⟶[SSet.{u}] z) ≫ eComp SSet.{u} x y z := by
  ext q a
  rfl

/-- Any SAME original component-isomorphism representatives act weakly on both full original precomposition Hom maps. -/
theorem pre_weak_of_component_iso_representatives (z : C) {x y : C}
    (e : objectOf.{u} C x ≅ objectOf.{u} C y)
    (A : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) (B : 𝟙_ SSet.{u} ⟶ (y ⟶[SSet.{u}] x))
    (hA : arrowOf C (SSet.unitHomEquiv _ A) = e.hom)
    (hB : arrowOf C (SSet.unitHomEquiv _ B) = e.inv) :
    SSet.realizationWeakEquivalences (pre z A) ∧ SSet.realizationWeakEquivalences (pre z B) := by
  let e' : objectOf.{u} Cᵒᵖ (op y) ≅ objectOf.{u} Cᵒᵖ (op x) :=
    (oppositeFunctor C).mapIso e.op
  have hA' : arrowOf Cᵒᵖ (SSet.unitHomEquiv _ A) = e'.hom := hA
  have hB' : arrowOf Cᵒᵖ (SSet.unitHomEquiv _ B) = e'.inv := hB
  exact post_weak_of_component_iso_representatives (C := Cᵒᵖ) (op z) e' A B hA' hB'

/-- The actual original chosen forward/inverse representatives are weak on their SAME whole precomposition maps. -/
theorem pre_weak_of_component_iso (z : C) {x y : C} (e : objectOf.{u} C x ≅ objectOf.{u} C y) :
    SSet.realizationWeakEquivalences (pre z (forwardUnit e)) ∧
      SSet.realizationWeakEquivalences (pre z (inverseUnit e)) :=
  pre_weak_of_component_iso_representatives z e (forwardUnit e) (inverseUnit e)
    (forwardUnit_class e) (inverseUnit_class e)

end CategoryTheory.SimplicialEnrichment.EnrichedHomPrecomposition
