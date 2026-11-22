/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomActionNaturality

/-!
# Actual original Hom weak maps transport along component isomorphisms

Both original full Hom actions are weak on original component
isomorphisms. Their exact naturality squares retain the SAME original
enriched map and its actual image unit-Hom representatives. Thus Hom
weakness is invariant under isomorphisms of either individual original
component object, with no Kan condition or assumed whole-map outcome.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomWeakRecognition
open ComponentCategory EnrichedHomVertexActions EnrichedHomWeakTransport
open EnrichedHomPrecomposition EnrichedHomActionNaturality

variable {C : Type v} [EnrichedCategory SSet.{u} C]
variable {D : Type w} [EnrichedCategory SSet.{u} D]
variable (F : EnrichedFunctor SSet.{u} C D)

/-- The SAME original Hom map's weakness is invariant under an actual isomorphism of its original target component
object. -/
theorem weak_post_iff (z : C) {x y : C} (e : objectOf.{u} C x ≅ objectOf.{u} C y) :
    SSet.realizationWeakEquivalences (F.map z x) ↔ SSet.realizationWeakEquivalences (F.map z y) := by
  let A := forwardUnit e
  let B := inverseUnit e
  let e' : objectOf.{u} D (F.obj x) ≅ objectOf.{u} D (F.obj y) := (mapFunctor F).mapIso e
  have hA' : arrowOf D (SSet.unitHomEquiv _ (A ≫ F.map x y)) = e'.hom :=
    (component_map_unit F A).symm.trans
      (congrArg (fun a => (mapFunctor F).map a) (forwardUnit_class e))
  have hB' : arrowOf D (SSet.unitHomEquiv _ (B ≫ F.map y x)) = e'.inv :=
    (component_map_unit F B).symm.trans
      (congrArg (fun a => (mapFunctor F).map a) (inverseUnit_class e))
  have sourceWeak := (post_weak_of_component_iso z e).1
  have targetWeak := (post_weak_of_component_iso_representatives (F.obj z) e'
    (A ≫ F.map x y) (B ≫ F.map y x) hA' hB').1
  let s := post z A
  let t := post (F.obj z) (A ≫ F.map x y)
  have square : s ≫ F.map z y = F.map z x ≫ t := post_natural F z A
  constructor
  · intro h
    apply SSet.realizationWeakEquivalences.of_precomp s (F.map z y) sourceWeak
    rw [square]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ h targetWeak
  · intro h
    apply SSet.realizationWeakEquivalences.of_postcomp (F.map z x) t targetWeak
    rw [← square]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ sourceWeak h

/-- The SAME original Hom map's weakness is invariant under an actual isomorphism of its original source component
object. -/
theorem weak_pre_iff (z : C) {x y : C} (e : objectOf.{u} C x ≅ objectOf.{u} C y) :
    SSet.realizationWeakEquivalences (F.map x z) ↔ SSet.realizationWeakEquivalences (F.map y z) := by
  let A := forwardUnit e
  let B := inverseUnit e
  let e' : objectOf.{u} D (F.obj x) ≅ objectOf.{u} D (F.obj y) := (mapFunctor F).mapIso e
  have hA' : arrowOf D (SSet.unitHomEquiv _ (A ≫ F.map x y)) = e'.hom :=
    (component_map_unit F A).symm.trans
      (congrArg (fun a => (mapFunctor F).map a) (forwardUnit_class e))
  have hB' : arrowOf D (SSet.unitHomEquiv _ (B ≫ F.map y x)) = e'.inv :=
    (component_map_unit F B).symm.trans
      (congrArg (fun a => (mapFunctor F).map a) (inverseUnit_class e))
  have sourceWeak := (pre_weak_of_component_iso z e).1
  have targetWeak := (pre_weak_of_component_iso_representatives (F.obj z) e'
    (A ≫ F.map x y) (B ≫ F.map y x) hA' hB').1
  let s := pre z A
  let t := pre (F.obj z) (A ≫ F.map x y)
  have square : s ≫ F.map x z = F.map y z ≫ t := pre_natural F z A
  constructor
  · intro h
    apply SSet.realizationWeakEquivalences.of_postcomp (F.map y z) t targetWeak
    rw [← square]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ sourceWeak h
  · intro h
    apply SSet.realizationWeakEquivalences.of_precomp s (F.map x z) sourceWeak
    rw [square]
    exact SSet.realizationWeakEquivalences.comp_mem _ _ h targetWeak

/-- Both SAME original Hom endpoints transport through actual original component isomorphisms without any fibrancy
hypothesis. -/
theorem weak_hom_iff_of_component_isos {x y x' y' : C}
    (e : objectOf.{u} C x ≅ objectOf.{u} C x') (f : objectOf.{u} C y ≅ objectOf.{u} C y') :
    SSet.realizationWeakEquivalences (F.map x y) ↔ SSet.realizationWeakEquivalences (F.map x' y') :=
  (weak_pre_iff F y e).trans (weak_post_iff F x' f)

end CategoryTheory.SimplicialEnrichment.EnrichedHomWeakRecognition
