/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalEquivalenceCountableIntervalDirectReadback

/-!
# Exact full original unit coefficient readbacks and component equivalences

Every original coefficient into a weak-unit enrichment is invertible in
its SAME actual component category, by the genuine fully faithful
unit-Hom projection. Evaluation of a whole original enriched-square
equality retains its unit coefficient and only the stated endpoint
transports, at independent original object universes.
-/

noncomputable section
universe u v w t
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.OriginalUnitCoefficientReadback

/-- Each original unit coefficient in an actual full weak-unit enrichment has its SAME component arrow invertible. -/
theorem component_isIso (C : Carrier.{u})
    (h : ∀ x y : C, SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit (x ⟶[SSet.{u}] y)))
    {x y : C} (q : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y)) :
    IsIso (ComponentCategory.arrowOf C (SSet.unitHomEquiv _ q)) := by
  let P := OriginalWeakUnitHomsPointRecognition.projection C
  let _ : (ComponentCategory.mapFunctor P).ReflectsIsomorphisms :=
    (EnrichedDwyerKan.componentFullyFaithful P
      (OriginalWeakUnitHomsPointRecognition.projection_localWeak C h)).reflectsIsomorphisms
  have hunit : Subsingleton (SSet.π₀ (𝟙_ SSet.{u})) := by
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
    cases a
    cases b
    rfl
  have he : (ComponentCategory.mapFunctor P).map
      (ComponentCategory.arrowOf C (SSet.unitHomEquiv _ q)) =
      (CodiscreteComponentIsomorphisms.iso C (P.obj x) (P.obj y)).hom :=
    @Subsingleton.elim (SSet.π₀ (𝟙_ SSet.{u})) hunit _ _
  let _ : IsIso ((ComponentCategory.mapFunctor P).map
      (ComponentCategory.arrowOf C (SSet.unitHomEquiv _ q))) :=
    (congrArg IsIso he).mpr (inferInstance : IsIso (CodiscreteComponentIsomorphisms.iso C (P.obj x) (P.obj y)).hom)
  exact isIso_of_reflects_iso _ (ComponentCategory.mapFunctor P)

/-- Equality of full original enriched functors retains the SAME coefficient after each actual original endpoint
equality. -/
theorem hom_eq_of_functor_eq {A : Type v} [EnrichedCategory SSet.{u} A]
    {D : Type w} [EnrichedCategory SSet.{u} D]
    {F G : EnrichedFunctor SSet.{u} A D} (h : F = G) (x y : A) :
    F.map x y ≫ eqToHom (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t)
      (congrArg (fun K => K.obj x) h) (congrArg (fun K => K.obj y) h)) = G.map x y := by
  cases h
  exact Category.comp_id _

/-- The SAME actual original unit coefficient through a square keeps the original supplied target endpoint transports.
-/
theorem square_unit {A : Type v} [EnrichedCategory SSet.{u} A]
    {E : Type w} [EnrichedCategory SSet.{u} E]
    {D : Type t} [EnrichedCategory SSet.{u} D]
    (L : EnrichedFunctor SSet.{u} A E) (r : EnrichedFunctor SSet.{u} E D)
    (b : EnrichedFunctor SSet.{u} A D) (h : EnrichedFunctor.comp SSet.{u} L r = b)
    (x y : A) (q : 𝟙_ SSet.{u} ⟶ (x ⟶[SSet.{u}] y))
    (dx dy : D) (hx : b.obj x = dx) (hy : b.obj y = dy) :
    (q ≫ L.map x y) ≫ (r.map (L.obj x) (L.obj y) ≫
      eqToHom (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t)
        ((congrArg (fun K => K.obj x) h).trans hx)
        ((congrArg (fun K => K.obj y) h).trans hy))) =
      q ≫ (b.map x y ≫ eqToHom (congrArg₂ (fun s t : D => s ⟶[SSet.{u}] t) hx hy)) := by
  cases h
  exact (Category.assoc q (L.map x y) _).trans
    (congrArg (fun k => q ≫ k) (Category.assoc (L.map x y) (r.map (L.obj x) (L.obj y)) _).symm)

end CategoryTheory.SimplicialEnrichment.OriginalUnitCoefficientReadback
