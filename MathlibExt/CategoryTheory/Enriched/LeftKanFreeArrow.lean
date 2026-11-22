/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.LeftKanFreeComparison
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Kan extension of every original arrow between free enriched diagrams

The target arrow is the original free extension of the source arrow's
full Hom coefficient, followed by the actual index Hom map. The Kan/free
unit and the two full Hom correspondences prove its whole comparison
square. Both endpoints, every coefficient and every original free arrow
are retained; no preservation or comparison outcome is an input.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uB
open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.LeftKanFreeArrow

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  (j : EnrichedFunctor V A B)

/-- The complete source Hom coefficient is mapped by the original full index Hom map. -/
def coefficient {a b : A} {X Y : V} (f : Free.object a X ⟶ Free.object b Y) :
    X ⟶ (Free.object (j.obj b) Y).toEnrichedFunctor.obj (j.obj a) :=
  Free.homEquiv a X (Free.object b Y) f ≫ (Y ◁ j.map b a)

/-- The target free arrow is the original extension of that actual coefficient. -/
def map {a b : A} {X Y : V} (f : Free.object a X ⟶ Free.object b Y) :
    Free.object (j.obj a) X ⟶ Free.object (j.obj b) Y :=
  Free.extend (j.obj a) X (Free.object (j.obj b) Y) (coefficient j f)

/-- Evaluating the whole target map gives exactly the full transported source coefficient. -/
theorem evaluate_map {a b : A} {X Y : V} (f : Free.object a X ⟶ Free.object b Y) :
    Free.evaluate (j.obj a) X (Free.object (j.obj b) Y) (map j f) = coefficient j f :=
  Free.evaluate_extend (j.obj a) X (Free.object (j.obj b) Y) _

variable
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) F.toEnrichedFunctor)]

/-- Every original free arrow satisfies the full Kan/free comparison square. -/
theorem map_square {a b : A} {X Y : V} (f : Free.object a X ⟶ Free.object b Y) :
    (leftKan j).map f ≫ LeftKanFreeComparison.hom j b Y =
      LeftKanFreeComparison.hom j a X ≫ map j f := by
  apply (leftKanHomEquiv j (Free.object a X) (Free.object (j.obj b) Y)).injective
  rw [leftKanHomEquiv_naturality_left, leftKanHomEquiv_naturality_right]
  have ha : leftKanHomEquiv j (Free.object a X) (Free.object (j.obj a) X)
      (LeftKanFreeComparison.hom j a X) = FreeHomTransport.map j a X :=
    (leftKanHomEquiv j (Free.object a X) (Free.object (j.obj a) X)).apply_symm_apply _
  have hb : leftKanHomEquiv j (Free.object b Y) (Free.object (j.obj b) Y)
      (LeftKanFreeComparison.hom j b Y) = FreeHomTransport.map j b Y :=
    (leftKanHomEquiv j (Free.object b Y) (Free.object (j.obj b) Y)).apply_symm_apply _
  rw [ha, hb]
  apply (Free.homEquiv a X (restrictionObject j (Free.object (j.obj b) Y))).injective
  change Free.evaluate a X (restrictionObject j (Free.object (j.obj b) Y))
      (f ≫ FreeHomTransport.map j b Y) =
    Free.evaluate a X (restrictionObject j (Free.object (j.obj b) Y))
      (FreeHomTransport.map j a X ≫ restrictionMap j (map j f))
  rw [Free.evaluate_postcomp, FreeHomTransport.evaluate_map, evaluate_map]
  change Free.evaluate a X (Free.object b Y) f ≫
    component (FreeHomTransport.map j b Y) a = coefficient j f
  rw [FreeHomTransport.map_component]
  rfl

/-- The inverse square keeps the same two original endpoint inverses. -/
theorem inverse_square {a b : A} {X Y : V} (f : Free.object a X ⟶ Free.object b Y) :
    map j f ≫ LeftKanFreeComparison.inv j b Y =
      LeftKanFreeComparison.inv j a X ≫ (leftKan j).map f := by
  apply (cancel_epi (LeftKanFreeComparison.iso j a X).hom).1
  rw [LeftKanFreeComparison.iso_hom, ← Category.assoc, ← map_square,
    Category.assoc, LeftKanFreeComparison.hom_inv_id, Category.comp_id,
    ← Category.assoc, LeftKanFreeComparison.hom_inv_id, Category.id_comp]

/-- The source coefficient construction agrees with conjugation by both whole endpoint maps. -/
theorem map_eq_conjugate {a b : A} {X Y : V} (f : Free.object a X ⟶ Free.object b Y) :
    map j f = LeftKanFreeComparison.inv j a X ≫ (leftKan j).map f ≫
      LeftKanFreeComparison.hom j b Y := by
  rw [map_square, ← Category.assoc, LeftKanFreeComparison.inv_hom_id, Category.id_comp]

/-- Identity arrows retain the original target identity on every free coefficient. -/
theorem map_id (a : A) (X : V) : map j (𝟙 (Free.object a X)) = 𝟙 (Free.object (j.obj a) X) := by
  rw [map_eq_conjugate, Functor.map_id, Category.id_comp, LeftKanFreeComparison.inv_hom_id]

/-- All original third indices and all three coefficients survive composition. -/
theorem map_comp {a b c : A} {X Y Z : V}
    (f : Free.object a X ⟶ Free.object b Y) (h : Free.object b Y ⟶ Free.object c Z) :
    map j (f ≫ h) = map j f ≫ map j h := by
  apply (cancel_epi (LeftKanFreeComparison.iso j a X).hom).1
  rw [LeftKanFreeComparison.iso_hom, ← map_square]
  calc
    _ = (leftKan j).map f ≫ (leftKan j).map h ≫ LeftKanFreeComparison.hom j c Z := by
      rw [Functor.map_comp, Category.assoc]
    _ = (leftKan j).map f ≫ (LeftKanFreeComparison.hom j b Y ≫ map j h) := by
      rw [map_square]
    _ = LeftKanFreeComparison.hom j a X ≫ (map j f ≫ map j h) := by
      rw [← Category.assoc, map_square, Category.assoc]

/-- Coefficient maps are exactly the original free coefficient maps at the target index. -/
theorem map_coefficient (a : A) {X Y : V} (f : X ⟶ Y) :
    map j (Free.coefficientMap a f) = Free.coefficientMap (j.obj a) f := by
  apply (cancel_epi (LeftKanFreeComparison.iso j a X).hom).1
  rw [LeftKanFreeComparison.iso_hom, ← map_square,
    LeftKanFreeComparison.hom_coefficient]

/-- Contravariant source-index maps retain the full original Hom point and index map. -/
theorem map_source {a a' : A} (e : 𝟙_ V ⟶ (a ⟶[V] a')) (X : V) :
    map j (Free.sourceMap e X) = Free.sourceMap (e ≫ j.map a a') X := by
  apply (cancel_epi (LeftKanFreeComparison.iso j a' X).hom).1
  rw [LeftKanFreeComparison.iso_hom, ← map_square, LeftKanFreeComparison.hom_source]

/-- The whole original Kan arrow has the same two complete endpoint isomorphisms. -/
def arrowIso {a b : A} {X Y : V} (f : Free.object a X ⟶ Free.object b Y) :
    Arrow.mk ((leftKan j).map f) ≅ Arrow.mk (map j f) :=
  Arrow.isoMk (LeftKanFreeComparison.iso j a X) (LeftKanFreeComparison.iso j b Y)
    (map_square j f).symm

/-- Every isomorphism-invariant class is transported by the actual complete free-arrow comparison. -/
theorem property_iff (P : MorphismProperty (EnrichedFunctorCat V B)) [P.RespectsIso]
    {a b : A} {X Y : V} (f : Free.object a X ⟶ Free.object b Y) :
    P ((leftKan j).map f) ↔ P (map j f) :=
  P.arrow_mk_iso_iff (arrowIso j f)

end CategoryTheory.EnrichedFunctorCat.LeftKanFreeArrow
