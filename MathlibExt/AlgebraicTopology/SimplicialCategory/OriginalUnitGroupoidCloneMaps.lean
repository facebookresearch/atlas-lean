/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidClone

/-!
# The SAME full original unit-groupoid clone maps preserve original DK weakness

The original functor acts on every old object and full Hom coefficient;
the actual new label is retained. Both whole projection maps commute
with that SAME functor. Their genuine original weakness proves weakness
of the actual clone map without fibrancy or cofibrancy hypotheses.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment.UnitGroupoidClone

variable {C D : Carrier.{u}} (F : C ⟶ D) (x : C)

/-- The SAME full original map on both actual old and new clone labels. -/
def map : object C x ⟶ object D (F.obj x) where
  obj := Sum.map F.obj id
  map a b := by
    cases a with
    | inl a =>
        cases b with
        | inl b => exact F.map a b
        | inr _b => exact F.map a x
    | inr _a =>
        cases b with
        | inl b => exact F.map x b
        | inr _b => exact F.map x x
  map_id a := by
    cases a with
    | inl a => exact F.map_id a
    | inr _a => exact F.map_id x
  map_comp a b c := by
    cases a <;> cases b <;> cases c
    all_goals exact F.map_comp _ _ _

/-- Every original old object maps to its SAME actual old target image. -/
theorem map_old (a : C) : (map F x).obj (Sum.inl a) = Sum.inl (F.obj a) := rfl

/-- The actual original new label remains the SAME new target label. -/
theorem map_new : (map F x).obj (newObject C x) = newObject D (F.obj x) := rfl

/-- The SAME two full original clone projections commute with the entire original functor. -/
theorem map_projection : map F x ≫ projection D (F.obj x) = projection C x ≫ F := by
  apply EnrichedFunctor.ext SSet.{u}
    (F := map F x ≫ projection D (F.obj x)) (G := projection C x ≫ F)
    (fun a => by cases a <;> rfl)
  intro a b
  cases a <;> cases b
  all_goals
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    rfl

/-- The SAME entire original old-family inclusion square commutes. -/
theorem inclusion_map : inclusion C x ≫ map F x = F ≫ inclusion D (F.obj x) := by
  apply EnrichedFunctor.ext SSet.{u}
    (F := inclusion C x ≫ map F x) (G := F ≫ inclusion D (F.obj x)) (fun _ => rfl)
  intro a b
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro p
  rfl

/-- Genuine weakness of the SAME original full functor gives weakness of its actual full clone map. -/
theorem map_weak (hF : EnrichedDwyerKan.weakEquivalences F) : EnrichedDwyerKan.weakEquivalences (map F x) := by
  have h : EnrichedDwyerKan.weakEquivalences (map F x ≫ projection D (F.obj x)) :=
    (congrArg (fun k : object C x ⟶ D => EnrichedDwyerKan.weakEquivalences k) (map_projection F x)).mpr
      (EnrichedDwyerKan.weakEquivalences.comp_mem _ _ (projection_weak C x) hF)
  exact EnrichedDwyerKan.weakEquivalences.of_postcomp _ _ (projection_weak D (F.obj x)) h

end CategoryTheory.SimplicialEnrichment.UnitGroupoidClone
