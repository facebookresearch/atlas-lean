/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.CategoryTheory.Reedy.Factorization
public import MathlibExt.CategoryTheory.Reedy.Corner
public import Mathlib.CategoryTheory.Limits.IsLimit

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Original corner comparisons for coefficient factorization

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure.RestrictedBoundary

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {s : ObjectProperty J}
  (hs : ∀ i : J, s i → ∀ k : J, r.degree k ≤ r.degree i → s k)
  (j : J) (hj : s j)

/-- The original ordinary incoming source arrow of a restricted latching object. -/
def latchingArrowOriginal (a : (r.restrict hs).Latching (⟨j, hj⟩ : s.FullSubcategory)) :
    ((r.restrict hs).latchingSource a).obj ⟶ j := ((r.restrict hs).latchingArrow a).hom

/-- The original ordinary outgoing source arrow of a restricted matching object. -/
def matchingArrowOriginal (a : (r.restrict hs).Matching (⟨j, hj⟩ : s.FullSubcategory)) :
    j ⟶ ((r.restrict hs).matchingTarget a).obj := ((r.restrict hs).matchingArrow a).hom

/-- Forgetting membership retains the full original latching source. -/
def latchingForget : (r.restrict hs).Latching (⟨j, hj⟩ : s.FullSubcategory) ⥤ r.Latching j where
  obj a := r.latchingMk (latchingArrowOriginal r hs j hj a)
    ((r.restrict hs).latchingArrow_mem a) a.property
  map {a b} f := ObjectProperty.homMk (Over.homMk
    ⟨((r.restrict hs).latchingComparison f).hom, (r.restrict hs).latchingComparison_mem f⟩ (by
      apply WideSubcategory.hom_ext
      exact congrArg (fun g => g.hom) ((r.restrict hs).latchingComparison_arrow f)))
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    rfl

/-- Forgetting membership retains the full original matching source. -/
def matchingForget : (r.restrict hs).Matching (⟨j, hj⟩ : s.FullSubcategory) ⥤ r.Matching j where
  obj a := r.matchingMk (matchingArrowOriginal r hs j hj a)
    ((r.restrict hs).matchingArrow_mem a) a.property
  map {a b} f := ObjectProperty.homMk (Under.homMk
    ⟨((r.restrict hs).matchingComparison f).hom, (r.restrict hs).matchingComparison_mem f⟩ (by
      apply WideSubcategory.hom_ext
      exact congrArg (fun g => g.hom) ((r.restrict hs).matchingArrow_comparison f)))
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply WideSubcategory.hom_ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply WideSubcategory.hom_ext
    rfl

/-- Every original incoming arrow is restored to the restricted source with its proved lower
membership. -/
def latchingLift : r.Latching j ⥤ (r.restrict hs).Latching (⟨j, hj⟩ : s.FullSubcategory) where
  obj a := (r.restrict hs).latchingMk
    (ObjectProperty.homMk (r.latchingArrow a) :
      (⟨r.latchingSource a, hs j hj _ (le_of_lt a.property)⟩ : s.FullSubcategory) ⟶ ⟨j, hj⟩)
    (r.latchingArrow_mem a) a.property
  map {a b} f := ObjectProperty.homMk (Over.homMk
    ⟨ObjectProperty.homMk (r.latchingComparison f), r.latchingComparison_mem f⟩ (by
      apply WideSubcategory.hom_ext
      apply ObjectProperty.hom_ext
      exact r.latchingComparison_arrow f))
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    rfl

/-- Every original outgoing arrow is restored to the restricted source with its proved lower
membership. -/
def matchingLift : r.Matching j ⥤ (r.restrict hs).Matching (⟨j, hj⟩ : s.FullSubcategory) where
  obj a := (r.restrict hs).matchingMk
    (ObjectProperty.homMk (r.matchingArrow a) :
      (⟨j, hj⟩ : s.FullSubcategory) ⟶ ⟨r.matchingTarget a, hs j hj _ (le_of_lt a.property)⟩)
    (r.matchingArrow_mem a) a.property
  map {a b} f := ObjectProperty.homMk (Under.homMk
    ⟨ObjectProperty.homMk (r.matchingComparison f), r.matchingComparison_mem f⟩ (by
      apply WideSubcategory.hom_ext
      apply ObjectProperty.hom_ext
      exact r.matchingArrow_comparison f))
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    rfl

/-- Restoring and forgetting preserves the entire original incoming object record. -/
theorem latchingForget_lift_obj (a : r.Latching j) :
    (latchingForget r hs j hj).obj ((latchingLift r hs j hj).obj a) = a := by
  rfl

/-- Forgetting and restoring preserves the entire actual restricted incoming object record. -/
theorem latchingLift_forget_obj (a : (r.restrict hs).Latching (⟨j, hj⟩ : s.FullSubcategory)) :
    (latchingLift r hs j hj).obj ((latchingForget r hs j hj).obj a) = a := by
  rfl

/-- Restoring and forgetting preserves the entire original outgoing object record. -/
theorem matchingForget_lift_obj (a : r.Matching j) :
    (matchingForget r hs j hj).obj ((matchingLift r hs j hj).obj a) = a := by
  rfl

/-- Forgetting and restoring preserves the entire actual restricted outgoing object record. -/
theorem matchingLift_forget_obj (a : (r.restrict hs).Matching (⟨j, hj⟩ : s.FullSubcategory)) :
    (matchingLift r hs j hj).obj ((matchingForget r hs j hj).obj a) = a := by
  rfl

/-- The actual restricted latching source is equivalent to the same full original latching
source. -/
def latchingEquivalence : (r.restrict hs).Latching (⟨j, hj⟩ : s.FullSubcategory) ≌
  r.Latching j where
  functor := latchingForget r hs j hj
  inverse := latchingLift r hs j hj
  unitIso := NatIso.ofComponents (fun a => eqToIso (latchingLift_forget_obj r hs j hj a).symm)
    (fun f => by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    change ((r.restrict hs).latchingComparison f).hom ≫ (𝟙 _) =
      (𝟙 _) ≫ ((r.restrict hs).latchingComparison f).hom
    rw [Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents (fun a => eqToIso (latchingForget_lift_obj r hs j hj a))
    (fun f => by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    change r.latchingComparison f ≫ (𝟙 _) = (𝟙 _) ≫ r.latchingComparison f
    rw [Category.comp_id, Category.id_comp])
  functor_unitIso_comp a := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    change (𝟙 (((r.restrict hs).latchingSource a).obj)) ≫ (𝟙 _) = 𝟙 _
    rw [Category.id_comp]

/-- The actual restricted matching source is equivalent to the same full original matching
source. -/
def matchingEquivalence : (r.restrict hs).Matching (⟨j, hj⟩ : s.FullSubcategory) ≌
  r.Matching j where
  functor := matchingForget r hs j hj
  inverse := matchingLift r hs j hj
  unitIso := NatIso.ofComponents (fun a => eqToIso (matchingLift_forget_obj r hs j hj a).symm)
    (fun f => by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    change ((r.restrict hs).matchingComparison f).hom ≫ (𝟙 _) =
      (𝟙 _) ≫ ((r.restrict hs).matchingComparison f).hom
    rw [Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents (fun a => eqToIso (matchingForget_lift_obj r hs j hj a))
    (fun f => by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply WideSubcategory.hom_ext
    change r.matchingComparison f ≫ (𝟙 _) = (𝟙 _) ≫ r.matchingComparison f
    rw [Category.comp_id, Category.id_comp])
  functor_unitIso_comp a := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply WideSubcategory.hom_ext
    change (𝟙 (((r.restrict hs).matchingTarget a).obj)) ≫ (𝟙 _) = 𝟙 _
    rw [Category.id_comp]

/-- The restricted incoming coefficient diagram is the same full original coefficient diagram. -/
theorem latchingDiagram_forget {C : Type uC} [Category.{vC} C] (X : J ⥤ C) :
    (r.restrict hs).latchingDiagram (s.ι ⋙ X) (⟨j, hj⟩ : s.FullSubcategory) =
      latchingForget r hs j hj ⋙ r.latchingDiagram X j := rfl

/-- The restricted outgoing coefficient diagram is the same full original coefficient diagram. -/
theorem matchingDiagram_forget {C : Type uC} [Category.{vC} C] (X : J ⥤ C) :
    (r.restrict hs).matchingDiagram (s.ι ⋙ X) (⟨j, hj⟩ : s.FullSubcategory) =
      matchingForget r hs j hj ⋙ r.matchingDiagram X j := rfl

@[simp]
theorem latchingForget_source (a : (r.restrict hs).Latching (⟨j, hj⟩ : s.FullSubcategory)) :
    r.latchingSource ((latchingForget r hs j hj).obj a) =
      ((r.restrict hs).latchingSource a).obj := rfl

@[simp]
theorem latchingForget_arrow (a : (r.restrict hs).Latching (⟨j, hj⟩ : s.FullSubcategory)) :
    r.latchingArrow ((latchingForget r hs j hj).obj a) =
      ((r.restrict hs).latchingArrow a).hom := rfl

@[simp]
theorem latchingForget_comparison
    {a b : (r.restrict hs).Latching (⟨j, hj⟩ : s.FullSubcategory)} (f : a ⟶ b) :
    r.latchingComparison ((latchingForget r hs j hj).map f) =
      ((r.restrict hs).latchingComparison f).hom := rfl

@[simp]
theorem matchingForget_target (a : (r.restrict hs).Matching (⟨j, hj⟩ : s.FullSubcategory)) :
    r.matchingTarget ((matchingForget r hs j hj).obj a) =
      ((r.restrict hs).matchingTarget a).obj := rfl

@[simp]
theorem matchingForget_arrow (a : (r.restrict hs).Matching (⟨j, hj⟩ : s.FullSubcategory)) :
    r.matchingArrow ((matchingForget r hs j hj).obj a) =
      ((r.restrict hs).matchingArrow a).hom := rfl

@[simp]
theorem matchingForget_comparison
    {a b : (r.restrict hs).Matching (⟨j, hj⟩ : s.FullSubcategory)} (f : a ⟶ b) :
    r.matchingComparison ((matchingForget r hs j hj).map f) =
      ((r.restrict hs).matchingComparison f).hom := rfl

end CategoryTheory.ReedyStructure.RestrictedBoundary

end ReedyPart1

section ReedyPart2

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure.StageBoundaryCones

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D) {d : D}

/-- Every original incoming source into an object through `d` lies below `d`. -/
abbrev latchingBelowAt (q : r.Through d) : r.Latching q.obj ⥤ r.Below d where
  obj a := ⟨r.latchingSource a, a.property.trans_le q.property⟩
  map f := ObjectProperty.homMk (r.latchingComparison f)
  map_id _ := by apply ObjectProperty.hom_ext; rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; rfl

/-- Every original outgoing target from an object through `d` lies below `d`. -/
abbrev matchingBelowAt (q : r.Through d) : r.Matching q.obj ⥤ r.Below d where
  obj a := ⟨r.matchingTarget a, a.property.trans_le q.property⟩
  map f := ObjectProperty.homMk (r.matchingComparison f)
  map_id _ := by apply ObjectProperty.hom_ext; rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; rfl

/-- The complete actual through-degree latching source retains every original triangle. -/
def throughLatching (q : r.Through d) : (r.throughStructure d).Latching q ≌ r.Latching q.obj :=
  RestrictedBoundary.latchingEquivalence r (fun _ hi _ hk => hk.trans hi) q.obj q.property

/-- The complete actual through-degree matching source retains every original triangle. -/
def throughMatching (q : r.Through d) : (r.throughStructure d).Matching q ≌ r.Matching q.obj :=
  RestrictedBoundary.matchingEquivalence r (fun _ hi _ hk => hk.trans hi) q.obj q.property

/-- The complete actual below-degree latching source retains every original triangle. -/
def belowLatching (q : r.Through d) (hq : r.degree q.obj < d) :
    (r.belowStructure d).Latching (⟨q.obj, hq⟩ : r.Below d) ≌ r.Latching q.obj :=
  RestrictedBoundary.latchingEquivalence r (fun _ hi _ hk => hk.trans_lt hi) q.obj hq

/-- The complete actual below-degree matching source retains every original triangle. -/
def belowMatching (q : r.Through d) (hq : r.degree q.obj < d) :
    (r.belowStructure d).Matching (⟨q.obj, hq⟩ : r.Below d) ≌ r.Matching q.obj :=
  RestrictedBoundary.matchingEquivalence r (fun _ hi _ hk => hk.trans_lt hi) q.obj hq

/-- The actual through-degree incoming source is below the new degree. -/
theorem latchingSource_lt (q : r.Through d) (a : (r.throughStructure d).Latching q) :
    r.degree ((r.throughStructure d).latchingSource a).obj < d := a.property.trans_le q.property

/-- The actual through-degree outgoing target is below the new degree. -/
theorem matchingTarget_lt (q : r.Through d) (a : (r.throughStructure d).Matching q) :
    r.degree ((r.throughStructure d).matchingTarget a).obj < d := a.property.trans_le q.property

variable {C : Type uC} [Category.{vC} C]

/-- The complete lower incoming coefficient diagram at any retained original object. -/
abbrev lowerLatchingAt (P : r.Below d ⥤ C) (q : r.Through d) : r.Latching q.obj ⥤ C :=
  latchingBelowAt r q ⋙ P

/-- The complete lower outgoing coefficient diagram at any retained original object. -/
abbrev lowerMatchingAt (P : r.Below d ⥤ C) (q : r.Through d) : r.Matching q.obj ⥤ C :=
  matchingBelowAt r q ⋙ P


end CategoryTheory.ReedyStructure.StageBoundaryCones

end ReedyPart2

section ReedyPart3

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

/-- Original latching-shape colimits transfer through the original degree restriction. -/
instance throughLatchingColimits [∀ j, HasColimitsOfShape (r.Latching j) C] (d : D) :
    ∀ q, HasColimitsOfShape ((r.throughStructure d).Latching q) C := fun q ↦
  hasColimitsOfShape_of_equivalence (StageBoundaryCones.throughLatching r q).symm

/-- Original matching-shape limits transfer through the original degree restriction. -/
instance throughMatchingLimits [∀ j, HasLimitsOfShape (r.Matching j) C] (d : D) :
    ∀ q, HasLimitsOfShape ((r.throughStructure d).Matching q) C := fun q ↦
  hasLimitsOfShape_of_equivalence (StageBoundaryCones.throughMatching r q).symm

/-- Original latching-shape colimits transfer to the strict lower-degree restriction. -/
instance belowLatchingColimits [∀ j, HasColimitsOfShape (r.Latching j) C] (d : D) :
    ∀ q, HasColimitsOfShape ((r.belowStructure d).Latching q) C := fun q ↦
  hasColimitsOfShape_of_equivalence
    (StageBoundaryCones.belowLatching r
      (⟨q.obj, le_of_lt q.property⟩ : r.Through d) q.property).symm

/-- Original matching-shape limits transfer to the strict lower-degree restriction. -/
instance belowMatchingLimits [∀ j, HasLimitsOfShape (r.Matching j) C] (d : D) :
    ∀ q, HasLimitsOfShape ((r.belowStructure d).Matching q) C := fun q ↦
  hasLimitsOfShape_of_equivalence
    (StageBoundaryCones.belowMatching r
      (⟨q.obj, le_of_lt q.property⟩ : r.Through d) q.property).symm

end CategoryTheory.ReedyStructure

end ReedyPart3

section ReedyPart4

open CategoryTheory Limits
open CategoryTheory.ReedyStructure.StageBoundaryCones

namespace CategoryTheory.ReedyStructure.StageBoundaryCones

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D) {d : D}
  {C : Type uC} [Category.{vC} C]

section LatchingFunctor

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The original full caller latching colimit is a complete cocone on its through-degree
restriction. -/
def latchingCoconeOfFunctor (X : J ⥤ C) (q : r.Through d) :
    Cocone ((r.throughStructure d).latchingDiagram (r.restrictThrough X d) q) :=
  (colimit.cocone (r.latchingDiagram X q.obj)).whisker (throughLatching r q).functor

/-- The original caller through-degree latching cocone is complete on every original triangle. -/
def latchingIsColimitOfFunctor (X : J ⥤ C) (q : r.Through d) :
    IsColimit (latchingCoconeOfFunctor r X q) :=
  (colimit.isColimit (r.latchingDiagram X q.obj)).whiskerEquivalence (throughLatching r q)

/-- The original caller latching map is unchanged under the complete through-degree source
comparison. -/
theorem latchingMapOfFunctor (X : J ⥤ C) (q : r.Through d) :
    (r.throughStructure d).latchingMapWith (r.restrictThrough X d) q
      (latchingCoconeOfFunctor r X q) (latchingIsColimitOfFunctor r X q) =
        latchingMap r X q.obj := by
  apply (latchingIsColimitOfFunctor r X q).hom_ext
  intro a
  rw [(r.throughStructure d).latchingMapWith_ι]
  change X.map ((r.throughStructure d).latchingArrow a).hom =
    colimit.ι (r.latchingDiagram X q.obj) ((throughLatching r q).functor.obj a) ≫
      latchingMap r X q.obj
  rw [latchingMap_ι r]
  rfl

/-- The same original caller latching cocone is complete on the actual old-degree source. -/
def belowLatchingCoconeOfFunctor (X : J ⥤ C) (q : r.Through d) (hq : r.degree q.obj < d) :
    Cocone ((r.belowStructure d).latchingDiagram (r.restrictBelow X d) (⟨q.obj, hq⟩ : r.Below d)) :=
  (colimit.cocone (r.latchingDiagram X q.obj)).whisker (belowLatching r q hq).functor

/-- The reindexed chosen latching cocone of the full functor is a colimit below the current
degree. -/
def belowLatchingIsColimitOfFunctor (X : J ⥤ C) (q : r.Through d) (hq : r.degree q.obj < d) :
    IsColimit (belowLatchingCoconeOfFunctor r X q hq) :=
  (colimit.isColimit (r.latchingDiagram X q.obj)).whiskerEquivalence (belowLatching r q hq)

/-- The original lower latching diagram has a complete cocone at the unchanged original lower
colimit. -/
def belowLatchingCocone (P : r.Below d ⥤ C) (q : r.Through d) (hq : r.degree q.obj < d) :
    Cocone ((r.belowStructure d).latchingDiagram P (⟨q.obj, hq⟩ : r.Below d)) :=
  (colimit.cocone (lowerLatchingAt r P q)).whisker (belowLatching r q hq).functor

/-- The reindexed latching cocone of the lower diagram is a colimit. -/
def belowLatchingIsColimit (P : r.Below d ⥤ C) (q : r.Through d) (hq : r.degree q.obj < d) :
    IsColimit (belowLatchingCocone r P q hq) :=
  (colimit.isColimit (lowerLatchingAt r P q)).whiskerEquivalence (belowLatching r q hq)

end LatchingFunctor

section MatchingFunctor

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The original full caller matching limit is a complete cone on its through-degree restriction. -/
def matchingConeOfFunctor (X : J ⥤ C) (q : r.Through d) :
    Cone ((r.throughStructure d).matchingDiagram (r.restrictThrough X d) q) :=
  (limit.cone (r.matchingDiagram X q.obj)).whisker (throughMatching r q).functor

/-- The chosen matching cone remains a limit after restriction through the current degree. -/
def matchingIsLimitOfFunctor (X : J ⥤ C) (q : r.Through d) :
    IsLimit (matchingConeOfFunctor r X q) :=
  (limit.isLimit (r.matchingDiagram X q.obj)).whiskerEquivalence (throughMatching r q)

/-- The original caller matching map is unchanged under the complete through-degree source
comparison. -/
theorem matchingMapOfFunctor (X : J ⥤ C) (q : r.Through d) :
    (r.throughStructure d).matchingMapWith (r.restrictThrough X d) q
      (matchingConeOfFunctor r X q) (matchingIsLimitOfFunctor r X q) = matchingMap r X q.obj := by
  apply (matchingIsLimitOfFunctor r X q).hom_ext
  intro a
  rw [(r.throughStructure d).matchingMapWith_π]
  change X.map ((r.throughStructure d).matchingArrow a).hom =
    matchingMap r X q.obj ≫ limit.π (r.matchingDiagram X q.obj)
      ((throughMatching r q).functor.obj a)
  rw [matchingMap_π r]
  rfl

/-- The same original caller matching cone is complete on the actual old-degree source. -/
def belowMatchingConeOfFunctor (X : J ⥤ C) (q : r.Through d) (hq : r.degree q.obj < d) :
    Cone ((r.belowStructure d).matchingDiagram (r.restrictBelow X d) (⟨q.obj, hq⟩ : r.Below d)) :=
  (limit.cone (r.matchingDiagram X q.obj)).whisker (belowMatching r q hq).functor

/-- The reindexed chosen matching cone of the full functor is a limit below the current degree. -/
def belowMatchingIsLimitOfFunctor (X : J ⥤ C) (q : r.Through d) (hq : r.degree q.obj < d) :
    IsLimit (belowMatchingConeOfFunctor r X q hq) :=
  (limit.isLimit (r.matchingDiagram X q.obj)).whiskerEquivalence (belowMatching r q hq)

/-- The original lower matching diagram has a complete cone at the unchanged original lower
limit. -/
def belowMatchingCone (P : r.Below d ⥤ C) (q : r.Through d) (hq : r.degree q.obj < d) :
    Cone ((r.belowStructure d).matchingDiagram P (⟨q.obj, hq⟩ : r.Below d)) :=
  (limit.cone (lowerMatchingAt r P q)).whisker (belowMatching r q hq).functor

/-- The reindexed matching cone of the lower diagram is a limit. -/
def belowMatchingIsLimit (P : r.Below d ⥤ C) (q : r.Through d) (hq : r.degree q.obj < d) :
    IsLimit (belowMatchingCone r P q hq) :=
  (limit.isLimit (lowerMatchingAt r P q)).whiskerEquivalence (belowMatching r q hq)

end MatchingFunctor

section Layer

variable [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  (a : LayerData (C := C) r d)

/-- Every original incoming coefficient of the extension is naturally its supplied lower
coefficient. -/
def latchingDiagramIso (q : r.Through d) :
    (r.throughStructure d).latchingDiagram a.extension q ≅
      (throughLatching r q).functor ⋙ lowerLatchingAt r a.lower q :=
  NatIso.ofComponents
    (fun x => a.oldIso ((r.throughStructure d).latchingSource x) (latchingSource_lt r q x))
    (fun {x y} g => a.lowerIso_naturality
      (ObjectProperty.homMk ((r.throughStructure d).latchingComparison g).hom :
        (⟨((r.throughStructure d).latchingSource x).obj, latchingSource_lt r q x⟩ : r.Below d) ⟶
          ⟨((r.throughStructure d).latchingSource y).obj, latchingSource_lt r q y⟩))

/-- Every original outgoing coefficient of the extension is naturally its supplied lower
coefficient. -/
def matchingDiagramIso (q : r.Through d) :
    (r.throughStructure d).matchingDiagram a.extension q ≅
      (throughMatching r q).functor ⋙ lowerMatchingAt r a.lower q :=
  NatIso.ofComponents
    (fun x => a.oldIso ((r.throughStructure d).matchingTarget x) (matchingTarget_lt r q x))
    (fun {x y} g => a.lowerIso_naturality
      (ObjectProperty.homMk ((r.throughStructure d).matchingComparison g).hom :
        (⟨((r.throughStructure d).matchingTarget x).obj, matchingTarget_lt r q x⟩ : r.Below d) ⟶
          ⟨((r.throughStructure d).matchingTarget y).obj, matchingTarget_lt r q y⟩))

/-- The complete actual lower latching colimit supplies the extension's whole latching cocone. -/
def latchingCocone (q : r.Through d) : Cocone
  ((r.throughStructure d).latchingDiagram a.extension q) :=
  (Cocone.precompose (latchingDiagramIso r a q).hom).obj
    ((colimit.cocone (lowerLatchingAt r a.lower q)).whisker (throughLatching r q).functor)

/-- The extension latching cocone is complete on every original incoming comparison. -/
def latchingIsColimit (q : r.Through d) : IsColimit (latchingCocone r a q) :=
  (IsColimit.precomposeHomEquiv (latchingDiagramIso r a q)
    ((colimit.cocone (lowerLatchingAt r a.lower q)).whisker (throughLatching r q).functor)).symm
    ((colimit.isColimit (lowerLatchingAt r a.lower q)).whiskerEquivalence (throughLatching r q))

/-- Every extension latching leg retains its exact original lower object transport and original
injection. -/
theorem latchingCocone_ι (q : r.Through d) (x : (r.throughStructure d).Latching q) :
    (latchingCocone r a q).ι.app x =
      (a.oldIso ((r.throughStructure d).latchingSource x) (latchingSource_lt r q x)).hom ≫
        colimit.ι (lowerLatchingAt r a.lower q) ((throughLatching r q).functor.obj x) := rfl

/-- The complete actual lower matching limit supplies the extension's whole matching cone. -/
def matchingCone (q : r.Through d) : Cone ((r.throughStructure d).matchingDiagram a.extension q) :=
  (Cone.postcompose (matchingDiagramIso r a q).inv).obj
    ((limit.cone (lowerMatchingAt r a.lower q)).whisker (throughMatching r q).functor)

/-- The extension matching cone is complete on every original outgoing comparison. -/
def matchingIsLimit (q : r.Through d) : IsLimit (matchingCone r a q) :=
  (IsLimit.postcomposeInvEquiv (matchingDiagramIso r a q)
    ((limit.cone (lowerMatchingAt r a.lower q)).whisker (throughMatching r q).functor)).symm
    ((limit.isLimit (lowerMatchingAt r a.lower q)).whiskerEquivalence (throughMatching r q))

/-- Every extension matching leg retains its original projection and exact inverse lower object
transport. -/
theorem matchingCone_π (q : r.Through d) (x : (r.throughStructure d).Matching q) :
    (matchingCone r a q).π.app x =
      limit.π (lowerMatchingAt r a.lower q) ((throughMatching r q).functor.obj x) ≫
        (a.oldIso ((r.throughStructure d).matchingTarget x) (matchingTarget_lt r q x)).inv := rfl

end Layer

end CategoryTheory.ReedyStructure.StageBoundaryCones

end ReedyPart4

section ReedyPart5

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure.BoundaryConeCongr

variable {C : Type u} [Category.{v} C]

/-- The given native pushout injections define a cocone for equal original source maps. -/
def pushoutCone {A B D : C} {f f' : A ⟶ B} {g g' : A ⟶ D}
    (hf : f = f') (hg : g = g') [HasPushout f' g'] : PushoutCocone f g :=
  PushoutCocone.mk (pushout.inl f' g') (pushout.inr f' g') (by
    rw [hf, hg]
    exact pushout.condition)

/-- Equal original source maps preserve the complete native pushout universal property. -/
def pushoutIsColimit {A B D : C} {f f' : A ⟶ B} {g g' : A ⟶ D}
    (hf : f = f') (hg : g = g') [HasPushout f' g'] : IsColimit (pushoutCone hf hg) := by
  cases hf
  cases hg
  exact pushoutIsPushout f g

@[simp]
theorem pushoutCone_inl {A B D : C} {f f' : A ⟶ B} {g g' : A ⟶ D}
    (hf : f = f') (hg : g = g') [HasPushout f' g'] :
    (pushoutCone hf hg).inl = pushout.inl f' g' := rfl

@[simp]
theorem pushoutCone_inr {A B D : C} {f f' : A ⟶ B} {g g' : A ⟶ D}
    (hf : f = f') (hg : g = g') [HasPushout f' g'] :
    (pushoutCone hf hg).inr = pushout.inr f' g' := rfl

/-- The given native pullback projections define a cone for equal original target maps. -/
def pullbackCone {A B D : C} {f f' : A ⟶ D} {g g' : B ⟶ D}
    (hf : f = f') (hg : g = g') [HasPullback f' g'] : PullbackCone f g :=
  PullbackCone.mk (pullback.fst f' g') (pullback.snd f' g') (by
    rw [hf, hg]
    exact pullback.condition)

/-- Equal original target maps preserve the complete native pullback universal property. -/
def pullbackIsLimit {A B D : C} {f f' : A ⟶ D} {g g' : B ⟶ D}
    (hf : f = f') (hg : g = g') [HasPullback f' g'] : IsLimit (pullbackCone hf hg) := by
  cases hf
  cases hg
  exact pullbackIsPullback f g

@[simp]
theorem pullbackCone_fst {A B D : C} {f f' : A ⟶ D} {g g' : B ⟶ D}
    (hf : f = f') (hg : g = g') [HasPullback f' g'] :
    (pullbackCone hf hg).fst = pullback.fst f' g' := rfl

@[simp]
theorem pullbackCone_snd {A B D : C} {f f' : A ⟶ D} {g g' : B ⟶ D}
    (hf : f = f') (hg : g = g') [HasPullback f' g'] :
    (pullbackCone hf hg).snd = pullback.snd f' g' := rfl

end CategoryTheory.ReedyStructure.BoundaryConeCongr

end ReedyPart5

section ReedyPart6

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure.RestrictionCorners

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {X Y : J ⥤ C} (f : X ⟶ Y) {d : D}

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The complete old-source caller latching map remains the original full caller map. -/
theorem belowLatchingMapOfFunctor (X : J ⥤ C) (q : r.Through d) (hq : r.degree q.obj < d) :
    (r.belowStructure d).latchingMapWith (r.restrictBelow X d) ⟨q.obj, hq⟩
      (StageBoundaryCones.belowLatchingCoconeOfFunctor r X q hq)
      (StageBoundaryCones.belowLatchingIsColimitOfFunctor r X q hq) = latchingMap r X q.obj := by
  apply (StageBoundaryCones.belowLatchingIsColimitOfFunctor r X q hq).hom_ext
  intro a
  rw [(r.belowStructure d).latchingMapWith_ι]
  change X.map ((r.belowStructure d).latchingArrow a).hom =
    colimit.ι (r.latchingDiagram X q.obj)
      ((CategoryTheory.ReedyStructure.StageBoundaryCones.belowLatching r q
      hq).functor.obj a) ≫
      latchingMap r X q.obj
  rw [latchingMap_ι r]
  rfl

/-- Every full original latching comparison is retained on the complete restricted source. -/
theorem latchingComparison (q : r.Through d) :
    (r.throughStructure d).latchingComparisonWith
      (Functor.whiskerLeft (r.throughObjects d).ι f) q
      (StageBoundaryCones.latchingCoconeOfFunctor r X q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
      (StageBoundaryCones.latchingCoconeOfFunctor r Y q) =
        colimMap (r.latchingTransformation f q.obj) := by
  apply (StageBoundaryCones.latchingIsColimitOfFunctor r X q).hom_ext
  intro a
  rw [(r.throughStructure d).latchingComparisonWith_ι]
  let b := (CategoryTheory.ReedyStructure.StageBoundaryCones.throughLatching r q).functor.obj a
  change f.app (r.latchingSource b) ≫ colimit.ι (r.latchingDiagram Y q.obj) b =
    colimit.ι (r.latchingDiagram X q.obj) b ≫ colimMap (r.latchingTransformation f q.obj)
  exact (ι_colimMap (r.latchingTransformation f q.obj) b).symm

variable [HasPushouts C]

/-- The original full pushout supplies the complete caller pushout of the restriction corner. -/
def latchingPushout (q : r.Through d) :
    PushoutCocone
      ((r.throughStructure d).latchingMapWith (r.restrictThrough X d) q
        (StageBoundaryCones.latchingCoconeOfFunctor r X q)
        (StageBoundaryCones.latchingIsColimitOfFunctor r X q))
      ((r.throughStructure d).latchingComparisonWith (Functor.whiskerLeft
        (r.throughObjects d).ι f) q
        (StageBoundaryCones.latchingCoconeOfFunctor r X q)
        (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
        (StageBoundaryCones.latchingCoconeOfFunctor r Y q)) :=
  BoundaryConeCongr.pushoutCone (StageBoundaryCones.latchingMapOfFunctor r X q)
    (latchingComparison r f q)

/-- The restricted latching square has the pushout universal property at the chosen latching
object. -/
def latchingPushoutIsColimit (q : r.Through d) : IsColimit (latchingPushout r f q) :=
  BoundaryConeCongr.pushoutIsColimit (StageBoundaryCones.latchingMapOfFunctor r X q)
    (latchingComparison r f q)

/-- The unchanged original chosen latching corner has its precise native endpoint types. -/
def latchingChosenCorner (q : r.Through d) :
    pushout (latchingMap r X q.obj) (colimMap (r.latchingTransformation f q.obj)) ⟶ Y.obj q.obj :=
  (r.throughStructure d).latchingCornerWith (Functor.whiskerLeft (r.throughObjects d).ι f) q
    (StageBoundaryCones.latchingCoconeOfFunctor r X q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
    (StageBoundaryCones.latchingCoconeOfFunctor r Y q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r Y q)
    (latchingPushout r f q) (latchingPushoutIsColimit r f q)

/-- The original restricted chosen corner is exactly the original full corner map. -/
theorem latchingCornerWith_eq (q : r.Through d) : latchingChosenCorner r f q =
    latchingCorner r f q.obj := by
  change (r.throughStructure d).latchingCornerWith (Functor.whiskerLeft (r.throughObjects d).ι f) q
    (StageBoundaryCones.latchingCoconeOfFunctor r X q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
    (StageBoundaryCones.latchingCoconeOfFunctor r Y q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r Y q)
    (latchingPushout r f q) (latchingPushoutIsColimit r f q) = latchingCorner r f q.obj
  apply PushoutCocone.IsColimit.hom_ext (latchingPushoutIsColimit r f q)
  · rw [(r.throughStructure d).latchingCornerWith_inl]
    change f.app q.obj = pushout.inl (latchingMap r X q.obj)
      (colimMap (r.latchingTransformation f q.obj)) ≫ latchingCorner r f q.obj
    exact (latchingCorner_inl r f q.obj).symm
  · rw [(r.throughStructure d).latchingCornerWith_inr, StageBoundaryCones.latchingMapOfFunctor]
    change latchingMap r Y q.obj = pushout.inr (latchingMap r X q.obj)
      (colimMap (r.latchingTransformation f q.obj)) ≫ latchingCorner r f q.obj
    exact (latchingCorner_inr r f q.obj).symm

/-- The full original latching corner and its genuine through-degree restriction are isomorphic
as arrows. -/
def latchingArrowIso (q : r.Through d) :
    Arrow.mk (latchingCorner r f q.obj) ≅
      Arrow.mk (latchingCorner (r.throughStructure d)
        (Functor.whiskerLeft (r.throughObjects d).ι f) q) :=
  Arrow.isoMk' (latchingCorner r f q.obj) (latchingChosenCorner r f q) (Iso.refl _) (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact latchingCornerWith_eq r f q) ≪≫
    latchingCornerWithArrowIso (r.throughStructure d)
      (Functor.whiskerLeft (r.throughObjects d).ι f) q
      (StageBoundaryCones.latchingCoconeOfFunctor r X q)
        (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
      (StageBoundaryCones.latchingCoconeOfFunctor r Y q)
        (StageBoundaryCones.latchingIsColimitOfFunctor r Y q)
      (latchingPushout r f q) (latchingPushoutIsColimit r f q)

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The complete old-source caller matching map remains the original full caller map. -/
theorem belowMatchingMapOfFunctor (X : J ⥤ C) (q : r.Through d) (hq : r.degree q.obj < d) :
    (r.belowStructure d).matchingMapWith (r.restrictBelow X d) ⟨q.obj, hq⟩
      (StageBoundaryCones.belowMatchingConeOfFunctor r X q hq)
      (StageBoundaryCones.belowMatchingIsLimitOfFunctor r X q hq) = matchingMap r X q.obj := by
  apply (StageBoundaryCones.belowMatchingIsLimitOfFunctor r X q hq).hom_ext
  intro a
  rw [(r.belowStructure d).matchingMapWith_π]
  change X.map ((r.belowStructure d).matchingArrow a).hom =
    matchingMap r X q.obj ≫ limit.π (r.matchingDiagram X q.obj)
      ((CategoryTheory.ReedyStructure.StageBoundaryCones.belowMatching r q hq).functor.obj a)
  rw [matchingMap_π r]
  rfl

/-- Every full original matching comparison is retained on the complete restricted source. -/
theorem matchingComparison (q : r.Through d) :
    (r.throughStructure d).matchingComparisonWith
      (Functor.whiskerLeft (r.throughObjects d).ι f) q
      (StageBoundaryCones.matchingConeOfFunctor r X q)
      (StageBoundaryCones.matchingConeOfFunctor r Y q)
      (StageBoundaryCones.matchingIsLimitOfFunctor r Y q) =
        limMap (r.matchingTransformation f q.obj) := by
  apply (StageBoundaryCones.matchingIsLimitOfFunctor r Y q).hom_ext
  intro a
  rw [(r.throughStructure d).matchingComparisonWith_π]
  let b := (CategoryTheory.ReedyStructure.StageBoundaryCones.throughMatching r q).functor.obj a
  change limit.π (r.matchingDiagram X q.obj) b ≫ f.app (r.matchingTarget b) =
    limMap (r.matchingTransformation f q.obj) ≫ limit.π (r.matchingDiagram Y q.obj) b
  exact (limMap_π (r.matchingTransformation f q.obj) b).symm

variable [HasPullbacks C]

/-- The original full pullback supplies the complete caller pullback of the restriction corner. -/
def matchingPullback (q : r.Through d) :
    PullbackCone
      ((r.throughStructure d).matchingComparisonWith (Functor.whiskerLeft
        (r.throughObjects d).ι f) q
        (StageBoundaryCones.matchingConeOfFunctor r X q)
          (StageBoundaryCones.matchingConeOfFunctor r Y q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r Y q))
      ((r.throughStructure d).matchingMapWith (r.restrictThrough Y d) q
        (StageBoundaryCones.matchingConeOfFunctor r Y q)
          (StageBoundaryCones.matchingIsLimitOfFunctor r Y q)) :=
  BoundaryConeCongr.pullbackCone (matchingComparison r f q)
    (StageBoundaryCones.matchingMapOfFunctor r Y q)

/-- The restricted matching square has the pullback universal property at the chosen matching
object. -/
def matchingPullbackIsLimit (q : r.Through d) : IsLimit (matchingPullback r f q) :=
  BoundaryConeCongr.pullbackIsLimit (matchingComparison r f q)
    (StageBoundaryCones.matchingMapOfFunctor r Y q)

/-- The unchanged original chosen matching corner has its precise native endpoint types. -/
def matchingChosenCorner (q : r.Through d) :
    X.obj q.obj ⟶ pullback (limMap (r.matchingTransformation f q.obj)) (matchingMap r Y q.obj) :=
  (r.throughStructure d).matchingCornerWith (Functor.whiskerLeft (r.throughObjects d).ι f) q
    (StageBoundaryCones.matchingConeOfFunctor r X q)
      (StageBoundaryCones.matchingIsLimitOfFunctor r X q)
    (StageBoundaryCones.matchingConeOfFunctor r Y q)
      (StageBoundaryCones.matchingIsLimitOfFunctor r Y q)
    (matchingPullback r f q) (matchingPullbackIsLimit r f q)

/-- The original restricted chosen corner is exactly the original full corner map. -/
theorem matchingCornerWith_eq (q : r.Through d) : matchingChosenCorner r f q =
    matchingCorner r f q.obj := by
  apply pullback.hom_ext
  · have h := (r.throughStructure d).matchingCornerWith_fst
      (Functor.whiskerLeft (r.throughObjects d).ι f) q
      (StageBoundaryCones.matchingConeOfFunctor r X q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r X q)
      (StageBoundaryCones.matchingConeOfFunctor r Y q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r Y q)
      (matchingPullback r f q) (matchingPullbackIsLimit r f q)
    change matchingChosenCorner r f q ≫ pullback.fst (limMap (r.matchingTransformation f q.obj))
      (matchingMap r Y q.obj) = (r.throughStructure d).matchingMapWith (r.restrictThrough X d) q
        (StageBoundaryCones.matchingConeOfFunctor r X q)
          (StageBoundaryCones.matchingIsLimitOfFunctor r X q) at h
    rw [StageBoundaryCones.matchingMapOfFunctor] at h
    exact h.trans (matchingCorner_fst r f q.obj).symm
  · have h := (r.throughStructure d).matchingCornerWith_snd
      (Functor.whiskerLeft (r.throughObjects d).ι f) q
      (StageBoundaryCones.matchingConeOfFunctor r X q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r X q)
      (StageBoundaryCones.matchingConeOfFunctor r Y q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r Y q)
      (matchingPullback r f q) (matchingPullbackIsLimit r f q)
    change matchingChosenCorner r f q ≫ pullback.snd (limMap (r.matchingTransformation f q.obj))
      (matchingMap r Y q.obj) = f.app q.obj at h
    exact h.trans (matchingCorner_snd r f q.obj).symm

/-- The full original matching corner and its genuine through-degree restriction are isomorphic
as arrows. -/
def matchingArrowIso (q : r.Through d) :
    Arrow.mk (matchingCorner r f q.obj) ≅
      Arrow.mk (matchingCorner (r.throughStructure d)
        (Functor.whiskerLeft (r.throughObjects d).ι f) q) :=
  Arrow.isoMk' (matchingCorner r f q.obj) (matchingChosenCorner r f q) (Iso.refl _) (Iso.refl _) (by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact matchingCornerWith_eq r f q) ≪≫
    matchingCornerWithArrowIso (r.throughStructure d)
      (Functor.whiskerLeft (r.throughObjects d).ι f) q
      (StageBoundaryCones.matchingConeOfFunctor r X q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r X q)
      (StageBoundaryCones.matchingConeOfFunctor r Y q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r Y q)
      (matchingPullback r f q) (matchingPullbackIsLimit r f q)

end Matching

end CategoryTheory.ReedyStructure.RestrictionCorners

end ReedyPart6

section ReedyPart7

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.StageCornerMaps

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {X Y : J ⥤ C} (f : X ⟶ Y) {d : D}
  (L : MapFactorizationData (⊤ : MorphismProperty (r.Below d ⥤ C)) ⊤
    (Functor.whiskerLeft (r.belowObjects d).ι f))

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The original lower left factor induces the same incoming comparison at every retained source
object. -/
def latchingIAt (q : r.Through d) :
    colimit (r.latchingDiagram X q.obj) ⟶
      colimit (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerLatchingAt r
      L.Z q) :=
  colimMap (Functor.whiskerLeft
    (CategoryTheory.ReedyStructure.StageBoundaryCones.latchingBelowAt r q) L.i)

@[reassoc]
theorem latchingIAt_ι (q : r.Through d) (a : r.Latching q.obj) :
    colimit.ι (r.latchingDiagram X q.obj) a ≫ latchingIAt r f L q =
      L.i.app ((CategoryTheory.ReedyStructure.StageBoundaryCones.latchingBelowAt r q).obj a) ≫
        colimit.ι (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerLatchingAt r L.Z q)
          a := ι_colimMap _ a

/-- The original lower latching map expressed on the complete original common source. -/
def belowLatchingMapAt (q : r.Through d) (hq : r.degree q.obj < d) :
    colimit (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerLatchingAt r L.Z q) ⟶
      L.Z.obj (⟨q.obj, hq⟩ : r.Below
      d) :=
  (r.belowStructure d).latchingMapWith L.Z ⟨q.obj, hq⟩
    (StageBoundaryCones.belowLatchingCocone r L.Z q hq)
    (StageBoundaryCones.belowLatchingIsColimit r L.Z q hq)

@[reassoc]
theorem belowLatchingMapAt_ι (q : r.Through d) (hq : r.degree q.obj < d) (a : r.Latching q.obj) :
    colimit.ι (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerLatchingAt r L.Z q) a ≫
      belowLatchingMapAt r f L q
      hq =
      L.Z.map (ObjectProperty.homMk (r.latchingArrow a) :
        (CategoryTheory.ReedyStructure.StageBoundaryCones.latchingBelowAt r q).obj a ⟶
          (⟨q.obj, hq⟩ : r.Below d)) :=
  (r.belowStructure d).latchingMapWith_ι L.Z ⟨q.obj, hq⟩
    (StageBoundaryCones.belowLatchingCocone r L.Z q hq)
    (StageBoundaryCones.belowLatchingIsColimit r L.Z q hq)
    ((CategoryTheory.ReedyStructure.StageBoundaryCones.belowLatching r q hq).inverse.obj a)

/-- The actual old source comparison is the unchanged original lower left comparison. -/
theorem belowLatchingComparison (q : r.Through d) (hq : r.degree q.obj < d) :
    (r.belowStructure d).latchingComparisonWith L.i ⟨q.obj, hq⟩
      (StageBoundaryCones.belowLatchingCoconeOfFunctor r X q hq)
      (StageBoundaryCones.belowLatchingIsColimitOfFunctor r X q hq)
      (StageBoundaryCones.belowLatchingCocone r L.Z q hq) = latchingIAt r f L q := by
  apply (StageBoundaryCones.belowLatchingIsColimitOfFunctor r X q hq).hom_ext
  intro a
  rw [(r.belowStructure d).latchingComparisonWith_ι]
  change L.i.app ((r.belowStructure d).latchingSource a) ≫
    colimit.ι (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerLatchingAt r L.Z q)
      ((CategoryTheory.ReedyStructure.StageBoundaryCones.belowLatching r q hq).functor.obj a) =
    colimit.ι (r.latchingDiagram X q.obj)
      ((CategoryTheory.ReedyStructure.StageBoundaryCones.belowLatching r q
      hq).functor.obj a) ≫
      latchingIAt r f L q
  exact (latchingIAt_ι r f L q
    ((CategoryTheory.ReedyStructure.StageBoundaryCones.belowLatching r q hq).functor.obj
    a)).symm

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The original lower right factor induces the same outgoing comparison at every retained
source object. -/
def matchingPAt (q : r.Through d) :
    limit (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerMatchingAt r L.Z q) ⟶
      limit (r.matchingDiagram Y q.obj)
      :=
  limMap (Functor.whiskerLeft
    (CategoryTheory.ReedyStructure.StageBoundaryCones.matchingBelowAt r q) L.p)

@[reassoc]
theorem matchingPAt_π (q : r.Through d) (a : r.Matching q.obj) :
    matchingPAt r f L q ≫ limit.π (r.matchingDiagram Y q.obj) a =
      limit.π (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerMatchingAt r L.Z q) a ≫
        L.p.app ((CategoryTheory.ReedyStructure.StageBoundaryCones.matchingBelowAt
          r q).obj a) := limMap_π _ a

/-- The original lower matching map expressed on the complete original common source. -/
def belowMatchingMapAt (q : r.Through d) (hq : r.degree q.obj < d) :
    L.Z.obj (⟨q.obj, hq⟩ : r.Below d) ⟶
      limit (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerMatchingAt r L.Z q)
      :=
  (r.belowStructure d).matchingMapWith L.Z ⟨q.obj, hq⟩
    (StageBoundaryCones.belowMatchingCone r L.Z q hq)
    (StageBoundaryCones.belowMatchingIsLimit r L.Z q hq)

@[reassoc]
theorem belowMatchingMapAt_π (q : r.Through d) (hq : r.degree q.obj < d) (a : r.Matching q.obj) :
    belowMatchingMapAt r f L q hq ≫
      limit.π (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerMatchingAt r L.Z q) a
      =
      L.Z.map (ObjectProperty.homMk (r.matchingArrow a) :
        (⟨q.obj, hq⟩ : r.Below d) ⟶
          (CategoryTheory.ReedyStructure.StageBoundaryCones.matchingBelowAt r q).obj a) :=
  (r.belowStructure d).matchingMapWith_π L.Z ⟨q.obj, hq⟩
    (StageBoundaryCones.belowMatchingCone r L.Z q hq)
    (StageBoundaryCones.belowMatchingIsLimit r L.Z q hq)
    ((CategoryTheory.ReedyStructure.StageBoundaryCones.belowMatching r q hq).inverse.obj a)

/-- The actual old target comparison is the unchanged original lower right comparison. -/
theorem belowMatchingComparison (q : r.Through d) (hq : r.degree q.obj < d) :
    (r.belowStructure d).matchingComparisonWith L.p ⟨q.obj, hq⟩
      (StageBoundaryCones.belowMatchingCone r L.Z q hq)
      (StageBoundaryCones.belowMatchingConeOfFunctor r Y q hq)
      (StageBoundaryCones.belowMatchingIsLimitOfFunctor r Y q hq) = matchingPAt r f L q := by
  apply (StageBoundaryCones.belowMatchingIsLimitOfFunctor r Y q hq).hom_ext
  intro a
  rw [(r.belowStructure d).matchingComparisonWith_π]
  change limit.π (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerMatchingAt r L.Z q)
      ((CategoryTheory.ReedyStructure.StageBoundaryCones.belowMatching r q hq).functor.obj a) ≫
        L.p.app ((r.belowStructure d).matchingTarget a) =
    matchingPAt r f L q ≫ limit.π (r.matchingDiagram Y q.obj)
      ((CategoryTheory.ReedyStructure.StageBoundaryCones.belowMatching r q hq).functor.obj a)
  exact (matchingPAt_π r f L q
    ((CategoryTheory.ReedyStructure.StageBoundaryCones.belowMatching r q hq).functor.obj
    a)).symm

end Matching

section Stage

variable [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C] {P Q : MorphismProperty C} (F : FactorizationData P Q)

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPushouts C] [HasPullbacks C] in
/-- The new-degree lower incoming comparison is exactly the actual source factory boundary
comparison. -/
theorem latchingIAt_new (q : r.Through d) (hq : r.degree q.obj = d) :
    latchingIAt r f L q = StageFactory.latchingI r f L q.obj hq := rfl

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C] [HasPullbacks C] in
/-- The new-degree lower outgoing comparison is exactly the actual source factory boundary
comparison. -/
theorem matchingPAt_new (q : r.Through d) (hq : r.degree q.obj = d) :
    matchingPAt r f L q = StageFactory.matchingP r f L q.obj hq := rfl

/-- The next prefix retains the exact original old coefficient object comparison. -/
def oldObjIso (q : r.Through d) (hq : r.degree q.obj < d) :
    (StageFactory.nextPrefix r f L F).Z.obj q ≅ L.Z.obj (⟨q.obj, hq⟩ : r.Below d) :=
  (StageFactory.layer r f L F).oldIso q hq

/-- The next prefix retains the exact actual factory coefficient object comparison. -/
def newObjIso (q : r.Through d) (hq : r.degree q.obj = d) :
    (StageFactory.nextPrefix r f L F).Z.obj q ≅
      (StageFactory.coefficientFactor r f L F q.obj hq).Z :=
  (StageFactory.layer r f L F).newIso q hq

/-- The latching cocone of the extended factorization prefix, inherited from its layer data. -/
def nextLatchingCocone (q : r.Through d) :
    Cocone ((r.throughStructure d).latchingDiagram (StageFactory.nextPrefix r f L F).Z q) :=
  StageBoundaryCones.latchingCocone r (StageFactory.layer r f L F) q

/-- The latching cocone inherited by the extended factorization prefix is a colimit. -/
def nextLatchingIsColimit (q : r.Through d) : IsColimit (nextLatchingCocone r f L F q) :=
  StageBoundaryCones.latchingIsColimit r (StageFactory.layer r f L F) q

theorem nextLatchingCocone_ι (q : r.Through d) (a : (r.throughStructure d).Latching q) :
    (nextLatchingCocone r f L F q).ι.app a =
      (oldObjIso r f L F ((r.throughStructure d).latchingSource a)
        (CategoryTheory.ReedyStructure.StageBoundaryCones.latchingSource_lt r q a)).hom ≫
        colimit.ι (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerLatchingAt r L.Z q)
          ((CategoryTheory.ReedyStructure.StageBoundaryCones.throughLatching r
            q).functor.obj a) := rfl

/-- The matching cone of the extended factorization prefix, inherited from its layer data. -/
def nextMatchingCone (q : r.Through d) :
    Cone ((r.throughStructure d).matchingDiagram (StageFactory.nextPrefix r f L F).Z q) :=
  StageBoundaryCones.matchingCone r (StageFactory.layer r f L F) q

/-- The matching cone inherited by the extended factorization prefix is a limit. -/
def nextMatchingIsLimit (q : r.Through d) : IsLimit (nextMatchingCone r f L F q) :=
  StageBoundaryCones.matchingIsLimit r (StageFactory.layer r f L F) q

theorem nextMatchingCone_π (q : r.Through d) (a : (r.throughStructure d).Matching q) :
    (nextMatchingCone r f L F q).π.app a =
      limit.π (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerMatchingAt r L.Z q)
        ((CategoryTheory.ReedyStructure.StageBoundaryCones.throughMatching r q).functor.obj a) ≫
        (oldObjIso r f L F ((r.throughStructure d).matchingTarget a)
          (CategoryTheory.ReedyStructure.StageBoundaryCones.matchingTarget_lt r q a)).inv := rfl

theorem nextI_old (q : r.Through d) (hq : r.degree q.obj < d) :
    (StageFactory.nextPrefix r f L F).i.app q =
      L.i.app (⟨q.obj, hq⟩ : r.Below d) ≫ (oldObjIso r f L F q hq).inv :=
  StageFactory.leftTransformation_old r f L F q hq

theorem nextP_old (q : r.Through d) (hq : r.degree q.obj < d) :
    (StageFactory.nextPrefix r f L F).p.app q =
      (oldObjIso r f L F q hq).hom ≫ L.p.app (⟨q.obj, hq⟩ : r.Below d) :=
  StageFactory.rightTransformation_old r f L F q hq

theorem nextI_new (q : r.Through d) (hq : r.degree q.obj = d) :
    (StageFactory.nextPrefix r f L F).i.app q =
      StageFactory.newI r f L F q.obj hq ≫ (newObjIso r f L F q hq).inv :=
  StageFactory.leftTransformation_new r f L F q hq

theorem nextP_new (q : r.Through d) (hq : r.degree q.obj = d) :
    (StageFactory.nextPrefix r f L F).p.app q =
      (newObjIso r f L F q hq).hom ≫ StageFactory.newP r f L F q.obj hq :=
  StageFactory.rightTransformation_new r f L F q hq

theorem nextZ_map_incoming {k q : r.Through d} (γ : k ⟶ q) (hγ : r.direct γ.hom)
    (hk : r.degree k.obj < d) (hq : r.degree q.obj = d) :
    (StageFactory.nextPrefix r f L F).Z.map γ =
      (oldObjIso r f L F k hk).hom ≫
        (StageFactory.layer r f L F).incomingInjection γ hγ hk hq ≫
        StageFactory.newIncoming r f L F q.obj hq ≫ (newObjIso r f L F q hq).inv := by
  change (StageFactory.layer r f L F).extension.map γ =
    (StageFactory.layer r f L F).incomingMap γ hγ hk hq
  rw [(StageFactory.layer r f L F).extension_direct,
    (StageFactory.layer r f L F).directMap_incoming]

theorem nextZ_map_outgoing {q k : r.Through d} (γ : q ⟶ k) (hγ : r.inverse γ.hom)
    (hq : r.degree q.obj = d) (hk : r.degree k.obj < d) :
    (StageFactory.nextPrefix r f L F).Z.map γ =
      (newObjIso r f L F q hq).hom ≫ StageFactory.newOutgoing r f L F q.obj hq ≫
        (StageFactory.layer r f L F).outgoingProjection γ hγ hq hk ≫
          (oldObjIso r f L F k hk).inv := by
  change (StageFactory.layer r f L F).extension.map γ =
    (StageFactory.layer r f L F).outgoingMap γ hγ hq hk
  rw [(StageFactory.layer r f L F).extension_inverse,
    (StageFactory.layer r f L F).inverseMap_outgoing]

/-- Every original old-degree map remains the supplied lower map with the same endpoint
transports. -/
theorem nextZ_map_old {k q : r.Through d} (γ : k ⟶ q)
    (hk : r.degree k.obj < d) (hq : r.degree q.obj < d) :
    (StageFactory.nextPrefix r f L F).Z.map γ =
      (oldObjIso r f L F k hk).hom ≫
        L.Z.map (ObjectProperty.homMk γ.hom : (⟨k.obj, hk⟩ : r.Below d) ⟶ ⟨q.obj, hq⟩) ≫
        (oldObjIso r f L F q hq).inv :=
  (StageFactory.layer r f L F).extension_map_old γ hk hq

/-- The next source-produced prefix keeps the full original lower left latching comparison. -/
theorem throughLatchingComparison (q : r.Through d) :
    (r.throughStructure d).latchingComparisonWith (StageFactory.nextPrefix r f L F).i q
      (StageBoundaryCones.latchingCoconeOfFunctor r X q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
      (nextLatchingCocone r f L F q) = latchingIAt r f L q := by
  apply (StageBoundaryCones.latchingIsColimitOfFunctor r X q).hom_ext
  intro a
  rw [(r.throughStructure d).latchingComparisonWith_ι]
  let k := (r.throughStructure d).latchingSource a
  let hk := CategoryTheory.ReedyStructure.StageBoundaryCones.latchingSource_lt r q a
  let b := (CategoryTheory.ReedyStructure.StageBoundaryCones.throughLatching r q).functor.obj a
  let ι : L.Z.obj (⟨k.obj, hk⟩ : r.Below d) ⟶
    colimit (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerLatchingAt
    r L.Z q) :=
    colimit.ι (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerLatchingAt r L.Z q) b
  change (StageFactory.nextPrefix r f L F).i.app k ≫
    (oldObjIso r f L F k hk).hom ≫ ι =
    colimit.ι (r.latchingDiagram X q.obj) b ≫ latchingIAt r f L q
  rw [nextI_old, Category.assoc, Iso.inv_hom_id_assoc]
  exact (latchingIAt_ι r f L q b).symm

/-- The next source-produced prefix keeps the full original lower right matching comparison. -/
theorem throughMatchingComparison (q : r.Through d) :
    (r.throughStructure d).matchingComparisonWith (StageFactory.nextPrefix r f L F).p q
      (nextMatchingCone r f L F q)
      (StageBoundaryCones.matchingConeOfFunctor r Y q)
      (StageBoundaryCones.matchingIsLimitOfFunctor r Y q) = matchingPAt r f L q := by
  apply (StageBoundaryCones.matchingIsLimitOfFunctor r Y q).hom_ext
  intro a
  rw [(r.throughStructure d).matchingComparisonWith_π]
  let k := (r.throughStructure d).matchingTarget a
  let hk := CategoryTheory.ReedyStructure.StageBoundaryCones.matchingTarget_lt r q a
  let b := (CategoryTheory.ReedyStructure.StageBoundaryCones.throughMatching r q).functor.obj a
  let π : limit (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerMatchingAt r L.Z q) ⟶
    L.Z.obj (⟨k.obj, hk⟩ :
    r.Below d) :=
    limit.π (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerMatchingAt r L.Z q) b
  change (π ≫ (oldObjIso r f L F k hk).inv) ≫
    (StageFactory.nextPrefix r f L F).p.app k =
    matchingPAt r f L q ≫ limit.π (r.matchingDiagram Y q.obj) b
  rw [nextP_old, Category.assoc, Iso.inv_hom_id_assoc]
  exact (matchingPAt_π r f L q b).symm

/-- At the new degree the complete latching map is the actual factory incoming map and original
object transport. -/
theorem throughLatchingMap_new (q : r.Through d) (hq : r.degree q.obj = d) :
    (r.throughStructure d).latchingMapWith (StageFactory.nextPrefix r f L F).Z q
      (nextLatchingCocone r f L F q)
      (nextLatchingIsColimit r f L F q) =
      StageFactory.newIncoming r f L F q.obj hq ≫ (newObjIso r f L F q hq).inv := by
  apply (nextLatchingIsColimit r f L F q).hom_ext
  intro a
  rw [(r.throughStructure d).latchingMapWith_ι]
  let k := (r.throughStructure d).latchingSource a
  let hk := CategoryTheory.ReedyStructure.StageBoundaryCones.latchingSource_lt r q a
  let b := (CategoryTheory.ReedyStructure.StageBoundaryCones.throughLatching r q).functor.obj a
  let γ := (r.throughStructure d).latchingArrow a
  have hγ : r.direct γ.hom := (r.throughStructure d).latchingArrow_mem a
  let ι : L.Z.obj (⟨k.obj, hk⟩ : r.Below d) ⟶ (nextLatchingCocone r f L F q).pt :=
    colimit.ι (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerLatchingAt r L.Z q) b
  let ni : (nextLatchingCocone r f L F q).pt ⟶
    (StageFactory.coefficientFactor r f L F q.obj hq).Z :=
    StageFactory.newIncoming r f L F q.obj hq
  have hleg : (nextLatchingCocone r f L F q).ι.app a = (oldObjIso r f L F k hk).hom ≫ ι := rfl
  rw [hleg]
  change (StageFactory.nextPrefix r f L F).Z.map γ =
    ((oldObjIso r f L F k hk).hom ≫ ι) ≫ (ni ≫ (newObjIso r f L F q hq).inv)
  rw [Category.assoc]
  have hm := nextZ_map_incoming r f L F γ hγ hk hq
  change (StageFactory.nextPrefix r f L F).Z.map γ =
    (oldObjIso r f L F k hk).hom ≫ ι ≫ ni ≫ (newObjIso r f L F q hq).inv at hm
  exact hm

/-- At the new degree the complete matching map is the original object transport and actual
factory outgoing map. -/
theorem throughMatchingMap_new (q : r.Through d) (hq : r.degree q.obj = d) :
    (r.throughStructure d).matchingMapWith (StageFactory.nextPrefix r f L F).Z q
      (nextMatchingCone r f L F q)
      (nextMatchingIsLimit r f L F q) =
      (newObjIso r f L F q hq).hom ≫ StageFactory.newOutgoing r f L F q.obj hq := by
  let o : (StageFactory.coefficientFactor r f L F q.obj hq).Z ⟶ (nextMatchingCone r f L F q).pt :=
    StageFactory.newOutgoing r f L F q.obj hq
  let m : (StageFactory.nextPrefix r f L F).Z.obj q ⟶ (nextMatchingCone r f L F q).pt :=
    (newObjIso r f L F q hq).hom ≫ o
  change (r.throughStructure d).matchingMapWith (StageFactory.nextPrefix r f L F).Z q
    (nextMatchingCone r f L F q) (nextMatchingIsLimit r f L F q) = m
  apply (nextMatchingIsLimit r f L F q).hom_ext
  intro a
  rw [(r.throughStructure d).matchingMapWith_π]
  let k := (r.throughStructure d).matchingTarget a
  let hk := CategoryTheory.ReedyStructure.StageBoundaryCones.matchingTarget_lt r q a
  let b := (CategoryTheory.ReedyStructure.StageBoundaryCones.throughMatching r q).functor.obj a
  let γ := (r.throughStructure d).matchingArrow a
  have hγ : r.inverse γ.hom := (r.throughStructure d).matchingArrow_mem a
  let π : (nextMatchingCone r f L F q).pt ⟶ L.Z.obj (⟨k.obj, hk⟩ : r.Below d) :=
    limit.π (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerMatchingAt r L.Z q) b
  have hleg : (nextMatchingCone r f L F q).π.app a = π ≫ (oldObjIso r f L F k hk).inv := rfl
  rw [hleg]
  change (StageFactory.nextPrefix r f L F).Z.map γ =
    ((newObjIso r f L F q hq).hom ≫ o) ≫ (π ≫ (oldObjIso r f L F k hk).inv)
  rw [Category.assoc]
  have hm := nextZ_map_outgoing r f L F γ hγ hq hk
  change (StageFactory.nextPrefix r f L F).Z.map γ =
    (newObjIso r f L F q hq).hom ≫ o ≫ π ≫ (oldObjIso r f L F k hk).inv at hm
  exact hm

/-- At every old degree the complete latching map is the original lower latching map and
endpoint transport. -/
theorem throughLatchingMap_old (q : r.Through d) (hq : r.degree q.obj < d) :
    (r.throughStructure d).latchingMapWith (StageFactory.nextPrefix r f L F).Z q
      (nextLatchingCocone r f L F q) (nextLatchingIsColimit r f L F q) =
      belowLatchingMapAt r f L q hq ≫ (oldObjIso r f L F q hq).inv := by
  let M : (nextLatchingCocone r f L F q).pt ⟶ L.Z.obj (⟨q.obj, hq⟩ : r.Below d) :=
    belowLatchingMapAt r f L q hq
  let m : (nextLatchingCocone r f L F q).pt ⟶ (StageFactory.nextPrefix r f L F).Z.obj q :=
    M ≫ (oldObjIso r f L F q hq).inv
  change (r.throughStructure d).latchingMapWith (StageFactory.nextPrefix r f L F).Z q
    (nextLatchingCocone r f L F q) (nextLatchingIsColimit r f L F q) = m
  apply (nextLatchingIsColimit r f L F q).hom_ext
  intro a
  rw [(r.throughStructure d).latchingMapWith_ι]
  let k := (r.throughStructure d).latchingSource a
  let hk := CategoryTheory.ReedyStructure.StageBoundaryCones.latchingSource_lt r q a
  let b := (CategoryTheory.ReedyStructure.StageBoundaryCones.throughLatching r q).functor.obj a
  let γ := (r.throughStructure d).latchingArrow a
  let ι : L.Z.obj (⟨k.obj, hk⟩ : r.Below d) ⟶ (nextLatchingCocone r f L F q).pt :=
    colimit.ι (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerLatchingAt r L.Z q) b
  have hleg : (nextLatchingCocone r f L F q).ι.app a = (oldObjIso r f L F k hk).hom ≫ ι := rfl
  have hι : ι ≫ M = L.Z.map (ObjectProperty.homMk γ.hom :
      (⟨k.obj, hk⟩ : r.Below d) ⟶ ⟨q.obj, hq⟩) := belowLatchingMapAt_ι r f L q hq b
  rw [hleg]
  change (StageFactory.nextPrefix r f L F).Z.map γ =
    ((oldObjIso r f L F k hk).hom ≫ ι) ≫ (M ≫ (oldObjIso r f L F q hq).inv)
  rw [Category.assoc, ← Category.assoc ι M, hι]
  exact nextZ_map_old r f L F γ hk hq

/-- At every old degree the complete matching map is the endpoint transport and original lower
matching map. -/
theorem throughMatchingMap_old (q : r.Through d) (hq : r.degree q.obj < d) :
    (r.throughStructure d).matchingMapWith (StageFactory.nextPrefix r f L F).Z q
      (nextMatchingCone r f L F q) (nextMatchingIsLimit r f L F q) =
      (oldObjIso r f L F q hq).hom ≫ belowMatchingMapAt r f L q hq := by
  let M : L.Z.obj (⟨q.obj, hq⟩ : r.Below d) ⟶ (nextMatchingCone r f L F q).pt :=
    belowMatchingMapAt r f L q hq
  let m : (StageFactory.nextPrefix r f L F).Z.obj q ⟶ (nextMatchingCone r f L F q).pt :=
    (oldObjIso r f L F q hq).hom ≫ M
  change (r.throughStructure d).matchingMapWith (StageFactory.nextPrefix r f L F).Z q
    (nextMatchingCone r f L F q) (nextMatchingIsLimit r f L F q) = m
  apply (nextMatchingIsLimit r f L F q).hom_ext
  intro a
  rw [(r.throughStructure d).matchingMapWith_π]
  let k := (r.throughStructure d).matchingTarget a
  let hk := CategoryTheory.ReedyStructure.StageBoundaryCones.matchingTarget_lt r q a
  let b := (CategoryTheory.ReedyStructure.StageBoundaryCones.throughMatching r q).functor.obj a
  let γ := (r.throughStructure d).matchingArrow a
  let π : (nextMatchingCone r f L F q).pt ⟶ L.Z.obj (⟨k.obj, hk⟩ : r.Below d) :=
    limit.π (CategoryTheory.ReedyStructure.StageBoundaryCones.lowerMatchingAt r L.Z q) b
  have hleg : (nextMatchingCone r f L F q).π.app a = π ≫ (oldObjIso r f L F k hk).inv := rfl
  have hπ : M ≫ π = L.Z.map (ObjectProperty.homMk γ.hom :
      (⟨q.obj, hq⟩ : r.Below d) ⟶ ⟨k.obj, hk⟩) := belowMatchingMapAt_π r f L q hq b
  rw [hleg]
  change (StageFactory.nextPrefix r f L F).Z.map γ =
    ((oldObjIso r f L F q hq).hom ≫ M) ≫ (π ≫ (oldObjIso r f L F k hk).inv)
  rw [Category.assoc, ← Category.assoc M π, hπ]
  exact nextZ_map_old r f L F γ hq hk

end Stage

end CategoryTheory.ReedyStructure.StageCornerMaps

end ReedyPart7

section ReedyPart8

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.StageCorners

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y) {d : D}
  (L : MapFactorizationData (⊤ : MorphismProperty (r.Below d ⥤ C)) ⊤
    (Functor.whiskerLeft (r.belowObjects d).ι f))
  {P Q : MorphismProperty C} (F : FactorizationData P Q)

/-- The same original pushout is a complete corner source for the actual next prefix. -/
def latchingPushout (q : r.Through d) :
    PushoutCocone
      ((r.throughStructure d).latchingMapWith (r.restrictThrough X d) q
        (StageBoundaryCones.latchingCoconeOfFunctor r X
        q) (StageBoundaryCones.latchingIsColimitOfFunctor r X q))
      ((r.throughStructure d).latchingComparisonWith (StageFactory.nextPrefix r f L F).i q
        (StageBoundaryCones.latchingCoconeOfFunctor r X q)
          (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
        (StageCornerMaps.nextLatchingCocone r f L F q)) :=
  BoundaryConeCongr.pushoutCone (StageBoundaryCones.latchingMapOfFunctor r X q)
    (StageCornerMaps.throughLatchingComparison r f L F q)

/-- The extended prefix latching square has the pushout universal property. -/
def latchingPushoutIsColimit (q : r.Through d) : IsColimit (latchingPushout r f L F q) :=
  BoundaryConeCongr.pushoutIsColimit (StageBoundaryCones.latchingMapOfFunctor r X q)
    (StageCornerMaps.throughLatchingComparison r f L F q)

/-- The actual next-prefix corner with its exact original native source and target types. -/
def latchingChosen (q : r.Through d) :
    pushout (latchingMap r X q.obj) (StageCornerMaps.latchingIAt r f L q) ⟶
      (StageFactory.nextPrefix r f L F).Z.obj q :=
  (r.throughStructure d).latchingCornerWith (StageFactory.nextPrefix r f L F).i q
    (StageBoundaryCones.latchingCoconeOfFunctor r X q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
    (StageCornerMaps.nextLatchingCocone r f L F q) (StageCornerMaps.nextLatchingIsColimit r f L F q)
      (latchingPushout r
    f L F q) (latchingPushoutIsColimit r f L F q)

theorem latchingChosen_inl (q : r.Through d) :
    pushout.inl (latchingMap r X q.obj) (StageCornerMaps.latchingIAt r f L q) ≫
      latchingChosen r f L F q =
      (StageFactory.nextPrefix r f L F).i.app q :=
  (r.throughStructure d).latchingCornerWith_inl (StageFactory.nextPrefix r f L F).i q
    (StageBoundaryCones.latchingCoconeOfFunctor r X q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
      (StageCornerMaps.nextLatchingCocone r f L F q)
        (StageCornerMaps.nextLatchingIsColimit r f L F q) (latchingPushout
      r f L F q) (latchingPushoutIsColimit r f L F q)

theorem latchingChosen_inr (q : r.Through d) :
    pushout.inr (latchingMap r X q.obj) (StageCornerMaps.latchingIAt r f L q) ≫
      latchingChosen r f L F q =
      (r.throughStructure d).latchingMapWith (StageFactory.nextPrefix r f L F).Z q
        (StageCornerMaps.nextLatchingCocone r
        f L F q) (StageCornerMaps.nextLatchingIsColimit r f L F q) :=
  (r.throughStructure d).latchingCornerWith_inr (StageFactory.nextPrefix r f L F).i q
    (StageBoundaryCones.latchingCoconeOfFunctor r X q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
      (StageCornerMaps.nextLatchingCocone r f L F q)
        (StageCornerMaps.nextLatchingIsColimit r f L F q) (latchingPushout
      r f L F q) (latchingPushoutIsColimit r f L F q)

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C] in
/-- The same original native pushout is complete for the original lower factor corner. -/
def belowLatchingPushout (q : r.Through d) (hq : r.degree q.obj < d) :
    PushoutCocone
      ((r.belowStructure d).latchingMapWith (r.restrictBelow X d) (⟨q.obj, hq⟩ : r.Below d)
        (StageBoundaryCones.belowLatchingCoconeOfFunctor r X q hq)
          (StageBoundaryCones.belowLatchingIsColimitOfFunctor r
        X q hq))
      ((r.belowStructure d).latchingComparisonWith L.i (⟨q.obj, hq⟩ : r.Below d)
        (StageBoundaryCones.belowLatchingCoconeOfFunctor r X q hq)
          (StageBoundaryCones.belowLatchingIsColimitOfFunctor r
        X q hq) (StageBoundaryCones.belowLatchingCocone r L.Z q hq)) :=
  BoundaryConeCongr.pushoutCone (RestrictionCorners.belowLatchingMapOfFunctor r X q hq)
    (StageCornerMaps.belowLatchingComparison r f L q hq)

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C] in
/-- The unchanged lower latching square has the pushout universal property below the current
degree. -/
def belowLatchingPushoutIsColimit (q : r.Through d) (hq : r.degree q.obj < d) :
    IsColimit (belowLatchingPushout r f L q hq) :=
  BoundaryConeCongr.pushoutIsColimit (RestrictionCorners.belowLatchingMapOfFunctor r X q hq)
    (StageCornerMaps.belowLatchingComparison r f L q hq)

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C] in
/-- The original lower corner on the same original native pushout. -/
def belowLatchingChosen (q : r.Through d) (hq : r.degree q.obj < d) :
    pushout (latchingMap r X q.obj) (StageCornerMaps.latchingIAt r f L q) ⟶
      L.Z.obj (⟨q.obj, hq⟩ : r.Below d) :=
  (r.belowStructure d).latchingCornerWith L.i (⟨q.obj, hq⟩ : r.Below d)
    (StageBoundaryCones.belowLatchingCoconeOfFunctor
    r X q hq) (StageBoundaryCones.belowLatchingIsColimitOfFunctor r X q hq)
      (StageBoundaryCones.belowLatchingCocone r
    L.Z q hq) (StageBoundaryCones.belowLatchingIsColimit r L.Z q hq)
      (belowLatchingPushout r f L q hq)
    (belowLatchingPushoutIsColimit r f L q hq)

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C] in
theorem belowLatchingChosen_inl (q : r.Through d) (hq : r.degree q.obj < d) :
    pushout.inl (latchingMap r X q.obj) (StageCornerMaps.latchingIAt r f L q) ≫
      belowLatchingChosen r f L q hq = L.i.app (⟨q.obj, hq⟩ : r.Below d) :=
  (r.belowStructure d).latchingCornerWith_inl L.i (⟨q.obj, hq⟩ : r.Below d)
    (StageBoundaryCones.belowLatchingCoconeOfFunctor r X q hq)
      (StageBoundaryCones.belowLatchingIsColimitOfFunctor r X q
      hq) (StageBoundaryCones.belowLatchingCocone r L.Z q hq)
        (StageBoundaryCones.belowLatchingIsColimit r L.Z q hq)
      (belowLatchingPushout r f L q hq) (belowLatchingPushoutIsColimit r f L q hq)

omit [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C] in
theorem belowLatchingChosen_inr (q : r.Through d) (hq : r.degree q.obj < d) :
    pushout.inr (latchingMap r X q.obj) (StageCornerMaps.latchingIAt r f L q) ≫
      belowLatchingChosen r f L q hq = StageCornerMaps.belowLatchingMapAt r f L q hq :=
  (r.belowStructure d).latchingCornerWith_inr L.i (⟨q.obj, hq⟩ : r.Below d)
    (StageBoundaryCones.belowLatchingCoconeOfFunctor r X q hq)
      (StageBoundaryCones.belowLatchingIsColimitOfFunctor r X q
      hq) (StageBoundaryCones.belowLatchingCocone r L.Z q hq)
        (StageBoundaryCones.belowLatchingIsColimit r L.Z q hq)
      (belowLatchingPushout r f L q hq) (belowLatchingPushoutIsColimit r f L q hq)

/-- The actual new-degree chosen corner is the original factory left map under its original
object comparison. -/
theorem latchingChosen_new (q : r.Through d) (hq : r.degree q.obj = d) :
    latchingChosen r f L F q ≫ (StageCornerMaps.newObjIso r f L F q hq).hom =
      (StageFactory.coefficientFactor r f L F q.obj hq).i := by
  let c : StageFactory.coefficientSource r f L q.obj hq ⟶
    (StageFactory.nextPrefix r f L F).Z.obj q :=
    latchingChosen r f L F q
  change c ≫ (StageCornerMaps.newObjIso r f L F q hq).hom =
    (StageFactory.coefficientFactor r f L F q.obj hq).i
  apply pushout.hom_ext
  · have hi : pushout.inl (latchingMap r X q.obj) (StageFactory.latchingI r f L q.obj hq) ≫ c =
        (StageFactory.nextPrefix r f L F).i.app q := latchingChosen_inl r f L F q
    rw [← Category.assoc, hi, StageCornerMaps.nextI_new r f L F q hq,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  · have hi : pushout.inr (latchingMap r X q.obj) (StageFactory.latchingI r f L q.obj hq) ≫ c =
        (r.throughStructure d).latchingMapWith (StageFactory.nextPrefix r f L F).Z q
          (StageCornerMaps.nextLatchingCocone r f L F q)
            (StageCornerMaps.nextLatchingIsColimit r f L F q) :=
        latchingChosen_inr r f L F q
    rw [← Category.assoc, hi, StageCornerMaps.throughLatchingMap_new r f L F q hq,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

/-- Every actual old-degree chosen corner is the unchanged lower corner under its original
object comparison. -/
theorem latchingChosen_old (q : r.Through d) (hq : r.degree q.obj < d) :
    latchingChosen r f L F q ≫
      (StageCornerMaps.oldObjIso r f L F q hq).hom = belowLatchingChosen r f L q hq := by
  apply pushout.hom_ext
  · rw [← Category.assoc, latchingChosen_inl, StageCornerMaps.nextI_old r f L F q hq,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, belowLatchingChosen_inl]
  · rw [← Category.assoc, latchingChosen_inr, StageCornerMaps.throughLatchingMap_old r f L F q hq,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, belowLatchingChosen_inr]

/-- The canonical actual new-degree latching corner is Arrow-isomorphic to the original
coefficient factory left map. -/
def latchingArrowIsoNew (q : r.Through d) (hq : r.degree q.obj = d) :
    Arrow.mk (latchingCorner (r.throughStructure d) (StageFactory.nextPrefix r f L F).i q) ≅
      Arrow.mk ((StageFactory.coefficientFactor r f L F q.obj hq).i) :=
  (latchingCornerWithArrowIso (r.throughStructure d) (StageFactory.nextPrefix r f L F).i q
    (StageBoundaryCones.latchingCoconeOfFunctor r X q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
    (StageCornerMaps.nextLatchingCocone r f L F q) (StageCornerMaps.nextLatchingIsColimit r f L F q)
      (latchingPushout r
    f L F q) (latchingPushoutIsColimit r f L F q)).symm ≪≫
    Arrow.isoMk' (latchingChosen r f L F q) ((StageFactory.coefficientFactor r f L F q.obj hq).i)
      (Iso.refl _) (StageCornerMaps.newObjIso r f L F q hq) (by
        let c : StageFactory.coefficientSource r f L q.obj hq ⟶
          (StageFactory.nextPrefix r f L F).Z.obj q :=
          latchingChosen r f L F q
        change (𝟙 (StageFactory.coefficientSource r f L q.obj hq)) ≫
          (StageFactory.coefficientFactor r f L F q.obj hq).i =
          c ≫ (StageCornerMaps.newObjIso r f L F q hq).hom
        rw [Category.id_comp]
        exact (latchingChosen_new r f L F q hq).symm)

/-- The canonical actual old-degree latching corner is Arrow-isomorphic to the original lower
factor corner. -/
def latchingArrowIsoOld (q : r.Through d) (hq : r.degree q.obj < d) :
    Arrow.mk (latchingCorner (r.throughStructure d) (StageFactory.nextPrefix r f L F).i q) ≅
      Arrow.mk (latchingCorner (r.belowStructure d) L.i (⟨q.obj, hq⟩ : r.Below d)) :=
  (latchingCornerWithArrowIso (r.throughStructure d) (StageFactory.nextPrefix r f L F).i q
    (StageBoundaryCones.latchingCoconeOfFunctor r X q)
      (StageBoundaryCones.latchingIsColimitOfFunctor r X q)
    (StageCornerMaps.nextLatchingCocone r f L F q) (StageCornerMaps.nextLatchingIsColimit r f L F q)
      (latchingPushout r
    f L F q) (latchingPushoutIsColimit r f L F q)).symm ≪≫
    Arrow.isoMk' (latchingChosen r f L F q) (belowLatchingChosen r f L q hq)
      (Iso.refl _) (StageCornerMaps.oldObjIso r f L F q hq) (by
        simp only [Iso.refl_hom, Category.id_comp]
        exact (latchingChosen_old r f L F q hq).symm) ≪≫
    latchingCornerWithArrowIso (r.belowStructure d) L.i (⟨q.obj, hq⟩ : r.Below d)
      (StageBoundaryCones.belowLatchingCoconeOfFunctor r X q hq)
        (StageBoundaryCones.belowLatchingIsColimitOfFunctor r X
      q hq) (StageBoundaryCones.belowLatchingCocone r L.Z q hq)
        (StageBoundaryCones.belowLatchingIsColimit r L.Z q hq)
      (belowLatchingPushout r f L q hq) (belowLatchingPushoutIsColimit r f L q hq)

/-- The same original pullback is a complete corner target for the actual next prefix. -/
def matchingPullback (q : r.Through d) :
    PullbackCone
      ((r.throughStructure d).matchingComparisonWith (StageFactory.nextPrefix r f L F).p q
        (StageCornerMaps.nextMatchingCone r f L F q)
          (StageBoundaryCones.matchingConeOfFunctor r Y q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r Y q))
      ((r.throughStructure d).matchingMapWith (r.restrictThrough Y d) q
        (StageBoundaryCones.matchingConeOfFunctor r Y q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r Y q)) :=
  BoundaryConeCongr.pullbackCone (StageCornerMaps.throughMatchingComparison r f L F q)
    (StageBoundaryCones.matchingMapOfFunctor r Y q)

/-- The extended prefix matching square has the pullback universal property. -/
def matchingPullbackIsLimit (q : r.Through d) : IsLimit (matchingPullback r f L F q) :=
  BoundaryConeCongr.pullbackIsLimit (StageCornerMaps.throughMatchingComparison r f L F q)
    (StageBoundaryCones.matchingMapOfFunctor r Y q)

/-- The actual next-prefix matching corner with its exact original native endpoint types. -/
def matchingChosen (q : r.Through d) :
    (StageFactory.nextPrefix r f L F).Z.obj q ⟶
      pullback (StageCornerMaps.matchingPAt r f L q) (matchingMap r Y q.obj) :=
  (r.throughStructure d).matchingCornerWith (StageFactory.nextPrefix r f L F).p q
    (StageCornerMaps.nextMatchingCone r f
    L F q) (StageCornerMaps.nextMatchingIsLimit r f L F q)
      (StageBoundaryCones.matchingConeOfFunctor r Y q)
    (StageBoundaryCones.matchingIsLimitOfFunctor r Y q) (matchingPullback r f L F q)
      (matchingPullbackIsLimit r f L F q)

theorem matchingChosen_fst (q : r.Through d) :
    matchingChosen r f L F q ≫ pullback.fst (StageCornerMaps.matchingPAt r f L q)
      (matchingMap r Y q.obj) =
      (r.throughStructure d).matchingMapWith (StageFactory.nextPrefix r f L F).Z q
        (StageCornerMaps.nextMatchingCone r f
        L F q) (StageCornerMaps.nextMatchingIsLimit r f L F q) :=
  (r.throughStructure d).matchingCornerWith_fst (StageFactory.nextPrefix r f L F).p q
    (StageCornerMaps.nextMatchingCone r f L F q) (StageCornerMaps.nextMatchingIsLimit r f L F q)
      (StageBoundaryCones.matchingConeOfFunctor r Y q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r Y q)
      (matchingPullback r f L F q) (matchingPullbackIsLimit r f L F q)

theorem matchingChosen_snd (q : r.Through d) :
    matchingChosen r f L F q ≫ pullback.snd (StageCornerMaps.matchingPAt r f L q)
      (matchingMap r Y q.obj) =
      (StageFactory.nextPrefix r f L F).p.app q :=
  (r.throughStructure d).matchingCornerWith_snd (StageFactory.nextPrefix r f L F).p q
    (StageCornerMaps.nextMatchingCone r f L F q) (StageCornerMaps.nextMatchingIsLimit r f L F q)
      (StageBoundaryCones.matchingConeOfFunctor r Y q)
        (StageBoundaryCones.matchingIsLimitOfFunctor r Y q)
      (matchingPullback r f L F q) (matchingPullbackIsLimit r f L F q)

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C] in
/-- The same original native pullback is complete for the original lower factor corner. -/
def belowMatchingPullback (q : r.Through d) (hq : r.degree q.obj < d) :
    PullbackCone
      ((r.belowStructure d).matchingComparisonWith L.p (⟨q.obj, hq⟩ : r.Below d)
        (StageBoundaryCones.belowMatchingCone r
        L.Z q hq) (StageBoundaryCones.belowMatchingConeOfFunctor r Y q hq)
        (StageBoundaryCones.belowMatchingIsLimitOfFunctor r Y q hq))
      ((r.belowStructure d).matchingMapWith (r.restrictBelow Y d) (⟨q.obj, hq⟩ : r.Below d)
        (StageBoundaryCones.belowMatchingConeOfFunctor r Y q hq)
          (StageBoundaryCones.belowMatchingIsLimitOfFunctor r Y q
        hq)) :=
  BoundaryConeCongr.pullbackCone (StageCornerMaps.belowMatchingComparison r f L q hq)
    (RestrictionCorners.belowMatchingMapOfFunctor r Y q hq)

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C] in
/-- The unchanged lower matching square has the pullback universal property below the current
degree. -/
def belowMatchingPullbackIsLimit (q : r.Through d) (hq : r.degree q.obj < d) :
    IsLimit (belowMatchingPullback r f L q hq) :=
  BoundaryConeCongr.pullbackIsLimit (StageCornerMaps.belowMatchingComparison r f L q hq)
    (RestrictionCorners.belowMatchingMapOfFunctor r Y q hq)

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C] in
/-- The original lower matching corner on the same original native pullback. -/
def belowMatchingChosen (q : r.Through d) (hq : r.degree q.obj < d) :
    L.Z.obj (⟨q.obj, hq⟩ : r.Below d) ⟶ pullback (StageCornerMaps.matchingPAt r f L q)
      (matchingMap r Y q.obj) :=
  (r.belowStructure d).matchingCornerWith L.p (⟨q.obj, hq⟩ : r.Below d)
    (StageBoundaryCones.belowMatchingCone r L.Z q
    hq) (StageBoundaryCones.belowMatchingIsLimit r L.Z q hq)
      (StageBoundaryCones.belowMatchingConeOfFunctor r Y q hq)
    (StageBoundaryCones.belowMatchingIsLimitOfFunctor r Y q hq) (belowMatchingPullback r f L q hq)
    (belowMatchingPullbackIsLimit r f L q hq)

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C] in
theorem belowMatchingChosen_fst (q : r.Through d) (hq : r.degree q.obj < d) :
    belowMatchingChosen r f L q hq ≫ pullback.fst (StageCornerMaps.matchingPAt r f L q)
      (matchingMap r Y q.obj) =
      StageCornerMaps.belowMatchingMapAt r f L q hq :=
  (r.belowStructure d).matchingCornerWith_fst L.p (⟨q.obj, hq⟩ : r.Below d)
    (StageBoundaryCones.belowMatchingCone r L.Z q hq)
      (StageBoundaryCones.belowMatchingIsLimit r L.Z q hq)
      (StageBoundaryCones.belowMatchingConeOfFunctor r Y q hq)
        (StageBoundaryCones.belowMatchingIsLimitOfFunctor r Y q
      hq) (belowMatchingPullback r f L q hq) (belowMatchingPullbackIsLimit r f L q hq)

omit [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C] in
theorem belowMatchingChosen_snd (q : r.Through d) (hq : r.degree q.obj < d) :
    belowMatchingChosen r f L q hq ≫ pullback.snd (StageCornerMaps.matchingPAt r f L q)
      (matchingMap r Y q.obj) =
      L.p.app (⟨q.obj, hq⟩ : r.Below d) :=
  (r.belowStructure d).matchingCornerWith_snd L.p (⟨q.obj, hq⟩ : r.Below d)
    (StageBoundaryCones.belowMatchingCone r L.Z q hq)
      (StageBoundaryCones.belowMatchingIsLimit r L.Z q hq)
      (StageBoundaryCones.belowMatchingConeOfFunctor r Y q hq)
        (StageBoundaryCones.belowMatchingIsLimitOfFunctor r Y q
      hq) (belowMatchingPullback r f L q hq) (belowMatchingPullbackIsLimit r f L q hq)

/-- The actual new-degree chosen corner is the original factory right map under its original
object comparison. -/
theorem matchingChosen_new (q : r.Through d) (hq : r.degree q.obj = d) :
    matchingChosen r f L F q = (StageCornerMaps.newObjIso r f L F q hq).hom ≫
      (StageFactory.coefficientFactor r f L F q.obj hq).p := by
  let c : (StageFactory.nextPrefix r f L F).Z.obj q ⟶
    StageFactory.coefficientTarget r f L q.obj hq :=
    matchingChosen r f L F q
  change c = (StageCornerMaps.newObjIso r f L F q hq).hom ≫
    (StageFactory.coefficientFactor r f L F q.obj hq).p
  apply pullback.hom_ext
  · have hp : c ≫ pullback.fst (StageFactory.matchingP r f L q.obj hq) (matchingMap r Y q.obj) =
        (r.throughStructure d).matchingMapWith (StageFactory.nextPrefix r f L F).Z q
          (StageCornerMaps.nextMatchingCone r f L F q)
            (StageCornerMaps.nextMatchingIsLimit r f L F q) :=
        matchingChosen_fst r f L F q
    rw [hp, StageCornerMaps.throughMatchingMap_new r f L F q hq, Category.assoc]
    rfl
  · have hp : c ≫ pullback.snd (StageFactory.matchingP r f L q.obj hq) (matchingMap r Y q.obj) =
        (StageFactory.nextPrefix r f L F).p.app q := matchingChosen_snd r f L F q
    rw [hp, StageCornerMaps.nextP_new r f L F q hq, Category.assoc]
    rfl

/-- Every actual old-degree chosen matching corner is the unchanged lower corner under the
original object comparison.
-/
theorem matchingChosen_old (q : r.Through d) (hq : r.degree q.obj < d) :
    matchingChosen r f L F q =
      (StageCornerMaps.oldObjIso r f L F q hq).hom ≫ belowMatchingChosen r f L q hq := by
  apply pullback.hom_ext
  · rw [matchingChosen_fst, StageCornerMaps.throughMatchingMap_old r f L F q hq, Category.assoc,
    belowMatchingChosen_fst]
  · rw [matchingChosen_snd, StageCornerMaps.nextP_old r f L F q hq, Category.assoc,
    belowMatchingChosen_snd]

/-- The canonical actual new-degree matching corner is Arrow-isomorphic to the original
coefficient factory right map.
-/
def matchingArrowIsoNew (q : r.Through d) (hq : r.degree q.obj = d) :
    Arrow.mk (matchingCorner (r.throughStructure d) (StageFactory.nextPrefix r f L F).p q) ≅
      Arrow.mk ((StageFactory.coefficientFactor r f L F q.obj hq).p) :=
  (matchingCornerWithArrowIso (r.throughStructure d) (StageFactory.nextPrefix r f L F).p q
    (StageCornerMaps.nextMatchingCone r f L F q) (StageCornerMaps.nextMatchingIsLimit r f L F q)
    (StageBoundaryCones.matchingConeOfFunctor r Y q)
      (StageBoundaryCones.matchingIsLimitOfFunctor r Y q)
    (matchingPullback r f L F q) (matchingPullbackIsLimit r f L F q)).symm ≪≫
    Arrow.isoMk' (matchingChosen r f L F q) ((StageFactory.coefficientFactor r f L F q.obj hq).p)
      (StageCornerMaps.newObjIso r f L F q hq) (Iso.refl _) (by
        let c : (StageFactory.nextPrefix r f L F).Z.obj q ⟶
          StageFactory.coefficientTarget r f L q.obj hq :=
          matchingChosen r f L F q
        change (StageCornerMaps.newObjIso r f L F q hq).hom ≫
          (StageFactory.coefficientFactor r f L F q.obj hq).p = c ≫ (𝟙 _)
        rw [Category.comp_id]
        exact (matchingChosen_new r f L F q hq).symm)

/-- The canonical actual old-degree matching corner is Arrow-isomorphic to the original lower
factor corner. -/
def matchingArrowIsoOld (q : r.Through d) (hq : r.degree q.obj < d) :
    Arrow.mk (matchingCorner (r.throughStructure d) (StageFactory.nextPrefix r f L F).p q) ≅
      Arrow.mk (matchingCorner (r.belowStructure d) L.p (⟨q.obj, hq⟩ : r.Below d)) :=
  (matchingCornerWithArrowIso (r.throughStructure d) (StageFactory.nextPrefix r f L F).p q
    (StageCornerMaps.nextMatchingCone r f L F q) (StageCornerMaps.nextMatchingIsLimit r f L F q)
    (StageBoundaryCones.matchingConeOfFunctor r Y q)
      (StageBoundaryCones.matchingIsLimitOfFunctor r Y q)
    (matchingPullback r f L F q) (matchingPullbackIsLimit r f L F q)).symm ≪≫
    Arrow.isoMk' (matchingChosen r f L F q) (belowMatchingChosen r f L q hq)
      (StageCornerMaps.oldObjIso r f L F q hq) (Iso.refl _) (by
        simp only [Iso.refl_hom, Category.comp_id]
        exact (matchingChosen_old r f L F q hq).symm) ≪≫
    matchingCornerWithArrowIso (r.belowStructure d) L.p (⟨q.obj, hq⟩ : r.Below d)
      (StageBoundaryCones.belowMatchingCone r L.Z q hq)
        (StageBoundaryCones.belowMatchingIsLimit r L.Z q hq)
      (StageBoundaryCones.belowMatchingConeOfFunctor r Y q hq)
        (StageBoundaryCones.belowMatchingIsLimitOfFunctor r Y q
      hq) (belowMatchingPullback r f L q hq) (belowMatchingPullbackIsLimit r f L q hq)

end CategoryTheory.ReedyStructure.StageCorners

end ReedyPart8

section ReedyPart9

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.RestrictionCorners

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {X Y : J ⥤ C} (f : X ⟶ Y) {d : D}

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C] [HasPushouts C]

/-- Every source class respecting isomorphisms recognizes the same original and restricted
latching corner. -/
theorem latching_mem_iff (P : MorphismProperty C) [P.RespectsIso] (q : r.Through d) :
    P (latchingCorner r f q.obj) ↔
      P (latchingCorner (r.throughStructure d) (Functor.whiskerLeft (r.throughObjects d).ι f) q) :=
  P.arrow_mk_iso_iff (latchingArrowIso r f q)

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C] [HasPullbacks C]

/-- Every source class respecting isomorphisms recognizes the same original and restricted
matching corner. -/
theorem matching_mem_iff (P : MorphismProperty C) [P.RespectsIso] (q : r.Through d) :
    P (matchingCorner r f q.obj) ↔
      P (matchingCorner (r.throughStructure d) (Functor.whiskerLeft (r.throughObjects d).ι f) q) :=
  P.arrow_mk_iso_iff (matchingArrowIso r f q)

end Matching

end CategoryTheory.ReedyStructure.RestrictionCorners

namespace CategoryTheory.ReedyStructure.StageCorners

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y) {d : D}
  (L : MapFactorizationData (⊤ : MorphismProperty (r.Below d ⥤ C)) ⊤
    (Functor.whiskerLeft (r.belowObjects d).ι f))
  {P Q : MorphismProperty C} (F : FactorizationData P Q)

/-- Every actual new-degree latching corner inherits the source factory left class. -/
theorem latching_new_mem [P.RespectsIso] (q : r.Through d) (hq : r.degree q.obj = d) :
    P (latchingCorner (r.throughStructure d) (StageFactory.nextPrefix r f L F).i q) :=
  (P.arrow_mk_iso_iff (latchingArrowIsoNew r f L F q hq)).mpr
    (StageFactory.coefficientFactor r f L F q.obj hq).hi

/-- Every actual new-degree matching corner inherits the source factory right class. -/
theorem matching_new_mem [Q.RespectsIso] (q : r.Through d) (hq : r.degree q.obj = d) :
    Q (matchingCorner (r.throughStructure d) (StageFactory.nextPrefix r f L F).p q) :=
  (Q.arrow_mk_iso_iff (matchingArrowIsoNew r f L F q hq)).mpr
    (StageFactory.coefficientFactor r f L F q.obj hq).hp

/-- Every source class respecting isomorphisms retains each actual old-degree latching corner
class. -/
theorem latching_old_mem_iff (R : MorphismProperty C) [R.RespectsIso]
    (q : r.Through d) (hq : r.degree q.obj < d) :
    R (latchingCorner (r.throughStructure d) (StageFactory.nextPrefix r f L F).i q) ↔
      R (latchingCorner (r.belowStructure d) L.i (⟨q.obj, hq⟩ : r.Below d)) :=
  R.arrow_mk_iso_iff (latchingArrowIsoOld r f L F q hq)

/-- Every source class respecting isomorphisms retains each actual old-degree matching corner
class. -/
theorem matching_old_mem_iff (R : MorphismProperty C) [R.RespectsIso]
    (q : r.Through d) (hq : r.degree q.obj < d) :
    R (matchingCorner (r.throughStructure d) (StageFactory.nextPrefix r f L F).p q) ↔
      R (matchingCorner (r.belowStructure d) L.p (⟨q.obj, hq⟩ : r.Below d)) :=
  R.arrow_mk_iso_iff (matchingArrowIsoOld r f L F q hq)

/-- Actual lower corner left classes and the actual source factory extend across the whole
degree step. -/
theorem latching_mem_all [P.RespectsIso]
    (hL : ∀ j : r.Below d, P (latchingCorner (r.belowStructure d) L.i j)) :
    ∀ q : r.Through d, P (latchingCorner (r.throughStructure d)
      (StageFactory.nextPrefix r f L F).i q) := by
  intro q
  by_cases hq : r.degree q.obj < d
  · exact (latching_old_mem_iff r f L F P q hq).mpr (hL ⟨q.obj, hq⟩)
  · have hq' : r.degree q.obj = d := le_antisymm q.property (le_of_not_gt hq)
    exact latching_new_mem r f L F q hq'

/-- Actual lower corner right classes and the actual source factory extend across the whole
degree step. -/
theorem matching_mem_all [Q.RespectsIso]
    (hL : ∀ j : r.Below d, Q (matchingCorner (r.belowStructure d) L.p j)) :
    ∀ q : r.Through d, Q (matchingCorner (r.throughStructure d)
      (StageFactory.nextPrefix r f L F).p q) := by
  intro q
  by_cases hq : r.degree q.obj < d
  · exact (matching_old_mem_iff r f L F Q q hq).mpr (hL ⟨q.obj, hq⟩)
  · have hq' : r.degree q.obj = d := le_antisymm q.property (le_of_not_gt hq)
    exact matching_new_mem r f L F q hq'

end CategoryTheory.ReedyStructure.StageCorners

end ReedyPart9

section ReedyPart10

open CategoryTheory Limits MorphismProperty

namespace CategoryTheory.ReedyStructure.DegreeFactorization

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {X Y : J ⥤ C} (f : X ⟶ Y) {P Q : MorphismProperty C} (F : FactorizationData P Q)

/-- The original global latching corner is the actual prefix corner at its own degree. -/
def factorLatchingArrowIso (j : J) :
    Arrow.mk (latchingCorner r (factor r f F).i j) ≅
      Arrow.mk (latchingCorner (r.throughStructure (r.degree j))
        (prefixAt r f F (r.degree j)).i (⟨j, le_rfl⟩ : r.Through (r.degree j))) :=
  RestrictionCorners.latchingArrowIso r (factor r f F).i
      (⟨j, le_rfl⟩ : r.Through (r.degree j)) ≪≫
    (latchingCornerArrow (r.throughStructure (r.degree j))
      (⟨j, le_rfl⟩ : r.Through (r.degree j))).mapIso
      (PrefixGluing.fullLeftArrowIso r f (prefixAt r f F)
        (prefixAt_extends r f F) (r.degree j))

/-- The original global matching corner is the actual prefix corner at its own degree. -/
def factorMatchingArrowIso (j : J) :
    Arrow.mk (matchingCorner r (factor r f F).p j) ≅
      Arrow.mk (matchingCorner (r.throughStructure (r.degree j))
        (prefixAt r f F (r.degree j)).p (⟨j, le_rfl⟩ : r.Through (r.degree j))) :=
  RestrictionCorners.matchingArrowIso r (factor r f F).p
      (⟨j, le_rfl⟩ : r.Through (r.degree j)) ≪≫
    (matchingCornerArrow (r.throughStructure (r.degree j))
      (⟨j, le_rfl⟩ : r.Through (r.degree j))).mapIso
      (PrefixGluing.fullRightArrowIso r f (prefixAt r f F)
        (prefixAt_extends r f F) (r.degree j))

/-- Every actual global latching corner inherits the original coefficient factory class. -/
theorem factor_latching_mem [P.RespectsIso] (j : J) :
    P (latchingCorner r (factor r f F).i j) := by
  apply (P.arrow_mk_iso_iff (factorLatchingArrowIso r f F j)).mpr
  rw [prefixAt_eq_nextPrefix]
  exact StageCorners.latching_new_mem r f (lowerAt r f F (r.degree j)) F
    (⟨j, le_rfl⟩ : r.Through (r.degree j)) rfl

/-- Every actual global matching corner inherits the original coefficient factory class. -/
theorem factor_matching_mem [Q.RespectsIso] (j : J) :
    Q (matchingCorner r (factor r f F).p j) := by
  apply (Q.arrow_mk_iso_iff (factorMatchingArrowIso r f F j)).mpr
  rw [prefixAt_eq_nextPrefix]
  exact StageCorners.matching_new_mem r f (lowerAt r f F (r.degree j)) F
    (⟨j, le_rfl⟩ : r.Through (r.degree j)) rfl

/-- The source coefficient factory constructs the full factor in its original two corner classes. -/
def classifiedFactor [P.RespectsIso] [Q.RespectsIso] :
    MapFactorizationData (latchingClass r P) (matchingClass r Q) f where
  Z := (factor r f F).Z
  i := (factor r f F).i
  p := (factor r f F).p
  fac := (factor r f F).fac
  hi := factor_latching_mem r f F
  hp := factor_matching_mem r f F

/-- The actual original coefficient factory supplies full Reedy factorization data. -/
def classifiedData [P.RespectsIso] [Q.RespectsIso] :
    FactorizationData (latchingClass r P) (matchingClass r Q) :=
  fun f ↦ classifiedFactor r f F

/-- Both whole original classified arrows recover the unchanged original transformation. -/
theorem classifiedFactor_fac [P.RespectsIso] [Q.RespectsIso] :
    (classifiedFactor r f F).i ≫ (classifiedFactor r f F).p = f :=
  (classifiedFactor r f F).fac

end CategoryTheory.ReedyStructure.DegreeFactorization

end ReedyPart10
