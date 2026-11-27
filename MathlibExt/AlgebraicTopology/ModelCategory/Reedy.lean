/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Reedy.FunctorialFactorization
public import MathlibExt.CategoryTheory.Reedy.Lifting
public import MathlibExt.CategoryTheory.Reedy.BoundaryLifting
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# The ordinary Reedy model with exactly its needed boundary shapes

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ReedyModel

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {F G : J ⥤ C} (f : F ⟶ G)

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The full original lower latching colimit comparison is a source cofibration. -/
theorem latchingColimMap_cofibration (j : J)
    (h : ∀ k : J, r.degree k < r.degree j → cofibrations C
      (CategoryTheory.ReedyStructure.latchingCorner r f k)) :
    cofibrations C (colimMap (r.latchingTransformation f j)) :=
  CategoryTheory.ReedyStructure.latchingColimMap_mem r f j (cofibrations C) (trivialFibrations C) h

/-- The full original lower latching colimit comparison is a source trivial cofibration. -/
theorem latchingColimMap_trivialCofibration (j : J)
    (h : ∀ k : J, r.degree k < r.degree j →
      trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f k)) :
    trivialCofibrations C (colimMap (r.latchingTransformation f j)) :=
  CategoryTheory.ReedyStructure.latchingColimMap_mem r f j (trivialCofibrations C) (fibrations C) h

/-- Every caller complete latching colimit comparison retains the source cofibration class. -/
theorem latchingComparisonWith_cofibration (j : J)
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (h : ∀ k : J, r.degree k < r.degree j → cofibrations C
      (CategoryTheory.ReedyStructure.latchingCorner r f k)) :
    cofibrations C (r.latchingComparisonWith f j cX hX cY) :=
  CategoryTheory.ReedyStructure.latchingComparisonWith_mem r f j (cofibrations C) (trivialFibrations
    C) cX hX cY hY h

/-- Every caller complete latching comparison retains the source trivial cofibration class. -/
theorem latchingComparisonWith_trivialCofibration (j : J)
    (cX : Cocone (r.latchingDiagram F j)) (hX : IsColimit cX)
    (cY : Cocone (r.latchingDiagram G j)) (hY : IsColimit cY)
    (h : ∀ k : J, r.degree k < r.degree j →
      trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f k)) :
    trivialCofibrations C (r.latchingComparisonWith f j cX hX cY) :=
  CategoryTheory.ReedyStructure.latchingComparisonWith_mem r f j (trivialCofibrations C) (fibrations
    C) cX hX cY hY h

/-- The original component of a map with all latching cofibration corners is a source cofibration.
-/
theorem component_cofibration_of_latchingCorners
    (h : ∀ j : J, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f j)) (j : J) :
    cofibrations C (f.app j) := by
  have hc := latchingColimMap_cofibration r f j (fun k _ => h k)
  have hi := (cofibrations C).pushout_inl (CategoryTheory.ReedyStructure.latchingMap r F j)
    (colimMap (r.latchingTransformation f j)) hc
  have hf := (cofibrations C).comp_mem _ _ hi (h j)
  simpa only [CategoryTheory.ReedyStructure.latchingCorner_inl r] using hf

/-- All trivial latching corners imply a trivial cofibration at each original component. -/
theorem component_trivialCofibration_of_latchingCorners
    (h : ∀ j : J, trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f j)) (j :
      J) :
    trivialCofibrations C (f.app j) := by
  have hc := latchingColimMap_trivialCofibration r f j (fun k _ => h k)
  have hi := (trivialCofibrations C).pushout_inl (CategoryTheory.ReedyStructure.latchingMap r F j)
    (colimMap (r.latchingTransformation f j)) hc
  have hf := (trivialCofibrations C).comp_mem _ _ hi (h j)
  simpa only [CategoryTheory.ReedyStructure.latchingCorner_inl r] using hf

/-- Genuine well founded recognition of each trivial latching corner from the original source weak
maps. -/
theorem latchingCorner_trivialCofibration_of_cofibration_weak
    (hc : ∀ j : J, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f j))
    (hw : ∀ j : J, weakEquivalences C (f.app j)) (j : J) :
    trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f j) := by
  induction j using (InvImage.wf r.degree wellFounded_lt).induction with
  | h j ih =>
    have hcol := latchingColimMap_trivialCofibration r f j ih
    have hi := (trivialCofibrations C).pushout_inl (CategoryTheory.ReedyStructure.latchingMap r F j)
      (colimMap (r.latchingTransformation f j)) hcol
    refine ⟨hc j, ?_⟩
    apply (weakEquivalences C).of_precomp _ _ hi.2
    rw [CategoryTheory.ReedyStructure.latchingCorner_inl r]
    exact hw j

/-- Trivial original latching corners are precisely cofibration corners with objectwise source weak
equivalences. -/
theorem latchingCorner_trivialCofibrations_iff :
    (∀ j : J, trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f j)) ↔
      (∀ j : J, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f j)) ∧
      (∀ j : J, weakEquivalences C (f.app j)) := by
  constructor
  · intro h
    exact ⟨fun j => (h j).1, fun j => (component_trivialCofibration_of_latchingCorners r f h j).2⟩
  · rintro ⟨hc, hw⟩
    exact fun j => latchingCorner_trivialCofibration_of_cofibration_weak r f hc hw j

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The full original lower matching limit comparison is a source fibration. -/
theorem matchingLimMap_fibration (j : J)
    (h : ∀ k : J, r.degree k < r.degree j → fibrations C
      (CategoryTheory.ReedyStructure.matchingCorner r f k)) :
    fibrations C (limMap (r.matchingTransformation f j)) :=
  CategoryTheory.ReedyStructure.matchingLimMap_mem r f j (trivialCofibrations C) (fibrations C) h

/-- The full original lower matching limit comparison is a source trivial fibration. -/
theorem matchingLimMap_trivialFibration (j : J)
    (h : ∀ k : J, r.degree k < r.degree j → trivialFibrations C
      (CategoryTheory.ReedyStructure.matchingCorner r f k)) :
    trivialFibrations C (limMap (r.matchingTransformation f j)) :=
  CategoryTheory.ReedyStructure.matchingLimMap_mem r f j (cofibrations C) (trivialFibrations C) h

/-- Every caller complete matching limit comparison retains the source fibration class. -/
theorem matchingComparisonWith_fibration (j : J)
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (h : ∀ k : J, r.degree k < r.degree j → fibrations C
      (CategoryTheory.ReedyStructure.matchingCorner r f k)) :
    fibrations C (r.matchingComparisonWith f j cX cY hY) :=
  CategoryTheory.ReedyStructure.matchingComparisonWith_mem r f j (trivialCofibrations C) (fibrations
    C) cX hX cY hY h

/-- Every caller complete matching comparison retains the source trivial fibration class. -/
theorem matchingComparisonWith_trivialFibration (j : J)
    (cX : Cone (r.matchingDiagram F j)) (hX : IsLimit cX)
    (cY : Cone (r.matchingDiagram G j)) (hY : IsLimit cY)
    (h : ∀ k : J, r.degree k < r.degree j → trivialFibrations C
      (CategoryTheory.ReedyStructure.matchingCorner r f k)) :
    trivialFibrations C (r.matchingComparisonWith f j cX cY hY) :=
  CategoryTheory.ReedyStructure.matchingComparisonWith_mem r f j (cofibrations C) (trivialFibrations
    C) cX hX cY hY h

/-- The original component of a map with all matching fibration corners is a source fibration. -/
theorem component_fibration_of_matchingCorners
    (h : ∀ j : J, fibrations C (CategoryTheory.ReedyStructure.matchingCorner r f j)) (j : J) :
    fibrations C (f.app j) := by
  have hc := matchingLimMap_fibration r f j (fun k _ => h k)
  have hp := (fibrations C).pullback_snd (limMap (r.matchingTransformation f j))
    (CategoryTheory.ReedyStructure.matchingMap r G j) hc
  have hf := (fibrations C).comp_mem _ _ (h j) hp
  simpa only [CategoryTheory.ReedyStructure.matchingCorner_snd r] using hf

/-- All trivial matching corners imply a trivial fibration at each original component. -/
theorem component_trivialFibration_of_matchingCorners
    (h : ∀ j : J, trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r f j)) (j : J)
      :
    trivialFibrations C (f.app j) := by
  have hc := matchingLimMap_trivialFibration r f j (fun k _ => h k)
  have hp := (trivialFibrations C).pullback_snd (limMap (r.matchingTransformation f j))
    (CategoryTheory.ReedyStructure.matchingMap r G j) hc
  have hf := (trivialFibrations C).comp_mem _ _ (h j) hp
  simpa only [CategoryTheory.ReedyStructure.matchingCorner_snd r] using hf

/-- Genuine well founded recognition of each trivial matching corner from the original source weak
maps. -/
theorem matchingCorner_trivialFibration_of_fibration_weak
    (hc : ∀ j : J, fibrations C (CategoryTheory.ReedyStructure.matchingCorner r f j))
    (hw : ∀ j : J, weakEquivalences C (f.app j)) (j : J) :
    trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r f j) := by
  induction j using (InvImage.wf r.degree wellFounded_lt).induction with
  | h j ih =>
    have hlim := matchingLimMap_trivialFibration r f j ih
    have hp := (trivialFibrations C).pullback_snd (limMap (r.matchingTransformation f j))
      (CategoryTheory.ReedyStructure.matchingMap r G j) hlim
    refine ⟨hc j, ?_⟩
    apply (weakEquivalences C).of_postcomp _ _ hp.2
    rw [CategoryTheory.ReedyStructure.matchingCorner_snd r]
    exact hw j

/-- Trivial original matching corners are precisely fibration corners with objectwise source weak
equivalences. -/
theorem matchingCorner_trivialFibrations_iff :
    (∀ j : J, trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r f j)) ↔
      (∀ j : J, fibrations C (CategoryTheory.ReedyStructure.matchingCorner r f j)) ∧
      (∀ j : J, weakEquivalences C (f.app j)) := by
  constructor
  · intro h
    exact ⟨fun j => (h j).1, fun j => (component_trivialFibration_of_matchingCorners r f h j).2⟩
  · rintro ⟨hc, hw⟩
    exact fun j => matchingCorner_trivialFibration_of_fibration_weak r f hc hw j

end Matching

end HomotopicalAlgebra.ReedyModel

end ReedyPart1

section ReedyPart2

open CategoryTheory Limits

namespace HomotopicalAlgebra.ReedyModel

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {F G : J ⥤ C} (f : F ⟶ G)

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- Arbitrary caller latching corners are trivial precisely when they are cofibrations and the
  original map is
objectwise weak. -/
theorem latchingCornerWith_trivialCofibrations_iff
    (cX : ∀ j : J, Cocone (r.latchingDiagram F j)) (hX : ∀ j : J, IsColimit (cX j))
    (cY : ∀ j : J, Cocone (r.latchingDiagram G j)) (hY : ∀ j : J, IsColimit (cY j))
    (cP : ∀ j : J, PushoutCocone (r.latchingMapWith F j (cX j) (hX j))
      (r.latchingComparisonWith f j (cX j) (hX j) (cY j)))
    (hP : ∀ j : J, IsColimit (cP j)) :
    (∀ j : J, trivialCofibrations C
      (r.latchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ↔
      (∀ j : J, cofibrations C
        (r.latchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ∧
      (∀ j : J, weakEquivalences C (f.app j)) := by
  have ht := forall_congr' (fun j =>
    CategoryTheory.ReedyStructure.latchingCornerWith_mem_iff r f j (trivialCofibrations C)
    (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))
  have hc := forall_congr' (fun j =>
    CategoryTheory.ReedyStructure.latchingCornerWith_mem_iff r f j (cofibrations C)
    (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))
  rw [ht, hc]
  exact latchingCorner_trivialCofibrations_iff r f

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- Arbitrary caller matching corners are trivial precisely when they are fibrations and the
  original map is
objectwise weak. -/
theorem matchingCornerWith_trivialFibrations_iff
    (cX : ∀ j : J, Cone (r.matchingDiagram F j)) (hX : ∀ j : J, IsLimit (cX j))
    (cY : ∀ j : J, Cone (r.matchingDiagram G j)) (hY : ∀ j : J, IsLimit (cY j))
    (cP : ∀ j : J, PullbackCone (r.matchingComparisonWith f j (cX j) (cY j) (hY j))
      (r.matchingMapWith G j (cY j) (hY j)))
    (hP : ∀ j : J, IsLimit (cP j)) :
    (∀ j : J, trivialFibrations C
      (r.matchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ↔
      (∀ j : J, fibrations C
        (r.matchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))) ∧
      (∀ j : J, weakEquivalences C (f.app j)) := by
  have ht := forall_congr' (fun j =>
    CategoryTheory.ReedyStructure.matchingCornerWith_mem_iff r f j (trivialFibrations C)
    (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))
  have hc := forall_congr' (fun j =>
    CategoryTheory.ReedyStructure.matchingCornerWith_mem_iff r f j (fibrations C)
    (cX j) (hX j) (cY j) (hY j) (cP j) (hP j))
  rw [ht, hc]
  exact matchingCorner_trivialFibrations_iff r f

end Matching

end HomotopicalAlgebra.ReedyModel

end ReedyPart2

section ReedyPart3

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ReedyModel

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  [HasPushouts C] [HasPullbacks C]
  {P Q : MorphismProperty C} [IsWeakFactorizationSystem P Q] (F : FactorizationData P Q)

include F

/-- An original source weak factorization system induces the full Reedy corner weak factorization
system. -/
theorem cornerWfs : IsWeakFactorizationSystem (CategoryTheory.ReedyStructure.latchingClass r P)
    (CategoryTheory.ReedyStructure.matchingClass r Q) := by
  let : P.IsStableUnderRetracts := by
    rw [← llp_eq_of_wfs P Q]
    infer_instance
  let : Q.IsStableUnderRetracts := by
    rw [← rlp_eq_of_wfs P Q]
    infer_instance
  let : HasFactorization (CategoryTheory.ReedyStructure.latchingClass r P)
      (CategoryTheory.ReedyStructure.matchingClass r Q) :=
    ⟨fun f => ⟨CategoryTheory.ReedyStructure.DegreeFactorization.classifiedFactor r f F⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp =>
    CategoryTheory.ReedyStructure.Lifting.hasLiftingProperty (r := r)
      (fun j => hasLiftingProperty_of_wfs _ _ (hi j) (hp j)))

end HomotopicalAlgebra.ReedyModel

end ReedyPart3

section ReedyPart4

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ReedyModel

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The source trivial latching class is exactly the original latching cofibration class intersected
  with objectwise
weak maps. -/
theorem latchingClass_trivialCofibrations :
    CategoryTheory.ReedyStructure.latchingClass r (trivialCofibrations C) =
      CategoryTheory.ReedyStructure.latchingClass r (cofibrations C) ⊓ (weakEquivalences
        C).functorCategory J := by
  ext X Y f
  exact latchingCorner_trivialCofibrations_iff r f

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The source trivial matching class is exactly the original matching fibration class intersected
  with objectwise
weak maps. -/
theorem matchingClass_trivialFibrations :
    CategoryTheory.ReedyStructure.matchingClass r (trivialFibrations C) =
      CategoryTheory.ReedyStructure.matchingClass r (fibrations C) ⊓ (weakEquivalences
        C).functorCategory J := by
  ext X Y f
  exact matchingCorner_trivialFibrations_iff r f

end Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The actual original source factories and corner lifting construct the ordinary Reedy model. -/
@[instance_reducible]
def modelCategory : ModelCategory (J ⥤ C) := by
  letI : CategoryWithCofibrations (J ⥤ C) := ⟨CategoryTheory.ReedyStructure.latchingClass r
    (cofibrations C)⟩
  letI : CategoryWithFibrations (J ⥤ C) := ⟨CategoryTheory.ReedyStructure.matchingClass r
    (fibrations C)⟩
  letI : CategoryWithWeakEquivalences (J ⥤ C) := ⟨(weakEquivalences C).functorCategory J⟩
  letI : IsWeakFactorizationSystem (cofibrations (J ⥤ C)) (trivialFibrations (J ⥤ C)) := by
    change IsWeakFactorizationSystem (CategoryTheory.ReedyStructure.latchingClass r (cofibrations
      C))
      (CategoryTheory.ReedyStructure.matchingClass r (fibrations C) ⊓ (weakEquivalences
        C).functorCategory J)
    rw [← matchingClass_trivialFibrations]
    exact cornerWfs r Fc.factorizationData
  letI : IsWeakFactorizationSystem (trivialCofibrations (J ⥤ C)) (fibrations (J ⥤ C)) := by
    change IsWeakFactorizationSystem
      (CategoryTheory.ReedyStructure.latchingClass r (cofibrations C) ⊓ (weakEquivalences
        C).functorCategory J)
      (CategoryTheory.ReedyStructure.matchingClass r (fibrations C))
    rw [← latchingClass_trivialCofibrations]
    exact cornerWfs r Ff.factorizationData
  letI : (weakEquivalences (J ⥤ C)).HasTwoOutOfThreeProperty :=
    inferInstanceAs ((weakEquivalences C).functorCategory J).HasTwoOutOfThreeProperty
  exact ModelCategory.mk' (J ⥤ C)

/-- The constructed model weak equivalences are the unchanged original objectwise source weak maps.
-/
theorem weakEquivalences_eq :
    letI := modelCategory r Fc Ff
    weakEquivalences (J ⥤ C) = (weakEquivalences C).functorCategory J := rfl

/-- The constructed model cofibrations are precisely the actual original latching-corner
cofibrations. -/
theorem cofibrations_eq :
    letI := modelCategory r Fc Ff
    cofibrations (J ⥤ C) = CategoryTheory.ReedyStructure.latchingClass r (cofibrations C) := rfl

/-- The constructed model fibrations are precisely the actual original matching-corner fibrations.
-/
theorem fibrations_eq :
    letI := modelCategory r Fc Ff
    fibrations (J ⥤ C) = CategoryTheory.ReedyStructure.matchingClass r (fibrations C) := rfl

/-- The constructed model trivial cofibrations are precisely the actual original source trivial
latching corners. -/
theorem trivialCofibrations_eq :
    letI := modelCategory r Fc Ff
    trivialCofibrations (J ⥤ C) = CategoryTheory.ReedyStructure.latchingClass r (trivialCofibrations
      C) :=
  (latchingClass_trivialCofibrations r).symm

/-- The constructed model trivial fibrations are precisely the actual original source trivial
matching corners. -/
theorem trivialFibrations_eq :
    letI := modelCategory r Fc Ff
    trivialFibrations (J ⥤ C) = CategoryTheory.ReedyStructure.matchingClass r (trivialFibrations C)
      :=
  (matchingClass_trivialFibrations r).symm

/-- The original source cofibration factory constructs the whole actual functorial Reedy cofibration
factor. -/
def cofibrantFactorizationData :
    letI := modelCategory r Fc Ff
    FunctorialFactorizationData (cofibrations (J ⥤ C)) (trivialFibrations (J ⥤ C)) := by
  letI := modelCategory r Fc Ff
  change FunctorialFactorizationData (CategoryTheory.ReedyStructure.latchingClass r (cofibrations
    C))
    (CategoryTheory.ReedyStructure.matchingClass r (fibrations C) ⊓ (weakEquivalences
      C).functorCategory J)
  exact (CategoryTheory.ReedyStructure.FunctorialConstruction.classifiedData r Fc).ofLE le_rfl
    (fun _ _ f h => (matchingCorner_trivialFibrations_iff r f).mp h)

/-- The original source fibration factory constructs the whole actual functorial Reedy fibration
factor. -/
def fibrantFactorizationData :
    letI := modelCategory r Fc Ff
    FunctorialFactorizationData (trivialCofibrations (J ⥤ C)) (fibrations (J ⥤ C)) := by
  letI := modelCategory r Fc Ff
  change FunctorialFactorizationData
    (CategoryTheory.ReedyStructure.latchingClass r (cofibrations C) ⊓ (weakEquivalences
      C).functorCategory J)
      (CategoryTheory.ReedyStructure.matchingClass r (fibrations C))
  exact (CategoryTheory.ReedyStructure.FunctorialConstruction.classifiedData r Ff).ofLE
    (fun _ _ f h => (latchingCorner_trivialCofibrations_iff r f).mp h) le_rfl

/-- The original source factories construct the full model, its five actual classes and both
  original functorial
factors. -/
theorem constructs :
    letI := modelCategory r Fc Ff
    ∃ (c : FunctorialFactorizationData (cofibrations (J ⥤ C)) (trivialFibrations (J ⥤ C)))
      (f : FunctorialFactorizationData (trivialCofibrations (J ⥤ C)) (fibrations (J ⥤ C))),
      c = cofibrantFactorizationData r Fc Ff ∧ f = fibrantFactorizationData r Fc Ff ∧
      weakEquivalences (J ⥤ C) = (weakEquivalences C).functorCategory J ∧
      cofibrations (J ⥤ C) = CategoryTheory.ReedyStructure.latchingClass r (cofibrations C) ∧
      fibrations (J ⥤ C) = CategoryTheory.ReedyStructure.matchingClass r (fibrations C) ∧
      trivialCofibrations (J ⥤ C) = CategoryTheory.ReedyStructure.latchingClass r
        (trivialCofibrations C) ∧
      trivialFibrations (J ⥤ C) = CategoryTheory.ReedyStructure.matchingClass r (trivialFibrations
        C) := by
  exact ⟨cofibrantFactorizationData r Fc Ff, fibrantFactorizationData r Fc Ff, rfl, rfl,
    weakEquivalences_eq r Fc Ff, cofibrations_eq r Fc Ff, fibrations_eq r Fc Ff,
    trivialCofibrations_eq r Fc Ff, trivialFibrations_eq r Fc Ff⟩

end HomotopicalAlgebra.ReedyModel

end ReedyPart4

section ReedyPart5

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ReedyModel

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  {X Y : J ⥤ C} (f : X ⟶ Y)

/-- The actual Reedy weak equivalences are exactly the original component weak equivalences. -/
theorem weakEquivalence_iff_source :
    letI := modelCategory r Fc Ff
    WeakEquivalence f ↔ ∀ j : J, WeakEquivalence (f.app j) := by
  simp only [HomotopicalAlgebra.weakEquivalence_iff]
  rfl

/-- The actual Reedy cofibrations are exactly the original source cofibrations of every latching
corner. -/
theorem cofibration_iff_source :
    letI := modelCategory r Fc Ff
    Cofibration f ↔ ∀ j : J, Cofibration (CategoryTheory.ReedyStructure.latchingCorner r f j) := by
  simp only [HomotopicalAlgebra.cofibration_iff]
  rfl

/-- The actual Reedy fibrations are exactly the original source fibrations of every matching corner.
-/
theorem fibration_iff_source :
    letI := modelCategory r Fc Ff
    Fibration f ↔ ∀ j : J, Fibration (CategoryTheory.ReedyStructure.matchingCorner r f j) := by
  simp only [HomotopicalAlgebra.fibration_iff]
  rfl

/-- The actual Reedy trivial cofibrations are exactly the original source trivial latching corners.
-/
theorem trivialCofibration_iff_source :
    letI := modelCategory r Fc Ff
    trivialCofibrations (J ⥤ C) f ↔
      ∀ j : J, trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f j) := by
  rw [trivialCofibrations_eq r Fc Ff]
  rfl

/-- The actual Reedy trivial fibrations are exactly the original source trivial matching corners. -/
theorem trivialFibration_iff_source :
    letI := modelCategory r Fc Ff
    trivialFibrations (J ⥤ C) f ↔
      ∀ j : J, trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r f j) := by
  rw [trivialFibrations_eq r Fc Ff]
  rfl

section Latching

variable
  (cX : ∀ j : J, Cocone (r.latchingDiagram X j)) (hX : ∀ j : J, IsColimit (cX j))
  (cY : ∀ j : J, Cocone (r.latchingDiagram Y j)) (hY : ∀ j : J, IsColimit (cY j))
  (cP : ∀ j : J, PushoutCocone (r.latchingMapWith X j (cX j) (hX j))
    (r.latchingComparisonWith f j (cX j) (hX j) (cY j)))
  (hP : ∀ j : J, IsColimit (cP j))

/-- Any original full caller latching boundary recognizes the same actual Reedy cofibration. -/
theorem cofibration_iff_chosen :
    letI := modelCategory r Fc Ff
    cofibrations (J ⥤ C) f ↔ ∀ j : J, cofibrations C
      (r.latchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j)) := by
  change (∀ j : J, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r f j)) ↔ _
  exact forall_congr' (fun j => (CategoryTheory.ReedyStructure.latchingCornerWith_mem_iff r f j
    (cofibrations C)
    (cX j) (hX j) (cY j) (hY j) (cP j) (hP j)).symm)

/-- Any original full caller latching boundary recognizes the same actual Reedy trivial cofibration.
-/
theorem trivialCofibration_iff_chosen :
    letI := modelCategory r Fc Ff
    trivialCofibrations (J ⥤ C) f ↔ ∀ j : J, trivialCofibrations C
      (r.latchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j)) := by
  rw [trivialCofibrations_eq r Fc Ff]
  exact forall_congr' (fun j => (CategoryTheory.ReedyStructure.latchingCornerWith_mem_iff r f j
    (trivialCofibrations C)
    (cX j) (hX j) (cY j) (hY j) (cP j) (hP j)).symm)

end Latching

section Matching

variable
  (cX : ∀ j : J, Cone (r.matchingDiagram X j)) (hX : ∀ j : J, IsLimit (cX j))
  (cY : ∀ j : J, Cone (r.matchingDiagram Y j)) (hY : ∀ j : J, IsLimit (cY j))
  (cP : ∀ j : J, PullbackCone (r.matchingComparisonWith f j (cX j) (cY j) (hY j))
    (r.matchingMapWith Y j (cY j) (hY j)))
  (hP : ∀ j : J, IsLimit (cP j))

/-- Any original full caller matching boundary recognizes the same actual Reedy fibration. -/
theorem fibration_iff_chosen :
    letI := modelCategory r Fc Ff
    fibrations (J ⥤ C) f ↔ ∀ j : J, fibrations C
      (r.matchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j)) := by
  change (∀ j : J, fibrations C (CategoryTheory.ReedyStructure.matchingCorner r f j)) ↔ _
  exact forall_congr' (fun j => (CategoryTheory.ReedyStructure.matchingCornerWith_mem_iff r f j
    (fibrations C)
    (cX j) (hX j) (cY j) (hY j) (cP j) (hP j)).symm)

/-- Any original full caller matching boundary recognizes the same actual Reedy trivial fibration.
-/
theorem trivialFibration_iff_chosen :
    letI := modelCategory r Fc Ff
    trivialFibrations (J ⥤ C) f ↔ ∀ j : J, trivialFibrations C
      (r.matchingCornerWith f j (cX j) (hX j) (cY j) (hY j) (cP j) (hP j)) := by
  rw [trivialFibrations_eq r Fc Ff]
  exact forall_congr' (fun j => (CategoryTheory.ReedyStructure.matchingCornerWith_mem_iff r f j
    (trivialFibrations C)
    (cX j) (hX j) (cY j) (hY j) (cP j) (hP j)).symm)

end Matching

end HomotopicalAlgebra.ReedyModel

end ReedyPart5

section ReedyPart6

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ReedyLifting

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C] [∀ j, HasColimitsOfShape (r.Latching j) C]
  {A B X Y : J ⥤ C} (i : A ⟶ B) (p : X ⟶ Y)

/-- Actual latching cofibrations and matching trivial fibrations give the same full natural lifting
property. -/
theorem cofibration_trivialFibration
    (hi : ∀ j, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r i j))
    (hp : ∀ j, trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r p j)) :
      HasLiftingProperty i p :=
  CategoryTheory.ReedyStructure.Lifting.hasLiftingProperty (r := r)
    (fun j => hasLiftingProperty_of_wfs _ _ (hi j) (hp j))

/-- Actual latching trivial cofibrations and matching fibrations give the same full natural lifting
property. -/
theorem trivialCofibration_fibration
    (hi : ∀ j, trivialCofibrations C (CategoryTheory.ReedyStructure.latchingCorner r i j))
    (hp : ∀ j, fibrations C (CategoryTheory.ReedyStructure.matchingCorner r p j)) :
      HasLiftingProperty i p :=
  CategoryTheory.ReedyStructure.Lifting.hasLiftingProperty (r := r)
    (fun j => hasLiftingProperty_of_wfs _ _ (hi j) (hp j))

/-- The actual full caller square has an original natural lift constructed from its source
coefficient corners. -/
def liftStruct {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b)
    (hi : ∀ j, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r i j))
    (hp : ∀ j, trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r p j)) :
      sq.LiftStruct :=
  CategoryTheory.ReedyStructure.Lifting.liftStruct r sq
    (fun j => hasLiftingProperty_of_wfs _ _ (hi j) (hp j))

/-- The complete constructed natural lift retains the unchanged original left caller map. -/
theorem liftStruct_left {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b)
    (hi : ∀ j, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r i j))
    (hp : ∀ j, trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r p j)) :
    i ≫ (liftStruct r i p sq hi hp).l = t := (liftStruct r i p sq hi hp).fac_left

/-- The complete constructed natural lift retains the unchanged original right caller map. -/
theorem liftStruct_right {t : A ⟶ X} {b : B ⟶ Y} (sq : CommSq t i p b)
    (hi : ∀ j, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner r i j))
    (hp : ∀ j, trivialFibrations C (CategoryTheory.ReedyStructure.matchingCorner r p j)) :
    (liftStruct r i p sq hi hp).l ≫ p = b := (liftStruct r i p sq hi hp).fac_right

end HomotopicalAlgebra.ReedyLifting

end ReedyPart6


/-! ## Full original factor functors and natural maps -/

namespace HomotopicalAlgebra.ReedyModel

open CategoryTheory Limits MorphismProperty

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The model's entire cofibration middle functor is the original constructed Arrow functor. -/
theorem cofibrantFactorizationData_Z :
    (cofibrantFactorizationData r Fc Ff).Z =
      CategoryTheory.ReedyStructure.FunctorialConstruction.middle r Fc := rfl

/-- The model's entire cofibration left natural map is the original constructed source map. -/
theorem cofibrantFactorizationData_i :
    (cofibrantFactorizationData r Fc Ff).i =
      CategoryTheory.ReedyStructure.FunctorialConstruction.left r Fc := rfl

/-- The model's entire cofibration right natural map is the original constructed target map. -/
theorem cofibrantFactorizationData_p :
    (cofibrantFactorizationData r Fc Ff).p =
      CategoryTheory.ReedyStructure.FunctorialConstruction.right r Fc := rfl

/-- The model's entire fibration middle functor is the original constructed Arrow functor. -/
theorem fibrantFactorizationData_Z :
    (fibrantFactorizationData r Fc Ff).Z =
      CategoryTheory.ReedyStructure.FunctorialConstruction.middle r Ff := rfl

/-- The model's entire fibration left natural map is the original constructed source map. -/
theorem fibrantFactorizationData_i :
    (fibrantFactorizationData r Fc Ff).i = CategoryTheory.ReedyStructure.FunctorialConstruction.left
      r Ff := rfl

/-- The model's entire fibration right natural map is the original constructed target map. -/
theorem fibrantFactorizationData_p :
    (fibrantFactorizationData r Fc Ff).p =
      CategoryTheory.ReedyStructure.FunctorialConstruction.right r Ff := rfl

end HomotopicalAlgebra.ReedyModel

/-! ## General construction through Mathlib's native Reedy interface -/

namespace HomotopicalAlgebra.ReedyStructure

open CategoryTheory Limits MorphismProperty
open scoped CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D]
  {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]

/-- Present native Reedy data with the unchanged original degree and complete chosen factor maps. -/
abbrev withOriginalDegree (s : HomotopicalAlgebra.ReedyStructure inverse direct (WithBot D))
    (degree : J → D) (hdegree : ∀ j : J, s.deg j = (degree j : WithBot D))
    (factor : ∀ {i j : J} (f : i ⟶ j), inverse.MapFactorizationData direct f) :
    CategoryTheory.ReedyStructure J D where
  degree := degree
  direct := direct
  inverse := inverse
  direct_multiplicative := inferInstance
  inverse_multiplicative := inferInstance
  native := s
  native_degree := hdegree
  factor := factor

section OriginalDegree

variable (s : HomotopicalAlgebra.ReedyStructure inverse direct (WithBot D))
  (degree : J → D) (hdegree : ∀ j : J, s.deg j = (degree j : WithBot D))
  (factor : ∀ {i j : J} (f : i ⟶ j), inverse.MapFactorizationData direct f)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape ((s.withOriginalDegree degree hdegree factor).Matching j) C]
  [∀ j, HasColimitsOfShape ((s.withOriginalDegree degree hdegree factor).Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The native general model construction retains every original degree, boundary and factory. -/
@[instance_reducible]
def modelCategoryWithOriginalDegree : ModelCategory (J ⥤ C) :=
  ReedyModel.modelCategory (s.withOriginalDegree degree hdegree factor) Fc Ff

/-- The native construction retains the full original functorial cofibration factor record. -/
def cofibrantFactorizationDataWithOriginalDegree :
    letI := s.modelCategoryWithOriginalDegree degree hdegree factor Fc Ff
    FunctorialFactorizationData (cofibrations (J ⥤ C)) (trivialFibrations (J ⥤ C)) :=
  ReedyModel.cofibrantFactorizationData (s.withOriginalDegree degree hdegree factor) Fc Ff

/-- The native construction retains the full original functorial fibration factor record. -/
def fibrantFactorizationDataWithOriginalDegree :
    letI := s.modelCategoryWithOriginalDegree degree hdegree factor Fc Ff
    FunctorialFactorizationData (trivialCofibrations (J ⥤ C)) (fibrations (J ⥤ C)) :=
  ReedyModel.fibrantFactorizationData (s.withOriginalDegree degree hdegree factor) Fc Ff

end OriginalDegree

section NativeDegree

variable [OrderBot D] [SuccOrder D]
  (s : HomotopicalAlgebra.ReedyStructure inverse direct D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape ((CategoryTheory.ReedyStructure.ofCanonical s).Matching j) C]
  [∀ j, HasColimitsOfShape ((CategoryTheory.ReedyStructure.ofCanonical s).Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The general Reedy model category on Mathlib's native Reedy data and the given coefficient
factories. -/
@[instance_reducible]
def modelCategory : ModelCategory (J ⥤ C) :=
  ReedyModel.modelCategory (CategoryTheory.ReedyStructure.ofCanonical s) Fc Ff

/-- The native general model's complete chosen cofibration factor, with all original natural maps.
-/
def cofibrantFactorizationData :
    letI := s.modelCategory Fc Ff
    FunctorialFactorizationData (cofibrations (J ⥤ C)) (trivialFibrations (J ⥤ C)) :=
  ReedyModel.cofibrantFactorizationData (CategoryTheory.ReedyStructure.ofCanonical s) Fc Ff

/-- The native general model's complete chosen fibration factor, with all original natural maps. -/
def fibrantFactorizationData :
    letI := s.modelCategory Fc Ff
    FunctorialFactorizationData (trivialCofibrations (J ⥤ C)) (fibrations (J ⥤ C)) :=
  ReedyModel.fibrantFactorizationData (CategoryTheory.ReedyStructure.ofCanonical s) Fc Ff

end NativeDegree

end HomotopicalAlgebra.ReedyStructure

namespace HomotopicalAlgebra.ReedyModel

open CategoryTheory Limits MorphismProperty

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : CategoryTheory.ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] [ModelCategory C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  (Fc : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The native presentation reconstructs exactly the original complete Reedy interface. -/
theorem nativeInterface_eq :
    r.toCanonical.withOriginalDegree r.degree r.native_degree r.factor = r := rfl

/-- The general native construction gives the same full model dictionary for the original data. -/
theorem modelCategory_eq_native :
    r.toCanonical.modelCategoryWithOriginalDegree r.degree r.native_degree r.factor Fc Ff =
      modelCategory r Fc Ff := rfl

/-- The general native construction retains the entire originally supplied cofibration factory. -/
theorem cofibrantFactorizationData_eq_native :
    r.toCanonical.cofibrantFactorizationDataWithOriginalDegree
        r.degree r.native_degree r.factor Fc Ff = cofibrantFactorizationData r Fc Ff := rfl

/-- The general native construction retains the entire originally supplied fibration factory. -/
theorem fibrantFactorizationData_eq_native :
    r.toCanonical.fibrantFactorizationDataWithOriginalDegree
        r.degree r.native_degree r.factor Fc Ff = fibrantFactorizationData r Fc Ff := rfl

end HomotopicalAlgebra.ReedyModel
