/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedDerivedKan
public import MathlibExt.CategoryTheory.Enriched.LeftKanFreeArrow

/-!
# Actual derived Kan images of complete free-map families

The original coefficient Q makes every chosen free endpoint cofibrant.
The original diagram q and Quillen Brown preservation give the first
comparison isomorphism. The actual coend/free map gives the second.
Their complete square retains every original arrow between free objects,
including arrows not induced by a coefficient map at one fixed index.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe w uA uB uV vV uI uD vD
open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Functor
open scoped MonoidalClosed

namespace HomotopicalAlgebra.OriginalEnrichedDerivedKan

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [Small.{w} B] [LocallySmall.{w} V]
  (g : CofibrantGenerationData V κ)
  (sA : OriginalEnrichedProjective.SourceConditions (A := A) g)
  (sB : OriginalEnrichedProjective.SourceConditions (A := B) g)

/-- The actual original free object on the original coefficient Q. -/
abbrev freeAfterQ (a : A) (X : V) :=
  EnrichedFunctorCat.Free.object a ((GeneratedFunctorialReplacements.fromGeneration g).Q.obj X)

/-- The source model's actual free Quillen pair earns every endpoint's cofibrancy. -/
theorem freeAfterQ_isCofibrant (a : A) (X : V) :
    letI := projectiveModel g sA
    IsCofibrant (freeAfterQ g a X) := by
  let := projectiveModel g sA
  let := free_isQuillen g sA a
  let : IsCofibrant ((GeneratedFunctorialReplacements.fromGeneration g).Q.obj X) :=
    (GeneratedFunctorialReplacements.fromGeneration g).q_cofibrant X
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
    (adj := EnrichedFunctorCat.Free.adjunction a) inferInstance

/-- The complete original q comparison is an Iso at each earned free endpoint. -/
def freeReplacementIso (j : EnrichedFunctor V A B) (a : A) (X : V) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    (derivedKan g sA sB j).obj
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).obj (freeAfterQ g a X)) ≅
      (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).obj
        ((originalKan g j).obj (freeAfterQ g a X)) := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  letI := original_isQuillen g sA sB j
  letI : IsCofibrant (freeAfterQ g a X) := freeAfterQ_isCofibrant g sA a X
  letI : IsIso ((DerivedFunctorCoherence.leftComparison (originalAdjunction g j)
      (projectiveReplacements g sA)).app (freeAfterQ g a X)) :=
    DerivedFunctorCoherence.leftComparison_isIso (originalAdjunction g j)
      (projectiveReplacements g sA) (freeAfterQ g a X)
  change (DerivedFunctorCoherence.projection (EnrichedFunctorCat V A) ⋙
      DerivedFunctorCoherence.left (originalAdjunction g j) (projectiveReplacements g sA)).obj
        (freeAfterQ g a X) ≅
    (originalKan g j ⋙ DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).obj
      (freeAfterQ g a X)
  exact asIso ((DerivedFunctorCoherence.leftComparison (originalAdjunction g j)
    (projectiveReplacements g sA)).app (freeAfterQ g a X))

/-- Its forward map is the literal original Kan image of the original diagram q. -/
theorem freeReplacementIso_hom (j : EnrichedFunctor V A B) (a : A) (X : V) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    (freeReplacementIso g sA sB j a X).hom =
      (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        ((originalKan g j).map ((projectiveReplacements g sA).q.app (freeAfterQ g a X))) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  let := original_isQuillen g sA sB j
  change (DerivedFunctorCoherence.leftComparison (originalAdjunction g j)
    (projectiveReplacements g sA)).app (freeAfterQ g a X) = _
  exact DerivedFunctorCoherence.leftComparison_app (originalAdjunction g j)
    (projectiveReplacements g sA) (freeAfterQ g a X)

/-- The two actual complete maps compare the derived Kan value to the original target free value. -/
def freeImageIso (j : EnrichedFunctor V A B) (a : A) (X : V) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    (derivedKan g sA sB j).obj
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).obj (freeAfterQ g a X)) ≅
      (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).obj (freeAfterQ g (j.obj a) X) := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  exact freeReplacementIso g sA sB j a X ≪≫
    (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).mapIso
      ((pointsetFreeIso g j a).app ((GeneratedFunctorialReplacements.fromGeneration g).Q.obj X))

/-- Both original comparison legs appear explicitly in the full forward map. -/
theorem freeImageIso_hom (j : EnrichedFunctor V A B) (a : A) (X : V) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    (freeImageIso g sA sB j a X).hom =
      (freeReplacementIso g sA sB j a X).hom ≫
        (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
          ((pointsetFreeIso g j a).hom.app ((GeneratedFunctorialReplacements.fromGeneration g).Q.obj X)) :=
  rfl

/-- Both original inverse legs remain in the full inverse comparison. -/
theorem freeImageIso_inv (j : EnrichedFunctor V A B) (a : A) (X : V) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    (freeImageIso g sA sB j a X).inv =
      (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
          ((pointsetFreeIso g j a).inv.app ((GeneratedFunctorialReplacements.fromGeneration g).Q.obj X)) ≫
        (freeReplacementIso g sA sB j a X).inv :=
  rfl

/-- Every arbitrary original free arrow has the full derived Kan comparison square. -/
theorem freeImageIso_naturality (j : EnrichedFunctor V A B) {a b : A} {X Y : V}
    (f : freeAfterQ g a X ⟶ freeAfterQ g b Y) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    (derivedKan g sA sB j).map ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map f) ≫
        (freeImageIso g sA sB j b Y).hom =
      (freeImageIso g sA sB j a X).hom ≫
        (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
          (EnrichedFunctorCat.LeftKanFreeArrow.map j f) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  let := original_isQuillen g sA sB j
  let := objectCoproducts g j
  let := relationCoproducts g j
  let := balanceCoequalizers g j
  have hn : (derivedKan g sA sB j).map
      ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map f) ≫
        (freeReplacementIso g sA sB j b Y).hom =
    (freeReplacementIso g sA sB j a X).hom ≫
      (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map ((originalKan g j).map f) := by
    change (DerivedFunctorCoherence.left (originalAdjunction g j)
        (projectiveReplacements g sA)).map
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map f) ≫ _ = _
    rw [DerivedFunctorCoherence.left_map, freeReplacementIso_hom, freeReplacementIso_hom]
    change (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        ((originalKan g j).map ((projectiveReplacements g sA).Q.map f)) ≫
        (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
          ((originalKan g j).map ((projectiveReplacements g sA).q.app (freeAfterQ g b Y))) =
      (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        ((originalKan g j).map ((projectiveReplacements g sA).q.app (freeAfterQ g a X))) ≫
        (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map ((originalKan g j).map f)
    have h := congrArg
      (fun t => (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        ((originalKan g j).map t)) ((projectiveReplacements g sA).q.naturality f)
    simpa only [Functor.id_map, Functor.id_obj, Functor.map_comp] using h
  have hs : (originalKan g j).map f ≫
      (pointsetFreeIso g j b).hom.app ((GeneratedFunctorialReplacements.fromGeneration g).Q.obj Y) =
    (pointsetFreeIso g j a).hom.app ((GeneratedFunctorialReplacements.fromGeneration g).Q.obj X) ≫
      EnrichedFunctorCat.LeftKanFreeArrow.map j f :=
    EnrichedFunctorCat.LeftKanFreeArrow.map_square j f
  rw [freeImageIso_hom, freeImageIso_hom]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, hs,
    Functor.map_comp, ← Category.assoc]

/-- The entire inverse square retains the same original free arrow and its computed image. -/
theorem freeImageIso_inverse_naturality (j : EnrichedFunctor V A B) {a b : A} {X Y : V}
    (f : freeAfterQ g a X ⟶ freeAfterQ g b Y) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    (DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        (EnrichedFunctorCat.LeftKanFreeArrow.map j f) ≫ (freeImageIso g sA sB j b Y).inv =
      (freeImageIso g sA sB j a X).inv ≫
        (derivedKan g sA sB j).map
          ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map f) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  apply (cancel_epi (freeImageIso g sA sB j a X).hom).1
  rw [← Category.assoc, ← freeImageIso_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The whole original derived free arrow has both complete comparison endpoints. -/
def freeImageArrowIso (j : EnrichedFunctor V A B) {a b : A} {X Y : V}
    (f : freeAfterQ g a X ⟶ freeAfterQ g b Y) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    Arrow.mk ((derivedKan g sA sB j).map
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map f)) ≅
      Arrow.mk ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        (EnrichedFunctorCat.LeftKanFreeArrow.map j f)) := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  exact Arrow.isoMk (freeImageIso g sA sB j a X) (freeImageIso g sA sB j b Y)
    (freeImageIso_naturality g sA sB j f).symm

/-- Invertibility of the actual derived image is tested on the computed original target free arrow. -/
theorem freeImage_isIso_iff (j : EnrichedFunctor V A B) {a b : A} {X Y : V}
    (f : freeAfterQ g a X ⟶ freeAfterQ g b Y) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    IsIso ((derivedKan g sA sB j).map
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map f)) ↔
      IsIso ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        (EnrichedFunctorCat.LeftKanFreeArrow.map j f)) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  exact (MorphismProperty.isomorphisms (projectiveHo g sB)).arrow_mk_iso_iff
    (freeImageArrowIso g sA sB j f)

/-- Every label of the specified original free-map family retains its complete derived Arrow comparison. -/
def freeFamilyArrowIso (j : EnrichedFunctor V A B) {I : Type uI}
    (a b : I → A) (X Y : I → V)
    (S : ∀ i : I, freeAfterQ g (a i) (X i) ⟶ freeAfterQ g (b i) (Y i)) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    ∀ i : I, Arrow.mk ((derivedKan g sA sB j).map
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map (S i))) ≅
      Arrow.mk ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        (EnrichedFunctorCat.LeftKanFreeArrow.map j (S i))) := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  exact fun i => freeImageArrowIso g sA sB j (S i)

/-- The entire specified family, with every index and coefficient retained, has the actual image criterion. -/
theorem freeFamily_isIso_iff (j : EnrichedFunctor V A B) {I : Type uI}
    (a b : I → A) (X Y : I → V)
    (S : ∀ i : I, freeAfterQ g (a i) (X i) ⟶ freeAfterQ g (b i) (Y i)) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    (∀ i : I, IsIso ((derivedKan g sA sB j).map
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map (S i)))) ↔
      ∀ i : I, IsIso ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        (EnrichedFunctorCat.LeftKanFreeArrow.map j (S i))) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  exact forall_congr' (fun i => freeImage_isIso_iff g sA sB j (S i))

section Postcomposition

variable {D : Type uD} [Category.{vD} D]

/-- Any actual target functor preserves both whole endpoint comparisons and their original map square. -/
def freeImageArrowIsoPost (j : EnrichedFunctor V A B) (H : projectiveHo g sB ⥤ D)
    {a b : A} {X Y : V} (f : freeAfterQ g a X ⟶ freeAfterQ g b Y) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    Arrow.mk (H.map ((derivedKan g sA sB j).map
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map f))) ≅
      Arrow.mk (H.map ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        (EnrichedFunctorCat.LeftKanFreeArrow.map j f))) := by
  letI := projectiveModel g sA
  letI := projectiveModel g sB
  exact Arrow.isoMk (H.mapIso (freeImageIso g sA sB j a X))
    (H.mapIso (freeImageIso g sA sB j b Y)) (by
      change H.map (freeImageIso g sA sB j a X).hom ≫
          H.map ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
            (EnrichedFunctorCat.LeftKanFreeArrow.map j f)) =
        H.map ((derivedKan g sA sB j).map
          ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map f)) ≫
          H.map (freeImageIso g sA sB j b Y).hom
      simpa only [Functor.map_comp] using
        congrArg H.map (freeImageIso_naturality g sA sB j f).symm)

/-- The same full computed image criterion holds after every actual target functor. -/
theorem freeImagePost_isIso_iff (j : EnrichedFunctor V A B) (H : projectiveHo g sB ⥤ D)
    {a b : A} {X Y : V} (f : freeAfterQ g a X ⟶ freeAfterQ g b Y) :
    letI := projectiveModel g sA
    letI := projectiveModel g sB
    IsIso (H.map ((derivedKan g sA sB j).map
        ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V A)).map f))) ↔
      IsIso (H.map ((DerivedFunctorCoherence.projection (EnrichedFunctorCat V B)).map
        (EnrichedFunctorCat.LeftKanFreeArrow.map j f))) := by
  let := projectiveModel g sA
  let := projectiveModel g sB
  exact (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
    (freeImageArrowIsoPost g sA sB j H f)

end Postcomposition

end HomotopicalAlgebra.OriginalEnrichedDerivedKan
