/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCoefficientRecovery

/-!
# Full coefficient action recovery from the original index and sphere actions

The coefficient is retained as its entire object. The original operator
composition, functor composition law and source unit reconstruct its action
from the original sphere action and the restricted index action. The right
orientation uses the actual index block braiding.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

/-- Postcomposition on the original index acts on the entire coefficient action. -/
theorem coefficientAction_postcompose
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k l a : I)
    (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    coefficientAction d S L F n k a f ≫
        ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map g =
      coefficientAction d S L F n l a (f ≫ g) := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let Y := F.toEnrichedFunctor.obj (⟨k⟩ : OperatorIndex d S L)
  let Z := F.toEnrichedFunctor.obj (⟨l⟩ : OperatorIndex d S L)
  let A := S.obj a
  let p := coefficientHom d S n k a f
  let q := eHomEquiv V g ≫ indexHom d S L k l
  let t := coefficientHom d S n l a (f ≫ g)
  let h := F.toEnrichedFunctor.map (⟨n⟩ : OperatorIndex d S L) ⟨k⟩
  let j := F.toEnrichedFunctor.map (⟨k⟩ : OperatorIndex d S L) ⟨l⟩
  let c := F.toEnrichedFunctor.map (⟨n⟩ : OperatorIndex d S L) ⟨l⟩
  let r : Y ⟶ Z :=
    ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map g
  have hRestriction : ((indexRestriction d S L).obj F).toEnrichedFunctor.map k l =
      indexHom d S L k l ≫ j := rfl
  have hPoint : eHomEquiv V r = q ≫ j :=
    (EnrichedFunctor.toOrdinaryFunctor_map
      ((indexRestriction d S L).obj F).toEnrichedFunctor g).trans
      ((congrArg (fun z => eHomEquiv V g ≫ z) hRestriction).trans
        (Category.assoc (eHomEquiv V g) (indexHom d S L k l) j).symm)
  have hFull : composition d S L n k l ≫ c =
      (h ⊗ₘ j) ≫ eComp V X Y Z := by
    have hF := F.toEnrichedFunctor.map_comp
      (⟨n⟩ : OperatorIndex d S L) ⟨k⟩ ⟨l⟩
    rw [operatorIndex_comp] at hF
    exact hF
  have hPair : (p ⊗ₘ q) ≫ (h ⊗ₘ j) = (p ≫ h) ⊗ₘ (q ≫ j) :=
    tensorHom_comp_tensorHom p q h j
  have hUnit : (ρ_ A).inv ≫ ((p ≫ h) ⊗ₘ (q ≫ j)) =
      (p ≫ h) ≫ (ρ_ ((ihom X).obj Y)).inv ≫ ((ihom X).obj Y) ◁ (q ≫ j) :=
    rightUnitor_inv_comp_tensorHom (p ≫ h) (q ≫ j)
  have hMapped : t ≫ c = (p ≫ h) ≫ eHomWhiskerLeft V X r := by
    calc
      _ = ((ρ_ A).inv ≫ (p ⊗ₘ q) ≫ composition d S L n k l) ≫ c :=
        congrArg (fun z => z ≫ c)
          (coefficientHom_postcompose d S L n k l a f g).symm
      _ = (ρ_ A).inv ≫ (p ⊗ₘ q) ≫
          ((h ⊗ₘ j) ≫ eComp V X Y Z) := by
        simpa only [Category.assoc] using
          congrArg (fun z => (ρ_ A).inv ≫ (p ⊗ₘ q) ≫ z) hFull
      _ = (ρ_ A).inv ≫ ((p ≫ h) ⊗ₘ (q ≫ j)) ≫ eComp V X Y Z := by
        simpa only [Category.assoc] using
          congrArg (fun z => (ρ_ A).inv ≫ z ≫ eComp V X Y Z) hPair
      _ = (p ≫ h) ≫ (ρ_ ((ihom X).obj Y)).inv ≫
          ((ihom X).obj Y) ◁ (q ≫ j) ≫ eComp V X Y Z :=
        (Category.assoc (ρ_ A).inv ((p ≫ h) ⊗ₘ (q ≫ j)) (eComp V X Y Z)).symm.trans
          ((congrArg (fun z => z ≫ eComp V X Y Z) hUnit).trans
            ((Category.assoc (p ≫ h)
              ((ρ_ ((ihom X).obj Y)).inv ≫ ((ihom X).obj Y) ◁ (q ≫ j))
              (eComp V X Y Z)).trans
                (congrArg (fun z => (p ≫ h) ≫ z)
                  (Category.assoc (ρ_ ((ihom X).obj Y)).inv
                    (((ihom X).obj Y) ◁ (q ≫ j)) (eComp V X Y Z)))))
      _ = _ := by
        rw [← hPoint]
        rfl
  have hAction : coefficientAction d S L F n k a f =
      MonoidalClosed.uncurry (p ≫ h) :=
    (MonoidalClosed.uncurry_natural_left p h).symm
  calc
    _ = MonoidalClosed.uncurry (p ≫ h) ≫ r :=
      congrArg (fun z => z ≫ r) hAction
    _ = MonoidalClosed.uncurry ((p ≫ h) ≫ eHomWhiskerLeft V X r) := by
      rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
        MonoidalClosed.uncurry_natural_right]
    _ = MonoidalClosed.uncurry (t ≫ c) := congrArg MonoidalClosed.uncurry hMapped.symm
    _ = _ := MonoidalClosed.uncurry_natural_left t c

/-- The original coefficient action is recovered using its full sphere object. -/
theorem coefficientAction_from_sphere_and_index
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k a : I)
    (f : a ⊗ n ⟶ k) :
    coefficientAction d S L F n k a f =
      coefficientAction d S L F n (a ⊗ n) a (𝟙 (a ⊗ n)) ≫
        ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map f := by
  exact (congrArg (coefficientAction d S L F n k a) (Category.id_comp f)).symm.trans
    (coefficientAction_postcompose d S L F n (a ⊗ n) k a (𝟙 (a ⊗ n)) f).symm

variable [BraidedCategory I]

/-- The entire coefficient action is recovered from the actual right sphere action. -/
theorem coefficientAction_from_rightSphere_and_index
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k a : I)
    (f : a ⊗ n ⟶ k) :
    coefficientAction d S L F n k a f =
      rightSphereAction d S L F n a ≫
        ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map
          ((β_ a n).inv ≫ f) := by
  exact (congrArg (coefficientAction d S L F n k a)
    (Iso.hom_inv_id_assoc (β_ a n) f)).symm.trans
      (coefficientAction_postcompose d S L F n (n ⊗ a) k a
        (β_ a n).hom ((β_ a n).inv ≫ f)).symm

end CategoryTheory.Enriched.SphereOperator
