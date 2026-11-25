/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.IndexEquivalence
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!# Fixed Hom, insertion, chosen adjunction and entire Arrow comparison contracts -/
set_option autoImplicit false
noncomputable section
universe w uD vD uS vS uM vM
open CategoryTheory Limits HomotopicalAlgebra
open HomotopicalAlgebra.FunctorProjective HomotopicalAlgebra.FunctorProjective.IndexEquivalence

namespace MathlibExtTest.FunctorProjectiveIndexEquivalence

variable {D : Type uD} [Category.{vD} D] {S : Type uS} [Category.{vS} S]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [LocallySmall.{w} S]
  (e : D ≌ S) (d : CofibrantGenerationData M κ)

example (s t : S) : (e.inverse.obj s ⟶ e.inverse.obj t) ≃ (s ⟶ t) :=
  homIndexEquiv e s t

example :
    (fun (s t : S) (f : e.inverse.obj s ⟶ e.inverse.obj t) => homIndexEquiv e s t f) =
      fun (s t : S) (f : e.inverse.obj s ⟶ e.inverse.obj t) =>
        e.counitInv.app s ≫ e.functor.map f ≫ e.counit.app t :=
  homIndexEquiv_forward_function e

example :
    (fun (s t : S) (f : s ⟶ t) => (homIndexEquiv e s t).symm f) =
      fun (s t : S) (f : s ⟶ t) => e.inverse.map f :=
  homIndexEquiv_inverse_function e

example {s t z : S} (f : e.inverse.obj s ⟶ e.inverse.obj t) (g : t ⟶ z) :
    homIndexEquiv e s z (f ≫ e.inverse.map g) = homIndexEquiv e s t f ≫ g :=
  homIndexEquiv_comp e f g

example (s t : S) (A : M) (h : e.inverse.obj s ⟶ e.inverse.obj t) :
    sourceInsertion e d s t A h ≫ (componentIso e d s t A).hom =
      targetInsertion d s t A (homIndexEquiv e s t h) :=
  componentIso_insertion_hom e d s t A h

example (s t : S) (A : M) (h : s ⟶ t) :
    targetInsertion d s t A h ≫ (componentIso e d s t A).inv =
      sourceInsertion e d s t A (e.inverse.map h) :=
  componentIso_insertion_inv e d s t A h

example (s t : S) {A B : M} (f : A ⟶ B)
    (h : e.inverse.obj s ⟶ e.inverse.obj t) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    sourceInsertion e d s t A h ≫
        ((freeFunctor (D := D) d (e.inverse.obj s)).map f).app (e.inverse.obj t) =
      f ≫ sourceInsertion e d s t B h := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact sourceInsertion_coefficient e d s t f h

example (s : S) {t z : S} (A : M) (h : e.inverse.obj s ⟶ e.inverse.obj t) (g : t ⟶ z) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    sourceInsertion e d s t A h ≫
        ((freeFunctor (D := D) d (e.inverse.obj s)).obj A).map (e.inverse.map g) =
      sourceInsertion e d s z A (h ≫ e.inverse.map g) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact sourceInsertion_index e d s A h g

example (s : S) {t z : S} (A : M) (g : t ⟶ z) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((freeFunctor (D := D) d (e.inverse.obj s)).obj A).map (e.inverse.map g) ≫
        (componentIso e d s z A).hom =
      (componentIso e d s t A).hom ≫ ((freeFunctor (D := S) d s).obj A).map g := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact componentIso_index_naturality e d s A g

example (s t : S) {A B : M} (f : A ⟶ B) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    ((freeFunctor (D := D) d (e.inverse.obj s)).map f).app (e.inverse.obj t) ≫
        (componentIso e d s t B).hom =
      (componentIso e d s t A).hom ≫ ((freeFunctor (D := S) d s).map f).app t := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact componentIso_coefficient_naturality e d s t f

example (s : S) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    e.inverse ⋙ (freeFunctor (D := D) d (e.inverse.obj s)).obj A ≅
      (freeFunctor (D := S) d s).obj A := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeObjectIso e d s A

example (s : S) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    freeFunctor (D := D) d (e.inverse.obj s) ⋙ (e.congrLeft (E := M)).functor ≅
      freeFunctor (D := S) d s := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeIso e d s

example (s : S) :
    (fun (A : M) (t : S) => ((freeIso e d s).hom.app A).app t) =
      fun (A : M) (t : S) => (componentIso e d s t A).hom :=
  freeIso_hom_component_function e d s

example (s : S) :
    (fun (A : M) (t : S) => ((freeIso e d s).inv.app A).app t) =
      fun (A : M) (t : S) => (componentIso e d s t A).inv :=
  freeIso_inv_component_function e d s

example (s : S) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A ≫
        ((freeIso e d s).hom.app A).app s =
      (freeEvaluationAdjunction (D := S) d s).unit.app A := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeIso_unit e d s A

example (s : S) (A : M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeEvaluationAdjunction (D := S) d s).unit.app A ≫
        ((freeIso e d s).inv.app A).app s =
      (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).unit.app A := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeIso_unit_inv e d s A

example (s : S) (X : D ⥤ M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeIso e d s).hom.app (X.obj (e.inverse.obj s)) ≫
        (freeEvaluationAdjunction (D := S) d s).counit.app (e.inverse ⋙ X) =
      (e.congrLeft (E := M)).functor.map
        ((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).counit.app X) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeIso_counit e d s X

example (s : S) (X : D ⥤ M) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeIso e d s).inv.app (X.obj (e.inverse.obj s)) ≫
        (e.congrLeft (E := M)).functor.map
          ((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).counit.app X) =
      (freeEvaluationAdjunction (D := S) d s).counit.app (e.inverse ⋙ X) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeIso_counit_inv e d s X

example (s : S) (A : M) (X : D ⥤ M)
    (f : letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor;
      (freeFunctor (D := D) d (e.inverse.obj s)).obj A ⟶ X) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeEvaluationAdjunction (D := S) d s).homEquiv A (e.inverse ⋙ X)
        ((freeIso e d s).inv.app A ≫ (e.congrLeft (E := M)).functor.map f) =
      (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).homEquiv A X f := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeIso_homEquiv e d s A X f

example (s : S) (A : M) (X : D ⥤ M) (f : A ⟶ X.obj (e.inverse.obj s)) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeIso e d s).hom.app A ≫
        ((freeEvaluationAdjunction (D := S) d s).homEquiv A (e.inverse ⋙ X)).symm f =
      (e.congrLeft (E := M)).functor.map
        (((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).homEquiv A X).symm f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeIso_homEquiv_symm e d s A X f

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (s : S) (A : M) (X : D ⥤ M)
      (f : letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor;
      (freeFunctor (D := D) d (e.inverse.obj s)).obj A ⟶ X) =>
      (freeEvaluationAdjunction (D := S) d s).homEquiv A (e.inverse ⋙ X)
        ((freeIso e d s).inv.app A ≫ (e.congrLeft (E := M)).functor.map f)) =
      fun (s : S) (A : M) (X : D ⥤ M)
        (f : letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor;
      (freeFunctor (D := D) d (e.inverse.obj s)).obj A ⟶ X) =>
        (freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).homEquiv A X f := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeIso_homEquiv_function e d

example :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (fun (s : S) (A : M) (X : D ⥤ M) (f : A ⟶ X.obj (e.inverse.obj s)) =>
      (freeIso e d s).hom.app A ≫
        ((freeEvaluationAdjunction (D := S) d s).homEquiv A (e.inverse ⋙ X)).symm f) =
      fun (s : S) (A : M) (X : D ⥤ M) (f : A ⟶ X.obj (e.inverse.obj s)) =>
        (e.congrLeft (E := M)).functor.map
          (((freeEvaluationAdjunction (D := D) d (e.inverse.obj s)).homEquiv A X).symm f) := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeIso_homEquiv_symm_function e d

example (s : S) (f : Arrow M) (t : S) :
    ((freeArrowComparison e d s).hom.app f).left.app t =
        (componentIso e d s t f.left).hom ∧
      ((freeArrowComparison e d s).hom.app f).right.app t =
        (componentIso e d s t f.right).hom ∧
      ((freeArrowComparison e d s).inv.app f).left.app t =
        (componentIso e d s t f.left).inv ∧
      ((freeArrowComparison e d s).inv.app f).right.app t =
        (componentIso e d s t f.right).inv :=
  freeArrowComparison_fields e d s f t

example (s : S) {f g : Arrow M} (a : f ⟶ g) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeFunctor (D := D) d (e.inverse.obj s) ⋙
        (e.congrLeft (E := M)).functor).mapArrow.map a ≫
        (freeArrowComparison e d s).hom.app g =
      (freeArrowComparison e d s).hom.app f ≫
        (freeFunctor (D := S) d s).mapArrow.map a := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeArrowComparison_naturality e d s a

example (s : S) {f g : Arrow M} (a : f ⟶ g) :
    letI : LocallySmall.{w} D := locallySmall_of_faithful e.functor
    (freeFunctor (D := S) d s).mapArrow.map a ≫
        (freeArrowComparison e d s).inv.app g =
      (freeArrowComparison e d s).inv.app f ≫
        (freeFunctor (D := D) d (e.inverse.obj s) ⋙
          (e.congrLeft (E := M)).functor).mapArrow.map a := by
  let _ : LocallySmall.{w} D := locallySmall_of_faithful e.functor
  exact freeArrowComparison_inv_naturality e d s a

section OriginalIndices

example :
    ∀ s : Discrete PEmpty,
      freeFunctor (D := Discrete PEmpty) d s ⋙
          ((CategoryTheory.Equivalence.refl (C := Discrete PEmpty)).congrLeft (E := M)).functor ≅
        freeFunctor (D := Discrete PEmpty) d s :=
  fun s => freeIso (CategoryTheory.Equivalence.refl (C := Discrete PEmpty)) d s

example (n : Discrete ℕ) :
    freeFunctor (D := Discrete ℕ) d n ⋙
        ((CategoryTheory.Equivalence.refl (C := Discrete ℕ)).congrLeft (E := M)).functor ≅
      freeFunctor (D := Discrete ℕ) d n :=
  freeIso (CategoryTheory.Equivalence.refl (C := Discrete ℕ)) d n

example (n : SingleObj (Multiplicative ℕ)) :
    freeFunctor (D := SingleObj (Multiplicative ℕ)) (κ := κ) d n ⋙
        ((CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))).congrLeft (E := M)).functor ≅
      freeFunctor (D := SingleObj (Multiplicative ℕ)) (κ := κ) d n :=
  freeIso (κ := κ) (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))) d n

/-- The original index uses the stock category on its raised object type. -/
local instance originalFreeRaisedCategory : Category.{vD} (ULift.{uD + 1} D) := uliftCategory D
/-- The original index uses the stock category on its independently raised Homs. -/
local instance originalFreeRaisedHomCategory :
    Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))

example (s : S) :
    let raised := (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm.trans e
    letI : LocallySmall.{w} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
      locallySmall_of_faithful raised.functor
    freeFunctor (D := ULiftHom.{vD + 1} (ULift.{uD + 1} D)) d
        (raised.inverse.obj s) ⋙ (raised.congrLeft (E := M)).functor ≅
      freeFunctor (D := S) d s := by
  let raised := (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm.trans e
  exact freeIso raised d s

end OriginalIndices

end MathlibExtTest.FunctorProjectiveIndexEquivalence
