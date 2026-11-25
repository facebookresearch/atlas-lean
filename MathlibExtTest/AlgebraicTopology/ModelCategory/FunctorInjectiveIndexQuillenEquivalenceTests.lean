/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.IndexQuillenEquivalence
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Original existing-model native Ran Quillen-equivalence clients

All criteria and preservation statements use the same supplied e and
native Ran adjunction. Same-index clients name both model records.
There is no selection of an injective model or factor algorithm.
-/

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM
open CategoryTheory Functor HomotopicalAlgebra

namespace MathlibExtTest.FunctorInjectiveIndexQuillenEquivalence

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]

section OriginalExistingModels

variable [ModelCategory (D ⥤ M)] [ModelCategory (E ⥤ M)]
  (e : D ≌ E) [∀ Y : D ⥤ M, e.functor.HasRightKanExtension Y]
  (hWD : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
  (hWE : weakEquivalences (E ⥤ M) = (weakEquivalences M).functorCategory E)
  (hCD : cofibrations (D ⥤ M) = (cofibrations M).functorCategory D)
  (hCE : cofibrations (E ⥤ M) = (cofibrations M).functorCategory E)
  (hTD : trivialCofibrations (D ⥤ M) = (trivialCofibrations M).functorCategory D)
  (hTE : trivialCofibrations (E ⥤ M) = (trivialCofibrations M).functorCategory E)

example : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
  FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
    e hWD hWE hCD hCE hTD hTE

example {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    weakEquivalences (D ⥤ M) f ↔
      weakEquivalences (E ⥤ M) ((e.functor.ranAdjunction M).homEquiv X Y f) :=
  FunctorInjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff_of_pointwise e hWD hWE f

example {X : E ⥤ M} {Y : D ⥤ M} (c : X ⟶ e.functor.ran.obj Y) :
    weakEquivalences (E ⥤ M) c ↔
      weakEquivalences (D ⥤ M) (((e.functor.ranAdjunction M).homEquiv X Y).symm c) :=
  FunctorInjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff_of_pointwise e hWD hWE c

example (X : E ⥤ M) (Y : D ⥤ M) [IsCofibrant X] [IsFibrant Y]
    (f : e.functor ⋙ X ⟶ Y) :
    weakEquivalences (D ⥤ M) f ↔
      weakEquivalences (E ⥤ M) ((e.functor.ranAdjunction M).homEquiv X Y f) := by
  let _ : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
    FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
      e hWD hWE hCD hCE hTD hTE
  exact Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff
    (adj := e.functor.ranAdjunction M) f

example (X : E ⥤ M) (Y : D ⥤ M) [IsCofibrant X] [IsFibrant Y]
    (c : X ⟶ e.functor.ran.obj Y) :
    weakEquivalences (E ⥤ M) c ↔
      weakEquivalences (D ⥤ M) (((e.functor.ranAdjunction M).homEquiv X Y).symm c) := by
  let _ : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
    FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
      e hWD hWE hCD hCE hTD hTE
  have h := Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff
    (adj := e.functor.ranAdjunction M) (((e.functor.ranAdjunction M).homEquiv X Y).symm c)
  simpa only [Equiv.apply_symm_apply] using h.symm

example {X X' : E ⥤ M} (f : X ⟶ X') (hf : cofibrations (E ⥤ M) f) :
    cofibrations (D ⥤ M) (((Functor.whiskeringLeft D E M).obj e.functor).map f) := by
  let _ : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
    FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
      e hWD hWE hCD hCE hTD hTE
  exact (inferInstance : (e.functor.ranAdjunction M).IsQuillenAdjunction).preservesCofibrations f hf

example {X X' : E ⥤ M} (f : X ⟶ X') (hf : trivialCofibrations (E ⥤ M) f) :
    trivialCofibrations (D ⥤ M) (((Functor.whiskeringLeft D E M).obj e.functor).map f) := by
  let _ : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
    FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
      e hWD hWE hCD hCE hTD hTE
  exact (inferInstance : (e.functor.ranAdjunction M).IsQuillenAdjunction).preservesTrivialCofibrations f hf

example {Y Y' : D ⥤ M} (f : Y ⟶ Y') (hf : fibrations (D ⥤ M) f) :
    fibrations (E ⥤ M) (e.functor.ran.map f) := by
  let _ : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
    FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
      e hWD hWE hCD hCE hTD hTE
  exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := e.functor.ranAdjunction M) f hf

example {Y Y' : D ⥤ M} (f : Y ⟶ Y') (hf : trivialFibrations (D ⥤ M) f) :
    trivialFibrations (E ⥤ M) (e.functor.ran.map f) := by
  let _ : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
    FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
      e hWD hWE hCD hCE hTD hTE
  exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := e.functor.ranAdjunction M) f hf

example (X : E ⥤ M) (hX : IsCofibrant X) : IsCofibrant (e.functor ⋙ X) := by
  let _ : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
    FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
      e hWD hWE hCD hCE hTD hTE
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := e.functor.ranAdjunction M) hX

example (Y : D ⥤ M) (hY : IsFibrant Y) : IsFibrant (e.functor.ran.obj Y) := by
  let _ : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
    FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
      e hWD hWE hCD hCE hTD hTE
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := e.functor.ranAdjunction M) hY

example (X : E ⥤ M) [IsCofibrant X] [IsFibrant (e.functor ⋙ X)] :
    weakEquivalences (E ⥤ M) ((e.functor.ranAdjunction M).unit.app X) := by
  let _ : IsFibrant (((Functor.whiskeringLeft D E M).obj e.functor).obj X) := by
    change IsFibrant (e.functor ⋙ X)
    infer_instance
  let _ : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
    FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
      e hWD hWE hCD hCE hTD hTE
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenEquivalence.weakEquivalence_unit (adj := e.functor.ranAdjunction M) X)

example (Y : D ⥤ M) [IsFibrant Y] [IsCofibrant (e.functor.ran.obj Y)] :
    weakEquivalences (D ⥤ M) ((e.functor.ranAdjunction M).counit.app Y) := by
  let _ : (e.functor.ranAdjunction M).IsQuillenEquivalence :=
    FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
      e hWD hWE hCD hCE hTD hTE
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenEquivalence.weakEquivalence_counit (adj := e.functor.ranAdjunction M) Y)

example (X : E ⥤ M) (Y : D ⥤ M) :
    (fun f : e.functor ⋙ X ⟶ Y => (e.functor.ranAdjunction M).homEquiv X Y f) =
      fun f => (e.functor.ranAdjunction M).unit.app X ≫ e.functor.ran.map f := by
  funext f
  exact Adjunction.homEquiv_apply (e.functor.ranAdjunction M) X Y f

example (X : E ⥤ M) (Y : D ⥤ M) :
    (fun c : X ⟶ e.functor.ran.obj Y => ((e.functor.ranAdjunction M).homEquiv X Y).symm c) =
      fun c => ((Functor.whiskeringLeft D E M).obj e.functor).map c ≫
        (e.functor.ranAdjunction M).counit.app Y := by
  funext c
  exact Adjunction.homEquiv_symm_apply (e.functor.ranAdjunction M) X Y c

end OriginalExistingModels

section RaisedOriginalCategories

local instance raisedOriginalObjectCategory : Category.{vD} (ULift.{uD + 1} D) := uliftCategory D
local instance raisedOriginalHomCategory :
    Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))

example [ModelCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M)] [ModelCategory (D ⥤ M)]
    [∀ Y : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M,
      (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm.functor.HasRightKanExtension Y]
    (hWD : weakEquivalences (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) =
      (weakEquivalences M).functorCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D)))
    (hWE : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
    (hCD : cofibrations (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) =
      (cofibrations M).functorCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D)))
    (hCE : cofibrations (D ⥤ M) = (cofibrations M).functorCategory D)
    (hTD : trivialCofibrations (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) =
      (trivialCofibrations M).functorCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D)))
    (hTE : trivialCofibrations (D ⥤ M) = (trivialCofibrations M).functorCategory D) :
    ((ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm.functor.ranAdjunction M).IsQuillenEquivalence :=
  FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
    (ULiftHomULiftCategory.equiv D).symm hWD hWE hCD hCE hTD hTE

end RaisedOriginalCategories

section ActualShapeModels

example (mD : ModelCategory (Discrete PEmpty.{1} ⥤ M)) (mE : ModelCategory (Discrete PEmpty.{1} ⥤ M))
    [∀ Y : Discrete PEmpty.{1} ⥤ M, (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})).functor.HasRightKanExtension Y]
    (hWD : letI : ModelCategory (Discrete PEmpty.{1} ⥤ M) := mD;
      weakEquivalences (Discrete PEmpty.{1} ⥤ M) = (weakEquivalences M).functorCategory (Discrete PEmpty.{1}))
    (hWE : letI : ModelCategory (Discrete PEmpty.{1} ⥤ M) := mE;
      weakEquivalences (Discrete PEmpty.{1} ⥤ M) = (weakEquivalences M).functorCategory (Discrete PEmpty.{1}))
    (hCD : letI : ModelCategory (Discrete PEmpty.{1} ⥤ M) := mD;
      cofibrations (Discrete PEmpty.{1} ⥤ M) = (cofibrations M).functorCategory (Discrete PEmpty.{1}))
    (hCE : letI : ModelCategory (Discrete PEmpty.{1} ⥤ M) := mE;
      cofibrations (Discrete PEmpty.{1} ⥤ M) = (cofibrations M).functorCategory (Discrete PEmpty.{1}))
    (hTD : letI : ModelCategory (Discrete PEmpty.{1} ⥤ M) := mD;
      trivialCofibrations (Discrete PEmpty.{1} ⥤ M) = (trivialCofibrations M).functorCategory (Discrete PEmpty.{1}))
    (hTE : letI : ModelCategory (Discrete PEmpty.{1} ⥤ M) := mE;
      trivialCofibrations (Discrete PEmpty.{1} ⥤ M) = (trivialCofibrations M).functorCategory (Discrete PEmpty.{1}))
    : @Adjunction.IsQuillenEquivalence _ _ _ _ mE mD _ _
      ((CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})).functor.ranAdjunction M) :=
  @FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
    (Discrete PEmpty.{1}) inferInstance (Discrete PEmpty.{1}) inferInstance M inferInstance inferInstance
    mD mE (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})) inferInstance hWD hWE hCD hCE hTD hTE

example (mD : ModelCategory (Discrete ℕ ⥤ M)) (mE : ModelCategory (Discrete ℕ ⥤ M))
    [∀ Y : Discrete ℕ ⥤ M, (CategoryTheory.Equivalence.refl (C := Discrete ℕ)).functor.HasRightKanExtension Y]
    (hWD : letI : ModelCategory (Discrete ℕ ⥤ M) := mD;
      weakEquivalences (Discrete ℕ ⥤ M) = (weakEquivalences M).functorCategory (Discrete ℕ))
    (hWE : letI : ModelCategory (Discrete ℕ ⥤ M) := mE;
      weakEquivalences (Discrete ℕ ⥤ M) = (weakEquivalences M).functorCategory (Discrete ℕ))
    (hCD : letI : ModelCategory (Discrete ℕ ⥤ M) := mD;
      cofibrations (Discrete ℕ ⥤ M) = (cofibrations M).functorCategory (Discrete ℕ))
    (hCE : letI : ModelCategory (Discrete ℕ ⥤ M) := mE;
      cofibrations (Discrete ℕ ⥤ M) = (cofibrations M).functorCategory (Discrete ℕ))
    (hTD : letI : ModelCategory (Discrete ℕ ⥤ M) := mD;
      trivialCofibrations (Discrete ℕ ⥤ M) = (trivialCofibrations M).functorCategory (Discrete ℕ))
    (hTE : letI : ModelCategory (Discrete ℕ ⥤ M) := mE;
      trivialCofibrations (Discrete ℕ ⥤ M) = (trivialCofibrations M).functorCategory (Discrete ℕ))
    : @Adjunction.IsQuillenEquivalence _ _ _ _ mE mD _ _
      ((CategoryTheory.Equivalence.refl (C := Discrete ℕ)).functor.ranAdjunction M) :=
  @FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
    (Discrete ℕ) inferInstance (Discrete ℕ) inferInstance M inferInstance inferInstance
    mD mE (CategoryTheory.Equivalence.refl (C := Discrete ℕ)) inferInstance hWD hWE hCD hCE hTD hTE

example (mD : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M)) (mE : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M))
    [∀ Y : SingleObj (Multiplicative ℕ) ⥤ M, (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))).functor.HasRightKanExtension Y]
    (hWD : letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) := mD;
      weakEquivalences (SingleObj (Multiplicative ℕ) ⥤ M) = (weakEquivalences M).functorCategory (SingleObj (Multiplicative ℕ)))
    (hWE : letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) := mE;
      weakEquivalences (SingleObj (Multiplicative ℕ) ⥤ M) = (weakEquivalences M).functorCategory (SingleObj (Multiplicative ℕ)))
    (hCD : letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) := mD;
      cofibrations (SingleObj (Multiplicative ℕ) ⥤ M) = (cofibrations M).functorCategory (SingleObj (Multiplicative ℕ)))
    (hCE : letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) := mE;
      cofibrations (SingleObj (Multiplicative ℕ) ⥤ M) = (cofibrations M).functorCategory (SingleObj (Multiplicative ℕ)))
    (hTD : letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) := mD;
      trivialCofibrations (SingleObj (Multiplicative ℕ) ⥤ M) = (trivialCofibrations M).functorCategory (SingleObj (Multiplicative ℕ)))
    (hTE : letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) := mE;
      trivialCofibrations (SingleObj (Multiplicative ℕ) ⥤ M) = (trivialCofibrations M).functorCategory (SingleObj (Multiplicative ℕ)))
    : @Adjunction.IsQuillenEquivalence _ _ _ _ mE mD _ _
      ((CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))).functor.ranAdjunction M) :=
  @FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
    (SingleObj (Multiplicative ℕ)) inferInstance (SingleObj (Multiplicative ℕ)) inferInstance M inferInstance inferInstance
    mD mE (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))) inferInstance hWD hWE hCD hCE hTD hTE

example (mD : ModelCategory (Discrete Bool ⥤ M)) (mE : ModelCategory (Discrete Bool ⥤ M))
    [∀ Y : Discrete Bool ⥤ M, (Discrete.equivalence (Equiv.swap false true)).functor.HasRightKanExtension Y]
    (hWD : letI : ModelCategory (Discrete Bool ⥤ M) := mD;
      weakEquivalences (Discrete Bool ⥤ M) = (weakEquivalences M).functorCategory (Discrete Bool))
    (hWE : letI : ModelCategory (Discrete Bool ⥤ M) := mE;
      weakEquivalences (Discrete Bool ⥤ M) = (weakEquivalences M).functorCategory (Discrete Bool))
    (hCD : letI : ModelCategory (Discrete Bool ⥤ M) := mD;
      cofibrations (Discrete Bool ⥤ M) = (cofibrations M).functorCategory (Discrete Bool))
    (hCE : letI : ModelCategory (Discrete Bool ⥤ M) := mE;
      cofibrations (Discrete Bool ⥤ M) = (cofibrations M).functorCategory (Discrete Bool))
    (hTD : letI : ModelCategory (Discrete Bool ⥤ M) := mD;
      trivialCofibrations (Discrete Bool ⥤ M) = (trivialCofibrations M).functorCategory (Discrete Bool))
    (hTE : letI : ModelCategory (Discrete Bool ⥤ M) := mE;
      trivialCofibrations (Discrete Bool ⥤ M) = (trivialCofibrations M).functorCategory (Discrete Bool))
    : @Adjunction.IsQuillenEquivalence _ _ _ _ mE mD _ _
      ((Discrete.equivalence (Equiv.swap false true)).functor.ranAdjunction M) :=
  @FunctorInjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
    (Discrete Bool) inferInstance (Discrete Bool) inferInstance M inferInstance inferInstance
    mD mE (Discrete.equivalence (Equiv.swap false true)) inferInstance hWD hWE hCD hCE hTD hTE

end ActualShapeModels

end MathlibExtTest.FunctorInjectiveIndexQuillenEquivalence
