/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.KanExtensions
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Whole native Ran comma, cofree and existing-model Quillen clients

The cone projections are those of the original StructuredArrow limits.
Index maps use actual precomposition of their original comma labels.
Existing diagram models keep their real Cof and TC hypotheses.
-/

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM
open CategoryTheory Functor Limits HomotopicalAlgebra

namespace MathlibExtTest.FunctorInjectiveKanExtensions

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M]

section NativeCommaFunctions

variable (u : D ⥤ E) [∀ Y : D ⥤ M, u.HasRightKanExtension Y]

example :
    (fun (X : E ⥤ M) (Y : D ⥤ M) (f : u ⋙ X ⟶ Y) =>
      (u.ranAdjunction M).homEquiv X Y f) =
    (fun X _Y f => (u.ranAdjunction M).unit.app X ≫ u.ran.map f) := by
  funext X Y f
  exact Adjunction.homEquiv_apply (u.ranAdjunction M) X Y f

example :
    (fun (X : E ⥤ M) (Y : D ⥤ M) (c : X ⟶ u.ran.obj Y) =>
      ((u.ranAdjunction M).homEquiv X Y).symm c) =
    (fun _X Y c => ((Functor.whiskeringLeft D E M).obj u).map c ≫
      (u.ranAdjunction M).counit.app Y) := by
  funext X Y c
  exact Adjunction.homEquiv_symm_apply (u.ranAdjunction M) X Y c

variable [∀ Y : D ⥤ M, u.HasPointwiseRightKanExtension Y]

example :
    (fun (Y : D ⥤ M) (t : E) (j : StructuredArrow t u) =>
      (u.ranObjObjIsoLimit Y t).hom ≫ limit.π (StructuredArrow.proj t u ⋙ Y) j) =
    (fun (Y : D ⥤ M) (t : E) (j : StructuredArrow t u) => (u.ran.obj Y).map j.hom ≫
      ((u.ranAdjunction M).counit.app Y).app j.right) := by
  funext Y t j
  rw [Functor.ranAdjunction_counit]
  exact Functor.ranObjObjIsoLimit_hom_π u Y t j

example :
    (fun (Y : D ⥤ M) (t : E) (j : StructuredArrow t u) =>
      (u.ranObjObjIsoLimit Y t).inv ≫ (u.ran.obj Y).map j.hom ≫
        ((u.ranAdjunction M).counit.app Y).app j.right) =
    (fun Y t j => limit.π (StructuredArrow.proj t u ⋙ Y) j) := by
  funext Y t j
  rw [Functor.ranAdjunction_counit]
  exact Functor.ranObjObjIsoLimit_inv_π u Y t j

/-- A fixed expected map joins the native Ran action to every original comma projection. -/
private theorem nativeIndexProjectionMap (Y : D ⥤ M) {t t' : E} (a : t ⟶ t')
    (j : StructuredArrow t' u) :
    (u.ran.obj Y).map a ≫ (u.ranObjObjIsoLimit Y t').hom ≫
        limit.π (StructuredArrow.proj t' u ⋙ Y) j =
      (u.ranObjObjIsoLimit Y t).hom ≫
        limit.π (StructuredArrow.proj t u ⋙ Y) ((StructuredArrow.map a).obj j) := by
  rw [Functor.ranObjObjIsoLimit_hom_π, Functor.ranObjObjIsoLimit_hom_π]
  change (u.ran.obj Y).map a ≫ (u.ran.obj Y).map j.hom ≫
      (u.ranCounit.app Y).app j.right =
    (u.ran.obj Y).map (a ≫ j.hom) ≫ (u.ranCounit.app Y).app j.right
  rw [Functor.map_comp, Category.assoc]

/-- A fixed expected coefficient map retains the original counit and every projection label. -/
private theorem nativeCoefficientProjectionMap {Y Y' : D ⥤ M} (b : Y ⟶ Y') (t : E)
    (j : StructuredArrow t u) :
    (u.ran.map b).app t ≫ (u.ranObjObjIsoLimit Y' t).hom ≫
        limit.π (StructuredArrow.proj t u ⋙ Y') j =
      (u.ranObjObjIsoLimit Y t).hom ≫
        limit.π (StructuredArrow.proj t u ⋙ Y) j ≫ b.app j.right := by
  rw [Functor.ranObjObjIsoLimit_hom_π, ← Category.assoc,
    ← (u.ran.map b).naturality j.hom, Category.assoc,
    Functor.ranObjObjIsoLimit_hom_π_assoc]
  exact congrArg (fun f => (u.ran.obj Y).map j.hom ≫ f)
    (congr_app (u.ranCounit.naturality b) j.right)

example :
    (fun (Y : D ⥤ M) (t t' : E) (a : t ⟶ t') (j : StructuredArrow t' u) =>
      (u.ran.obj Y).map a ≫ (u.ranObjObjIsoLimit Y t').hom ≫
        limit.π (StructuredArrow.proj t' u ⋙ Y) j) =
    (fun Y t _t' a j => (u.ranObjObjIsoLimit Y t).hom ≫
      limit.π (StructuredArrow.proj t u ⋙ Y) ((StructuredArrow.map a).obj j)) := by
  funext Y t t' a j
  exact nativeIndexProjectionMap u Y a j

example :
    (fun (Y : D ⥤ M) (t t' : E) (a : t ⟶ t') (j : StructuredArrow t' u) =>
      (u.ranObjObjIsoLimit Y t).inv ≫ (u.ran.obj Y).map a ≫
        (u.ranObjObjIsoLimit Y t').hom ≫ limit.π (StructuredArrow.proj t' u ⋙ Y) j) =
    (fun Y t _t' a j => limit.π (StructuredArrow.proj t u ⋙ Y)
      ((StructuredArrow.map a).obj j)) := by
  funext Y t t' a j
  have h := congrArg (fun f => (u.ranObjObjIsoLimit Y t).inv ≫ f)
    (nativeIndexProjectionMap u Y a j)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

example :
    (fun (Y Y' : D ⥤ M) (b : Y ⟶ Y') (t : E) (j : StructuredArrow t u) =>
      (u.ran.map b).app t ≫ (u.ranObjObjIsoLimit Y' t).hom ≫
        limit.π (StructuredArrow.proj t u ⋙ Y') j) =
    (fun Y _Y' b t j => (u.ranObjObjIsoLimit Y t).hom ≫
      limit.π (StructuredArrow.proj t u ⋙ Y) j ≫ b.app j.right) := by
  funext Y Y' b t j
  exact nativeCoefficientProjectionMap u b t j

example :
    (fun (Y Y' : D ⥤ M) (b : Y ⟶ Y') (t : E) (j : StructuredArrow t u) =>
      (u.ranObjObjIsoLimit Y t).inv ≫ (u.ran.map b).app t ≫
        (u.ranObjObjIsoLimit Y' t).hom ≫ limit.π (StructuredArrow.proj t u ⋙ Y') j) =
    (fun Y _Y' b t j => limit.π (StructuredArrow.proj t u ⋙ Y) j ≫ b.app j.right) := by
  funext Y Y' b t j
  have h := congrArg (fun f => (u.ranObjObjIsoLimit Y t).inv ≫ f)
    (nativeCoefficientProjectionMap u b t j)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

example (Y : D ⥤ M) (t : E) :
    (u.ran.obj Y).map (𝟙 t) = 𝟙 ((u.ran.obj Y).obj t) := (u.ran.obj Y).map_id t

example (Y : D ⥤ M) {t t' t'' : E} (a : t ⟶ t') (b : t' ⟶ t'') :
    (u.ran.obj Y).map (a ≫ b) = (u.ran.obj Y).map a ≫ (u.ran.obj Y).map b :=
  (u.ran.obj Y).map_comp a b

end NativeCommaFunctions

section NativeCofreeCommaActions

variable (d : E)
  [∀ Y : Discrete PUnit.{1} ⥤ M,
    ((Functor.const (Discrete PUnit.{1}) (C := E)).obj d).HasRightKanExtension Y]
  [∀ Y : Discrete PUnit.{1} ⥤ M,
    ((Functor.const (Discrete PUnit.{1}) (C := E)).obj d).HasPointwiseRightKanExtension Y]

example (A : M) (t : E) :
    (fun j : StructuredArrow t ((Functor.const (Discrete PUnit.{1}) (C := E)).obj d) =>
      (StructuredArrow.proj t ((Functor.const (Discrete PUnit.{1}) (C := E)).obj d) ⋙
        (Functor.const (Discrete PUnit.{1}) (C := M)).obj A).obj j) =
      fun _ => A := rfl

example (A : M) :
    let u := (Functor.const (Discrete PUnit.{1}) (C := E)).obj d
    let Y := (Functor.const (Discrete PUnit.{1}) (C := M)).obj A
    (fun (t : E) (b : t ⟶ d) => (u.ranObjObjIsoLimit Y t).hom ≫
      limit.π (StructuredArrow.proj t u ⋙ Y) (StructuredArrow.mk (Y := Discrete.mk PUnit.unit) b)) =
    (fun _t b => (u.ran.obj Y).map b ≫ ((u.ranAdjunction M).counit.app Y).app (.mk PUnit.unit)) := by
  dsimp only
  funext t b
  rw [Functor.ranAdjunction_counit]
  exact Functor.ranObjObjIsoLimit_hom_π
    ((Functor.const (Discrete PUnit.{1}) (C := E)).obj d)
    ((Functor.const (Discrete PUnit.{1}) (C := M)).obj A) t
    (StructuredArrow.mk (T := (Functor.const (Discrete PUnit.{1}) (C := E)).obj d)
      (Y := Discrete.mk PUnit.unit) b)

example (A : M) :
    let u := (Functor.const (Discrete PUnit.{1}) (C := E)).obj d
    let Y := (Functor.const (Discrete PUnit.{1}) (C := M)).obj A
    (fun (t t' : E) (a : t ⟶ t') (b : t' ⟶ d) =>
      (u.ran.obj Y).map a ≫ (u.ranObjObjIsoLimit Y t').hom ≫
        limit.π (StructuredArrow.proj t' u ⋙ Y) (StructuredArrow.mk (Y := Discrete.mk PUnit.unit) b)) =
    (fun t _t' a b => (u.ranObjObjIsoLimit Y t).hom ≫
      limit.π (StructuredArrow.proj t u ⋙ Y) (StructuredArrow.mk (Y := Discrete.mk PUnit.unit) (a ≫ b))) := by
  dsimp only
  funext t t' a b
  simpa only [StructuredArrow.map_mk] using
    nativeIndexProjectionMap ((Functor.const (Discrete PUnit.{1}) (C := E)).obj d)
      ((Functor.const (Discrete PUnit.{1}) (C := M)).obj A) a (StructuredArrow.mk (Y := Discrete.mk PUnit.unit) b)

example {A B : M} (b : A ⟶ B) :
    let u := (Functor.const (Discrete PUnit.{1}) (C := E)).obj d
    let Y := (Functor.const (Discrete PUnit.{1}) (C := M)).obj A
    let Y' := (Functor.const (Discrete PUnit.{1}) (C := M)).obj B
    (fun (t : E) (a : t ⟶ d) =>
      (u.ran.map ((Functor.const (Discrete PUnit.{1}) (C := M)).map b)).app t ≫
        (u.ranObjObjIsoLimit Y' t).hom ≫
          limit.π (StructuredArrow.proj t u ⋙ Y') (StructuredArrow.mk (Y := Discrete.mk PUnit.unit) a)) =
    (fun t a => (u.ranObjObjIsoLimit Y t).hom ≫
      limit.π (StructuredArrow.proj t u ⋙ Y) (StructuredArrow.mk (Y := Discrete.mk PUnit.unit) a) ≫ b) := by
  dsimp only
  funext t a
  exact nativeCoefficientProjectionMap ((Functor.const (Discrete PUnit.{1}) (C := E)).obj d)
    ((Functor.const (Discrete PUnit.{1}) (C := M)).map b) t (StructuredArrow.mk (Y := Discrete.mk PUnit.unit) a)

end NativeCofreeCommaActions

section GenuineCommaDictionaries

example (u : D ⥤ E)
    [∀ Y : D ⥤ M, ∀ t : E, HasLimit (StructuredArrow.proj t u ⋙ Y)] :
    ∀ Y : D ⥤ M, u.HasRightKanExtension Y := fun _ => inferInstance

end GenuineCommaDictionaries

section ExistingModels

variable [ModelCategory M] [ModelCategory (D ⥤ M)] [ModelCategory (E ⥤ M)]
  (u : D ⥤ E) [∀ Y : D ⥤ M, u.HasRightKanExtension Y]
  (hCD : cofibrations (D ⥤ M) = (cofibrations M).functorCategory D)
  (hCE : cofibrations (E ⥤ M) = (cofibrations M).functorCategory E)
  (hTD : trivialCofibrations (D ⥤ M) = (trivialCofibrations M).functorCategory D)
  (hTE : trivialCofibrations (E ⥤ M) = (trivialCofibrations M).functorCategory E)

example : (u.ranAdjunction M).IsQuillenAdjunction :=
  FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes u hCD hCE hTD hTE

example :
    PreservesCofibrations ((Functor.whiskeringLeft D E M).obj u) ∧
      PreservesTrivialCofibrations ((Functor.whiskeringLeft D E M).obj u) :=
  FunctorInjective.KanExtensions.preserves_left_classes_of_eqs hCD hCE hTD hTE u

example {X X' : E ⥤ M} (f : X ⟶ X') (hf : cofibrations (E ⥤ M) f) :
    cofibrations (D ⥤ M) (((Functor.whiskeringLeft D E M).obj u).map f) :=
  (FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes
    u hCD hCE hTD hTE).preservesCofibrations f hf

example {X X' : E ⥤ M} (f : X ⟶ X') (hf : trivialCofibrations (E ⥤ M) f) :
    trivialCofibrations (D ⥤ M) (((Functor.whiskeringLeft D E M).obj u).map f) :=
  (FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes
    u hCD hCE hTD hTE).preservesTrivialCofibrations f hf

example {Y Y' : D ⥤ M} (f : Y ⟶ Y') (hf : fibrations (D ⥤ M) f) :
    fibrations (E ⥤ M) (u.ran.map f) := by
  let _ : (u.ranAdjunction M).IsQuillenAdjunction :=
    FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes u hCD hCE hTD hTE
  exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := u.ranAdjunction M) f hf

example {Y Y' : D ⥤ M} (f : Y ⟶ Y') (hf : trivialFibrations (D ⥤ M) f) :
    trivialFibrations (E ⥤ M) (u.ran.map f) := by
  let _ : (u.ranAdjunction M).IsQuillenAdjunction :=
    FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes u hCD hCE hTD hTE
  exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := u.ranAdjunction M) f hf

example (X : E ⥤ M) (hX : IsCofibrant X) : IsCofibrant (u ⋙ X) := by
  let _ : (u.ranAdjunction M).IsQuillenAdjunction :=
    FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes u hCD hCE hTD hTE
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := u.ranAdjunction M) hX

example (Y : D ⥤ M) (hY : IsFibrant Y) : IsFibrant (u.ran.obj Y) := by
  let _ : (u.ranAdjunction M).IsQuillenAdjunction :=
    FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes u hCD hCE hTD hTE
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := u.ranAdjunction M) hY

end ExistingModels

section ExistingModelsFromActualCommaLimits

example [ModelCategory M] [ModelCategory (D ⥤ M)] [ModelCategory (E ⥤ M)] (u : D ⥤ E)
    [∀ Y : D ⥤ M, ∀ t : E, HasLimit (StructuredArrow.proj t u ⋙ Y)]
    (hCD : cofibrations (D ⥤ M) = (cofibrations M).functorCategory D)
    (hCE : cofibrations (E ⥤ M) = (cofibrations M).functorCategory E)
    (hTD : trivialCofibrations (D ⥤ M) = (trivialCofibrations M).functorCategory D)
    (hTE : trivialCofibrations (E ⥤ M) = (trivialCofibrations M).functorCategory E) :
    letI : ∀ Y : D ⥤ M, u.HasRightKanExtension Y := fun _ => inferInstance
    (u.ranAdjunction M).IsQuillenAdjunction := by
  let _ : ∀ Y : D ⥤ M, u.HasRightKanExtension Y := fun _ => inferInstance
  exact FunctorInjective.KanExtensions.isQuillen_of_pointwise_left_classes u hCD hCE hTD hTE

end ExistingModelsFromActualCommaLimits

set_option pp.universes true
set_option pp.all true
set_option pp.proofs true

#check @nativeIndexProjectionMap
#print axioms nativeIndexProjectionMap
#check @nativeCoefficientProjectionMap
#print axioms nativeCoefficientProjectionMap

run_cmd do
  let indexName ← Lean.Elab.Command.liftTermElabM do
    let value ← Lean.Elab.Term.elabTerm (← `(@nativeIndexProjectionMap)) none
    pure value.getAppFn.constName!
  let coefficientName ← Lean.Elab.Command.liftTermElabM do
    let value ← Lean.Elab.Term.elabTerm (← `(@nativeCoefficientProjectionMap)) none
    pure value.getAppFn.constName!
  Lean.logInfo m!"RAN_COMMA_OWNER_PRIVATE_NAME {indexName}"
  Lean.logInfo m!"RAN_COMMA_OWNER_PRIVATE_NAME {coefficientName}"

end MathlibExtTest.FunctorInjectiveKanExtensions
