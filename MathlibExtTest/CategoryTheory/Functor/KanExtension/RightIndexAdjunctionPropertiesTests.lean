/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import all MathlibExt.CategoryTheory.Functor.KanExtension.RightIndexAdjunctionProperties
import all Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Whole original native Ran and inverse-index contracts

Both Hom functions are the native ones. The comparison is the standard
right-adjoint uniqueness Iso with the supplied e's inverse precomposition.
The coefficient category is arbitrary until the scalar model tests.
-/

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM
open CategoryTheory Functor MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.FunctorRightIndexAdjunctionProperties

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M]
  (e : D ≌ E) [∀ F : D ⥤ M, e.functor.HasRightKanExtension F]

section OriginalProperty

variable (P : MorphismProperty M) [P.RespectsIso]

example {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    (∀ d : D, P (f.app d)) ↔
      ∀ t : E, P (((e.functor.ranAdjunction M).homEquiv X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff e P f

example {X : E ⥤ M} {Y : D ⥤ M} (c : X ⟶ e.functor.ran.obj Y) :
    (∀ t : E, P (c.app t)) ↔
      ∀ d : D, P ((((e.functor.ranAdjunction M).homEquiv X Y).symm c).app d) :=
  RightIndexAdjunctionProperties.inverse_property_iff e P c

example {X X' : E ⥤ M} (c : X ⟶ X') :
    P.functorCategory E c ↔
      (P.functorCategory D)
        (((Functor.whiskeringLeft D E M).obj e.functor).map c) := by
  change P.functorCategory E c ↔
    ((P.functorCategory D).inverseImage (e.congrLeft (E := M)).inverse) c
  rw [functorCategory_inverseImage_congrLeft_inverse e P]

end OriginalProperty

section WholeNativeFunctions

example :
    (fun (X : E ⥤ M) (Y : D ⥤ M) (f : e.functor ⋙ X ⟶ Y) =>
      (e.functor.ranAdjunction M).homEquiv X Y f) =
    (fun X _Y f => (e.functor.ranAdjunction M).unit.app X ≫ e.functor.ran.map f) := by
  funext X Y f
  exact Adjunction.homEquiv_apply (e.functor.ranAdjunction M) X Y f

example :
    (fun (X : E ⥤ M) (Y : D ⥤ M) (c : X ⟶ e.functor.ran.obj Y) =>
      ((e.functor.ranAdjunction M).homEquiv X Y).symm c) =
    (fun _X Y c => ((Functor.whiskeringLeft D E M).obj e.functor).map c ≫
      (e.functor.ranAdjunction M).counit.app Y) := by
  funext X Y c
  exact Adjunction.homEquiv_symm_apply (e.functor.ranAdjunction M) X Y c

example :
    (fun (X : E ⥤ M) (Y : D ⥤ M) (f : e.functor ⋙ X ⟶ Y) (t : E) =>
      ((e.functor.ranAdjunction M).homEquiv X Y f).app t) =
    (fun X _Y f t => ((e.functor.ranAdjunction M).unit.app X).app t ≫
      (e.functor.ran.map f).app t) := by
  funext X Y f t
  rw [Adjunction.homEquiv_apply]
  rfl

example :
    (fun (X : E ⥤ M) (Y : D ⥤ M) (c : X ⟶ e.functor.ran.obj Y) (d : D) =>
      (((e.functor.ranAdjunction M).homEquiv X Y).symm c).app d) =
    (fun _X Y c d => c.app (e.functor.obj d) ≫
      ((e.functor.ranAdjunction M).counit.app Y).app d) := by
  funext X Y c d
  rw [Adjunction.homEquiv_symm_apply]
  rfl

example (X : E ⥤ M) (Y : D ⥤ M) :
    (fun f : e.functor ⋙ X ⟶ Y => (e.functor.ranAdjunction M).homEquiv X Y f) =
      fun f => liftOfIsRightKanExtension (e.functor.ran.obj Y)
        (e.functor.ranCounit.app Y) X f := by
  funext f
  apply ((e.functor.ranAdjunction M).homEquiv X Y).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply, Functor.ranAdjunction_counit]
  exact (Functor.liftOfIsRightKanExtension_fac (e.functor.ran.obj Y)
    (e.functor.ranCounit.app Y) X f).symm

example (Y : D ⥤ M) :
    (e.functor.ranAdjunction M).counit.app Y = e.functor.ranCounit.app Y := by
  rw [Functor.ranAdjunction_counit]

example {X' X : E ⥤ M} {Y : D ⥤ M} (a : X' ⟶ X) (f : e.functor ⋙ X ⟶ Y) :
    (e.functor.ranAdjunction M).homEquiv X' Y
        (((Functor.whiskeringLeft D E M).obj e.functor).map a ≫ f) =
      a ≫ (e.functor.ranAdjunction M).homEquiv X Y f :=
  (e.functor.ranAdjunction M).homEquiv_naturality_left a f

example {X : E ⥤ M} {Y Y' : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) (a : Y ⟶ Y') :
    (e.functor.ranAdjunction M).homEquiv X Y' (f ≫ a) =
      (e.functor.ranAdjunction M).homEquiv X Y f ≫ e.functor.ran.map a :=
  (e.functor.ranAdjunction M).homEquiv_naturality_right f a

example {X' X : E ⥤ M} {Y : D ⥤ M} (a : X' ⟶ X) (c : X ⟶ e.functor.ran.obj Y) :
    ((e.functor.ranAdjunction M).homEquiv X' Y).symm (a ≫ c) =
      ((Functor.whiskeringLeft D E M).obj e.functor).map a ≫
        ((e.functor.ranAdjunction M).homEquiv X Y).symm c :=
  (e.functor.ranAdjunction M).homEquiv_naturality_left_symm a c

example {X : E ⥤ M} {Y Y' : D ⥤ M} (c : X ⟶ e.functor.ran.obj Y) (a : Y ⟶ Y') :
    ((e.functor.ranAdjunction M).homEquiv X Y').symm (c ≫ e.functor.ran.map a) =
      ((e.functor.ranAdjunction M).homEquiv X Y).symm c ≫ a :=
  (e.functor.ranAdjunction M).homEquiv_naturality_right_symm c a

example (X : E ⥤ M) : IsIso ((e.functor.ranAdjunction M).unit.app X) := inferInstance
example (Y : D ⥤ M) : IsIso ((e.functor.ranAdjunction M).counit.app Y) := inferInstance

example (X : E ⥤ M) (t : E) :
    IsIso (((e.functor.ranAdjunction M).unit.app X).app t) := inferInstance

example (Y : D ⥤ M) (d : D) :
    IsIso (((e.functor.ranAdjunction M).counit.app Y).app d) := inferInstance

end WholeNativeFunctions

section OriginalIndexComparison

/-- The full inverse-function client joins the two original right-adjoint transposes. -/
theorem nativeInverseIndexComparison {X : E ⥤ M} {Y : D ⥤ M}
    (c : X ⟶ e.functor.ran.obj Y) :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    ((e.functor.ranAdjunction M).homEquiv X Y).symm c =
      ((e.congrLeft (E := M)).symm.toAdjunction.homEquiv X Y).symm (c ≫ i.hom.app Y) := by
  let a := e.functor.ranAdjunction M
  let b := (e.congrLeft (E := M)).symm.toAdjunction
  let i := Adjunction.rightAdjointUniq a b
  change (a.homEquiv X Y).symm c = (b.homEquiv X Y).symm (c ≫ i.hom.app Y)
  rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply,
    Functor.map_comp, Category.assoc, Adjunction.rightAdjointUniq_hom_app_counit]
  rfl

/-- The full forward-function client retains the same actual right-adjoint comparison. -/
theorem nativeForwardIndexComparison {X : E ⥤ M} {Y : D ⥤ M}
    (f : e.functor ⋙ X ⟶ Y) :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    (e.functor.ranAdjunction M).homEquiv X Y f =
      (e.congrLeft (E := M)).symm.toAdjunction.homEquiv X Y f ≫ i.inv.app Y := by
  let a := e.functor.ranAdjunction M
  let b := (e.congrLeft (E := M)).symm.toAdjunction
  let i := Adjunction.rightAdjointUniq a b
  change a.homEquiv X Y f = b.homEquiv X Y f ≫ i.inv.app Y
  apply (a.homEquiv X Y).symm.injective
  rw [Equiv.symm_apply_apply]
  have h := nativeInverseIndexComparison e (b.homEquiv X Y f ≫ i.inv.app Y)
  change (a.homEquiv X Y).symm (b.homEquiv X Y f ≫ i.inv.app Y) =
    (b.homEquiv X Y).symm ((b.homEquiv X Y f ≫ i.inv.app Y) ≫ i.hom.app Y) at h
  rw [h]
  simp only [Category.assoc, ← NatTrans.comp_app, i.inv_hom_id,
    NatTrans.id_app, Category.comp_id, Equiv.symm_apply_apply]

example :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    (fun (X : E ⥤ M) (Y : D ⥤ M) (f : e.functor ⋙ X ⟶ Y) =>
      (e.functor.ranAdjunction M).homEquiv X Y f) =
    (fun X Y f => (e.congrLeft (E := M)).symm.toAdjunction.homEquiv X Y f ≫ i.inv.app Y) := by
  dsimp only
  funext X Y f
  exact nativeForwardIndexComparison e f

example :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    (fun (X : E ⥤ M) (Y : D ⥤ M) (c : X ⟶ e.functor.ran.obj Y) =>
      ((e.functor.ranAdjunction M).homEquiv X Y).symm c) =
    (fun X Y c => ((e.congrLeft (E := M)).symm.toAdjunction.homEquiv X Y).symm
      (c ≫ i.hom.app Y)) := by
  dsimp only
  funext X Y c
  exact nativeInverseIndexComparison e c

example :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    (fun (X : E ⥤ M) (Y : D ⥤ M) (f : e.functor ⋙ X ⟶ Y) (t : E) =>
      ((e.functor.ranAdjunction M).homEquiv X Y f).app t) =
    (fun X Y f t => (X.map (e.counitInv.app t) ≫ f.app (e.inverse.obj t)) ≫
      (i.inv.app Y).app t) := by
  dsimp only
  funext X Y f t
  rw [nativeForwardIndexComparison e f, Adjunction.homEquiv_apply]
  simp [Equivalence.congrLeft, Equivalence.toAdjunction]

example :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    (fun (X : E ⥤ M) (Y : D ⥤ M) (c : X ⟶ e.functor.ran.obj Y) (d : D) =>
      (((e.functor.ranAdjunction M).homEquiv X Y).symm c).app d) =
    (fun _X Y c d => c.app (e.functor.obj d) ≫
      (i.hom.app Y).app (e.functor.obj d) ≫ Y.map (e.unitInv.app d)) := by
  dsimp only
  funext X Y c d
  rw [nativeInverseIndexComparison e c, Adjunction.homEquiv_symm_apply]
  simp [Equivalence.congrLeft, Equivalence.toAdjunction]

example :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    (fun (X : E ⥤ M) (t : E) => ((e.functor.ranAdjunction M).unit.app X).app t ≫
      (i.hom.app (e.functor ⋙ X)).app t) =
    (fun X t => X.map (e.counitInv.app t)) := by
  dsimp only
  funext X t
  have h := congr_app (Adjunction.unit_rightAdjointUniq_hom_app
    (e.functor.ranAdjunction M) (e.congrLeft (E := M)).symm.toAdjunction X) t
  simpa [Equivalence.congrLeft, Equivalence.toAdjunction, Equivalence.symm] using h

example :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    (fun (Y : D ⥤ M) (d : D) =>
      (i.hom.app Y).app (e.functor.obj d) ≫ Y.map (e.unitInv.app d)) =
    (fun Y d => ((e.functor.ranAdjunction M).counit.app Y).app d) := by
  dsimp only
  funext Y d
  have h := congr_app (Adjunction.rightAdjointUniq_hom_app_counit
    (e.functor.ranAdjunction M) (e.congrLeft (E := M)).symm.toAdjunction Y) d
  simpa [Equivalence.congrLeft, Equivalence.toAdjunction, Equivalence.symm] using h

example :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    (fun (X : E ⥤ M) (t : E) => X.map (e.counitInv.app t) ≫
      (i.inv.app (e.functor ⋙ X)).app t) =
    (fun X t => ((e.functor.ranAdjunction M).unit.app X).app t) := by
  dsimp only
  funext X t
  have h := Adjunction.unit_rightAdjointUniq_hom_app
    (e.congrLeft (E := M)).symm.toAdjunction (e.functor.ranAdjunction M) X
  rw [← Adjunction.rightAdjointUniq_inv_app
    (e.functor.ranAdjunction M) (e.congrLeft (E := M)).symm.toAdjunction
    ((e.congrLeft (E := M)).symm.functor.obj X)] at h
  simpa [Equivalence.congrLeft, Equivalence.toAdjunction, Equivalence.symm] using congr_app h t

example :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    (fun (Y : D ⥤ M) (d : D) => (i.inv.app Y).app (e.functor.obj d) ≫
      ((e.functor.ranAdjunction M).counit.app Y).app d) =
    (fun Y d => Y.map (e.unitInv.app d)) := by
  dsimp only
  funext Y d
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (e.congrLeft (E := M)).symm.toAdjunction (e.functor.ranAdjunction M) Y
  rw [← Adjunction.rightAdjointUniq_inv_app
    (e.functor.ranAdjunction M) (e.congrLeft (E := M)).symm.toAdjunction Y] at h
  simpa [Equivalence.congrLeft, Equivalence.toAdjunction, Equivalence.symm] using congr_app h d

example {Y Y' : D ⥤ M} (a : Y ⟶ Y') :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    e.functor.ran.map a ≫ i.hom.app Y' =
      i.hom.app Y ≫ ((Functor.whiskeringLeft E D M).obj e.inverse).map a :=
  (Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
    (e.congrLeft (E := M)).symm.toAdjunction).hom.naturality a

example {Y Y' : D ⥤ M} (a : Y ⟶ Y') :
    let i := Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
      (e.congrLeft (E := M)).symm.toAdjunction
    ((Functor.whiskeringLeft E D M).obj e.inverse).map a ≫ i.inv.app Y' =
      i.inv.app Y ≫ e.functor.ran.map a :=
  (Adjunction.rightAdjointUniq (e.functor.ranAdjunction M)
    (e.congrLeft (E := M)).symm.toAdjunction).inv.naturality a

end OriginalIndexComparison

section OriginalUnitCounitMaps

example {X X' : E ⥤ M} (a : X ⟶ X') :
    a ≫ (e.functor.ranAdjunction M).unit.app X' =
      (e.functor.ranAdjunction M).unit.app X ≫
        e.functor.ran.map (((Functor.whiskeringLeft D E M).obj e.functor).map a) :=
  (e.functor.ranAdjunction M).unit.naturality a

example {Y Y' : D ⥤ M} (a : Y ⟶ Y') :
    ((Functor.whiskeringLeft D E M).obj e.functor).map (e.functor.ran.map a) ≫
        (e.functor.ranAdjunction M).counit.app Y' =
      (e.functor.ranAdjunction M).counit.app Y ≫ a :=
  (e.functor.ranAdjunction M).counit.naturality a

example (X : E ⥤ M) {t t' : E} (a : t ⟶ t') :
    X.map a ≫ ((e.functor.ranAdjunction M).unit.app X).app t' =
      ((e.functor.ranAdjunction M).unit.app X).app t ≫
        (e.functor.ran.obj (e.functor ⋙ X)).map a :=
  ((e.functor.ranAdjunction M).unit.app X).naturality a

example (Y : D ⥤ M) {d d' : D} (a : d ⟶ d') :
    (e.functor.ran.obj Y).map (e.functor.map a) ≫
        ((e.functor.ranAdjunction M).counit.app Y).app d' =
      ((e.functor.ranAdjunction M).counit.app Y).app d ≫ Y.map a :=
  ((e.functor.ranAdjunction M).counit.app Y).naturality a

example (X : E ⥤ M) :
    ((e.functor.ranAdjunction M).homEquiv X (e.functor ⋙ X)).symm
      ((e.functor.ranAdjunction M).unit.app X) = 𝟙 _ :=
  (e.functor.ranAdjunction M).homEquiv_symm_unit X

example (X : E ⥤ M) :
    ((Functor.whiskeringLeft D E M).obj e.functor).map
        ((e.functor.ranAdjunction M).unit.app X) ≫
      (e.functor.ranAdjunction M).counit.app (e.functor ⋙ X) = 𝟙 _ :=
  (e.functor.ranAdjunction M).left_triangle_components X

example (Y : D ⥤ M) :
    (e.functor.ranAdjunction M).unit.app (e.functor.ran.obj Y) ≫
      e.functor.ran.map ((e.functor.ranAdjunction M).counit.app Y) = 𝟙 _ :=
  (e.functor.ranAdjunction M).right_triangle_components Y

end OriginalUnitCounitMaps

section ScalarComponentProperties

example {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    (∀ d : D, IsIso (f.app d)) ↔
      ∀ t : E, IsIso (((e.functor.ranAdjunction M).homEquiv X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff e (isomorphisms M) f

example {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    (∀ d : D, Mono (f.app d)) ↔
      ∀ t : E, Mono (((e.functor.ranAdjunction M).homEquiv X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff e (monomorphisms M) f

example {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    (∀ d : D, Epi (f.app d)) ↔
      ∀ t : E, Epi (((e.functor.ranAdjunction M).homEquiv X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff e (epimorphisms M) f

variable [ModelCategory M]

example {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    (∀ d : D, weakEquivalences M (f.app d)) ↔
      ∀ t : E, weakEquivalences M (((e.functor.ranAdjunction M).homEquiv X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff e (weakEquivalences M) f

example {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    (∀ d : D, cofibrations M (f.app d)) ↔
      ∀ t : E, cofibrations M (((e.functor.ranAdjunction M).homEquiv X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff e (cofibrations M) f

example {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    (∀ d : D, fibrations M (f.app d)) ↔
      ∀ t : E, fibrations M (((e.functor.ranAdjunction M).homEquiv X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff e (fibrations M) f

example {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    (∀ d : D, trivialCofibrations M (f.app d)) ↔
      ∀ t : E, trivialCofibrations M (((e.functor.ranAdjunction M).homEquiv X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff e (trivialCofibrations M) f

example {X : E ⥤ M} {Y : D ⥤ M} (f : e.functor ⋙ X ⟶ Y) :
    (∀ d : D, trivialFibrations M (f.app d)) ↔
      ∀ t : E, trivialFibrations M (((e.functor.ranAdjunction M).homEquiv X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff e (trivialFibrations M) f

end ScalarComponentProperties

section ActualIndices

variable (P : MorphismProperty M) [P.RespectsIso]

example [∀ F : Discrete PEmpty.{1} ⥤ M,
    (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})).functor.HasRightKanExtension F]
    {X Y : Discrete PEmpty.{1} ⥤ M}
    (f : (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})).functor ⋙ X ⟶ Y) :
    (∀ d : Discrete PEmpty.{1}, P (f.app d)) ↔
      ∀ t : Discrete PEmpty.{1},
        P ((Adjunction.homEquiv
          ((CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})).functor.ranAdjunction M)
          X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff
    (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})) P f

example [∀ F : Discrete ℕ ⥤ M,
    (CategoryTheory.Equivalence.refl (C := Discrete ℕ)).functor.HasRightKanExtension F]
    {X Y : Discrete ℕ ⥤ M}
    (c : X ⟶ (CategoryTheory.Equivalence.refl (C := Discrete ℕ)).functor.ran.obj Y) :
    (∀ t : Discrete ℕ, P (c.app t)) ↔
      ∀ d : Discrete ℕ,
        P (((Adjunction.homEquiv
          ((CategoryTheory.Equivalence.refl (C := Discrete ℕ)).functor.ranAdjunction M)
          X Y).symm c).app d) :=
  RightIndexAdjunctionProperties.inverse_property_iff
    (CategoryTheory.Equivalence.refl (C := Discrete ℕ)) P c

example [∀ F : SingleObj (Multiplicative ℕ) ⥤ M,
    (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))).functor.HasRightKanExtension F]
    {X Y : SingleObj (Multiplicative ℕ) ⥤ M}
    (f : (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))).functor ⋙ X ⟶ Y) :
    (∀ d : SingleObj (Multiplicative ℕ), P (f.app d)) ↔
      ∀ t : SingleObj (Multiplicative ℕ),
        P ((Adjunction.homEquiv
          ((CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))).functor.ranAdjunction M)
          X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff
    (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))) P f

/-- This fixture actually interchanges the two original component labels. -/
def swapIndex : Discrete Bool ≌ Discrete Bool :=
  Discrete.equivalence (Equiv.swap false true)

example : swapIndex.functor.obj (.mk false) = .mk true := by
  simp [swapIndex, Discrete.equivalence]

example : swapIndex.inverse.obj (.mk true) = .mk false := by
  simp [swapIndex, Discrete.equivalence]

example [∀ F : Discrete Bool ⥤ M, swapIndex.functor.HasRightKanExtension F]
    {X Y : Discrete Bool ⥤ M} (f : swapIndex.functor ⋙ X ⟶ Y) :
    (P (f.app (.mk false)) ∧ P (f.app (.mk true))) ↔
      (P (((swapIndex.functor.ranAdjunction M).homEquiv X Y f).app (.mk false)) ∧
        P (((swapIndex.functor.ranAdjunction M).homEquiv X Y f).app (.mk true))) := by
  have h := RightIndexAdjunctionProperties.homEquiv_property_iff swapIndex P f
  change (∀ d : Discrete Bool, P (f.app d)) ↔
    ∀ t : Discrete Bool, P (((swapIndex.functor.ranAdjunction M).homEquiv X Y f).app t) at h
  simpa only [Discrete.forall, Bool.forall_bool] using h

local instance originalIndexRaisedCategory : Category.{vD} (ULift.{uD + 1} D) :=
  uliftCategory D

local instance originalIndexRaisedHomCategory :
    Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))

example [∀ F : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M,
    (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm.functor.HasRightKanExtension F]
    {X : D ⥤ M} {Y : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M}
    (f : (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm.functor ⋙ X ⟶ Y) :
    (∀ t : ULiftHom.{vD + 1} (ULift.{uD + 1} D), P (f.app t)) ↔
      ∀ d : D,
        P ((Adjunction.homEquiv
          ((ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm.functor.ranAdjunction M)
          X Y f).app d) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff (ULiftHomULiftCategory.equiv D).symm P f

local instance originalCoefficientRaisedCategory : Category.{vM} (ULift.{uM + 1} M) :=
  uliftCategory M

example (Q : MorphismProperty (ULift.{uM + 1} M)) [Q.RespectsIso]
    [∀ F : D ⥤ ULift.{uM + 1} M, e.functor.HasRightKanExtension F]
    {X : E ⥤ ULift.{uM + 1} M} {Y : D ⥤ ULift.{uM + 1} M}
    (f : e.functor ⋙ X ⟶ Y) :
    (∀ d : D, Q (f.app d)) ↔
      ∀ t : E, Q (((e.functor.ranAdjunction (ULift.{uM + 1} M)).homEquiv X Y f).app t) :=
  RightIndexAdjunctionProperties.homEquiv_property_iff e Q f

end ActualIndices

end MathlibExtTest.FunctorRightIndexAdjunctionProperties
