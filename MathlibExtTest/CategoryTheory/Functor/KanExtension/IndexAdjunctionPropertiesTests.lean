/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

import all MathlibExt.CategoryTheory.Functor.KanExtension.IndexAdjunctionProperties
import all Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Original native Lan component and inverse-index contracts

These clients retain the actual native adjunction. The comparison is the
standard left-adjoint uniqueness Iso for this adjunction and the supplied
index equivalence's precomposition adjunction. No new factory is tested.
-/

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM
open CategoryTheory Functor MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.FunctorIndexAdjunctionProperties

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M]
  (e : D ≌ E) [∀ F : D ⥤ M, e.functor.HasLeftKanExtension F]

section OriginalProperty

variable (P : MorphismProperty M) [P.RespectsIso]

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    (∀ t : E, P (f.app t)) ↔
      ∀ d : D, P (((e.functor.lanAdjunction M).homEquiv X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff e P f

example {X : D ⥤ M} {Y : E ⥤ M} (c : X ⟶ e.functor ⋙ Y) :
    (∀ d : D, P (c.app d)) ↔
      ∀ t : E, P ((((e.functor.lanAdjunction M).homEquiv X Y).symm c).app t) :=
  IndexAdjunctionProperties.inverse_property_iff e P c

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    (P.functorCategory D)
        (((Functor.whiskeringLeft D E M).obj e.functor).map f) ↔
      P.functorCategory E f := by
  change ((P.functorCategory D).inverseImage (e.congrLeft (E := M)).inverse) f ↔
    P.functorCategory E f
  rw [functorCategory_inverseImage_congrLeft_inverse e P]

end OriginalProperty

section WholeNativeFunctions

example :
    (fun (X : D ⥤ M) (Y : E ⥤ M) (f : e.functor.lan.obj X ⟶ Y) =>
      (e.functor.lanAdjunction M).homEquiv X Y f) =
    (fun X _Y f => (e.functor.lanAdjunction M).unit.app X ≫
      ((Functor.whiskeringLeft D E M).obj e.functor).map f) := by
  funext X Y f
  exact Adjunction.homEquiv_apply (e.functor.lanAdjunction M) X Y f

example :
    (fun (X : D ⥤ M) (Y : E ⥤ M) (c : X ⟶ e.functor ⋙ Y) =>
      ((e.functor.lanAdjunction M).homEquiv X Y).symm c) =
    (fun _X Y c => e.functor.lan.map c ≫ (e.functor.lanAdjunction M).counit.app Y) := by
  funext X Y c
  exact Adjunction.homEquiv_symm_apply (e.functor.lanAdjunction M) X Y c

example :
    (fun (X : D ⥤ M) (Y : E ⥤ M) (f : e.functor.lan.obj X ⟶ Y) (d : D) =>
      ((e.functor.lanAdjunction M).homEquiv X Y f).app d) =
    (fun X _Y f d => ((e.functor.lanAdjunction M).unit.app X).app d ≫
      f.app (e.functor.obj d)) := by
  funext X Y f d
  rw [Adjunction.homEquiv_apply]
  rfl

example :
    (fun (X : D ⥤ M) (Y : E ⥤ M) (c : X ⟶ e.functor ⋙ Y) (t : E) =>
      (((e.functor.lanAdjunction M).homEquiv X Y).symm c).app t) =
    (fun _X Y c t => (e.functor.lan.map c).app t ≫
      ((e.functor.lanAdjunction M).counit.app Y).app t) := by
  funext X Y c t
  rw [Adjunction.homEquiv_symm_apply]
  rfl

example {X' X : D ⥤ M} {Y : E ⥤ M} (a : X' ⟶ X)
    (f : e.functor.lan.obj X ⟶ Y) :
    (e.functor.lanAdjunction M).homEquiv X' Y (e.functor.lan.map a ≫ f) =
      a ≫ (e.functor.lanAdjunction M).homEquiv X Y f :=
  (e.functor.lanAdjunction M).homEquiv_naturality_left a f

example {X : D ⥤ M} {Y Y' : E ⥤ M}
    (f : e.functor.lan.obj X ⟶ Y) (a : Y ⟶ Y') :
    (e.functor.lanAdjunction M).homEquiv X Y' (f ≫ a) =
      (e.functor.lanAdjunction M).homEquiv X Y f ≫
        ((Functor.whiskeringLeft D E M).obj e.functor).map a :=
  (e.functor.lanAdjunction M).homEquiv_naturality_right f a

example {X' X : D ⥤ M} {Y : E ⥤ M} (a : X' ⟶ X)
    (c : X ⟶ e.functor ⋙ Y) :
    ((e.functor.lanAdjunction M).homEquiv X' Y).symm (a ≫ c) =
      e.functor.lan.map a ≫ ((e.functor.lanAdjunction M).homEquiv X Y).symm c :=
  (e.functor.lanAdjunction M).homEquiv_naturality_left_symm a c

example {X : D ⥤ M} {Y Y' : E ⥤ M}
    (c : X ⟶ e.functor ⋙ Y) (a : Y ⟶ Y') :
    ((e.functor.lanAdjunction M).homEquiv X Y').symm
        (c ≫ ((Functor.whiskeringLeft D E M).obj e.functor).map a) =
      ((e.functor.lanAdjunction M).homEquiv X Y).symm c ≫ a :=
  (e.functor.lanAdjunction M).homEquiv_naturality_right_symm c a

example (X : D ⥤ M) : IsIso ((e.functor.lanAdjunction M).unit.app X) :=
  inferInstance

example (Y : E ⥤ M) : IsIso ((e.functor.lanAdjunction M).counit.app Y) :=
  inferInstance

example (X : D ⥤ M) (d : D) :
    IsIso (((e.functor.lanAdjunction M).unit.app X).app d) :=
  inferInstance

example (Y : E ⥤ M) (t : E) :
    IsIso (((e.functor.lanAdjunction M).counit.app Y).app t) :=
  inferInstance

end WholeNativeFunctions

section OriginalIndexComparison

/-- A fixed full-value client joins the two actual forward Hom functions. -/
theorem nativeForwardIndexComparison {X : D ⥤ M} {Y : E ⥤ M}
    (f : e.functor.lan.obj X ⟶ Y) :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    (e.functor.lanAdjunction M).homEquiv X Y f =
      (e.congrLeft (E := M)).toAdjunction.homEquiv X Y (i.inv.app X ≫ f) := by
  let a := e.functor.lanAdjunction M
  let b := (e.congrLeft (E := M)).toAdjunction
  let i := Adjunction.leftAdjointUniq a b
  change a.homEquiv X Y f = b.homEquiv X Y (i.inv.app X ≫ f)
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, Functor.map_comp,
    ← Category.assoc]
  have h := Adjunction.unit_leftAdjointUniq_hom_app b a X
  rw [← Adjunction.leftAdjointUniq_inv_app a b X] at h
  exact congrArg (fun t => t ≫ ((Functor.whiskeringLeft D E M).obj e.functor).map f) h.symm

/-- The complete inverse-function client retains the same standard comparison Iso. -/
theorem nativeInverseIndexComparison {X : D ⥤ M} {Y : E ⥤ M}
    (c : X ⟶ e.functor ⋙ Y) :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    ((e.functor.lanAdjunction M).homEquiv X Y).symm c =
      i.hom.app X ≫ ((e.congrLeft (E := M)).toAdjunction.homEquiv X Y).symm c := by
  let a := e.functor.lanAdjunction M
  let b := (e.congrLeft (E := M)).toAdjunction
  let i := Adjunction.leftAdjointUniq a b
  change (a.homEquiv X Y).symm c = i.hom.app X ≫ (b.homEquiv X Y).symm c
  apply (a.homEquiv X Y).injective
  rw [Equiv.apply_symm_apply]
  have h := nativeForwardIndexComparison e (i.hom.app X ≫ (b.homEquiv X Y).symm c)
  change a.homEquiv X Y (i.hom.app X ≫ (b.homEquiv X Y).symm c) =
    b.homEquiv X Y (i.inv.app X ≫ (i.hom.app X ≫ (b.homEquiv X Y).symm c)) at h
  rw [h]
  simp only [← Category.assoc, ← NatTrans.comp_app, i.inv_hom_id,
    NatTrans.id_app, Category.id_comp, Equiv.apply_symm_apply]

example :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    (fun (X : D ⥤ M) (Y : E ⥤ M) (f : e.functor.lan.obj X ⟶ Y) =>
      (e.functor.lanAdjunction M).homEquiv X Y f) =
    (fun X Y f => (e.congrLeft (E := M)).toAdjunction.homEquiv X Y
      (i.inv.app X ≫ f)) := by
  dsimp only
  funext X Y f
  exact nativeForwardIndexComparison e f

example :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    (fun (X : D ⥤ M) (Y : E ⥤ M) (c : X ⟶ e.functor ⋙ Y) =>
      ((e.functor.lanAdjunction M).homEquiv X Y).symm c) =
    (fun X Y c => i.hom.app X ≫
      ((e.congrLeft (E := M)).toAdjunction.homEquiv X Y).symm c) := by
  dsimp only
  funext X Y c
  exact nativeInverseIndexComparison e c

example :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    (fun (X : D ⥤ M) (Y : E ⥤ M) (f : e.functor.lan.obj X ⟶ Y) (d : D) =>
      ((e.functor.lanAdjunction M).homEquiv X Y f).app d) =
    (fun X _Y f d => X.map (e.unit.app d) ≫
      ((i.inv.app X).app (e.functor.obj d) ≫ f.app (e.functor.obj d))) := by
  dsimp only
  funext X Y f d
  rw [nativeForwardIndexComparison e f, Adjunction.homEquiv_apply]
  simp [Equivalence.congrLeft, Equivalence.toAdjunction]

example :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    (fun (X : D ⥤ M) (Y : E ⥤ M) (c : X ⟶ e.functor ⋙ Y) (t : E) =>
      (((e.functor.lanAdjunction M).homEquiv X Y).symm c).app t) =
    (fun X Y c t => (i.hom.app X).app t ≫
      (c.app (e.inverse.obj t) ≫ Y.map (e.counit.app t))) := by
  dsimp only
  funext X Y c t
  rw [nativeInverseIndexComparison e c, Adjunction.homEquiv_symm_apply]
  simp [Equivalence.congrLeft, Equivalence.toAdjunction]

example :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    (fun (X : D ⥤ M) (d : D) => ((e.functor.lanAdjunction M).unit.app X).app d ≫
      (i.hom.app X).app (e.functor.obj d)) =
    (fun X d => X.map (e.unit.app d)) := by
  dsimp only
  funext X d
  have h := congr_app (Adjunction.unit_leftAdjointUniq_hom_app
    (e.functor.lanAdjunction M) (e.congrLeft (E := M)).toAdjunction X) d
  simpa [Equivalence.congrLeft, Equivalence.toAdjunction] using h

example :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    (fun (Y : E ⥤ M) (t : E) =>
      (i.hom.app (e.functor ⋙ Y)).app t ≫ Y.map (e.counit.app t)) =
    (fun Y t => ((e.functor.lanAdjunction M).counit.app Y).app t) := by
  dsimp only
  funext Y t
  have h := congr_app (Adjunction.leftAdjointUniq_hom_app_counit
    (e.functor.lanAdjunction M) (e.congrLeft (E := M)).toAdjunction Y) t
  simpa [Equivalence.congrLeft, Equivalence.toAdjunction] using h

example :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    (fun (X : D ⥤ M) (d : D) => X.map (e.unit.app d) ≫
      (i.inv.app X).app (e.functor.obj d)) =
    (fun X d => ((e.functor.lanAdjunction M).unit.app X).app d) := by
  dsimp only
  funext X d
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (e.congrLeft (E := M)).toAdjunction (e.functor.lanAdjunction M) X
  rw [← Adjunction.leftAdjointUniq_inv_app
    (e.functor.lanAdjunction M) (e.congrLeft (E := M)).toAdjunction X] at h
  simpa [Equivalence.congrLeft, Equivalence.toAdjunction] using congr_app h d

example :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    (fun (Y : E ⥤ M) (t : E) => (i.inv.app (e.functor ⋙ Y)).app t ≫
      ((e.functor.lanAdjunction M).counit.app Y).app t) =
    (fun Y t => Y.map (e.counit.app t)) := by
  dsimp only
  funext Y t
  have h := Adjunction.leftAdjointUniq_hom_app_counit
    (e.congrLeft (E := M)).toAdjunction (e.functor.lanAdjunction M) Y
  rw [← Adjunction.leftAdjointUniq_inv_app
    (e.functor.lanAdjunction M) (e.congrLeft (E := M)).toAdjunction
    ((e.congrLeft (E := M)).inverse.obj Y)] at h
  simpa [Equivalence.congrLeft, Equivalence.toAdjunction] using congr_app h t

example {X X' : D ⥤ M} (a : X ⟶ X') :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    e.functor.lan.map a ≫ i.hom.app X' =
      i.hom.app X ≫ ((Functor.whiskeringLeft E D M).obj e.inverse).map a :=
  (Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
    (e.congrLeft (E := M)).toAdjunction).hom.naturality a

example {X X' : D ⥤ M} (a : X ⟶ X') :
    let i := Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
      (e.congrLeft (E := M)).toAdjunction
    ((Functor.whiskeringLeft E D M).obj e.inverse).map a ≫ i.inv.app X' =
      i.inv.app X ≫ e.functor.lan.map a :=
  (Adjunction.leftAdjointUniq (e.functor.lanAdjunction M)
    (e.congrLeft (E := M)).toAdjunction).inv.naturality a

end OriginalIndexComparison

section OriginalUnitCounitMaps

example {X X' : D ⥤ M} (a : X ⟶ X') :
    a ≫ (e.functor.lanAdjunction M).unit.app X' =
      (e.functor.lanAdjunction M).unit.app X ≫
        ((Functor.whiskeringLeft D E M).obj e.functor).map (e.functor.lan.map a) :=
  (e.functor.lanAdjunction M).unit.naturality a

example {Y Y' : E ⥤ M} (a : Y ⟶ Y') :
    e.functor.lan.map (((Functor.whiskeringLeft D E M).obj e.functor).map a) ≫
        (e.functor.lanAdjunction M).counit.app Y' =
      (e.functor.lanAdjunction M).counit.app Y ≫ a :=
  (e.functor.lanAdjunction M).counit.naturality a

example (X : D ⥤ M) {d d' : D} (a : d ⟶ d') :
    X.map a ≫ ((e.functor.lanAdjunction M).unit.app X).app d' =
      ((e.functor.lanAdjunction M).unit.app X).app d ≫
        (e.functor.lan.obj X).map (e.functor.map a) :=
  ((e.functor.lanAdjunction M).unit.app X).naturality a

example (Y : E ⥤ M) {t t' : E} (a : t ⟶ t') :
    (e.functor.lan.obj (e.functor ⋙ Y)).map a ≫
        ((e.functor.lanAdjunction M).counit.app Y).app t' =
      ((e.functor.lanAdjunction M).counit.app Y).app t ≫ Y.map a :=
  ((e.functor.lanAdjunction M).counit.app Y).naturality a

example (X : D ⥤ M) :
    ((e.functor.lanAdjunction M).homEquiv X (e.functor.lan.obj X)).symm
      ((e.functor.lanAdjunction M).unit.app X) = 𝟙 _ :=
  (e.functor.lanAdjunction M).homEquiv_symm_unit X

example (Y : E ⥤ M) :
    e.functor.lan.map ((e.functor.lanAdjunction M).unit.app (e.functor ⋙ Y)) ≫
      (e.functor.lanAdjunction M).counit.app (e.functor.lan.obj (e.functor ⋙ Y)) = 𝟙 _ :=
  (e.functor.lanAdjunction M).left_triangle_components (e.functor ⋙ Y)

example (X : D ⥤ M) :
    (e.functor.lanAdjunction M).unit.app (e.functor ⋙ e.functor.lan.obj X) ≫
      ((Functor.whiskeringLeft D E M).obj e.functor).map
        ((e.functor.lanAdjunction M).counit.app (e.functor.lan.obj X)) = 𝟙 _ :=
  (e.functor.lanAdjunction M).right_triangle_components (e.functor.lan.obj X)

end OriginalUnitCounitMaps

section ScalarComponentProperties

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    (∀ t : E, IsIso (f.app t)) ↔
      ∀ d : D, IsIso (((e.functor.lanAdjunction M).homEquiv X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff e (isomorphisms M) f

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    (∀ t : E, Mono (f.app t)) ↔
      ∀ d : D, Mono (((e.functor.lanAdjunction M).homEquiv X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff e (monomorphisms M) f

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    (∀ t : E, Epi (f.app t)) ↔
      ∀ d : D, Epi (((e.functor.lanAdjunction M).homEquiv X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff e (epimorphisms M) f

-- These are scalar pointwise classes. No global projective Cof equality is asserted.
variable [ModelCategory M]

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    (∀ t : E, weakEquivalences M (f.app t)) ↔
      ∀ d : D, weakEquivalences M (((e.functor.lanAdjunction M).homEquiv X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff e (weakEquivalences M) f

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    (∀ t : E, cofibrations M (f.app t)) ↔
      ∀ d : D, cofibrations M (((e.functor.lanAdjunction M).homEquiv X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff e (cofibrations M) f

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    (∀ t : E, fibrations M (f.app t)) ↔
      ∀ d : D, fibrations M (((e.functor.lanAdjunction M).homEquiv X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff e (fibrations M) f

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    (∀ t : E, trivialCofibrations M (f.app t)) ↔
      ∀ d : D, trivialCofibrations M (((e.functor.lanAdjunction M).homEquiv X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff e (trivialCofibrations M) f

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    (∀ t : E, trivialFibrations M (f.app t)) ↔
      ∀ d : D, trivialFibrations M (((e.functor.lanAdjunction M).homEquiv X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff e (trivialFibrations M) f

end ScalarComponentProperties

section ActualIndices

variable (P : MorphismProperty M) [P.RespectsIso]

example [∀ F : Discrete PEmpty.{1} ⥤ M,
    (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})).functor.HasLeftKanExtension F]
    {X Y : Discrete PEmpty.{1} ⥤ M}
    (f : (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})).functor.lan.obj X ⟶ Y) :
    (∀ t : Discrete PEmpty.{1}, P (f.app t)) ↔
      ∀ d : Discrete PEmpty.{1},
        P ((Adjunction.homEquiv
          ((CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})).functor.lanAdjunction M)
          X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff
    (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1})) P f

example [∀ F : Discrete ℕ ⥤ M,
    (CategoryTheory.Equivalence.refl (C := Discrete ℕ)).functor.HasLeftKanExtension F]
    {X Y : Discrete ℕ ⥤ M}
    (c : X ⟶ (CategoryTheory.Equivalence.refl (C := Discrete ℕ)).functor ⋙ Y) :
    (∀ d : Discrete ℕ, P (c.app d)) ↔
      ∀ t : Discrete ℕ,
        P (((Adjunction.homEquiv
          ((CategoryTheory.Equivalence.refl (C := Discrete ℕ)).functor.lanAdjunction M)
          X Y).symm c).app t) :=
  IndexAdjunctionProperties.inverse_property_iff (CategoryTheory.Equivalence.refl (C := Discrete ℕ)) P c

example [∀ F : SingleObj (Multiplicative ℕ) ⥤ M,
    (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))).functor.HasLeftKanExtension F]
    {X Y : SingleObj (Multiplicative ℕ) ⥤ M}
    (f : (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))).functor.lan.obj X ⟶ Y) :
    (∀ t : SingleObj (Multiplicative ℕ), P (f.app t)) ↔
      ∀ d : SingleObj (Multiplicative ℕ),
        P ((Adjunction.homEquiv
          ((CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))).functor.lanAdjunction M)
          X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff
    (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ))) P f

/-- A real permutation changes the original discrete component labels. -/
def swapIndex : Discrete Bool ≌ Discrete Bool :=
  Discrete.equivalence (Equiv.swap false true)

example : swapIndex.functor.obj (.mk false) = .mk true := by
  simp [swapIndex, Discrete.equivalence]

example : swapIndex.inverse.obj (.mk true) = .mk false := by
  simp [swapIndex, Discrete.equivalence]

example [∀ F : Discrete Bool ⥤ M, swapIndex.functor.HasLeftKanExtension F]
    {X Y : Discrete Bool ⥤ M} (f : swapIndex.functor.lan.obj X ⟶ Y) :
    (P (f.app (.mk false)) ∧ P (f.app (.mk true))) ↔
      (P (((swapIndex.functor.lanAdjunction M).homEquiv X Y f).app (.mk false)) ∧
        P (((swapIndex.functor.lanAdjunction M).homEquiv X Y f).app (.mk true))) := by
  have h := IndexAdjunctionProperties.homEquiv_property_iff swapIndex P f
  change (∀ t : Discrete Bool, P (f.app t)) ↔
    ∀ d : Discrete Bool, P (((swapIndex.functor.lanAdjunction M).homEquiv X Y f).app d) at h
  simpa only [Discrete.forall, Bool.forall_bool] using h

local instance originalIndexRaisedCategory : Category.{vD} (ULift.{uD + 1} D) :=
  uliftCategory D

local instance originalIndexRaisedHomCategory :
    Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))

example [∀ F : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M,
    (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm.functor.HasLeftKanExtension F]
    {X : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M} {Y : D ⥤ M}
    (f : (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm.functor.lan.obj X ⟶ Y) :
    (∀ d : D, P (f.app d)) ↔
      ∀ t : ULiftHom.{vD + 1} (ULift.{uD + 1} D),
        P ((Adjunction.homEquiv
          ((ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm.functor.lanAdjunction M)
          X Y f).app t) :=
  IndexAdjunctionProperties.homEquiv_property_iff (ULiftHomULiftCategory.equiv D).symm P f

local instance originalCoefficientRaisedCategory : Category.{vM} (ULift.{uM + 1} M) :=
  uliftCategory M

example (Q : MorphismProperty (ULift.{uM + 1} M)) [Q.RespectsIso]
    [∀ F : D ⥤ ULift.{uM + 1} M, e.functor.HasLeftKanExtension F]
    {X : D ⥤ ULift.{uM + 1} M} {Y : E ⥤ ULift.{uM + 1} M}
    (f : e.functor.lan.obj X ⟶ Y) :
    (∀ t : E, Q (f.app t)) ↔
      ∀ d : D, Q (((e.functor.lanAdjunction (ULift.{uM + 1} M)).homEquiv X Y f).app d) :=
  IndexAdjunctionProperties.homEquiv_property_iff e Q f

end ActualIndices

end MathlibExtTest.FunctorIndexAdjunctionProperties
