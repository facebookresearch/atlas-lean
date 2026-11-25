/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.NatIso

/-! # Functor comparisons and transport through equivalences

Whole functors, natural transformations, bifunctors and representing Hom equivalences are
transported with their
original maps.
-/

/-! ## Functor composition and natural transformations -/
@[expose] public section

section
/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/



/-!
# Whole bifunctor conjugation through actual equivalences

All source and target maps use the original equivalence functors. Passing
through an intermediate presentation is compared with direct transport by
the actual original unit isomorphism.
-/


set_option autoImplicit false
noncomputable section

universe uA vA uB vB uD vD

open CategoryTheory Opposite

namespace CategoryTheory.MappingEndFunctorTransport

variable {A : Type uA} [Category.{vA} A]
  {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]

/-- Restrict both original inputs and reconstruct the complete original output. -/
def conjugate (K : A ≌ B) (H : Aᵒᵖ ⥤ A ⥤ A) : Bᵒᵖ ⥤ B ⥤ B :=
  K.inverse.op ⋙ H ⋙
    (Functor.whiskeringLeft B A A).obj K.inverse ⋙
      (Functor.whiskeringRight B A B).obj K.functor

/-- Iterated actual conjugation retains the complete composite equivalence. -/
def composition (K : A ≌ B) (E : B ≌ D) (H : Aᵒᵖ ⥤ A ⥤ A) :
    conjugate E (conjugate K H) ≅ conjugate (K.trans E) H :=
  Iso.refl _

/-- Actual isomorphisms of the two whole equivalence functors compare both transported inputs. -/
def changeFunctors (E E' : A ≌ D) (H : Aᵒᵖ ⥤ A ⥤ A)
    (i : E.inverse ≅ E'.inverse) (f : E.functor ≅ E'.functor) :
    conjugate E H ≅ conjugate E' H :=
  Functor.isoWhiskerRight (NatIso.op i.symm)
      (H ⋙ (Functor.whiskeringLeft D A A).obj E.inverse ⋙
        (Functor.whiskeringRight D A D).obj E.functor) ≪≫
    Functor.isoWhiskerLeft (E'.inverse.op ⋙ H)
      (Functor.isoWhiskerRight ((Functor.whiskeringLeft D A A).mapIso i)
        ((Functor.whiskeringRight D A D).obj E.functor)) ≪≫
    Functor.isoWhiskerLeft
      (E'.inverse.op ⋙ H ⋙ (Functor.whiskeringLeft D A A).obj E'.inverse)
      ((Functor.whiskeringRight D A D).mapIso f)

/-- The same complete original intermediate unit recovers the direct native bifunctor. -/
def cancelPresentation (K : A ≌ B) (E : A ≌ D) (H : Aᵒᵖ ⥤ A ⥤ A) :
    conjugate (K.symm.trans E) (conjugate K H) ≅ conjugate E H := by
  let J := K.symm.trans E
  let i : (K.trans J).inverse ≅ E.inverse :=
    Functor.isoWhiskerLeft E.inverse K.unitIso.symm ≪≫ Functor.rightUnitor E.inverse
  let f : (K.trans J).functor ≅ E.functor :=
    Functor.isoWhiskerRight K.unitIso.symm E.functor ≪≫ Functor.leftUnitor E.functor
  exact composition K J H ≪≫ changeFunctors (K.trans J) E H i f

end CategoryTheory.MappingEndFunctorTransport

end
end
/-! ## Transport along functor equalities -/
section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD

open CategoryTheory

namespace CategoryTheory.FunctorEqualityComparisonReadback

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F F₀ G : C ⥤ D}

/-- Retarget a complete comparison through an identity of the entire source functor. -/
def comparison (h : F = F₀) (n : F ≅ G) : F₀ ≅ G := (eqToIso h).symm ≪≫ n

/-- Only after the whole source identity, retrieve each complete comparison component. -/
theorem comparison_app (h : F = F₀) (n : F ≅ G) (X : C) :
    (comparison h n).app X =
      (eqToIso (congrArg (fun F : C ⥤ D => F.obj X) h)).symm ≪≫ n.app X := by
  cases h
  rfl

end CategoryTheory.FunctorEqualityComparisonReadback
end
end
/-! ## Naturality of object replacement -/
section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD

open CategoryTheory

namespace CategoryTheory.FunctorReplacementFamilyTransport

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) {H H' : C → D} (h : H = H')
  (e : ∀ X, F.obj X = H X) (e' : ∀ X, F.obj X = H' X)

include h

/-- Identities of whole object families preserve the entire replacement functor. -/
theorem functor_eq :
    F.copyObj H (fun X => eqToIso (e X)) = F.copyObj H' (fun X => eqToIso (e' X)) := by
  cases h
  cases Subsingleton.elim e e'
  rfl

/-- Eliminate the complete object-family identity before comparing the whole replacement
isomorphisms. -/
theorem inverseComparison_heq {G : C ⥤ D} (n : F ≅ G) :
    HEq ((F.isoCopyObj H (fun X => eqToIso (e X))).symm ≪≫ n)
      ((F.isoCopyObj H' (fun X => eqToIso (e' X))).symm ≪≫ n) := by
  cases h
  cases Subsingleton.elim e e'
  rfl

/-- Retarget the entire constructed comparison after eliminating the complete replacement-family
identity. -/
theorem comparison {G : C ⥤ D} (n : F ≅ G) :
    (eqToIso (functor_eq F h e e')).symm ≪≫
      (F.isoCopyObj H (fun X => eqToIso (e X))).symm ≪≫ n =
        (F.isoCopyObj H' (fun X => eqToIso (e' X))).symm ≪≫ n := by
  cases h
  cases Subsingleton.elim e e'
  simp

end CategoryTheory.FunctorReplacementFamilyTransport
end
end
/-! ## Transport of isomorphisms -/
section
set_option autoImplicit false
noncomputable section

universe uC vC uA

open CategoryTheory

namespace CategoryTheory.IsoRepresentationTransport

variable {C : Type uC} [Category.{vC} C] {X X' P : C} (i : X ≅ X')
  {A : Type uA} (H : (P ⟶ X') ≃ A)

/-- Both correspondence functions through the entire value isomorphism. -/
def homEquiv : (P ⟶ X) ≃ A := (Iso.homCongr (Iso.refl P) i).trans H

/-- The complete forward function uses the full original value comparison. -/
theorem homEquiv_apply (f : P ⟶ X) : homEquiv i H f = H (f ≫ i.hom) := by
  dsimp only [homEquiv, Equiv.trans, Iso.homCongr, Iso.refl]
  simp only [Category.id_comp]
  rfl

/-- The complete inverse function uses the full original inverse value comparison. -/
theorem homEquiv_symm_apply (a : A) : (homEquiv i H).symm a = H.symm a ≫ i.inv := by
  dsimp only [homEquiv, Equiv.trans, Equiv.symm, Iso.homCongr, Iso.refl]
  simp only [Category.id_comp]
  rfl

/-- Every inverse representing map retains every original end projection. -/
theorem inverse_projection (a : A) {K : C} (π : X' ⟶ K) :
    (homEquiv i H).symm a ≫ (i.hom ≫ π) = H.symm a ≫ π := by
  rw [homEquiv_symm_apply, Category.assoc, Iso.inv_hom_id_assoc]

/-- Unique representation through the full value isomorphism, for any complete family predicate. -/
theorem existsUnique (Q : (P ⟶ X') → Prop) (h : ∃! f, Q f) :
    ∃! f : P ⟶ X, Q (f ≫ i.hom) := by
  obtain ⟨f, hf, huniq⟩ := h
  refine ⟨f ≫ i.inv, ?_, ?_⟩
  · simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hf
  · intro g hg
    apply (cancel_mono i.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact huniq _ hg

end CategoryTheory.IsoRepresentationTransport
end
end
/-! ## Tensor and functor transport -/
section
/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/



/-!
# Whole native tensor comparison through complete original module equivalences

Both tensor inputs and the output use the actual equivalence functors. The
constructed module tensor comparison is transported through the original unit
and both native functor maps; all source and target map functions are retained.
-/


set_option autoImplicit false
noncomputable section

universe uA vA uB vB uN vN

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.RelativeTensorNativeFunctorTransport

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {N : Type uN} [Category.{vN} N]

/-- Reconstruct both whole native tensor inputs and the entire native output. -/
def conjugate (E : A ≌ N) (T : A ⥤ A ⥤ A) : N ⥤ N ⥤ N :=
  E.inverse ⋙ T ⋙ (Functor.whiskeringLeft N A A).obj E.inverse ⋙
    (Functor.whiskeringRight N A N).obj E.functor

/-- Every transported tensor object retains both complete original inverse objects. -/
theorem conjugate_obj (E : A ≌ N) (T : A ⥤ A ⥤ A) (X Y : N) :
    ((conjugate E T).obj X).obj Y =
      E.functor.obj ((T.obj (E.inverse.obj X)).obj (E.inverse.obj Y)) := rfl

/-- Every transported first-variable tensor map retains its original source component. -/
theorem conjugate_source (E : A ≌ N) (T : A ⥤ A ⥤ A)
    {X X' : N} (f : X ⟶ X') (Y : N) :
    ((conjugate E T).map f).app Y =
      E.functor.map ((T.map (E.inverse.map f)).app (E.inverse.obj Y)) := rfl

/-- Every transported second-variable tensor map retains its original target component. -/
theorem conjugate_target (E : A ≌ N) (T : A ⥤ A ⥤ A)
    (X : N) {Y Y' : N} (g : Y ⟶ Y') :
    ((conjugate E T).obj X).map g =
      E.functor.map ((T.obj (E.inverse.obj X)).map (E.inverse.map g)) := rfl

/-- The transported tensor bifunctor is the original monoidal transport tensor. -/
theorem conjugate_curriedTensor [MonoidalCategory A] (E : A ≌ N) :
    letI := Monoidal.transport E
    conjugate E (MonoidalCategory.curriedTensor A) = MonoidalCategory.curriedTensor N := rfl

/-- Both original inverse and forward native functor comparisons retain all tensor maps. -/
def changeFunctors (E E' : A ≌ N) (T : A ⥤ A ⥤ A)
    (i : E.inverse ≅ E'.inverse) (f : E.functor ≅ E'.functor) :
    conjugate E T ≅ conjugate E' T :=
  Functor.isoWhiskerRight i
      (T ⋙ (Functor.whiskeringLeft N A A).obj E.inverse ⋙
        (Functor.whiskeringRight N A N).obj E.functor) ≪≫
    Functor.isoWhiskerLeft (E'.inverse ⋙ T)
      (Functor.isoWhiskerRight ((Functor.whiskeringLeft N A A).mapIso i)
        ((Functor.whiskeringRight N A N).obj E.functor)) ≪≫
    Functor.isoWhiskerLeft
      (E'.inverse ⋙ T ⋙ (Functor.whiskeringLeft N A A).obj E'.inverse)
      ((Functor.whiskeringRight N A N).mapIso f)

/-- Iterated original tensor transport is the complete original composite equivalence. -/
def composition (K : A ≌ B) (E : B ≌ N) (T : A ⥤ A ⥤ A) :
    conjugate E (conjugate K T) ≅ conjugate (K.trans E) T := Iso.refl _

/-- The complete original presentation unit recovers the directly transported native tensor. -/
def cancelPresentation (K : A ≌ B) (E : A ≌ N) (T : A ⥤ A ⥤ A) :
    conjugate (K.symm.trans E) (conjugate K T) ≅ conjugate E T := by
  let J := K.symm.trans E
  let i : (K.trans J).inverse ≅ E.inverse :=
    Functor.isoWhiskerLeft E.inverse K.unitIso.symm ≪≫ Functor.rightUnitor E.inverse
  let f : (K.trans J).functor ≅ E.functor :=
    Functor.isoWhiskerRight K.unitIso.symm E.functor ≪≫ Functor.leftUnitor E.functor
  exact composition K J T ≪≫ changeFunctors (K.trans J) E T i f

/-- Both whole original tensor outputs retain the original equivalence unit. -/
def unitOutputs (K : A ≌ B) (T : A ⥤ A ⥤ A) :
    T ≅ T ⋙ (Functor.whiskeringRight A A B).obj K.functor ⋙
      (Functor.whiskeringRight A B A).obj K.inverse :=
  NatIso.ofComponents (fun X =>
    NatIso.ofComponents (fun Y => K.unitIso.app ((T.obj X).obj Y)) (by
      intro Y Y' f
      exact K.unitIso.hom.naturality ((T.obj X).map f))) (by
    intro X X' f
    apply NatTrans.ext
    funext Y
    exact K.unitIso.hom.naturality ((T.map f).app Y))

/-- The complete original module tensor comparison is recovered through both original unit maps. -/
def pullbackComparison (K : A ≌ B) (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B)
    (h : T ⋙ (Functor.whiskeringRight A A B).obj K.functor ≅
      K.functor ⋙ U ⋙ (Functor.whiskeringLeft A B B).obj K.functor) :
    T ≅ K.functor ⋙ U ⋙ (Functor.whiskeringLeft A B B).obj K.functor ⋙
      (Functor.whiskeringRight A B A).obj K.inverse :=
  unitOutputs K T ≪≫ Functor.isoWhiskerRight h
    ((Functor.whiskeringRight A B A).obj K.inverse)

/-- Both full module and native equivalences transport the constructed whole tensor bifunctor
comparison. -/
def comparison (K : A ≌ B) (E : A ≌ N) (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B)
    (h : T ⋙ (Functor.whiskeringRight A A B).obj K.functor ≅
      K.functor ⋙ U ⋙ (Functor.whiskeringLeft A B B).obj K.functor) :
    conjugate E T ≅ conjugate (K.symm.trans E) U := by
  let WL := (Functor.whiskeringLeft N A A).obj E.inverse
  let WR := (Functor.whiskeringRight N A N).obj E.functor
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft E.inverse
      (pullbackComparison K T U h)) WL) WR

/-- Every native forward component is the exact original unit and module comparison path. -/
theorem comparison_hom_app (K : A ≌ B) (E : A ≌ N) (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B)
    (h : T ⋙ (Functor.whiskeringRight A A B).obj K.functor ≅
      K.functor ⋙ U ⋙ (Functor.whiskeringLeft A B B).obj K.functor) (X Y : N) :
    ((comparison K E T U h).hom.app X).app Y =
      E.functor.map (K.unitIso.hom.app ((T.obj (E.inverse.obj X)).obj (E.inverse.obj Y)) ≫
        K.inverse.map ((h.hom.app (E.inverse.obj X)).app (E.inverse.obj Y))) := rfl

/-- Every native inverse component retains both original inverse comparison maps. -/
theorem comparison_inv_app (K : A ≌ B) (E : A ≌ N) (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B)
    (h : T ⋙ (Functor.whiskeringRight A A B).obj K.functor ≅
      K.functor ⋙ U ⋙ (Functor.whiskeringLeft A B B).obj K.functor) (X Y : N) :
    ((comparison K E T U h).inv.app X).app Y =
      E.functor.map (K.inverse.map ((h.inv.app (E.inverse.obj X)).app (E.inverse.obj Y)) ≫
        K.unitIso.inv.app ((T.obj (E.inverse.obj X)).obj (E.inverse.obj Y))) := rfl

/-- Both complete native equivalences identify the directly transported original tensor functors. -/
def nativeComparison (E : A ≌ N) (O : B ≌ N) (T : A ⥤ A ⥤ A) (U : B ⥤ B ⥤ B)
    (h : T ⋙ (Functor.whiskeringRight A A B).obj (E.trans O.symm).functor ≅
      (E.trans O.symm).functor ⋙ U ⋙
        (Functor.whiskeringLeft A B B).obj (E.trans O.symm).functor) :
    conjugate E T ≅ conjugate O U := by
  let K := E.trans O.symm
  let J := K.symm.trans E
  let i : J.inverse ≅ O.inverse :=
    Functor.isoWhiskerRight E.counitIso O.inverse ≪≫ Functor.leftUnitor O.inverse
  let f : J.functor ≅ O.functor :=
    Functor.isoWhiskerLeft O.functor E.counitIso ≪≫ Functor.rightUnitor O.functor
  exact comparison K E T U h ≪≫ changeFunctors J O U i f

end CategoryTheory.RelativeTensorNativeFunctorTransport
end
end
/-! ## Mapping-source functor comparisons -/
section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe uA vA uB vB uV vV uI vI uD vD

open CategoryTheory Opposite

namespace CategoryTheory.NativeMappingSourceFrame.Primitive

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]

/-- The entire source transformation is reconstructed through the two original E functors. -/
theorem conjugate_map (E : A ≌ B) (H : Aᵒᵖ ⥤ A ⥤ A)
    {X X' : B} (f : X' ⟶ X) :
    (MappingEndFunctorTransport.conjugate E H).map f.op =
      Functor.whiskerRight (Functor.whiskerLeft E.inverse (H.map (E.inverse.map f).op))
        E.functor := rfl

/-- Both actual whiskerings preserve the whole source transformation through proved functor
equalities. -/
theorem whisker_heq (E : A ≌ B) {F F' G G' : A ⥤ A}
    (eF : F = F') (eG : G = G') (a : F ⟶ G) (b : F' ⟶ G') (h : HEq a b) :
    HEq (Functor.whiskerRight (Functor.whiskerLeft E.inverse a) E.functor)
      (Functor.whiskerRight (Functor.whiskerLeft E.inverse b) E.functor) := by
  cases eF
  cases eG
  cases h
  rfl

/-- A whole transformation equality retains every original object component. -/
theorem app_heq {F F' G G' : A ⥤ B}
    (eF : F = F') (eG : G = G') (a : F ⟶ G) (b : F' ⟶ G') (h : HEq a b) (X : A) :
    HEq (a.app X) (b.app X) := by
  cases eF
  cases eG
  cases h
  rfl

end CategoryTheory.NativeMappingSourceFrame.Primitive
end
end
