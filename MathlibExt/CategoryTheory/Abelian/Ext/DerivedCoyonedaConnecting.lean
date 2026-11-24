/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaFunctor
public import MathlibExt.CategoryTheory.Abelian.RightDerived.HorseshoeExtBoundary

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasInjectiveResolutions C] [HasExt.{v} C]
variable {S : ShortComplex C} {hS : S.ShortExact}

set_option backward.isDefEq.respectTransparency false in
omit [HasInjectiveResolutions C] in
/--
The SAME Coyoneda homology connector corresponds to composition with the original covariant Yoneda
class on arbitrary chosen horseshoes.
-/
theorem original_coyoneda_horseshoe_delta (Z : C)
    (H : Functor.RightDerived.HorseshoeData S hS) (q : ℕ) :
    (H.mapped_shortExact (preadditiveCoyoneda.obj (op Z))).δ q (q + 1) rfl ≫
        (homologyDataExt Z H.res₁ (q + 1)).homologyIso.hom =
      (homologyDataExt Z H.res₃ q).homologyIso.hom ≫
        AddCommGrpCat.ofHom (hS.extClass.postcomp Z (by omega)) := by
  let := HasDerivedCategory.standard C
  let E₃ := homologyDataExt Z H.res₃ q
  apply (cancel_epi ((mappedCocomplex Z H.res₃).sc q).homologyπ).mp
  apply (cancel_epi E₃.cyclesIso.inv).mp
  apply AddCommGrpCat.ext
  intro c
  have hc := H.extMk_original_boundary q c.val c.property
  have hd := H.mapped_delta_cycles (preadditiveCoyoneda.obj (op Z)) q
  have hπ := E₃.homologyπ_comp_homologyIso_hom
  have hπ₃ : E₃.cyclesIso.inv ≫ ((mappedCocomplex Z H.res₃).sc q).homologyπ ≫
      E₃.homologyIso.hom = E₃.π := by
    exact (congrArg (fun t => E₃.cyclesIso.inv ≫ t)
      E₃.homologyπ_comp_homologyIso_hom).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun t => t ≫ E₃.π) E₃.cyclesIso.inv_hom_id).trans (Category.id_comp _)))
  rw [reassoc_of% hπ₃]
  simp only [ConcreteCategory.comp_apply]
  change (homologyDataExt Z H.res₁ (q + 1)).homologyIso.hom
      ((H.mapped_shortExact (preadditiveCoyoneda.obj (op Z))).δ q (q + 1) rfl
        ((mappedCocomplex Z H.res₃).homologyπ q (E₃.cyclesIso.inv c))) =
    (H.res₃.extMk c.val (q + 1) rfl c.property).comp hS.extClass rfl
  rw [hc]
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun t => E₃.cyclesIso.inv ≫ t ≫
      (homologyDataExt Z H.res₁ (q + 1)).homologyIso.hom) hd) c
  simp only [ConcreteCategory.comp_apply] at hh
  refine hh.trans ?_
  let E₁ := homologyDataExt Z H.res₁ (q + 1)
  have he := E₁.homologyπ_comp_homologyIso_hom
  have hec := ConcreteCategory.congr_hom he
    (((H.mapped (preadditiveCoyoneda.obj (op Z))).X₁.liftCycles
      (HomologicalComplex.splitConnectingRepresentative (H.mapped (preadditiveCoyoneda.obj (op Z)))
        (H.mappedSplitting (preadditiveCoyoneda.obj (op Z))) q
        ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles q))
      (q + 2) (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl))
      (HomologicalComplex.splitConnectingRepresentative_cycle (H.mapped (preadditiveCoyoneda.obj (op Z)))
        (H.mappedSplitting (preadditiveCoyoneda.obj (op Z))) q
        ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles q)
        ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles_d q (q + 1))))
      (E₃.cyclesIso.inv c))
  simp only [ConcreteCategory.comp_apply] at hec
  refine hec.trans ?_
  let c₁ : E₁.K := ⟨H.originalConnectingRepresentative q c.val,
    H.originalConnectingRepresentative_cycle q c.val c.property⟩
  change E₁.π _ = E₁.π c₁
  apply congrArg E₁.π
  apply Subtype.ext
  have hv := ConcreteCategory.congr_hom E₁.cyclesIso_hom_comp_i
    (((H.mapped (preadditiveCoyoneda.obj (op Z))).X₁.liftCycles
      (HomologicalComplex.splitConnectingRepresentative (H.mapped (preadditiveCoyoneda.obj (op Z)))
        (H.mappedSplitting (preadditiveCoyoneda.obj (op Z))) q
        ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles q))
      (q + 2) (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl))
      (HomologicalComplex.splitConnectingRepresentative_cycle (H.mapped (preadditiveCoyoneda.obj (op Z)))
        (H.mappedSplitting (preadditiveCoyoneda.obj (op Z))) q
        ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles q)
        ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles_d q (q + 1))))
      (E₃.cyclesIso.inv c))
  simp only [ConcreteCategory.comp_apply] at hv
  change _ = ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₁.iCycles (q + 1)) _ at hv
  change ((E₁.cyclesIso.hom
    (((H.mapped (preadditiveCoyoneda.obj (op Z))).X₁.liftCycles
      (HomologicalComplex.splitConnectingRepresentative (H.mapped (preadditiveCoyoneda.obj (op Z)))
        (H.mappedSplitting (preadditiveCoyoneda.obj (op Z))) q
        ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles q))
      (q + 2) (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl)) _)
      (E₃.cyclesIso.inv c))).val) = _
  refine hv.trans ?_
  have hl := ConcreteCategory.congr_hom
    ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₁.liftCycles_i
      (HomologicalComplex.splitConnectingRepresentative (H.mapped (preadditiveCoyoneda.obj (op Z)))
        (H.mappedSplitting (preadditiveCoyoneda.obj (op Z))) q
        ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles q))
      (q + 2) (ComplexShape.next_eq' _ (ComplexShape.up_mk _ _ rfl))
      (HomologicalComplex.splitConnectingRepresentative_cycle (H.mapped (preadditiveCoyoneda.obj (op Z)))
        (H.mappedSplitting (preadditiveCoyoneda.obj (op Z))) q
        ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles q)
        ((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles_d q (q + 1))))
      (E₃.cyclesIso.inv c)
  simp only [ConcreteCategory.comp_apply] at hl
  refine hl.trans ?_
  have h₃ := ConcreteCategory.congr_hom E₃.cyclesIso_inv_comp_iCycles c
  simp only [ConcreteCategory.comp_apply] at h₃
  dsimp only [HomologicalComplex.splitConnectingRepresentative, HomologicalComplex.splitCycleLift,
    Functor.RightDerived.HorseshoeData.mappedSplitting,
    Functor.RightDerived.HorseshoeData.originalConnectingRepresentative]
  simp only [ConcreteCategory.comp_apply]
  change ((((H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles q
      (E₃.cyclesIso.inv c)) ≫ (H.split q).s) ≫ H.res₂.cocomplex.d q (q + 1)) ≫
        (H.split (q + 1)).r = _
  have hv₃ : (H.mapped (preadditiveCoyoneda.obj (op Z))).X₃.iCycles q
      (E₃.cyclesIso.inv c) = c.val := h₃
  dsimp only [c₁, Functor.RightDerived.HorseshoeData.originalConnectingRepresentative]
  simpa only [Category.assoc] using congrArg (fun t => ((t ≫ (H.split q).s) ≫ H.res₂.cocomplex.d q (q + 1)) ≫
    (H.split (q + 1)).r) hv₃

end CategoryTheory.DerivedCoyoneda

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C] [HasInjectiveResolutions C]
variable {S : ShortComplex C} {hS : S.ShortExact}

/-- The original chosen-resolution Coyoneda comparison as the SAME additive-group isomorphism. -/
def chosenCoyonedaExtIso (Z : C) {Y : C} (R : InjectiveResolution Y) (q : ℕ) :
    ((preadditiveCoyoneda.obj (op Z)).rightDerived q).obj Y ≅
      AddCommGrpCat.of (Abelian.Ext.{v} Z Y q) :=
  R.isoRightDerivedObj (preadditiveCoyoneda.obj (op Z)) q ≪≫
    (homologyDataExt Z R q).homologyIso

set_option backward.isDefEq.respectTransparency false in
/--
The SAME chosen-resolution right-derived comparison intertwines every horseshoe connector with the
original covariant Ext-class composition.
-/
theorem chosenCoyonedaExtIso_delta (Z : C)
    (H : Functor.RightDerived.HorseshoeData S hS) (q : ℕ) :
    H.delta (preadditiveCoyoneda.obj (op Z)) q (q + 1) rfl ≫
      (chosenCoyonedaExtIso Z H.res₁ (q + 1)).hom =
    (chosenCoyonedaExtIso Z H.res₃ q).hom ≫
      AddCommGrpCat.ofHom (hS.extClass.postcomp Z (by omega)) := by
  dsimp only [Functor.RightDerived.HorseshoeData.delta, chosenCoyonedaExtIso, Iso.trans_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun t => (H.res₃.isoRightDerivedObj (preadditiveCoyoneda.obj (op Z)) q).hom ≫ t)
    (original_coyoneda_horseshoe_delta Z H q)

end CategoryTheory.DerivedCoyoneda

end

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace CategoryTheory.DerivedCoyoneda
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable [HasInjectiveResolutions C]

set_option backward.isDefEq.respectTransparency false in
/-- The existing canonical functor-level comparison is exactly the original
chosen-resolution comparison on the canonical resolution. -/
theorem canonicalCoyonedaExtIso_app (Z Y : C) (q : ℕ) :
    (Abelian.rightDerivedCoyonedaIsoExtFunctorObj Z q).app Y =
      chosenCoyonedaExtIso Z (injectiveResolution Y) q := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The SAME existing canonical RD-Coyoneda/Ext family preserves its horseshoe connector and the
original covariant Yoneda boundary.
-/
theorem canonicalCoyonedaExtIso_connecting (Z : C) (q : ℕ)
    (S : ShortComplex C) (hS : S.ShortExact) :
    (Functor.rightDerivedConnecting (preadditiveCoyoneda.obj (op Z)) q).app ⟨S, hS⟩ ≫
      ((Abelian.rightDerivedCoyonedaIsoExtFunctorObj Z (q + 1)).app S.X₁).hom =
    ((Abelian.rightDerivedCoyonedaIsoExtFunctorObj Z q).app S.X₃).hom ≫
      AddCommGrpCat.ofHom (hS.extClass.postcomp Z (by omega)) := by
  let H := Functor.RightDerived.HorseshoeData.ofEndpoints S hS
    (injectiveResolution S.X₁) (injectiveResolution S.X₃)
  have h := chosenCoyonedaExtIso_delta Z H q
  rw [canonicalCoyonedaExtIso_app, canonicalCoyonedaExtIso_app]
  change H.delta (preadditiveCoyoneda.obj (op Z)) q (q + 1) rfl ≫ _ = _
  exact h

end CategoryTheory.DerivedCoyoneda

end
