/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductPentagon
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSecondTranslationCommaNaturality
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTotalTranslationAction
public import MathlibExt.CategoryTheory.Monoidal.SInverseSSwap

/-!
# Coherent second-coordinate translations over the fixed base

The translating core uses the chosen biproduct monoidal structure. The
translation functors are the actual additive `S⁻¹S` second translations and
their right-comma endofunctors. Coordinate isomorphisms use the existing
zero-stabilizer core-pair inclusion.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject MonoidalCategory Simplicial

universe v u w wv

namespace CategoryTheory.SInverseS

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

private theorem pairIso_refl_hom (X : Pair C) :
    (pairIsoOfCoordinateIsos (X := X) (Y := X)
      (Iso.refl X.fst) (Iso.refl X.snd)).hom = 𝟙 X := by
  change (corePairInclusion (C := C)).map
    (𝟙 ((⟨X.fst⟩ : Core C), (⟨X.snd⟩ : Core C))) = 𝟙 X
  exact Functor.map_id _ _

private theorem pairIso_hom_comp {X Y Z : Pair C}
    (e : X.fst ≅ Y.fst) (d : X.snd ≅ Y.snd)
    (e' : Y.fst ≅ Z.fst) (d' : Y.snd ≅ Z.snd) :
    (pairIsoOfCoordinateIsos (X := X) (Y := Y) e d).hom ≫
      (pairIsoOfCoordinateIsos (X := Y) (Y := Z) e' d').hom =
      (pairIsoOfCoordinateIsos (X := X) (Y := Z) (e.trans e') (d.trans d')).hom := by
  change (corePairInclusion (C := C)).map
      ((⟨e⟩, ⟨d⟩) :
        ((⟨X.fst⟩ : Core C), (⟨X.snd⟩ : Core C)) ⟶
        ((⟨Y.fst⟩ : Core C), (⟨Y.snd⟩ : Core C))) ≫
    (corePairInclusion (C := C)).map
      ((⟨e'⟩, ⟨d'⟩) :
        ((⟨Y.fst⟩ : Core C), (⟨Y.snd⟩ : Core C)) ⟶
        ((⟨Z.fst⟩ : Core C), (⟨Z.snd⟩ : Core C))) = _
  rw [← Functor.map_comp]
  rfl

private theorem swap_map_translateSecond (A : C) {X Y : Pair C} (f : X ⟶ Y) :
    (swapFunctor (C := C)).map ((translateSecondFunctor A).map f) =
      (translateFirstFunctor A).map ((swapFunctor (C := C)).map f) := by
  induction f using Quotient.inductionOn
  rfl

/-- A second-coordinate isomorphism fixes the first-coordinate translation base. -/
theorem translationProjection_pairIsoSecond (P : C) {Q R : C} (e : Q ≅ R) :
    (translationProjection (C := C)).map
      (pairIsoOfCoordinateIsos (X := ⟨P, Q⟩) (Y := ⟨P, R⟩) (Iso.refl P) e).hom =
      𝟙 (⟨P⟩ : Translation C) := by
  rw [pairIsoOfCoordinateIsos_hom]
  change Translation.Hom.mk
      { stabilizer := 0,
        hom := (isoZeroBiprod (isZero_zero C)).symm.trans (Iso.refl P) } =
    Translation.Hom.mk { stabilizer := 0, hom := (isoZeroBiprod (isZero_zero C)).symm }
  simp only [Iso.trans_refl]

/-- Isomorphic translating objects induce the canonical second-translation
natural isomorphism, with identity first coordinate. -/
def translateSecondIsoOfIso {A A' : C} (e : A ≅ A') :
    translateSecondFunctor A ≅ translateSecondFunctor A' :=
  NatIso.ofComponents
    (fun X => pairIsoOfCoordinateIsos (Iso.refl X.fst)
      (biprod.mapIso e (Iso.refl X.snd))) (by
        intro X Y f
        apply (swapEquivalence (C := C)).fullyFaithfulFunctor.map_injective
        dsimp only [swapEquivalence, Equivalence.mk]
        simp only [Functor.map_comp, swap_map_translateSecond]
        exact (translateFirstIsoOfIso e).hom.naturality
          ((swapFunctor (C := C)).map f))

/-- Second-coordinate translation by zero has the canonical zero-unitor
comparison with the identity. -/
def translateSecondZeroIso : translateSecondFunctor (0 : C) ≅ 𝟭 (Pair C) :=
  NatIso.ofComponents
    (fun X => pairIsoOfCoordinateIsos (Iso.refl X.fst)
      (isoZeroBiprod (isZero_zero C)).symm) (by
        intro X Y f
        apply (swapEquivalence (C := C)).fullyFaithfulFunctor.map_injective
        dsimp only [swapEquivalence, Equivalence.mk]
        simp only [Functor.map_comp, Functor.id_map,
          swap_map_translateSecond]
        exact (translateFirstZeroIso (C := C)).hom.naturality
          ((swapFunctor (C := C)).map f))

/-- The canonical associator compares translation by a biproduct with
second translation by the second summand followed by the first summand. -/
def translateSecondBiprodIso (A B : C) :
    translateSecondFunctor (A ⊞ B) ≅
      translateSecondFunctor B ⋙ translateSecondFunctor A :=
  NatIso.ofComponents
    (fun X => pairIsoOfCoordinateIsos (Iso.refl X.fst)
      (biprod.associator A B X.snd)) (by
        intro X Y f
        apply (swapEquivalence (C := C)).fullyFaithfulFunctor.map_injective
        dsimp only [swapEquivalence, Equivalence.mk]
        simp only [Functor.map_comp, Functor.comp_map,
          swap_map_translateSecond]
        exact (translateFirstBiprodIso A B).hom.naturality
          ((swapFunctor (C := C)).map f))

omit [HasZeroObject C] in
private theorem mapIso_refl_refl (A Q : C) :
    biprod.mapIso (Iso.refl A) (Iso.refl Q) = Iso.refl (A ⊞ Q) := by
  apply Iso.ext
  apply biprod.hom_ext <;> simp

omit [HasZeroObject C] in
private theorem mapIso_id_trans (A : C) {X Y Z : C} (e : X ≅ Y) (d : Y ≅ Z) :
    biprod.mapIso (Iso.refl A) (e.trans d) =
      (biprod.mapIso (Iso.refl A) e).trans (biprod.mapIso (Iso.refl A) d) := by
  apply Iso.ext
  apply biprod.hom_ext <;> simp

/-- Identity parameter isomorphisms act as identity natural transformations. -/
@[simp]
theorem translateSecondIsoOfIso_refl (A : C) :
    (translateSecondIsoOfIso (Iso.refl A)).hom = 𝟙 (translateSecondFunctor A) := by
  apply NatTrans.ext
  funext X
  change (pairIsoOfCoordinateIsos (X := translateSecondObj A X)
    (Y := translateSecondObj A X) (Iso.refl X.fst)
    (biprod.mapIso (Iso.refl A) (Iso.refl X.snd))).hom = 𝟙 _
  rw [mapIso_refl_refl]
  exact pairIso_refl_hom _

/-- Parameter composition is the composition of the computed natural transformations. -/
theorem translateSecondIsoOfIso_trans {A B D : C} (e : A ≅ B) (d : B ≅ D) :
    (translateSecondIsoOfIso e).hom ≫ (translateSecondIsoOfIso d).hom =
      (translateSecondIsoOfIso (e.trans d)).hom := by
  apply NatTrans.ext
  funext X
  change (pairIsoOfCoordinateIsos (X := translateSecondObj A X)
      (Y := translateSecondObj B X) (Iso.refl X.fst)
      (biprod.mapIso e (Iso.refl X.snd))).hom ≫
    (pairIsoOfCoordinateIsos (X := translateSecondObj B X)
      (Y := translateSecondObj D X) (Iso.refl X.fst)
      (biprod.mapIso d (Iso.refl X.snd))).hom = _
  rw [pairIso_hom_comp]
  have h : (biprod.mapIso e (Iso.refl X.snd)).trans
      (biprod.mapIso d (Iso.refl X.snd)) =
      biprod.mapIso (e.trans d) (Iso.refl X.snd) := by
    apply Iso.ext
    apply biprod.hom_ext <;> simp
  rw [h, Iso.refl_trans]
  rfl

private theorem swap_zero_unit (A Q : C) :
    (swapStabilizerIso A (0 : C) Q).trans
      (biprod.mapIso (Iso.refl A) (isoZeroBiprod (isZero_zero C)).symm) =
      (isoZeroBiprod (X := (0 : C)) (Y := A ⊞ Q) (isZero_zero C)).symm := by
  obtain ⟨e, _, h⟩ := RawHom.translateSecond_id_rel A (⟨(0 : C), Q⟩ : Pair C)
  let e0 : (0 : C) ≅ 0 := e
  have he : e0 = Iso.refl (0 : C) := by
    apply Iso.ext
    exact (isZero_zero C).eq_of_src _ _
  have h0 : (stabilizerIso e0 (A ⊞ Q)).trans
      (isoZeroBiprod (isZero_zero C)).symm =
    (swapStabilizerIso A (0 : C) Q).trans
      (biprod.mapIso (Iso.refl A) (isoZeroBiprod (isZero_zero C)).symm) := h
  rw [he, stabilizerIso_refl, Iso.refl_trans] at h0
  exact h0.symm

private theorem translateSecond_pairIso_hom (A : C) {X Y : Pair C}
    (e : X.fst ≅ Y.fst) (d : X.snd ≅ Y.snd) :
    (translateSecondFunctor A).map
      (pairIsoOfCoordinateIsos (X := X) (Y := Y) e d).hom =
      (pairIsoOfCoordinateIsos (X := translateSecondObj A X)
        (Y := translateSecondObj A Y) e (biprod.mapIso (Iso.refl A) d)).hom := by
  rw [pairIsoOfCoordinateIsos_hom, pairIsoOfCoordinateIsos_hom]
  change Hom.mk ((RawHom.ofCoordinateIsos (X := X) (Y := Y) e d).translateSecond A) =
    Hom.mk (RawHom.ofCoordinateIsos (X := translateSecondObj A X)
      (Y := translateSecondObj A Y) e (biprod.mapIso (Iso.refl A) d))
  apply _root_.Quotient.sound
  refine ⟨Iso.refl (0 : C), ?_, ?_⟩
  · simp only [RawHom.ofCoordinateIsos, RawHom.ofCorePair, RawHom.translateSecond,
      stabilizerIso_refl, Iso.refl_trans, Core.isoMk_hom_iso]
  · simp only [RawHom.ofCoordinateIsos, RawHom.ofCorePair, RawHom.translateSecond,
      stabilizerIso_refl, Iso.refl_trans, Core.isoMk_hom_iso]
    rw [mapIso_id_trans, ← Iso.trans_assoc, swap_zero_unit]

private abbrev secondCoordinateHom (P : C) {Q R : C} (e : Q ≅ R) :
    (⟨P, Q⟩ : Pair C) ⟶ ⟨P, R⟩ :=
  (pairIsoOfCoordinateIsos (X := ⟨P, Q⟩) (Y := ⟨P, R⟩) (Iso.refl P) e).hom

private theorem secondCoordinateHom_comp (P : C) {Q R S : C}
    (e : Q ≅ R) (d : R ≅ S) :
    secondCoordinateHom P e ≫ secondCoordinateHom P d =
      secondCoordinateHom P (e.trans d) := by
  simpa only [secondCoordinateHom, Iso.refl_trans] using
    pairIso_hom_comp (X := ⟨P, Q⟩) (Y := ⟨P, R⟩) (Z := ⟨P, S⟩)
      (Iso.refl P) e (Iso.refl P) d

private theorem translateSecond_secondCoordinateHom (A P : C) {Q R : C}
    (e : Q ≅ R) :
    (translateSecondFunctor A).map (secondCoordinateHom P e) =
      secondCoordinateHom P (biprod.mapIso (Iso.refl A) e) :=
  translateSecond_pairIso_hom A (X := ⟨P, Q⟩) (Y := ⟨P, R⟩) (Iso.refl P) e

omit [HasZeroObject C] in
private theorem parameter_biprod_iso {A A' B B' : C}
    (e : A ≅ A') (d : B ≅ B') (Q : C) :
    (biprod.mapIso (biprod.mapIso e d) (Iso.refl Q)).trans
        (biprod.associator A' B' Q) =
      (biprod.associator A B Q).trans
        ((biprod.mapIso (Iso.refl A) (biprod.mapIso d (Iso.refl Q))).trans
          (biprod.mapIso e (Iso.refl (B' ⊞ Q)))) := by
  apply Iso.ext
  exact coreLeftBiprodBiprodIso_parameter_naturality_component e d (⟨Q⟩ : Core C)

private theorem leftUnit_biprod_iso (A Q : C) :
    (biprod.associator (0 : C) A Q).trans
        (isoZeroBiprod (X := (0 : C)) (Y := A ⊞ Q) (isZero_zero C)).symm =
      biprod.mapIso (isoZeroBiprod (X := (0 : C)) (Y := A) (isZero_zero C)).symm
        (Iso.refl Q) := by
  apply Iso.ext
  exact coreLeftBiprodBiprodIso_leftUnit_component A Q

private theorem rightUnit_biprod_iso (A Q : C) :
    (biprod.associator A (0 : C) Q).trans
        (biprod.mapIso (Iso.refl A)
          (isoZeroBiprod (X := (0 : C)) (Y := Q) (isZero_zero C)).symm) =
      biprod.mapIso (isoBiprodZero (X := A) (Y := (0 : C)) (isZero_zero C)).symm
        (Iso.refl Q) := by
  apply Iso.ext
  exact coreLeftBiprodBiprodIso_rightUnit_component A Q

omit [HasZeroObject C] in
private theorem pentagon_biprod_iso (A B D Q : C) :
    (biprod.associator (A ⊞ B) D Q).trans (biprod.associator A B (D ⊞ Q)) =
      (biprod.mapIso (biprod.associator A B D) (Iso.refl Q)).trans
        ((biprod.associator A (B ⊞ D) Q).trans
          (biprod.mapIso (Iso.refl A) (biprod.associator B D Q))) := by
  apply Iso.ext
  exact coreLeftBiprodBiprodIso_pentagon_component A B D Q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The multiplication comparison is natural in both translating objects. -/
theorem translateSecondBiprodIso_parameter_naturality
    {A A' B B' : C} (e : A ≅ A') (d : B ≅ B') :
    translateSecondIsoOfIso (biprod.mapIso e d) ≪≫ translateSecondBiprodIso A' B' =
      translateSecondBiprodIso A B ≪≫
        Functor.isoWhiskerRight (translateSecondIsoOfIso d) (translateSecondFunctor A) ≪≫
        Functor.isoWhiskerLeft (translateSecondFunctor B') (translateSecondIsoOfIso e) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change secondCoordinateHom X.fst (biprod.mapIso (biprod.mapIso e d) (Iso.refl X.snd)) ≫
      secondCoordinateHom X.fst (biprod.associator A' B' X.snd) =
    secondCoordinateHom X.fst (biprod.associator A B X.snd) ≫
      (translateSecondFunctor A).map
        (secondCoordinateHom X.fst (biprod.mapIso d (Iso.refl X.snd))) ≫
      secondCoordinateHom X.fst (biprod.mapIso e (Iso.refl (B' ⊞ X.snd)))
  rw [translateSecond_secondCoordinateHom, secondCoordinateHom_comp,
    secondCoordinateHom_comp, secondCoordinateHom_comp, parameter_biprod_iso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The zero-first-parameter triangle uses the canonical left zero unitor. -/
theorem translateSecondBiprodIso_leftUnit (A : C) :
    translateSecondBiprodIso (0 : C) A ≪≫
        Functor.isoWhiskerLeft (translateSecondFunctor A) translateSecondZeroIso ≪≫
        Functor.rightUnitor (translateSecondFunctor A) =
      translateSecondIsoOfIso (isoZeroBiprod (X := (0 : C)) (Y := A)
        (isZero_zero C)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change secondCoordinateHom X.fst (biprod.associator (0 : C) A X.snd) ≫
      secondCoordinateHom X.fst
        (isoZeroBiprod (X := (0 : C)) (Y := A ⊞ X.snd) (isZero_zero C)).symm ≫ 𝟙 _ =
    secondCoordinateHom X.fst
      (biprod.mapIso (isoZeroBiprod (X := (0 : C)) (Y := A) (isZero_zero C)).symm
        (Iso.refl X.snd))
  rw [Category.comp_id, secondCoordinateHom_comp, leftUnit_biprod_iso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The zero-second-parameter triangle uses the canonical right zero unitor. -/
theorem translateSecondBiprodIso_rightUnit (A : C) :
    translateSecondBiprodIso A (0 : C) ≪≫
        Functor.isoWhiskerRight translateSecondZeroIso (translateSecondFunctor A) ≪≫
        Functor.leftUnitor (translateSecondFunctor A) =
      translateSecondIsoOfIso (isoBiprodZero (X := A) (Y := (0 : C))
        (isZero_zero C)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change secondCoordinateHom X.fst (biprod.associator A (0 : C) X.snd) ≫
      (translateSecondFunctor A).map (secondCoordinateHom X.fst
        (isoZeroBiprod (X := (0 : C)) (Y := X.snd) (isZero_zero C)).symm) ≫ 𝟙 _ =
    secondCoordinateHom X.fst
      (biprod.mapIso (isoBiprodZero (X := A) (Y := (0 : C)) (isZero_zero C)).symm
        (Iso.refl X.snd))
  rw [Category.comp_id, translateSecond_secondCoordinateHom,
    secondCoordinateHom_comp, rightUnit_biprod_iso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two canonical associator routes agree for three translating objects. -/
theorem translateSecondBiprodIso_pentagon (A B D : C) :
    translateSecondBiprodIso (A ⊞ B) D ≪≫
        Functor.isoWhiskerLeft (translateSecondFunctor D) (translateSecondBiprodIso A B) =
      translateSecondIsoOfIso (biprod.associator A B D) ≪≫
        translateSecondBiprodIso A (B ⊞ D) ≪≫
        Functor.isoWhiskerRight (translateSecondBiprodIso B D) (translateSecondFunctor A) ≪≫
        Functor.associator (translateSecondFunctor D) (translateSecondFunctor B)
          (translateSecondFunctor A) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change secondCoordinateHom X.fst (biprod.associator (A ⊞ B) D X.snd) ≫
      secondCoordinateHom X.fst (biprod.associator A B (D ⊞ X.snd)) =
    secondCoordinateHom X.fst (biprod.mapIso (biprod.associator A B D) (Iso.refl X.snd)) ≫
      secondCoordinateHom X.fst (biprod.associator A (B ⊞ D) X.snd) ≫
      (translateSecondFunctor A).map
        (secondCoordinateHom X.fst (biprod.associator B D X.snd)) ≫ 𝟙 _
  rw [Category.comp_id, translateSecond_secondCoordinateHom,
    secondCoordinateHom_comp, secondCoordinateHom_comp, secondCoordinateHom_comp,
    pentagon_biprod_iso]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Parameter isomorphisms lift to the actual second-translation comma functors. -/
def secondTranslationCostructuredIsoOfIso {A A' : C} (e : A ≅ A')
    (B : Translation C) :
    secondTranslationCostructuredMap A B ≅ secondTranslationCostructuredMap A' B :=
  NatIso.ofComponents
    (fun X => CostructuredArrow.isoMk ((translateSecondIsoOfIso e).app X.left) (by
      simp [secondTranslationCostructuredMap,
        secondTranslationProjectionNatTrans, translateSecondIsoOfIso]
      simpa only [pairIsoOfCoordinateIsos_hom] using
        (congrArg (fun k => k ≫ X.hom)
          (translationProjection_pairIsoSecond X.left.fst
            (biprod.mapIso e (Iso.refl X.left.snd)))).trans (Category.id_comp X.hom))) (by
      intro X Y f
      apply CostructuredArrow.ext
      exact (translateSecondIsoOfIso e).hom.naturality f.left)

/-- The scalar comma component is the prescribed zero-stabilizer pair component. -/
@[simp]
theorem secondTranslationCostructuredIsoOfIso_hom_app_left
    {A A' : C} (e : A ≅ A') (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((secondTranslationCostructuredIsoOfIso e B).hom.app X).left =
      (translateSecondIsoOfIso e).hom.app X.left := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical zero-unitor comparison lifts to every right-comma category. -/
def secondTranslationCostructuredZeroIso (B : Translation C) :
    secondTranslationCostructuredMap (0 : C) B ≅
      𝟭 (CostructuredArrow (translationProjection (C := C)) B) :=
  NatIso.ofComponents
    (fun X => CostructuredArrow.isoMk ((translateSecondZeroIso (C := C)).app X.left) (by
      simp [secondTranslationCostructuredMap,
        secondTranslationProjectionNatTrans, translateSecondZeroIso]
      simpa only [pairIsoOfCoordinateIsos_hom] using
        (congrArg (fun k => k ≫ X.hom)
          (translationProjection_pairIsoSecond X.left.fst
            (isoZeroBiprod (X := (0 : C)) (Y := X.left.snd) (isZero_zero C)).symm)).trans
              (Category.id_comp X.hom))) (by
      intro X Y f
      apply CostructuredArrow.ext
      exact (translateSecondZeroIso (C := C)).hom.naturality f.left)

/-- The comma zero comparison has the canonical pair zero-unitor component. -/
@[simp]
theorem secondTranslationCostructuredZeroIso_hom_app_left
    (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((secondTranslationCostructuredZeroIso B).hom.app X).left =
      (translateSecondZeroIso (C := C)).hom.app X.left := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The biproduct associator lifts to the actual right-comma translations. -/
def secondTranslationCostructuredBiprodIso (A A' : C) (B : Translation C) :
    secondTranslationCostructuredMap (A ⊞ A') B ≅
      secondTranslationCostructuredMap A' B ⋙ secondTranslationCostructuredMap A B :=
  NatIso.ofComponents
    (fun X => CostructuredArrow.isoMk ((translateSecondBiprodIso A A').app X.left) (by
      simp [secondTranslationCostructuredMap,
        secondTranslationProjectionNatTrans, translateSecondBiprodIso]
      simpa only [pairIsoOfCoordinateIsos_hom] using
        (congrArg (fun k => k ≫ X.hom)
          (translationProjection_pairIsoSecond X.left.fst
            (biprod.associator A A' X.left.snd))).trans (Category.id_comp X.hom))) (by
      intro X Y f
      apply CostructuredArrow.ext
      exact (translateSecondBiprodIso A A').hom.naturality f.left)

/-- The comma multiplication comparison has the canonical pair associator component. -/
@[simp]
theorem secondTranslationCostructuredBiprodIso_hom_app_left
    (A A' : C) (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    ((secondTranslationCostructuredBiprodIso A A' B).hom.app X).left =
      (translateSecondBiprodIso A A').hom.app X.left := rfl

/-- Identity translating-object isomorphisms give identity comma transformations. -/
@[simp]
theorem secondTranslationCostructuredIsoOfIso_refl (A : C) (B : Translation C) :
    (secondTranslationCostructuredIsoOfIso (Iso.refl A) B).hom =
      𝟙 (secondTranslationCostructuredMap A B) := by
  apply NatTrans.ext
  funext X
  apply CostructuredArrow.ext
  change (translateSecondIsoOfIso (Iso.refl A)).hom.app X.left = 𝟙 _
  rw [translateSecondIsoOfIso_refl]
  rfl

/-- Composition of parameter isomorphisms is composition of comma transformations. -/
theorem secondTranslationCostructuredIsoOfIso_trans
    {A A' A'' : C} (e : A ≅ A') (d : A' ≅ A'') (B : Translation C) :
    (secondTranslationCostructuredIsoOfIso e B).hom ≫
        (secondTranslationCostructuredIsoOfIso d B).hom =
      (secondTranslationCostructuredIsoOfIso (e.trans d) B).hom := by
  apply NatTrans.ext
  funext X
  apply CostructuredArrow.ext
  exact congrArg (fun α => α.app X.left) (translateSecondIsoOfIso_trans e d)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Comma multiplication is natural in both translating-object isomorphisms. -/
theorem secondTranslationCostructuredBiprodIso_parameter_naturality
    {A A' D D' : C} (e : A ≅ A') (d : D ≅ D') (B : Translation C) :
    secondTranslationCostructuredIsoOfIso (biprod.mapIso e d) B ≪≫
        secondTranslationCostructuredBiprodIso A' D' B =
      secondTranslationCostructuredBiprodIso A D B ≪≫
        Functor.isoWhiskerRight (secondTranslationCostructuredIsoOfIso d B)
          (secondTranslationCostructuredMap A B) ≪≫
        Functor.isoWhiskerLeft (secondTranslationCostructuredMap D' B)
          (secondTranslationCostructuredIsoOfIso e B) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply CostructuredArrow.ext
  exact congrArg (fun i => i.hom.app X.left)
    (translateSecondBiprodIso_parameter_naturality e d)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The left zero-unit triangle holds in every actual right-comma category. -/
theorem secondTranslationCostructuredBiprodIso_leftUnit (A : C) (B : Translation C) :
    secondTranslationCostructuredBiprodIso (0 : C) A B ≪≫
        Functor.isoWhiskerLeft (secondTranslationCostructuredMap A B)
          (secondTranslationCostructuredZeroIso B) ≪≫
        Functor.rightUnitor (secondTranslationCostructuredMap A B) =
      secondTranslationCostructuredIsoOfIso
        (isoZeroBiprod (X := (0 : C)) (Y := A) (isZero_zero C)).symm B := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply CostructuredArrow.ext
  exact congrArg (fun i => i.hom.app X.left) (translateSecondBiprodIso_leftUnit A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The right zero-unit triangle holds in every actual right-comma category. -/
theorem secondTranslationCostructuredBiprodIso_rightUnit (A : C) (B : Translation C) :
    secondTranslationCostructuredBiprodIso A (0 : C) B ≪≫
        Functor.isoWhiskerRight (secondTranslationCostructuredZeroIso B)
          (secondTranslationCostructuredMap A B) ≪≫
        Functor.leftUnitor (secondTranslationCostructuredMap A B) =
      secondTranslationCostructuredIsoOfIso
        (isoBiprodZero (X := A) (Y := (0 : C)) (isZero_zero C)).symm B := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply CostructuredArrow.ext
  exact congrArg (fun i => i.hom.app X.left) (translateSecondBiprodIso_rightUnit A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Associativity pentagon coherence holds in every actual right-comma category. -/
theorem secondTranslationCostructuredBiprodIso_pentagon
    (A D E : C) (B : Translation C) :
    secondTranslationCostructuredBiprodIso (A ⊞ D) E B ≪≫
        Functor.isoWhiskerLeft (secondTranslationCostructuredMap E B)
          (secondTranslationCostructuredBiprodIso A D B) =
      secondTranslationCostructuredIsoOfIso (biprod.associator A D E) B ≪≫
        secondTranslationCostructuredBiprodIso A (D ⊞ E) B ≪≫
        Functor.isoWhiskerRight (secondTranslationCostructuredBiprodIso D E B)
          (secondTranslationCostructuredMap A B) ≪≫
        Functor.associator (secondTranslationCostructuredMap E B)
          (secondTranslationCostructuredMap D B) (secondTranslationCostructuredMap A B) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply CostructuredArrow.ext
  exact congrArg (fun i => i.hom.app X.left) (translateSecondBiprodIso_pentagon A D E)

/-- Parameter isomorphisms satisfy the exchange law for successive comma translations. -/
theorem secondTranslationCostructuredIsoOfIso_exchange
    {A A' D D' : C} (e : A ≅ A') (d : D ≅ D') (B : Translation C)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (secondTranslationCostructuredMap A B).map
          ((secondTranslationCostructuredIsoOfIso d B).hom.app X) ≫
        (secondTranslationCostructuredIsoOfIso e B).hom.app
          ((secondTranslationCostructuredMap D' B).obj X) =
      (secondTranslationCostructuredIsoOfIso e B).hom.app
          ((secondTranslationCostructuredMap D B).obj X) ≫
        (secondTranslationCostructuredMap A' B).map
          ((secondTranslationCostructuredIsoOfIso d B).hom.app X) :=
  (secondTranslationCostructuredIsoOfIso e B).hom.naturality _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Base change commutes with the canonical scalar comparison, including its lineators. -/
theorem secondTranslationCostructuredIsoOfIso_baseChange
    {A A' : C} (e : A ≅ A') {B D : Translation C} (g : B ⟶ D)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (secondTranslationCostructuredMapNaturalityIso A g).hom.app X ≫
        (CostructuredArrow.map g).map
          ((secondTranslationCostructuredIsoOfIso e B).hom.app X) =
      (secondTranslationCostructuredIsoOfIso e D).hom.app
          ((CostructuredArrow.map g).obj X) ≫
        (secondTranslationCostructuredMapNaturalityIso A' g).hom.app X := by
  apply CostructuredArrow.ext
  change 𝟙 _ ≫ (translateSecondIsoOfIso e).hom.app X.left =
    (translateSecondIsoOfIso e).hom.app X.left ≫ 𝟙 _
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Base change commutes with the canonical zero-unitor comparison. -/
theorem secondTranslationCostructuredZeroIso_baseChange
    {B D : Translation C} (g : B ⟶ D)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (secondTranslationCostructuredMapNaturalityIso (0 : C) g).hom.app X ≫
        (CostructuredArrow.map g).map ((secondTranslationCostructuredZeroIso B).hom.app X) =
      (secondTranslationCostructuredZeroIso D).hom.app
        ((CostructuredArrow.map g).obj X) := by
  apply CostructuredArrow.ext
  change 𝟙 _ ≫ (translateSecondZeroIso (C := C)).hom.app X.left =
    (translateSecondZeroIso (C := C)).hom.app X.left
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Base change respects the multiplication comparison and both iterated lineators. -/
theorem secondTranslationCostructuredBiprodIso_baseChange
    (A A' : C) {B D : Translation C} (g : B ⟶ D)
    (X : CostructuredArrow (translationProjection (C := C)) B) :
    (secondTranslationCostructuredMapNaturalityIso (A ⊞ A') g).hom.app X ≫
        (CostructuredArrow.map g).map
          ((secondTranslationCostructuredBiprodIso A A' B).hom.app X) =
      (secondTranslationCostructuredBiprodIso A A' D).hom.app
          ((CostructuredArrow.map g).obj X) ≫
        (secondTranslationCostructuredMap A D).map
          ((secondTranslationCostructuredMapNaturalityIso A' g).hom.app X) ≫
        (secondTranslationCostructuredMapNaturalityIso A g).hom.app
          ((secondTranslationCostructuredMap A' B).obj X) := by
  apply CostructuredArrow.ext
  change 𝟙 _ ≫ (translateSecondBiprodIso A A').hom.app X.left =
    (translateSecondBiprodIso A A').hom.app X.left ≫
      (translateSecondFunctor A).map (𝟙 _) ≫ 𝟙 _
  rw [Functor.map_id]
  simp

private theorem eqToHom_functorApp_left {B D : Translation C}
    {F G : CostructuredArrow (translationProjection (C := C)) B ⥤
      CostructuredArrow (translationProjection (C := C)) D}
    (h : F = G) (X : CostructuredArrow (translationProjection (C := C)) B)
    (hleft : (F.obj X).left = (G.obj X).left) :
    ((eqToHom h).app X).left = eqToHom hleft := by
  cases h
  rw [show hleft = rfl from Subsingleton.elim _ _]
  rfl

private theorem nerveHomotopyMap_eq_of_functor_eq
    {I J : Type w} [Category.{wv} I] [Category.{wv} J]
    {F F' G G' : I ⥤ J} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G')
    (h : eqToHom hF ≫ β = α ≫ eqToHom hG) :
    NatTrans.nerveHomotopyMap α = NatTrans.nerveHomotopyMap β := by
  cases hF
  cases hG
  have hh : β = α := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h
  exact congrArg NatTrans.nerveHomotopyMap hh.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar-comparison cylinder is strictly natural under right-comma base change. -/
theorem secondTranslationCostructuredIsoOfIso_nerveMap_baseChange
    {A A' : C} (e : A ≅ A') {B D : Translation C} (g : B ⟶ D) :
    (nerveMap (CostructuredArrow.map (S := translationProjection (C := C)) g) ▷
        (Δ[1] : SSet.{max u v})) ≫
        NatTrans.nerveHomotopyMap (secondTranslationCostructuredIsoOfIso e D).hom =
      NatTrans.nerveHomotopyMap (secondTranslationCostructuredIsoOfIso e B).hom ≫
        nerveMap (CostructuredArrow.map (S := translationProjection (C := C)) g) := by
  rw [NatTrans.nerveHomotopyMap_precomp, NatTrans.nerveHomotopyMap_postcomp]
  apply nerveHomotopyMap_eq_of_functor_eq
    (secondTranslationCostructuredMap_naturality A g)
    (secondTranslationCostructuredMap_naturality A' g)
  apply NatTrans.ext
  funext X
  apply CostructuredArrow.ext
  have hs := eqToHom_functorApp_left
    (secondTranslationCostructuredMap_naturality A g) X rfl
  have ht := eqToHom_functorApp_left
    (secondTranslationCostructuredMap_naturality A' g) X rfl
  change ((eqToHom (secondTranslationCostructuredMap_naturality A g)).app X).left ≫
      (translateSecondIsoOfIso e).hom.app X.left =
    (translateSecondIsoOfIso e).hom.app X.left ≫
      ((eqToHom (secondTranslationCostructuredMap_naturality A' g)).app X).left
  rw [hs, ht]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The zero-unitor cylinder is strictly natural under right-comma base change. -/
theorem secondTranslationCostructuredZeroIso_nerveMap_baseChange
    {B D : Translation C} (g : B ⟶ D) :
    (nerveMap (CostructuredArrow.map (S := translationProjection (C := C)) g) ▷
        (Δ[1] : SSet.{max u v})) ≫
        NatTrans.nerveHomotopyMap (secondTranslationCostructuredZeroIso D).hom =
      NatTrans.nerveHomotopyMap (secondTranslationCostructuredZeroIso B).hom ≫
        nerveMap (CostructuredArrow.map (S := translationProjection (C := C)) g) := by
  rw [NatTrans.nerveHomotopyMap_precomp, NatTrans.nerveHomotopyMap_postcomp]
  let hG :
      CostructuredArrow.map (S := translationProjection (C := C)) g ⋙
          𝟭 (CostructuredArrow (translationProjection (C := C)) D) =
        𝟭 (CostructuredArrow (translationProjection (C := C)) B) ⋙
          CostructuredArrow.map g := rfl
  apply nerveHomotopyMap_eq_of_functor_eq
    (secondTranslationCostructuredMap_naturality (0 : C) g) hG
  apply NatTrans.ext
  funext X
  apply CostructuredArrow.ext
  have hs := eqToHom_functorApp_left
    (secondTranslationCostructuredMap_naturality (0 : C) g) X rfl
  have ht := eqToHom_functorApp_left hG X rfl
  change ((eqToHom (secondTranslationCostructuredMap_naturality (0 : C) g)).app X).left ≫
      (translateSecondZeroIso (C := C)).hom.app X.left =
    (translateSecondZeroIso (C := C)).hom.app X.left ≫ ((eqToHom hG).app X).left
  rw [hs, ht]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The multiplication cylinder is strictly natural under right-comma base change. -/
theorem secondTranslationCostructuredBiprodIso_nerveMap_baseChange
    (A A' : C) {B D : Translation C} (g : B ⟶ D) :
    (nerveMap (CostructuredArrow.map (S := translationProjection (C := C)) g) ▷
        (Δ[1] : SSet.{max u v})) ≫
        NatTrans.nerveHomotopyMap (secondTranslationCostructuredBiprodIso A A' D).hom =
      NatTrans.nerveHomotopyMap (secondTranslationCostructuredBiprodIso A A' B).hom ≫
        nerveMap (CostructuredArrow.map (S := translationProjection (C := C)) g) := by
  rw [NatTrans.nerveHomotopyMap_precomp, NatTrans.nerveHomotopyMap_postcomp]
  let hG :
      CostructuredArrow.map (S := translationProjection (C := C)) g ⋙
          (secondTranslationCostructuredMap A' D ⋙ secondTranslationCostructuredMap A D) =
        (secondTranslationCostructuredMap A' B ⋙ secondTranslationCostructuredMap A B) ⋙
          CostructuredArrow.map g := by
    calc
      _ = (CostructuredArrow.map g ⋙ secondTranslationCostructuredMap A' D) ⋙
          secondTranslationCostructuredMap A D := rfl
      _ = (secondTranslationCostructuredMap A' B ⋙ CostructuredArrow.map g) ⋙
          secondTranslationCostructuredMap A D := by
        rw [secondTranslationCostructuredMap_naturality A' g]
      _ = secondTranslationCostructuredMap A' B ⋙
          (CostructuredArrow.map g ⋙ secondTranslationCostructuredMap A D) := rfl
      _ = secondTranslationCostructuredMap A' B ⋙
          (secondTranslationCostructuredMap A B ⋙ CostructuredArrow.map g) := by
        rw [secondTranslationCostructuredMap_naturality A g]
      _ = _ := rfl
  apply nerveHomotopyMap_eq_of_functor_eq
    (secondTranslationCostructuredMap_naturality (A ⊞ A') g) hG
  apply NatTrans.ext
  funext X
  apply CostructuredArrow.ext
  have hs := eqToHom_functorApp_left
    (secondTranslationCostructuredMap_naturality (A ⊞ A') g) X rfl
  have ht := eqToHom_functorApp_left hG X rfl
  change ((eqToHom (secondTranslationCostructuredMap_naturality (A ⊞ A') g)).app X).left ≫
      (translateSecondBiprodIso A A').hom.app X.left =
    (translateSecondBiprodIso A A').hom.app X.left ≫ ((eqToHom hG).app X).left
  rw [hs, ht]
  simp

section SmallUniverse

variable {C₀ : Type u} [Category.{u} C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀]

/-- Isomorphic scalar objects give homotopic maps of each right-comma nerve. -/
def secondTranslationRightCommaScalarHomotopy {A A' : C₀} (e : A ≅ A')
    (B : Translation C₀) :
    SSet.Homotopy
      ((secondTranslationRightCommaNerveDiagramNatTrans A).app B)
      ((secondTranslationRightCommaNerveDiagramNatTrans A').app B) :=
  NatTrans.nerveHomotopy (secondTranslationCostructuredIsoOfIso e B).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Translation by zero is homotopic to the identity on each right-comma nerve. -/
def secondTranslationRightCommaZeroHomotopy (B : Translation C₀) :
    SSet.Homotopy
      ((secondTranslationRightCommaNerveDiagramNatTrans (0 : C₀)).app B)
      (𝟙 (nerve (CostructuredArrow (translationProjection (C := C₀)) B))) := by
  simpa only [secondTranslationRightCommaNerveDiagramNatTrans_app, nerveMap_id] using
    NatTrans.nerveHomotopy (secondTranslationCostructuredZeroIso B).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Multiplication of scalar objects gives the corresponding nerve homotopy. -/
def secondTranslationRightCommaBiprodHomotopy (A A' : C₀) (B : Translation C₀) :
    SSet.Homotopy
      ((secondTranslationRightCommaNerveDiagramNatTrans (A ⊞ A')).app B)
      ((secondTranslationRightCommaNerveDiagramNatTrans A').app B ≫
        (secondTranslationRightCommaNerveDiagramNatTrans A).app B) := by
  simpa only [secondTranslationRightCommaNerveDiagramNatTrans_app, nerveMap_comp] using
    NatTrans.nerveHomotopy (secondTranslationCostructuredBiprodIso A A' B).hom

end SmallUniverse

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coordinate swap strictly conjugates the actual second translation to
the actual first translation. -/
theorem translateSecondFunctor_comp_swapFunctor (A : C) :
    translateSecondFunctor A ⋙ swapFunctor (C := C) =
      swapFunctor (C := C) ⋙ translateFirstFunctor A := by
  refine Functor.ext
    (F := translateSecondFunctor A ⋙ swapFunctor (C := C))
    (G := swapFunctor (C := C) ⋙ translateFirstFunctor A) (fun _ => rfl) ?_
  intro X Y f
  simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    swap_map_translateSecond A f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical coordinate-swap translation comparison. -/
def translateSecondSwapIso (A : C) :
    translateSecondFunctor A ⋙ swapFunctor (C := C) ≅
      swapFunctor (C := C) ⋙ translateFirstFunctor A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    simpa only [Functor.comp_map, Iso.refl_hom, Category.id_comp, Category.comp_id] using
      swap_map_translateSecond A f)

/-- The comparison preserves the literal translated pair at every object. -/
@[simp]
theorem translateSecondSwapIso_hom_app (A : C) (X : Pair C) :
    (translateSecondSwapIso A).hom.app X = 𝟙 _ := rfl

end CategoryTheory.SInverseS

end
