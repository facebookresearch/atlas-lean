/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CompactlyGenerated.CartesianClosed
public import Mathlib.Topology.Homeomorph.Quotient

/-!
# Quotient products of compactly generated spaces

Products in the compactly generated category preserve quotient maps without
local compactness or separation hypotheses.  The key homeomorphism is the
native form of Strickland's quotient-product theorem.
-/

public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology MonoidalCategory

universe u v

namespace CompactlyGenerated

private noncomputable def binaryKificationIso
    (X Y : CompactlyGenerated.{u, v}) :
    TopCat.toCompactlyGenerated.obj
        (TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y))) ≅ X ⊗ Y := by
  let PF : ULift.{v} WalkingPair → CompactlyGenerated.{u, v}
    | ⟨WalkingPair.left⟩ => X
    | ⟨WalkingPair.right⟩ => Y
  let hp :
      ((TopCat.piFan (fun j => compactlyGeneratedToTop.obj (PF j))).pt : Type v) ≃ₜ
        ↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y) :=
    { toEquiv :=
        { toFun := fun g =>
            (show X from g (ULift.up WalkingPair.left),
              show Y from g (ULift.up WalkingPair.right))
          invFun := fun p j => match j with
            | ⟨WalkingPair.left⟩ => p.1
            | ⟨WalkingPair.right⟩ => p.2
          left_inv := fun g => by
            funext j
            rcases j with ⟨_ | _⟩ <;> rfl
          right_inv := fun p => by rcases p with ⟨x, y⟩; rfl }
      continuous_toFun :=
        (continuous_apply (ULift.up WalkingPair.left)).prodMk
          (continuous_apply (ULift.up WalkingPair.right))
      continuous_invFun := by
        apply continuous_pi
        intro j
        rcases j with ⟨_ | _⟩
        · exact continuous_fst
        · exact continuous_snd }
  let eTensor : (∏ᶜ PF) ≅ X ⊗ Y := by
    let c : Fan PF := Fan.mk (X ⊗ Y) (fun j => match j with
      | ⟨WalkingPair.left⟩ => CartesianMonoidalCategory.fst X Y
      | ⟨WalkingPair.right⟩ => CartesianMonoidalCategory.snd X Y)
    let hc : IsLimit c := by
      refine
        { lift := fun s => CartesianMonoidalCategory.lift
            (s.π.app ⟨ULift.up WalkingPair.left⟩)
            (s.π.app ⟨ULift.up WalkingPair.right⟩)
          fac := ?_
          uniq := ?_ }
      · rintro s ⟨⟨j⟩⟩
        cases j
        · exact CartesianMonoidalCategory.lift_fst _ _
        · exact CartesianMonoidalCategory.lift_snd _ _
      · intro s m hm
        apply CartesianMonoidalCategory.hom_ext
        · exact (hm ⟨ULift.up WalkingPair.left⟩).trans
            (CartesianMonoidalCategory.lift_fst _ _).symm
        · exact (hm ⟨ULift.up WalkingPair.right⟩).trans
            (CartesianMonoidalCategory.lift_snd _ _).symm
    exact (limit.isLimit _).conePointUniqueUpToIso hc
  exact
    TopCat.toCompactlyGenerated.mapIso
        (TopCat.isoOfHomeo hp.symm) ≪≫
      (piIsoPi PF).symm ≪≫ eTensor

private theorem binaryKificationIso_hom_proj
    (X Y : CompactlyGenerated.{u, v}) :
    ((binaryKificationIso X Y).hom ≫
          CartesianMonoidalCategory.fst X Y =
        TopCat.toCompactlyGenerated.map
            (TopCat.prodFst : TopCat.of
              (↥(compactlyGeneratedToTop.obj X) ×
                ↥(compactlyGeneratedToTop.obj Y)) ⟶
              compactlyGeneratedToTop.obj X) ≫
          (asIso (adj.unit.app X)).inv) ∧
      ((binaryKificationIso X Y).hom ≫
          CartesianMonoidalCategory.snd X Y =
        TopCat.toCompactlyGenerated.map
            (TopCat.prodSnd : TopCat.of
              (↥(compactlyGeneratedToTop.obj X) ×
                ↥(compactlyGeneratedToTop.obj Y)) ⟶
              compactlyGeneratedToTop.obj Y) ≫
          (asIso (adj.unit.app Y)).inv) := by
  let PF : ULift.{v} WalkingPair → CompactlyGenerated.{u, v}
    | ⟨WalkingPair.left⟩ => X
    | ⟨WalkingPair.right⟩ => Y
  let hp :
      ((TopCat.piFan (fun j => compactlyGeneratedToTop.obj (PF j))).pt : Type v) ≃ₜ
        ↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y) :=
    { toEquiv :=
        { toFun := fun g =>
            (show X from g (ULift.up WalkingPair.left),
              show Y from g (ULift.up WalkingPair.right))
          invFun := fun p j => match j with
            | ⟨WalkingPair.left⟩ => p.1
            | ⟨WalkingPair.right⟩ => p.2
          left_inv := fun g => by
            funext j
            rcases j with ⟨_ | _⟩ <;> rfl
          right_inv := fun p => by rcases p with ⟨x, y⟩; rfl }
      continuous_toFun :=
        (continuous_apply (ULift.up WalkingPair.left)).prodMk
          (continuous_apply (ULift.up WalkingPair.right))
      continuous_invFun := by
        apply continuous_pi
        intro j
        rcases j with ⟨_ | _⟩
        · exact continuous_fst
        · exact continuous_snd }
  let eTensor : (∏ᶜ PF) ≅ X ⊗ Y := by
    let c : Fan PF := Fan.mk (X ⊗ Y) (fun j => match j with
      | ⟨WalkingPair.left⟩ => CartesianMonoidalCategory.fst X Y
      | ⟨WalkingPair.right⟩ => CartesianMonoidalCategory.snd X Y)
    let hc : IsLimit c := by
      refine
        { lift := fun s => CartesianMonoidalCategory.lift
            (s.π.app ⟨ULift.up WalkingPair.left⟩)
            (s.π.app ⟨ULift.up WalkingPair.right⟩)
          fac := ?_
          uniq := ?_ }
      · rintro s ⟨⟨j⟩⟩
        cases j
        · exact CartesianMonoidalCategory.lift_fst _ _
        · exact CartesianMonoidalCategory.lift_snd _ _
      · intro s m hm
        apply CartesianMonoidalCategory.hom_ext
        · exact (hm ⟨ULift.up WalkingPair.left⟩).trans
            (CartesianMonoidalCategory.lift_fst _ _).symm
        · exact (hm ⟨ULift.up WalkingPair.right⟩).trans
            (CartesianMonoidalCategory.lift_snd _ _).symm
    exact (limit.isLimit _).conePointUniqueUpToIso hc
  constructor
  · let h : TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
        ↥(compactlyGeneratedToTop.obj Y)) ⟶
        (TopCat.piFan (fun j => compactlyGeneratedToTop.obj (PF j))).pt :=
      (TopCat.isoOfHomeo hp.symm).hom
    have hRaw : h ≫ (TopCat.piFan (fun j => compactlyGeneratedToTop.obj
        (PF j))).π.app
        ⟨ULift.up WalkingPair.left⟩ = TopCat.prodFst := by
      apply TopCat.hom_ext
      ext p
      rfl
    have hTensor : eTensor.hom ≫
        CartesianMonoidalCategory.fst X Y =
      Pi.π PF (ULift.up WalkingPair.left) := by
      apply (cancel_epi eTensor.inv).1
      simp [eTensor]
    have hPi : (piIsoPi PF).symm.hom ≫
          Pi.π PF (ULift.up WalkingPair.left) =
        piπ PF (ULift.up WalkingPair.left) :=
      IsLimit.conePointUniqueUpToIso_inv_comp
        (limit.isLimit _) (piFanIsLimit PF)
        ⟨ULift.up WalkingPair.left⟩
    simp only [binaryKificationIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    rw [hTensor, hPi]
    calc
      _ = TopCat.toCompactlyGenerated.map h ≫
          piπ PF (ULift.up WalkingPair.left) := rfl
      _ = _ := by
        unfold piπ
        rw [← Category.assoc, ← TopCat.toCompactlyGenerated.map_comp, hRaw]
  · let h : TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
        ↥(compactlyGeneratedToTop.obj Y)) ⟶
        (TopCat.piFan (fun j => compactlyGeneratedToTop.obj (PF j))).pt :=
      (TopCat.isoOfHomeo hp.symm).hom
    have hRaw : h ≫ (TopCat.piFan (fun j => compactlyGeneratedToTop.obj
        (PF j))).π.app
        ⟨ULift.up WalkingPair.right⟩ = TopCat.prodSnd := by
      apply TopCat.hom_ext
      ext p
      rfl
    have hTensor : eTensor.hom ≫
        CartesianMonoidalCategory.snd X Y =
      Pi.π PF (ULift.up WalkingPair.right) := by
      apply (cancel_epi eTensor.inv).1
      simp [eTensor]
    have hPi : (piIsoPi PF).symm.hom ≫
          Pi.π PF (ULift.up WalkingPair.right) =
        piπ PF (ULift.up WalkingPair.right) :=
      IsLimit.conePointUniqueUpToIso_inv_comp
        (limit.isLimit _) (piFanIsLimit PF)
        ⟨ULift.up WalkingPair.right⟩
    simp only [binaryKificationIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    rw [hTensor, hPi]
    calc
      _ = TopCat.toCompactlyGenerated.map h ≫
          piπ PF (ULift.up WalkingPair.right) := rfl
      _ = _ := by
        unfold piπ
        rw [← Category.assoc, ← TopCat.toCompactlyGenerated.map_comp, hRaw]

private theorem binaryKificationIso_braiding
    [BraidedCategory CompactlyGenerated.{u, v}]
    (X Y : CompactlyGenerated.{u, v}) :
    (binaryKificationIso Y X).hom ≫ (β_ Y X).hom =
      TopCat.toCompactlyGenerated.map (TopCat.ofHom
          ⟨fun p : ↥(compactlyGeneratedToTop.obj Y) ×
              ↥(compactlyGeneratedToTop.obj X) => (p.2, p.1),
            continuous_snd.prodMk continuous_fst⟩) ≫
        (binaryKificationIso X Y).hom := by
  let swap : TopCat.toCompactlyGenerated.obj
        (TopCat.of (↥(compactlyGeneratedToTop.obj Y) ×
          ↥(compactlyGeneratedToTop.obj X))) ⟶
      TopCat.toCompactlyGenerated.obj
        (TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y))) :=
    TopCat.toCompactlyGenerated.map (TopCat.ofHom
      ⟨fun p => (p.2, p.1), continuous_snd.prodMk continuous_fst⟩)
  have hSwapFst : swap ≫ TopCat.toCompactlyGenerated.map
        (TopCat.prodFst : TopCat.of
          (↥(compactlyGeneratedToTop.obj X) ×
            ↥(compactlyGeneratedToTop.obj Y)) ⟶
          compactlyGeneratedToTop.obj X) =
      TopCat.toCompactlyGenerated.map
        (TopCat.prodSnd : TopCat.of
          (↥(compactlyGeneratedToTop.obj Y) ×
            ↥(compactlyGeneratedToTop.obj X)) ⟶
          compactlyGeneratedToTop.obj X) := by
    dsimp only [swap]
    rw [← TopCat.toCompactlyGenerated.map_comp]
    congr 1
  have hSwapSnd : swap ≫ TopCat.toCompactlyGenerated.map
        (TopCat.prodSnd : TopCat.of
          (↥(compactlyGeneratedToTop.obj X) ×
            ↥(compactlyGeneratedToTop.obj Y)) ⟶
          compactlyGeneratedToTop.obj Y) =
      TopCat.toCompactlyGenerated.map
        (TopCat.prodFst : TopCat.of
          (↥(compactlyGeneratedToTop.obj Y) ×
            ↥(compactlyGeneratedToTop.obj X)) ⟶
          compactlyGeneratedToTop.obj Y) := by
    dsimp only [swap]
    rw [← TopCat.toCompactlyGenerated.map_comp]
    congr 1
  change (binaryKificationIso Y X).hom ≫ (β_ Y X).hom =
    swap ≫ (binaryKificationIso X Y).hom
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc,
      CartesianMonoidalCategory.braiding_hom_fst]
    rw [(binaryKificationIso_hom_proj Y X).2,
      (binaryKificationIso_hom_proj X Y).1]
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ (asIso (adj.unit.app X)).inv)
        hSwapFst).symm
  · simp only [Category.assoc,
      CartesianMonoidalCategory.braiding_hom_snd]
    rw [(binaryKificationIso_hom_proj Y X).1,
      (binaryKificationIso_hom_proj X Y).2]
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ (asIso (adj.unit.app Y)).inv)
        hSwapSnd).symm

private theorem binaryKificationIso_inv_braiding_apply
    [BraidedCategory CompactlyGenerated.{u, v}]
    (X Y : CompactlyGenerated.{u, v}) (y : Y) (x : X) :
    (binaryKificationIso X Y).inv
        ((β_ Y X).hom ((binaryKificationIso Y X).hom (y, x))) =
      (x, y) := by
  let e := binaryKificationIso X Y
  have hp := ConcreteCategory.congr_hom
    (binaryKificationIso_braiding X Y) (y, x)
  change (β_ Y X).hom ((binaryKificationIso Y X).hom (y, x)) =
    e.hom (x, y) at hp
  change e.inv ((β_ Y X).hom
    ((binaryKificationIso Y X).hom (y, x))) = (x, y)
  rw [hp]
  exact TopCat.hom_inv_id_apply
    (compactlyGeneratedToTop.mapIso e) (x, y)

private theorem curry_apply_binaryKificationIso
    {X Y Z : CompactlyGenerated.{u, v}} (f : X ⊗ Y ⟶ Z)
    (y : Y) (x : X) :
    (internalHomToCompactOpen X Z (CompactlyGenerated.curry f y)) x =
      f ((binaryKificationIso X Y).hom (x, y)) := by
  unfold CompactlyGenerated.curry
  dsimp [CompactlyGenerated.internalHomAdjunction,
    binaryKificationIso]
  rfl

/-- The product of two setoids, transported to the carrier of the native
compactly generated product. -/
@[expose] noncomputable def prodSetoid {X Y : CompactlyGenerated.{u, v}}
    (s : Setoid ↥(compactlyGeneratedToTop.obj X))
    (t : Setoid ↥(compactlyGeneratedToTop.obj Y)) :
      Setoid ↥(compactlyGeneratedToTop.obj (X ⊗ Y)) := by
  let PF : ULift.{v} WalkingPair → CompactlyGenerated.{u, v}
    | ⟨WalkingPair.left⟩ => X
    | ⟨WalkingPair.right⟩ => Y
  let hp :
      ((TopCat.piFan (fun j => compactlyGeneratedToTop.obj (PF j))).pt : Type v) ≃ₜ
        ↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y) :=
    { toEquiv :=
        { toFun := fun g =>
            (show X from g (ULift.up WalkingPair.left),
              show Y from g (ULift.up WalkingPair.right))
          invFun := fun p j => match j with
            | ⟨WalkingPair.left⟩ => p.1
            | ⟨WalkingPair.right⟩ => p.2
          left_inv := fun g => by
            funext j
            rcases j with ⟨_ | _⟩ <;> rfl
          right_inv := fun p => by rcases p with ⟨x, y⟩; rfl }
      continuous_toFun :=
        (continuous_apply (ULift.up WalkingPair.left)).prodMk
          (continuous_apply (ULift.up WalkingPair.right))
      continuous_invFun := by
        apply continuous_pi
        intro j
        rcases j with ⟨_ | _⟩
        · exact continuous_fst
        · exact continuous_snd }
  let eTensor : (∏ᶜ PF) ≅ X ⊗ Y := by
    let c : Fan PF := Fan.mk (X ⊗ Y) (fun j => match j with
      | ⟨WalkingPair.left⟩ => CartesianMonoidalCategory.fst X Y
      | ⟨WalkingPair.right⟩ => CartesianMonoidalCategory.snd X Y)
    let hc : IsLimit c := by
      refine
        { lift := fun q => CartesianMonoidalCategory.lift
            (q.π.app ⟨ULift.up WalkingPair.left⟩)
            (q.π.app ⟨ULift.up WalkingPair.right⟩)
          fac := ?_
          uniq := ?_ }
      · rintro q ⟨⟨j⟩⟩
        cases j
        · exact CartesianMonoidalCategory.lift_fst _ _
        · exact CartesianMonoidalCategory.lift_snd _ _
      · intro q m hm
        apply CartesianMonoidalCategory.hom_ext
        · exact (hm ⟨ULift.up WalkingPair.left⟩).trans
            (CartesianMonoidalCategory.lift_fst _ _).symm
        · exact (hm ⟨ULift.up WalkingPair.right⟩).trans
            (CartesianMonoidalCategory.lift_snd _ _).symm
    exact (limit.isLimit _).conePointUniqueUpToIso hc
  let e : TopCat.toCompactlyGenerated.obj
        (TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y))) ≅ X ⊗ Y :=
    TopCat.toCompactlyGenerated.mapIso
        (TopCat.isoOfHomeo hp.symm) ≪≫
      (piIsoPi PF).symm ≪≫ eTensor
  exact Setoid.comap
    (CompactlyGenerated.homeoOfIso e.symm).toEquiv (s.prod t)

/-- Strickland's quotient-product homeomorphism for the native compactly
generated product, with no separation or local-compactness assumption. -/
noncomputable def quotientProdHomeomorph
    (X Y : CompactlyGenerated.{u, v})
    (s : Setoid ↥(compactlyGeneratedToTop.obj X)) :
    Quotient (prodSetoid (Y := Y) s (⊥ : Setoid Y)) ≃ₜ
      ↥(compactlyGeneratedToTop.obj
        ((@CompactlyGenerated.of.{u, v} (Quotient s) inferInstance
          (@instUCompactlyGeneratedSpaceQuotient.{u, v}
            ↥(compactlyGeneratedToTop.obj X) X.toTop.str s
            X.is_compactly_generated)) ⊗ Y)) := by
  let _ : UCompactlyGeneratedSpace.{u}
      ↥(compactlyGeneratedToTop.obj (X ⊗ Y)) :=
    (X ⊗ Y).is_compactly_generated
  let _ : BraidedCategory CompactlyGenerated.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CompactlyGenerated.{u, v} :=
    CartesianMonoidalCategory.toSymmetricCategory
  let QX : CompactlyGenerated.{u, v} :=
    @CompactlyGenerated.of.{u, v} (Quotient s) inferInstance
      (@instUCompactlyGeneratedSpaceQuotient.{u, v}
        ↥(compactlyGeneratedToTop.obj X) X.toTop.str s
        X.is_compactly_generated)
  let QProd : CompactlyGenerated.{u, v} :=
    CompactlyGenerated.of
      (Quotient (prodSetoid (Y := Y) s (⊥ : Setoid Y)))
  let eXY := binaryKificationIso X Y
  let eQY := binaryKificationIso QX Y
  let qX : X ⟶ QX := ConcreteCategory.ofHom
    ⟨(@Quotient.mk' _ s), continuous_quotient_mk'⟩
  let rawForward : TopCat.toCompactlyGenerated.obj
        (TopCat.of (↥(compactlyGeneratedToTop.obj X) ×
          ↥(compactlyGeneratedToTop.obj Y))) ⟶
      TopCat.toCompactlyGenerated.obj
        (TopCat.of (↥(compactlyGeneratedToTop.obj QX) ×
          ↥(compactlyGeneratedToTop.obj Y))) :=
    TopCat.toCompactlyGenerated.map (TopCat.ofHom
      ⟨fun p => ((show QX from Quotient.mk' p.1), p.2),
        (continuous_quotient_mk'.comp continuous_fst).prodMk continuous_snd⟩)
  let forward0 : X ⊗ Y ⟶ QX ⊗ Y :=
    eXY.inv ≫ rawForward ≫ eQY.hom
  have forward0_compat : ∀ p q,
      prodSetoid s (⊥ : Setoid Y) p q → forward0 p = forward0 q := by
    intro p q hpq
    let a := (binaryKificationIso X Y).inv p
    let b := (binaryKificationIso X Y).inv q
    change s a.1 b.1 ∧ a.2 = b.2 at hpq
    change eQY.hom (Quotient.mk' a.1, a.2) =
      eQY.hom (Quotient.mk' b.1, b.2)
    apply congrArg eQY.hom
    apply Prod.ext
    · exact Quotient.sound hpq.1
    · exact hpq.2
  let quotientProjection : X ⊗ Y ⟶ QProd :=
    ConcreteCategory.ofHom
      ⟨(@Quotient.mk' _ (prodSetoid (Y := Y) s (⊥ : Setoid Y))),
        continuous_quotient_mk'⟩
  let qRight : Y ⊗ X ⟶ QProd :=
    (β_ Y X).hom ≫ quotientProjection
  let qSharp : X ⟶ (internalHom Y).obj QProd :=
    CompactlyGenerated.curry qRight
  have qSharp_compat : ∀ x x', s x x' → qSharp x = qSharp x' := by
    intro x x' hxx'
    apply ContinuousMap.ext
    intro y
    dsimp only [qSharp]
    change (internalHomToCompactOpen Y QProd
        (CompactlyGenerated.curry qRight x)) y =
      (internalHomToCompactOpen Y QProd
        (CompactlyGenerated.curry qRight x')) y
    rw [curry_apply_binaryKificationIso qRight x y,
      curry_apply_binaryKificationIso qRight x' y]
    dsimp only [qRight, quotientProjection, ConcreteCategory.comp_apply]
    apply Quotient.sound
    unfold prodSetoid
    change s
        ((binaryKificationIso X Y).inv
          ((β_ Y X).hom ((binaryKificationIso Y X).hom (y, x)))).1
        ((binaryKificationIso X Y).inv
          ((β_ Y X).hom ((binaryKificationIso Y X).hom (y, x')))).1 ∧
      ((binaryKificationIso X Y).inv
          ((β_ Y X).hom ((binaryKificationIso Y X).hom (y, x)))).2 =
        ((binaryKificationIso X Y).inv
          ((β_ Y X).hom ((binaryKificationIso Y X).hom (y, x')))).2
    rw [binaryKificationIso_inv_braiding_apply X Y y x,
      binaryKificationIso_inv_braiding_apply X Y y x']
    exact ⟨hxx', rfl⟩
  let qSharpLift : QX ⟶ (internalHom Y).obj QProd :=
    ConcreteCategory.ofHom
      ⟨Quotient.lift qSharp qSharp_compat,
        (ConcreteCategory.hom qSharp).continuous.quotient_lift qSharp_compat⟩
  let inverse : QX ⊗ Y ⟶ QProd :=
    (β_ QX Y).hom ≫ CompactlyGenerated.uncurry qSharpLift
  have binary_inv_fst (A B : CompactlyGenerated.{u, v}) :
      (binaryKificationIso A B).inv ≫
          TopCat.toCompactlyGenerated.map
            (TopCat.prodFst : TopCat.of
              (↥(compactlyGeneratedToTop.obj A) ×
                ↥(compactlyGeneratedToTop.obj B)) ⟶
              compactlyGeneratedToTop.obj A) ≫
          (asIso (adj.unit.app A)).inv =
        CartesianMonoidalCategory.fst A B := by
    apply (cancel_epi (binaryKificationIso A B).hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      (binaryKificationIso_hom_proj A B).1.symm
  have binary_inv_snd (A B : CompactlyGenerated.{u, v}) :
      (binaryKificationIso A B).inv ≫
          TopCat.toCompactlyGenerated.map
            (TopCat.prodSnd : TopCat.of
              (↥(compactlyGeneratedToTop.obj A) ×
                ↥(compactlyGeneratedToTop.obj B)) ⟶
              compactlyGeneratedToTop.obj B) ≫
          (asIso (adj.unit.app B)).inv =
        CartesianMonoidalCategory.snd A B := by
    apply (cancel_epi (binaryKificationIso A B).hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
      (binaryKificationIso_hom_proj A B).2.symm
  have rawForward_fst : rawForward ≫
        TopCat.toCompactlyGenerated.map
          (TopCat.prodFst : TopCat.of
            (↥(compactlyGeneratedToTop.obj QX) ×
              ↥(compactlyGeneratedToTop.obj Y)) ⟶
            compactlyGeneratedToTop.obj QX) =
      TopCat.toCompactlyGenerated.map
          (TopCat.prodFst : TopCat.of
            (↥(compactlyGeneratedToTop.obj X) ×
              ↥(compactlyGeneratedToTop.obj Y)) ⟶
            compactlyGeneratedToTop.obj X) ≫
        TopCat.toCompactlyGenerated.map
          (compactlyGeneratedToTop.map qX) := by
    dsimp only [rawForward, qX]
    rw [← TopCat.toCompactlyGenerated.map_comp,
      ← TopCat.toCompactlyGenerated.map_comp]
    congr 1
  have rawForward_snd : rawForward ≫
        TopCat.toCompactlyGenerated.map
          (TopCat.prodSnd : TopCat.of
            (↥(compactlyGeneratedToTop.obj QX) ×
              ↥(compactlyGeneratedToTop.obj Y)) ⟶
            compactlyGeneratedToTop.obj Y) =
      TopCat.toCompactlyGenerated.map
        (TopCat.prodSnd : TopCat.of
          (↥(compactlyGeneratedToTop.obj X) ×
            ↥(compactlyGeneratedToTop.obj Y)) ⟶
          compactlyGeneratedToTop.obj Y) := by
    dsimp only [rawForward]
    rw [← TopCat.toCompactlyGenerated.map_comp]
    congr 1
  have forward0_eq : forward0 = qX ⊗ₘ 𝟙 Y := by
    apply CartesianMonoidalCategory.hom_ext
    · calc
        forward0 ≫ CartesianMonoidalCategory.fst QX Y =
            eXY.inv ≫ rawForward ≫
              ((eQY.hom ≫ CartesianMonoidalCategory.fst QX Y)) := by
                simp only [forward0, Category.assoc]
        _ = eXY.inv ≫ rawForward ≫
            (TopCat.toCompactlyGenerated.map TopCat.prodFst ≫
              (asIso (adj.unit.app QX)).inv) := by
                rw [(binaryKificationIso_hom_proj QX Y).1]
        _ = eXY.inv ≫
            (TopCat.toCompactlyGenerated.map TopCat.prodFst ≫
              TopCat.toCompactlyGenerated.map
                (compactlyGeneratedToTop.map qX)) ≫
              (asIso (adj.unit.app QX)).inv := by
                simpa only [Category.assoc] using congrArg
                  (fun k => eXY.inv ≫ k ≫
                    (asIso (adj.unit.app QX)).inv) rawForward_fst
        _ = (eXY.inv ≫
              TopCat.toCompactlyGenerated.map TopCat.prodFst ≫
                (asIso (adj.unit.app X)).inv) ≫ qX := by
                  simpa only [Category.assoc, Functor.id_map,
                    Functor.comp_map, asIso_inv] using congrArg
                      (fun k => eXY.inv ≫
                        TopCat.toCompactlyGenerated.map TopCat.prodFst ≫ k)
                      (adj.unit.naturality_inv qX).symm
        _ = CartesianMonoidalCategory.fst X Y ≫ qX := by
              rw [binary_inv_fst]
        _ = (qX ⊗ₘ 𝟙 Y) ≫
            CartesianMonoidalCategory.fst QX Y := by
              rw [CartesianMonoidalCategory.tensorHom_fst]
    · calc
        forward0 ≫ CartesianMonoidalCategory.snd QX Y =
            eXY.inv ≫ rawForward ≫
              (eQY.hom ≫ CartesianMonoidalCategory.snd QX Y) := by
                simp only [forward0, Category.assoc]
        _ = eXY.inv ≫ rawForward ≫
            (TopCat.toCompactlyGenerated.map TopCat.prodSnd ≫
              (asIso (adj.unit.app Y)).inv) := by
                rw [(binaryKificationIso_hom_proj QX Y).2]
        _ = eXY.inv ≫
            TopCat.toCompactlyGenerated.map TopCat.prodSnd ≫
              (asIso (adj.unit.app Y)).inv := by
                simpa only [Category.assoc] using congrArg
                  (fun k => eXY.inv ≫ k ≫
                    (asIso (adj.unit.app Y)).inv) rawForward_snd
        _ = CartesianMonoidalCategory.snd X Y := binary_inv_snd X Y
        _ = (qX ⊗ₘ 𝟙 Y) ≫
            CartesianMonoidalCategory.snd QX Y := by
              rw [CartesianMonoidalCategory.tensorHom_snd]
              simp
  have tensor_compat : ∀ p q,
      prodSetoid s (⊥ : Setoid Y) p q →
        (qX ⊗ₘ 𝟙 Y) p = (qX ⊗ₘ 𝟙 Y) q := by
    intro p q hpq
    rw [← forward0_eq]
    exact forward0_compat p q hpq
  let forward : QProd ⟶ QX ⊗ Y :=
    ConcreteCategory.ofHom
      ⟨Quotient.lift (qX ⊗ₘ 𝟙 Y) tensor_compat,
        (ConcreteCategory.hom (qX ⊗ₘ 𝟙 Y)).continuous.quotient_lift
          tensor_compat⟩
  have projection_forward :
      quotientProjection ≫ forward = qX ⊗ₘ 𝟙 Y := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  have qX_qSharpLift : qX ≫ qSharpLift = qSharp := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have uncurry_qSharp : CompactlyGenerated.uncurry qSharp = qRight := by
    dsimp only [qSharp]
    exact ((internalHomAdjunction Y).homEquiv X QProd).symm_apply_apply qRight
  have tensor_inverse : (qX ⊗ₘ 𝟙 Y) ≫ inverse = quotientProjection := by
    calc
      (qX ⊗ₘ 𝟙 Y) ≫ inverse =
          ((qX ⊗ₘ 𝟙 Y) ≫ (β_ QX Y).hom) ≫
            CompactlyGenerated.uncurry qSharpLift := by
              simp only [inverse, Category.assoc]
      _ = ((β_ X Y).hom ≫ (𝟙 Y ⊗ₘ qX)) ≫
            CompactlyGenerated.uncurry qSharpLift := by
              rw [BraidedCategory.braiding_naturality]
      _ = (β_ X Y).hom ≫
            ((Y ◁ qX) ≫ CompactlyGenerated.uncurry qSharpLift) := by
              simp only [Category.assoc, id_tensorHom]
      _ = (β_ X Y).hom ≫
            CompactlyGenerated.uncurry (qX ≫ qSharpLift) := by
              exact congrArg (fun k => (β_ X Y).hom ≫ k)
                ((internalHomAdjunction Y).homEquiv_naturality_left_symm
                  qX qSharpLift).symm
      _ = (β_ X Y).hom ≫ CompactlyGenerated.uncurry qSharp := by
              rw [qX_qSharpLift]
      _ = (β_ X Y).hom ≫ qRight := by rw [uncurry_qSharp]
      _ = (β_ X Y).hom ≫ (β_ Y X).hom ≫ quotientProjection := by
            rfl
      _ = quotientProjection := by simp
  have projection_forward_inverse :
      quotientProjection ≫ forward ≫ inverse = quotientProjection := by
    rw [← Category.assoc, projection_forward, tensor_inverse]
  have inverse_forward : ∀ z, inverse (forward z) = z := by
    intro z
    induction z using Quotient.inductionOn'
    exact ConcreteCategory.congr_hom projection_forward_inverse _
  have forward_surjective : Function.Surjective forward := by
    intro z
    let a := eQY.inv z
    let x := a.1.out
    let p := eXY.hom (x, a.2)
    refine ⟨(@Quotient.mk' _ (prodSetoid (Y := Y) s (⊥ : Setoid Y))) p, ?_⟩
    dsimp only [forward]
    have hp := ConcreteCategory.congr_hom forward0_eq p
    change (qX ⊗ₘ 𝟙 Y) p = z
    rw [← hp]
    calc
      forward0 p = eQY.hom (Quotient.mk' x, a.2) := by
        simp only [forward0, p, rawForward,
          ConcreteCategory.comp_apply]
        rw [show eXY.inv (eXY.hom (x, a.2)) = (x, a.2) from
          TopCat.hom_inv_id_apply
            (compactlyGeneratedToTop.mapIso eXY) (x, a.2)]
        apply congrArg eQY.hom
        rfl
      _ = eQY.hom (a.1, a.2) := by
        apply congrArg eQY.hom
        apply Prod.ext
        · exact Quotient.out_eq a.1
        · rfl
      _ = z := TopCat.inv_hom_id_apply
        (compactlyGeneratedToTop.mapIso eQY) z
  exact
    { toFun := forward
      invFun := inverse
      left_inv := inverse_forward
      right_inv := by
        intro z
        obtain ⟨w, rfl⟩ := forward_surjective z
        rw [inverse_forward]
      continuous_toFun := (ConcreteCategory.hom forward).continuous
      continuous_invFun := (ConcreteCategory.hom inverse).continuous }

private theorem prodMap_left_isQuotientMap
    {W X Y : CompactlyGenerated.{u, v}} (f : W ⟶ X)
    (hf : IsQuotientMap (ConcreteCategory.hom f)) :
    IsQuotientMap (ConcreteCategory.hom (f ⊗ₘ 𝟙 Y)) := by
  let r : Setoid ↥(compactlyGeneratedToTop.obj W) :=
    Setoid.ker (ConcreteCategory.hom f)
  let QW : CompactlyGenerated.{u, v} :=
    @CompactlyGenerated.of.{u, v} (Quotient r) inferInstance
      (@instUCompactlyGeneratedSpaceQuotient.{u, v}
        ↥(compactlyGeneratedToTop.obj W) W.toTop.str r
        W.is_compactly_generated)
  let QProd : CompactlyGenerated.{u, v} :=
    @CompactlyGenerated.of.{u, v}
      (Quotient (prodSetoid (Y := Y) r (⊥ : Setoid Y))) inferInstance
      (@instUCompactlyGeneratedSpaceQuotient.{u, v}
        ↥(compactlyGeneratedToTop.obj (W ⊗ Y)) (W ⊗ Y).toTop.str
        (prodSetoid (Y := Y) r (⊥ : Setoid Y))
        (W ⊗ Y).is_compactly_generated)
  let qW : W ⟶ QW := ConcreteCategory.ofHom
    ⟨(@Quotient.mk' _ r), continuous_quotient_mk'⟩
  let qProd : W ⊗ Y ⟶ QProd := ConcreteCategory.ofHom
    ⟨(@Quotient.mk' _ (prodSetoid (Y := Y) r (⊥ : Setoid Y))),
      continuous_quotient_mk'⟩
  let hQ := quotientProdHomeomorph W Y r
  let hQHom : QProd ⟶ QW ⊗ Y :=
    ConcreteCategory.ofHom ⟨hQ, hQ.continuous⟩
  let e : QW ≅ X := CompactlyGenerated.isoOfHomeo hf.homeomorph
  let eTensor : QW ⊗ Y ≅ X ⊗ Y := e ⊗ᵢ Iso.refl Y
  have qProd_hQ : qProd ≫ hQHom = qW ⊗ₘ 𝟙 Y := by
    apply ConcreteCategory.hom_ext
    intro p
    dsimp only [hQHom, hQ, qProd, qW]
    unfold quotientProdHomeomorph
    rfl
  have qW_e : qW ≫ e.hom = f := by
    apply ConcreteCategory.hom_ext
    intro w
    rfl
  let factor : W ⊗ Y ⟶ X ⊗ Y := qProd ≫ hQHom ≫ eTensor.hom
  have factor_eq : factor = f ⊗ₘ 𝟙 Y := by
    dsimp only [factor, eTensor]
    rw [← Category.assoc, qProd_hQ, tensorIso_hom,
      MonoidalCategory.tensorHom_comp_tensorHom, qW_e]
    simp
  have hqProd : IsQuotientMap (ConcreteCategory.hom qProd) :=
    isQuotientMap_quotient_mk'
  have hhQ : IsQuotientMap (ConcreteCategory.hom hQHom) :=
    hQ.isQuotientMap
  have heTensor : IsQuotientMap (ConcreteCategory.hom eTensor.hom) :=
    (CompactlyGenerated.homeoOfIso eTensor).isQuotientMap
  have hfactor : IsQuotientMap (ConcreteCategory.hom factor) := by
    change IsQuotientMap
      (fun x => eTensor.hom (hQHom (qProd x)))
    exact heTensor.comp (hhQ.comp hqProd)
  rw [factor_eq] at hfactor
  exact hfactor

/-- The native product of two quotient maps of compactly generated spaces is
a quotient map.  This is the native form of Strickland Proposition 2.20. -/
theorem prodQuotientMap
    {W X Y Z : CompactlyGenerated.{u, v}}
    (f : W ⟶ X) (g : Y ⟶ Z)
    (hf : IsQuotientMap (ConcreteCategory.hom f))
    (hg : IsQuotientMap (ConcreteCategory.hom g)) :
    IsQuotientMap (ConcreteCategory.hom (f ⊗ₘ g)) := by
  let _ : BraidedCategory CompactlyGenerated.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CompactlyGenerated.{u, v} :=
    CartesianMonoidalCategory.toSymmetricCategory
  have hLeft : IsQuotientMap
      (ConcreteCategory.hom (f ⊗ₘ 𝟙 Y)) :=
    prodMap_left_isQuotientMap f hf
  have hMid : IsQuotientMap
      (ConcreteCategory.hom (g ⊗ₘ 𝟙 X)) :=
    prodMap_left_isQuotientMap g hg
  have hBraid1 : IsQuotientMap
      (ConcreteCategory.hom (β_ X Y).hom) :=
    (CompactlyGenerated.homeoOfIso (β_ X Y)).isQuotientMap
  have hBraid2 : IsQuotientMap
      (ConcreteCategory.hom (β_ Z X).hom) :=
    (CompactlyGenerated.homeoOfIso (β_ Z X)).isQuotientMap
  let rightFactor : X ⊗ Y ⟶ X ⊗ Z :=
    (β_ X Y).hom ≫ (g ⊗ₘ 𝟙 X) ≫ (β_ Z X).hom
  have rightFactor_eq : rightFactor = 𝟙 X ⊗ₘ g := by
    dsimp only [rightFactor]
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality]
    simp
  have hRightFactor : IsQuotientMap
      (ConcreteCategory.hom rightFactor) := by
    change IsQuotientMap (fun x =>
      (β_ Z X).hom ((g ⊗ₘ 𝟙 X) ((β_ X Y).hom x)))
    exact hBraid2.comp (hMid.comp hBraid1)
  rw [rightFactor_eq] at hRightFactor
  have hComp : IsQuotientMap
      (ConcreteCategory.hom ((f ⊗ₘ 𝟙 Y) ≫ (𝟙 X ⊗ₘ g))) := by
    change IsQuotientMap (fun x =>
      (𝟙 X ⊗ₘ g) ((f ⊗ₘ 𝟙 Y) x))
    exact hRightFactor.comp hLeft
  simpa only [MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id, Category.id_comp] using hComp

end CompactlyGenerated
