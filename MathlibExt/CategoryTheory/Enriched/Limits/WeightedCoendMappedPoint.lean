/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendMapped

/-!
# Entire tensor-mapped coend balance from arbitrary unit Hom points

Only the enriched Hom parameter is tested by the actual tensor-unit
separator. The parameter object, weight and diagram values remain entire.
The conclusion is the complete original tensor-mapped enriched relation,
before any selected coend descent or operator functor is constructed.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uA

namespace CategoryTheory.Enriched.weightedCoend.Mapped

open MonoidalCategory BraidedCategory Opposite Limits
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

private theorem unitPoint_associator (M A H : V) (p : 𝟙_ V ⟶ H) :
    ((ρ_ (M ⊗ A)).inv ≫ (M ⊗ A) ◁ p) ≫ (α_ M A H).hom =
      M ◁ ((ρ_ A).inv ≫ A ◁ p) := by
  rw [Category.assoc, associator_naturality_right,
    ← whiskerLeft_rightUnitor_inv_assoc, ← whiskerLeft_comp]

private theorem hom_eq_of_rightUnitPoints [MonoidalClosed V]
    (hU : IsSeparator (𝟙_ V)) {A H Z : V} {f g : A ⊗ H ⟶ Z}
    (h : ∀ (p : 𝟙_ V ⟶ H),
      ((ρ_ A).inv ≫ A ◁ p) ≫ f = ((ρ_ A).inv ≫ A ◁ p) ≫ g) : f = g := by
  apply MonoidalClosed.curry_injective
  apply hU.def
  intro p
  apply MonoidalClosed.uncurry_injective
  have hf : MonoidalClosed.uncurry (p ≫ MonoidalClosed.curry f) = (A ◁ p) ≫ f :=
    (MonoidalClosed.uncurry_natural_left p (MonoidalClosed.curry f)).trans
      (congrArg (fun q => (A ◁ p) ≫ q) (MonoidalClosed.uncurry_curry f))
  have hg : MonoidalClosed.uncurry (p ≫ MonoidalClosed.curry g) = (A ◁ p) ≫ g :=
    (MonoidalClosed.uncurry_natural_left p (MonoidalClosed.curry g)).trans
      (congrArg (fun q => (A ◁ p) ≫ q) (MonoidalClosed.uncurry_curry g))
  have hPoint : (A ◁ p) ≫ f = (A ◁ p) ≫ g :=
    (cancel_epi (ρ_ A).inv).1 (by simpa only [Category.assoc] using h p)
  exact hf.trans (hPoint.trans hg.symm)

private theorem relationPoint_left (U U' H A : V)
    (p : 𝟙_ V ⟶ H) (r : U ⊗ H ⟶ U') :
    (U ◁ ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A))) ≫
        (α_ U H A).inv ≫ (r ⊗ₘ 𝟙 A) =
      (((ρ_ U).inv ≫ U ◁ p ≫ r) ⊗ₘ 𝟙 A) := by
  have hNatural :
      U ◁ (p ⊗ₘ 𝟙 A) ≫ (α_ U H A).inv =
        (α_ U (𝟙_ V) A).inv ≫ ((U ◁ p) ▷ A) := by
    simpa only [id_tensorHom, tensorHom_id] using
      associator_inv_naturality (𝟙 U) p (𝟙 A)
  have hTriangle :
      U ◁ (λ_ A).inv ≫ (α_ U (𝟙_ V) A).inv = (ρ_ U).inv ▷ A := by
    monoidal
  calc
    _ = U ◁ (λ_ A).inv ≫
        (U ◁ (p ⊗ₘ 𝟙 A) ≫ (α_ U H A).inv) ≫ (r ⊗ₘ 𝟙 A) := by
      simp only [whiskerLeft_comp, Category.assoc]
    _ = U ◁ (λ_ A).inv ≫ (α_ U (𝟙_ V) A).inv ≫
        ((U ◁ p) ▷ A) ≫ (r ⊗ₘ 𝟙 A) := by
      simpa only [Category.assoc] using congrArg
        (fun q => U ◁ (λ_ A).inv ≫ q ≫ (r ⊗ₘ 𝟙 A)) hNatural
    _ = ((ρ_ U).inv ▷ A) ≫ ((U ◁ p) ▷ A) ≫ (r ⊗ₘ 𝟙 A) := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ ((U ◁ p) ▷ A) ≫ (r ⊗ₘ 𝟙 A)) hTriangle
    _ = _ := by
      simpa only [comp_whiskerRight, Category.assoc] using
        whiskerRight_comp_tensorHom ((ρ_ U).inv ≫ U ◁ p) r (𝟙 A)

variable [BraidedCategory V]

private theorem relationPoint_cross (A H : V) (p : 𝟙_ V ⟶ H) :
    ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)) ≫ (β_ H A).hom =
      (ρ_ A).inv ≫ A ◁ p := by
  simpa only [id_tensorHom, Category.assoc,
    braiding_tensorUnit_left, Iso.inv_hom_id_assoc] using
    congrArg (fun q => (λ_ A).inv ≫ q) (braiding_naturality p (𝟙 A))

private theorem relationPoint_right (U A A' H : V)
    (p : 𝟙_ V ⟶ H) (r : A ⊗ H ⟶ A') :
    (U ◁ ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A))) ≫
        U ◁ ((β_ H A).hom ≫ r) =
      U ◁ ((ρ_ A).inv ≫ A ◁ p ≫ r) := by
  rw [← whiskerLeft_comp]
  let insert := (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)
  have hAssoc : insert ≫ ((β_ H A).hom ≫ r) = (insert ≫ (β_ H A).hom) ≫ r :=
    (Category.assoc insert (β_ H A).hom r).symm
  have hCross : (insert ≫ (β_ H A).hom) ≫ r =
      ((ρ_ A).inv ≫ A ◁ p) ≫ r :=
    congrArg (fun q => q ≫ r) (relationPoint_cross A H p)
  have hLast : ((ρ_ A).inv ≫ A ◁ p) ≫ r = (ρ_ A).inv ≫ A ◁ p ≫ r :=
    Category.assoc (ρ_ A).inv (A ◁ p) r
  exact congrArg (fun q => U ◁ q) (hAssoc.trans (hCross.trans hLast))

/-- Each arbitrary unit Hom point specializes the complete original relation. -/
theorem relation_unitPoint (U U' A A' H Z : V)
    (r : U ⊗ H ⟶ U') (s : A ⊗ H ⟶ A')
    (qa : U' ⊗ A ⟶ Z) (qb : U ⊗ A' ⟶ Z)
    (hFull : ((α_ U H A).inv ≫ (r ⊗ₘ 𝟙 A)) ≫ qa =
      (U ◁ ((β_ H A).hom ≫ s)) ≫ qb) (p : 𝟙_ V ⟶ H) :
    (((ρ_ U).inv ≫ U ◁ p ≫ r) ⊗ₘ 𝟙 A) ≫ qa =
      (𝟙 U ⊗ₘ ((ρ_ A).inv ≫ A ◁ p ≫ s)) ≫ qb := by
  let pre := U ◁ ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A))
  let l := (α_ U H A).inv ≫ (r ⊗ₘ 𝟙 A)
  let t := U ◁ ((β_ H A).hom ≫ s)
  have hl : pre ≫ l = ((ρ_ U).inv ≫ U ◁ p ≫ r) ⊗ₘ 𝟙 A :=
    relationPoint_left U U' H A p r
  have ht : pre ≫ t = 𝟙 U ⊗ₘ ((ρ_ A).inv ≫ A ◁ p ≫ s) :=
    (relationPoint_right U A A' H p s).trans
      (id_tensorHom U ((ρ_ A).inv ≫ A ◁ p ≫ s)).symm
  have hLeft : pre ≫ (l ≫ qa) = (((ρ_ U).inv ≫ U ◁ p ≫ r) ⊗ₘ 𝟙 A) ≫ qa :=
    (Category.assoc pre l qa).symm.trans (congrArg (fun q => q ≫ qa) hl)
  have hRight : pre ≫ (t ≫ qb) = (𝟙 U ⊗ₘ ((ρ_ A).inv ≫ A ◁ p ≫ s)) ≫ qb :=
    (Category.assoc pre t qb).symm.trans (congrArg (fun q => q ≫ qb) ht)
  exact hLeft.symm.trans ((congrArg (fun q => pre ≫ q) hFull).trans hRight)

private theorem middleShuffle_unitPoint (M U A H : V) (p : 𝟙_ V ⟶ H) :
    ((ρ_ (M ⊗ (U ⊗ A))).inv ≫ (M ⊗ (U ⊗ A)) ◁ p) ≫
        (α_ M (U ⊗ A) H).hom ≫
        (M ◁ (α_ U A H).hom) ≫ (M ◁ (U ◁ (β_ H A).inv)) =
      M ◁ (U ◁ ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A))) := by
  have hFirst := unitPoint_associator M (U ⊗ A) H p
  have hSecond := unitPoint_associator U A H p
  have hCross : ((ρ_ A).inv ≫ A ◁ p) ≫ (β_ H A).inv =
      (λ_ A).inv ≫ (p ⊗ₘ 𝟙 A) := by
    rw [← relationPoint_cross A H p, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = (M ◁ ((ρ_ (U ⊗ A)).inv ≫ (U ⊗ A) ◁ p)) ≫
        (M ◁ (α_ U A H).hom) ≫ (M ◁ (U ◁ (β_ H A).inv)) := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ (M ◁ (α_ U A H).hom) ≫ (M ◁ (U ◁ (β_ H A).inv))) hFirst
    _ = (M ◁ (U ◁ ((ρ_ A).inv ≫ A ◁ p))) ≫ (M ◁ (U ◁ (β_ H A).inv)) := by
      simpa only [whiskerLeft_comp, Category.assoc] using congrArg
        (fun q => (M ◁ q) ≫ (M ◁ (U ◁ (β_ H A).inv))) hSecond
    _ = M ◁ (U ◁ (((ρ_ A).inv ≫ A ◁ p) ≫ (β_ H A).inv)) := by
      simp only [whiskerLeft_comp]
    _ = _ := congrArg (fun q => M ◁ (U ◁ q)) hCross

private theorem hom_eq_of_middleUnitPoints [MonoidalClosed V]
    (hU : IsSeparator (𝟙_ V)) (M U A H Z : V)
    {f g : M ⊗ (U ⊗ (H ⊗ A)) ⟶ Z}
    (h : ∀ (p : 𝟙_ V ⟶ H),
      (M ◁ (U ◁ ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)))) ≫ f =
        (M ◁ (U ◁ ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A)))) ≫ g) : f = g := by
  let q : (M ⊗ (U ⊗ A)) ⊗ H ⟶ M ⊗ (U ⊗ (H ⊗ A)) :=
    (α_ M (U ⊗ A) H).hom ≫
      (M ◁ (α_ U A H).hom) ≫ (M ◁ (U ◁ (β_ H A).inv))
  have : IsIso q := by
    dsimp only [q]
    infer_instance
  apply (cancel_epi q).1
  apply hom_eq_of_rightUnitPoints hU
  intro p
  have hq :
      ((ρ_ (M ⊗ (U ⊗ A))).inv ≫ (M ⊗ (U ⊗ A)) ◁ p) ≫ q =
        M ◁ (U ◁ ((λ_ A).inv ≫ (p ⊗ₘ 𝟙 A))) :=
    middleShuffle_unitPoint M U A H p
  have hf := (Category.assoc
    ((ρ_ (M ⊗ (U ⊗ A))).inv ≫ (M ⊗ (U ⊗ A)) ◁ p) q f).symm.trans
      (congrArg (fun r => r ≫ f) hq)
  have hg := (Category.assoc
    ((ρ_ (M ⊗ (U ⊗ A))).inv ≫ (M ⊗ (U ⊗ A)) ◁ p) q g).symm.trans
      (congrArg (fun r => r ≫ g) hq)
  exact hf.trans ((h p).trans hg.symm)

variable [MonoidalClosed V] {A : Type uA} [EnrichedCategory V A]

/-- Arbitrary Hom unit points establish the entire original tensor-mapped relation. -/
theorem balanced_of_unitPoints
    (W : EnrichedFunctor V Aᵒᵖ V) (F : EnrichedFunctor V A V)
    (hU : IsSeparator (𝟙_ V)) (M Z : V)
    (q : ∀ a, M ⊗ (W.obj (op a) ⊗ F.obj a) ⟶ Z)
    (hq : ∀ (a b : A) (p : 𝟙_ V ⟶ (a ⟶[V] b)),
      (M ◁ (((ρ_ (W.obj (op b))).inv ≫ W.obj (op b) ◁ p ≫
        MonoidalClosed.uncurry (W.map (op b) (op a))) ⊗ₘ 𝟙 (F.obj a))) ≫ q a =
      (M ◁ (𝟙 (W.obj (op b)) ⊗ₘ
        ((ρ_ (F.obj a)).inv ≫ F.obj a ◁ p ≫
          MonoidalClosed.uncurry (F.map a b)))) ≫ q b) :
    Balanced W F (tensorLeft M) q := by
  intro a b
  let U := W.obj (op b)
  let U' := W.obj (op a)
  let H : V := a ⟶[V] b
  let X := F.obj a
  let Y := F.obj b
  let r := MonoidalClosed.uncurry (W.map (op b) (op a))
  let s := MonoidalClosed.uncurry (F.map a b)
  let wf : U ⊗ (H ⊗ X) ⟶ U' ⊗ X := (α_ U H X).inv ≫ (r ⊗ₘ 𝟙 X)
  let df : U ⊗ (H ⊗ X) ⟶ U ⊗ Y := U ◁ ((β_ H X).hom ≫ s)
  change (M ◁ wf) ≫ q a = (M ◁ df) ≫ q b
  apply hom_eq_of_middleUnitPoints hU M U X H Z
  intro p
  let pre := M ◁ (U ◁ ((λ_ X).inv ≫ (p ⊗ₘ 𝟙 X)))
  let wa := (ρ_ U).inv ≫ U ◁ p ≫ r
  let fa := (ρ_ X).inv ≫ X ◁ p ≫ s
  have hLeft : pre ≫ (M ◁ wf) = M ◁ (wa ⊗ₘ 𝟙 X) :=
    (whiskerLeft_comp M (U ◁ ((λ_ X).inv ≫ (p ⊗ₘ 𝟙 X))) wf).symm.trans
      (congrArg (fun t => M ◁ t) (relationPoint_left U U' H X p r))
  have hRight : pre ≫ (M ◁ df) = M ◁ (𝟙 U ⊗ₘ fa) :=
    (whiskerLeft_comp M (U ◁ ((λ_ X).inv ≫ (p ⊗ₘ 𝟙 X))) df).symm.trans
      ((congrArg (fun t => M ◁ t) (relationPoint_right U X Y H p s)).trans
        (congrArg (fun t => M ◁ t) (id_tensorHom U fa).symm))
  have hLeftAppend : pre ≫ ((M ◁ wf) ≫ q a) = (M ◁ (wa ⊗ₘ 𝟙 X)) ≫ q a :=
    (Category.assoc pre (M ◁ wf) (q a)).symm.trans
      (congrArg (fun t => t ≫ q a) hLeft)
  have hRightAppend : pre ≫ ((M ◁ df) ≫ q b) = (M ◁ (𝟙 U ⊗ₘ fa)) ≫ q b :=
    (Category.assoc pre (M ◁ df) (q b)).symm.trans
      (congrArg (fun t => t ≫ q b) hRight)
  exact hLeftAppend.trans ((hq a b p).trans hRightAppend.symm)

end CategoryTheory.Enriched.weightedCoend.Mapped
