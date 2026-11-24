/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Enriched.SphereOperator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

/-- Two actual tensor-unit points inserted on the left have the canonical
associator padding. This is a full morphism equation, not point separation. -/
private theorem doubleLeftPointPaddingForProof (H C B : V)
    (p : (𝟙_ V) ⟶ C) (q : (𝟙_ V) ⟶ B) :
    (λ_ H).inv ≫
        (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ⊗ₘ 𝟙 H) ≫
        (α_ C B H).hom =
      ((λ_ H).inv ≫ (p ⊗ₘ 𝟙 H)) ≫
        C ◁ ((λ_ H).inv ≫ (q ⊗ₘ 𝟙 H)) := by
  have hSplit :
      (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q)) ⊗ₘ 𝟙 H) =
        ((λ_ (𝟙_ V)).inv ⊗ₘ 𝟙 H) ≫ ((p ⊗ₘ q) ⊗ₘ 𝟙 H) := by
    simpa only [Category.id_comp] using
      (tensorHom_comp_tensorHom (λ_ (𝟙_ V)).inv (𝟙 H)
        (p ⊗ₘ q) (𝟙 H)).symm
  have hNatural : ((p ⊗ₘ q) ⊗ₘ 𝟙 H) ≫ (α_ C B H).hom =
      (α_ (𝟙_ V) (𝟙_ V) H).hom ≫ (p ⊗ₘ (q ⊗ₘ 𝟙 H)) :=
    associator_naturality p q (𝟙 H)
  have hUnit :
      (λ_ H).inv ≫ ((λ_ (𝟙_ V)).inv ▷ H) ≫
          (α_ (𝟙_ V) (𝟙_ V) H).hom =
        (λ_ H).inv ≫ (𝟙_ V ◁ (λ_ H).inv) := by
    monoidal
  have hExchange :
      (p ▷ H) ≫ C ◁ (λ_ H).inv =
        (𝟙_ V ◁ (λ_ H).inv) ≫ (p ▷ ((𝟙_ V) ⊗ H)) :=
    (tensorHom_def p (λ_ H).inv).symm.trans
      (tensorHom_def' p (λ_ H).inv)
  calc
    _ = (λ_ H).inv ≫ ((λ_ (𝟙_ V)).inv ⊗ₘ 𝟙 H) ≫
        (((p ⊗ₘ q) ⊗ₘ 𝟙 H) ≫ (α_ C B H).hom) := by
      rw [hSplit]
      simp only [Category.assoc]
    _ = (λ_ H).inv ≫ ((λ_ (𝟙_ V)).inv ▷ H) ≫
        (α_ (𝟙_ V) (𝟙_ V) H).hom ≫ (p ⊗ₘ (q ⊗ₘ 𝟙 H)) := by
      rw [hNatural]
      simp only [tensorHom_id]
    _ = (λ_ H).inv ≫ (𝟙_ V ◁ (λ_ H).inv) ≫
        (p ⊗ₘ (q ⊗ₘ 𝟙 H)) := by
      simpa only [Category.assoc] using congrArg
        (fun z : H ⟶ (𝟙_ V) ⊗ ((𝟙_ V) ⊗ H) =>
          z ≫ (p ⊗ₘ (q ⊗ₘ 𝟙 H))) hUnit
    _ = (λ_ H).inv ≫ (𝟙_ V ◁ (λ_ H).inv) ≫
        (p ▷ ((𝟙_ V) ⊗ H)) ≫ C ◁ (q ⊗ₘ 𝟙 H) := by
      rw [tensorHom_def p (q ⊗ₘ 𝟙 H)]
    _ = (λ_ H).inv ≫ (p ▷ H) ≫ C ◁ (λ_ H).inv ≫
        C ◁ (q ⊗ₘ 𝟙 H) := by
      simpa only [Category.assoc] using congrArg
        (fun z : (𝟙_ V) ⊗ H ⟶ C ⊗ ((𝟙_ V) ⊗ H) =>
          (λ_ H).inv ≫ z ≫ C ◁ (q ⊗ₘ 𝟙 H)) hExchange.symm
    _ = _ := by
      simp only [tensorHom_id, MonoidalCategory.whiskerLeft_comp,
        Category.assoc]

/-- Left tensor-unit insertion is natural on the entire morphism object. -/
private theorem leftPointInsertionNaturalForProof {H K C : V}
    (p : (𝟙_ V) ⟶ C) (f : H ⟶ K) :
    ((λ_ H).inv ≫ (p ⊗ₘ 𝟙 H)) ≫ C ◁ f =
      f ≫ (λ_ K).inv ≫ (p ⊗ₘ 𝟙 K) := by
  have hPair : (p ⊗ₘ 𝟙 H) ≫ C ◁ f = p ⊗ₘ f := by
    simpa only [Category.comp_id, Category.id_comp, id_tensorHom] using
      tensorHom_comp_tensorHom p (𝟙 H) (𝟙 C) f
  calc
    _ = (λ_ H).inv ≫ (p ⊗ₘ f) := by
      rw [Category.assoc, hPair]
    _ = _ := by
      simpa only [tensorHom_id] using leftUnitor_inv_comp_tensorHom p f

variable [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

/-- The actual full associator naturality, specialized only at the identities
of c and b. The remaining I(x,y) Hom object is retained in full. -/
theorem associator_third_full_hom
    (d : EnrichedMonoidalCategoryData V I) (c b x y : I) :
    ((λ_ (x ⟶[V] y)).inv ≫
        (eId V (c ⊗ b) ⊗ₘ 𝟙 (x ⟶[V] y)) ≫
        d.tensorMap (c ⊗ b) (c ⊗ b) x y) ≫
        eHomWhiskerLeft V ((c ⊗ b) ⊗ x) (α_ c b y).hom =
      ((λ_ (x ⟶[V] y)).inv ≫
          (eId V b ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap b b x y ≫
          (λ_ ((b ⊗ x) ⟶[V] (b ⊗ y))).inv ≫
          (eId V c ⊗ₘ 𝟙 ((b ⊗ x) ⟶[V] (b ⊗ y))) ≫
          d.tensorMap c c (b ⊗ x) (b ⊗ y)) ≫
        eHomWhiskerRight V (α_ c b x).hom (c ⊗ (b ⊗ y)) := by
  let H : V := x ⟶[V] y
  let C : V := c ⟶[V] c
  let B : V := b ⟶[V] b
  let Hb : V := (b ⊗ x) ⟶[V] (b ⊗ y)
  let t : (𝟙_ V) ⟶ C ⊗ B :=
    (λ_ (𝟙_ V)).inv ≫ (eId V c ⊗ₘ eId V b)
  let q : H ⟶ (C ⊗ B) ⊗ H := (λ_ H).inv ≫ (t ⊗ₘ 𝟙 H)
  let f : (C ⊗ B) ⊗ H ⟶ (((c ⊗ b) ⊗ x) ⟶[V] ((c ⊗ b) ⊗ y)) :=
    (d.tensorMap c c b b ▷ H) ≫ d.tensorMap (c ⊗ b) (c ⊗ b) x y
  let g : (C ⊗ B) ⊗ H ⟶ ((c ⊗ (b ⊗ x)) ⟶[V] (c ⊗ (b ⊗ y))) :=
    (α_ C B H).hom ≫ C ◁ d.tensorMap b b x y ≫
      d.tensorMap c c (b ⊗ x) (b ⊗ y)
  let j (K : V) : K ⟶ C ⊗ K := (λ_ K).inv ≫ (eId V c ⊗ₘ 𝟙 K)
  let qb : H ⟶ B ⊗ H := (λ_ H).inv ≫ (eId V b ⊗ₘ 𝟙 H)
  let lb : H ⟶ Hb := qb ≫ d.tensorMap b b x y
  let lc : Hb ⟶ ((c ⊗ (b ⊗ x)) ⟶[V] (c ⊗ (b ⊗ y))) :=
    j Hb ≫ d.tensorMap c c (b ⊗ x) (b ⊗ y)
  let lcb : H ⟶ (((c ⊗ b) ⊗ x) ⟶[V] ((c ⊗ b) ⊗ y)) :=
    (λ_ H).inv ≫ (eId V (c ⊗ b) ⊗ₘ 𝟙 H) ≫
      d.tensorMap (c ⊗ b) (c ⊗ b) x y
  have hWhole : f ≫
      eHomWhiskerLeft V ((c ⊗ b) ⊗ x) (α_ c b y).hom =
      g ≫ eHomWhiskerRight V (α_ c b x).hom (c ⊗ (b ⊗ y)) :=
    unitGradedNaturality_eq_whisker f g (α_ c b x).hom (α_ c b y).hom
      (d.associatorNaturality c c b b x y)
  have hId : t ≫ d.tensorMap c c b b = eId V (c ⊗ b) := by
    simpa only [t, Enriched.prodEId] using d.tensorMap_id c b
  have hPair : (t ⊗ₘ 𝟙 H) ≫ (d.tensorMap c c b b ▷ H) =
      eId V (c ⊗ b) ⊗ₘ 𝟙 H := by
    have h := tensorHom_comp_tensorHom t (𝟙 H)
      (d.tensorMap c c b b) (𝟙 H)
    simpa only [Category.id_comp, tensorHom_id, hId] using h
  have hLeft : q ≫ f = lcb := by
    change ((λ_ H).inv ≫ (t ⊗ₘ 𝟙 H)) ≫
        ((d.tensorMap c c b b ▷ H) ≫
          d.tensorMap (c ⊗ b) (c ⊗ b) x y) = lcb
    calc
      _ = (λ_ H).inv ≫ ((t ⊗ₘ 𝟙 H) ≫ (d.tensorMap c c b b ▷ H)) ≫
          d.tensorMap (c ⊗ b) (c ⊗ b) x y := by
        simp only [Category.assoc]
      _ = (λ_ H).inv ≫ (eId V (c ⊗ b) ⊗ₘ 𝟙 H) ≫
          d.tensorMap (c ⊗ b) (c ⊗ b) x y := by
        rw [hPair]
      _ = lcb := rfl
  have hPadding : q ≫ (α_ C B H).hom = j H ≫ C ◁ qb := by
    simpa only [q, t, j, qb, C, B, Category.assoc] using
      doubleLeftPointPaddingForProof H C B (eId V c) (eId V b)
  have hInsert : j H ≫ C ◁ lb = lb ≫ j Hb := by
    simpa only [j] using leftPointInsertionNaturalForProof (eId V c) lb
  have hRight : q ≫ g = lb ≫ lc := by
    change q ≫ ((α_ C B H).hom ≫ C ◁ d.tensorMap b b x y ≫
        d.tensorMap c c (b ⊗ x) (b ⊗ y)) = lb ≫ lc
    calc
      _ = (q ≫ (α_ C B H).hom) ≫ C ◁ d.tensorMap b b x y ≫
          d.tensorMap c c (b ⊗ x) (b ⊗ y) := by
        simp only [Category.assoc]
      _ = (j H ≫ C ◁ qb) ≫ C ◁ d.tensorMap b b x y ≫
          d.tensorMap c c (b ⊗ x) (b ⊗ y) := by
        rw [hPadding]
      _ = (j H ≫ C ◁ lb) ≫ d.tensorMap c c (b ⊗ x) (b ⊗ y) := by
        simp only [lb, MonoidalCategory.whiskerLeft_comp, Category.assoc]
      _ = (lb ≫ j Hb) ≫ d.tensorMap c c (b ⊗ x) (b ⊗ y) := by
        rw [hInsert]
      _ = lb ≫ lc := by
        simp only [lc, Category.assoc]
  have hPre := congrArg
    (fun z : (C ⊗ B) ⊗ H ⟶
        (((c ⊗ b) ⊗ x) ⟶[V] (c ⊗ (b ⊗ y))) => q ≫ z) hWhole
  have hLeftEnd : q ≫
      (f ≫ eHomWhiskerLeft V ((c ⊗ b) ⊗ x) (α_ c b y).hom) =
      lcb ≫ eHomWhiskerLeft V ((c ⊗ b) ⊗ x) (α_ c b y).hom :=
    (Category.assoc q f
      (eHomWhiskerLeft V ((c ⊗ b) ⊗ x) (α_ c b y).hom)).symm.trans
      (congrArg
        (fun z : H ⟶ (((c ⊗ b) ⊗ x) ⟶[V] ((c ⊗ b) ⊗ y)) =>
          z ≫ eHomWhiskerLeft V ((c ⊗ b) ⊗ x) (α_ c b y).hom) hLeft)
  have hRightEnd : q ≫
      (g ≫ eHomWhiskerRight V (α_ c b x).hom (c ⊗ (b ⊗ y))) =
      (lb ≫ lc) ≫ eHomWhiskerRight V (α_ c b x).hom (c ⊗ (b ⊗ y)) :=
    (Category.assoc q g
      (eHomWhiskerRight V (α_ c b x).hom (c ⊗ (b ⊗ y)))).symm.trans
      (congrArg
        (fun z : H ⟶ ((c ⊗ (b ⊗ x)) ⟶[V] (c ⊗ (b ⊗ y))) =>
          z ≫ eHomWhiskerRight V (α_ c b x).hom (c ⊗ (b ⊗ y))) hRight)
  simpa only [lcb, lb, lc, j, qb, H, Hb, Category.assoc] using
    hLeftEnd.symm.trans (hPre.trans hRightEnd)

end CategoryTheory.Enriched.SphereOperator
