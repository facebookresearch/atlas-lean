/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexGeneratorAssociativity
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexAssociator
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCategory
public import MathlibExt.CategoryTheory.Enriched.ScalarCoherence

/-!
# Right tensor shifts of the full sphere-operator coend

The original weight map and unchanged coefficient functor induce an enriched
right tensor shift on the full sphere-operator category. Its characteristic,
unit and composition equations retain all coend pairs and original tensor data.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace CategoryTheory.Enriched

namespace GenericRightTensor

universe uG vG uA vA

open CategoryTheory.Enriched.SphereOperator
open Opposite CategoryTheory.BraidedCategory

variable {Vg : Type uG} [Category.{vG} Vg] [MonoidalCategory Vg]
  [BraidedCategory Vg]
  {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
  [EnrichedOrdinaryCategory Vg A]

attribute [local instance] MonoidalClosed.enrichedCategorySelf

/-- This is the actual final-factor extension of the original source label. -/
def label (r n k a : A) (f : a ⊗ n ⟶ k) : a ⊗ (n ⊗ r) ⟶ k ⊗ r :=
  (α_ a n r).inv ≫ (f ▷ r)

/-- The whole original weight Hom is shifted by the existing enriched tensor
functor and the original inverse associator. -/
def weightShiftMap (d : EnrichedMonoidalCategoryData Vg A) (r n k a : A) :
    ((a ⊗ n) ⟶[Vg] k) ⟶ ((a ⊗ (n ⊗ r)) ⟶[Vg] (k ⊗ r)) :=
  (fixedRightTensor d r).map (a ⊗ n) k ≫
    eHomWhiskerRight Vg (α_ a n r).inv (k ⊗ r)

set_option backward.isDefEq.respectTransparency false in
/-- Every original source point keeps its exact original shifted label. -/
theorem weightShiftMap_point (d : EnrichedMonoidalCategoryData Vg A)
    (r n k a : A) (f : a ⊗ n ⟶ k) :
    eHomEquiv Vg f ≫ weightShiftMap d r n k a = eHomEquiv Vg (label r n k a f) := by
  unfold weightShiftMap label
  rw [← Category.assoc, fixedRightTensor_point]
  exact eHomEquiv_comp_eHomWhiskerRight Vg A (α_ a n r).inv (f ▷ r)

/-- The full source-point family is retained before any native coefficient
or particular generator is substituted. -/
theorem weightShiftMap_point_function (d : EnrichedMonoidalCategoryData Vg A) :
    (fun (r n k a : A) (f : a ⊗ n ⟶ k) =>
      eHomEquiv Vg f ≫ weightShiftMap d r n k a) =
      fun (r n k a : A) (f : a ⊗ n ⟶ k) => eHomEquiv Vg (label r n k a f) := by
  funext r n k a f
  exact weightShiftMap_point d r n k a f

/-- The shifted original unit label is the original unitor at the shifted
object, with no change of coefficient-unit data. -/
theorem label_unit (r n : A) :
    label r n n (𝟙_ A) (λ_ n).hom = (λ_ (n ⊗ r)).hom := by
  unfold label
  monoidal

/-- The whole actual enriched unit-point function is preserved. -/
theorem weightShiftMap_unit_point (d : EnrichedMonoidalCategoryData Vg A) (r n : A) :
    eHomEquiv Vg (λ_ n).hom ≫ weightShiftMap d r n n (𝟙_ A) =
      eHomEquiv Vg (λ_ (n ⊗ r)).hom := by
  rw [weightShiftMap_point, label_unit]

set_option backward.isDefEq.respectTransparency false in
/-- The original associator compares twice right-tensoring with tensoring
by the original product. Its equation retains the complete coefficient Hom. -/
private theorem rightTensor_associator (d : EnrichedMonoidalCategoryData Vg A)
    (r n a b : A) :
    ((fixedRightTensor d n).map a b ≫
        (fixedRightTensor d r).map (a ⊗ n) (b ⊗ n)) ≫
        eHomWhiskerLeft Vg ((a ⊗ n) ⊗ r) (α_ b n r).hom =
      (fixedRightTensor d (n ⊗ r)).map a b ≫
        eHomWhiskerRight Vg (α_ a n r).hom (b ⊗ (n ⊗ r)) := by
  let H : Vg := a ⟶[Vg] b
  let N : Vg := n ⟶[Vg] n
  let R : Vg := r ⟶[Vg] r
  let K : Vg := (a ⊗ n) ⟶[Vg] (b ⊗ n)
  let v : H ⟶ H ⊗ N := (ρ_ H).inv ≫ (𝟙 H ⊗ₘ eId Vg n)
  let q : H ⟶ (H ⊗ N) ⊗ R :=
    v ≫ (ρ_ (H ⊗ N)).inv ≫ (𝟙 (H ⊗ N) ⊗ₘ eId Vg r)
  let leftMap : (H ⊗ N) ⊗ R ⟶
      (((a ⊗ n) ⊗ r) ⟶[Vg] ((b ⊗ n) ⊗ r)) :=
    (d.tensorMap a b n n ▷ R) ≫ d.tensorMap (a ⊗ n) (b ⊗ n) r r
  let rightMap : (H ⊗ N) ⊗ R ⟶
      ((a ⊗ (n ⊗ r)) ⟶[Vg] (b ⊗ (n ⊗ r))) :=
    (α_ H N R).hom ≫ (H ◁ d.tensorMap n n r r) ≫
      d.tensorMap a b (n ⊗ r) (n ⊗ r)
  have hNatural : leftMap ≫
        eHomWhiskerLeft Vg ((a ⊗ n) ⊗ r) (α_ b n r).hom =
      rightMap ≫ eHomWhiskerRight Vg (α_ a n r).hom (b ⊗ (n ⊗ r)) := by
    apply unitGradedNaturality_eq_whisker
    simpa only [leftMap, rightMap, H, N, R, Category.assoc] using
      d.associatorNaturality a b n n r r
  have hLeft : q ≫ leftMap =
      (fixedRightTensor d n).map a b ≫
        (fixedRightTensor d r).map (a ⊗ n) (b ⊗ n) := by
    have hUnit : (ρ_ (H ⊗ N)).inv ≫
        (d.tensorMap a b n n ⊗ₘ eId Vg r) =
        d.tensorMap a b n n ≫ (ρ_ K).inv ≫ (𝟙 K ⊗ₘ eId Vg r) := by
      simpa only [id_tensorHom] using
        rightUnitor_inv_comp_tensorHom (d.tensorMap a b n n) (eId Vg r)
    calc
      q ≫ leftMap = v ≫ (ρ_ (H ⊗ N)).inv ≫
          (d.tensorMap a b n n ⊗ₘ eId Vg r) ≫
          d.tensorMap (a ⊗ n) (b ⊗ n) r r := by
        dsimp only [q, leftMap]
        simp only [← tensorHom_id, Category.assoc, tensorHom_comp_tensorHom_assoc,
          Category.comp_id, Category.id_comp]
      _ = v ≫ d.tensorMap a b n n ≫ (ρ_ K).inv ≫
          (𝟙 K ⊗ₘ eId Vg r) ≫ d.tensorMap (a ⊗ n) (b ⊗ n) r r := by
        simpa only [Category.assoc] using congrArg
          (fun z => v ≫ z ≫ d.tensorMap (a ⊗ n) (b ⊗ n) r r) hUnit
      _ = _ := by
        simp only [fixedRightTensor_map, v, H, K, Category.assoc]
  have hIdentity : (λ_ (𝟙_ Vg)).inv ≫ (eId Vg n ⊗ₘ eId Vg r) ≫
      d.tensorMap n n r r = eId Vg (n ⊗ r) := by
    simpa only [Enriched.prodEId, Category.assoc] using d.tensorMap_id n r
  have hPrefix : q ≫ (α_ H N R).hom ≫ (H ◁ d.tensorMap n n r r) =
      (ρ_ H).inv ≫ H ◁ ((λ_ (𝟙_ Vg)).inv ≫
        (eId Vg n ⊗ₘ eId Vg r) ≫ d.tensorMap n n r r) := by
    let e : H ⊗ (𝟙_ Vg) ⟶ H ⊗ N := 𝟙 H ⊗ₘ eId Vg n
    have hMove : e ≫ (ρ_ (H ⊗ N)).inv =
        (ρ_ (H ⊗ (𝟙_ Vg))).inv ≫ (e ▷ (𝟙_ Vg)) :=
      rightUnitor_inv_naturality e
    have hPair : (e ▷ (𝟙_ Vg)) ≫ (𝟙 (H ⊗ N) ⊗ₘ eId Vg r) =
        e ⊗ₘ eId Vg r := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp]
    have hAssoc : (e ⊗ₘ eId Vg r) ≫ (α_ H N R).hom =
        (α_ H (𝟙_ Vg) (𝟙_ Vg)).hom ≫
          (𝟙 H ⊗ₘ (eId Vg n ⊗ₘ eId Vg r)) :=
      associator_naturality (𝟙 H) (eId Vg n) (eId Vg r)
    have hUnit : (ρ_ (H ⊗ (𝟙_ Vg))).inv ≫
        (α_ H (𝟙_ Vg) (𝟙_ Vg)).hom = H ◁ (λ_ (𝟙_ Vg)).inv := by
      monoidal
    calc
      q ≫ (α_ H N R).hom ≫ H ◁ d.tensorMap n n r r =
          (ρ_ H).inv ≫ e ≫ (ρ_ (H ⊗ N)).inv ≫
            (𝟙 (H ⊗ N) ⊗ₘ eId Vg r) ≫ (α_ H N R).hom ≫
              H ◁ d.tensorMap n n r r := by
        simp only [q, v, e, Category.assoc]
      _ = (ρ_ H).inv ≫ (ρ_ (H ⊗ (𝟙_ Vg))).inv ≫
          (e ⊗ₘ eId Vg r) ≫ (α_ H N R).hom ≫ H ◁ d.tensorMap n n r r := by
        rw [← Category.assoc e, hMove]
        simp only [Category.assoc]
        rw [← Category.assoc (e ▷ (𝟙_ Vg)), hPair]
      _ = (ρ_ H).inv ≫ (ρ_ (H ⊗ (𝟙_ Vg))).inv ≫
          (α_ H (𝟙_ Vg) (𝟙_ Vg)).hom ≫
            (𝟙 H ⊗ₘ (eId Vg n ⊗ₘ eId Vg r)) ≫ H ◁ d.tensorMap n n r r := by
        rw [← Category.assoc (e ⊗ₘ eId Vg r), hAssoc]
        simp only [Category.assoc]
      _ = (ρ_ H).inv ≫ H ◁ (λ_ (𝟙_ Vg)).inv ≫
          (𝟙 H ⊗ₘ (eId Vg n ⊗ₘ eId Vg r)) ≫ H ◁ d.tensorMap n n r r := by
        rw [← Category.assoc (ρ_ (H ⊗ (𝟙_ Vg))).inv, hUnit]
      _ = _ := by
        simp only [id_tensorHom, whiskerLeft_comp]
  have hRight : q ≫ rightMap = (fixedRightTensor d (n ⊗ r)).map a b := by
    calc
      q ≫ rightMap = (q ≫ (α_ H N R).hom ≫ H ◁ d.tensorMap n n r r) ≫
          d.tensorMap a b (n ⊗ r) (n ⊗ r) := by
        simp only [rightMap, Category.assoc]
      _ = ((ρ_ H).inv ≫ H ◁ ((λ_ (𝟙_ Vg)).inv ≫
          (eId Vg n ⊗ₘ eId Vg r) ≫ d.tensorMap n n r r)) ≫
          d.tensorMap a b (n ⊗ r) (n ⊗ r) :=
        congrArg (fun z => z ≫ d.tensorMap a b (n ⊗ r) (n ⊗ r)) hPrefix
      _ = ((ρ_ H).inv ≫ H ◁ eId Vg (n ⊗ r)) ≫
          d.tensorMap a b (n ⊗ r) (n ⊗ r) := by rw [hIdentity]
      _ = _ := by
        simp only [fixedRightTensor_map, H, id_tensorHom, Category.assoc]
  have h := congrArg (fun z => q ≫ z) hNatural
  simpa only [← Category.assoc, hLeft, hRight] using h

/-- The original associator equation holds for the complete right-tensor
map functions, before a source Hom or native label is substituted. -/
theorem rightTensor_associator_function (d : EnrichedMonoidalCategoryData Vg A) :
    (fun (r n a b : A) =>
      ((fixedRightTensor d n).map a b ≫
          (fixedRightTensor d r).map (a ⊗ n) (b ⊗ n)) ≫
        eHomWhiskerLeft Vg ((a ⊗ n) ⊗ r) (α_ b n r).hom) =
      fun (r n a b : A) =>
        (fixedRightTensor d (n ⊗ r)).map a b ≫
          eHomWhiskerRight Vg (α_ a n r).hom (b ⊗ (n ⊗ r)) := by
  funext r n a b
  exact rightTensor_associator d r n a b


set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the original associator keeps the whole enriched Hom
when comparing single and repeated final-factor tensoring. -/
private theorem rightTensor_associator_inv (d : EnrichedMonoidalCategoryData Vg A)
    (r n a b : A) :
    (fixedRightTensor d (n ⊗ r)).map a b ≫
        eHomWhiskerLeft Vg (a ⊗ (n ⊗ r)) (α_ b n r).inv =
      ((fixedRightTensor d n).map a b ≫
        (fixedRightTensor d r).map (a ⊗ n) (b ⊗ n)) ≫
        eHomWhiskerRight Vg (α_ a n r).inv ((b ⊗ n) ⊗ r) := by
  have h := congrArg
    (fun z => z ≫ eHomWhiskerRight Vg (α_ a n r).inv (b ⊗ (n ⊗ r)) ≫
      eHomWhiskerLeft Vg (a ⊗ (n ⊗ r)) (α_ b n r).inv)
    (rightTensor_associator d r n a b)
  simpa only [fixedRightTensor_obj, Category.assoc, eHom_whisker_exchange_assoc,
    ← eHomWhiskerLeft_comp, ← eHomWhiskerRight_comp,
    ← eHomWhiskerLeft_comp_assoc, ← eHomWhiskerRight_comp_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, eHomWhiskerLeft_id,
    eHomWhiskerRight_id, Category.id_comp, Category.comp_id] using h.symm

/-- Both full inverse-associator Hom functions agree before specialization. -/
theorem rightTensor_associator_inv_function (d : EnrichedMonoidalCategoryData Vg A) :
    (fun (r n a b : A) =>
      (fixedRightTensor d (n ⊗ r)).map a b ≫
        eHomWhiskerLeft Vg (a ⊗ (n ⊗ r)) (α_ b n r).inv) =
      fun (r n a b : A) =>
        ((fixedRightTensor d n).map a b ≫
          (fixedRightTensor d r).map (a ⊗ n) (b ⊗ n)) ≫
          eHomWhiskerRight Vg (α_ a n r).inv ((b ⊗ n) ⊗ r) := by
  funext r n a b
  exact rightTensor_associator_inv d r n a b

variable [MonoidalClosed Vg]

set_option backward.isDefEq.respectTransparency false in
/-- The actual final-factor weight map commutes with the full uncurried
enriched action. Both weight Hom factors and the whole index Hom are retained. -/
theorem weightShiftMap_naturality (d : EnrichedMonoidalCategoryData Vg A)
    (r n k a b : A) :
    MonoidalClosed.uncurry ((weight d n k).map (op b) (op a)) ≫
        weightShiftMap d r n k a =
      (weightShiftMap d r n k b ⊗ₘ 𝟙 (a ⟶[Vg] b)) ≫
        MonoidalClosed.uncurry
          ((weight d (n ⊗ r) (k ⊗ r)).map (op b) (op a)) := by
  let an : A := a ⊗ n
  let bn : A := b ⊗ n
  let anr : A := an ⊗ r
  let bnr : A := bn ⊗ r
  let X : A := a ⊗ (n ⊗ r)
  let Y : A := b ⊗ (n ⊗ r)
  let Z : A := k ⊗ r
  let H : Vg := a ⟶[Vg] b
  let W : Vg := bn ⟶[Vg] k
  let P : Vg := an ⟶[Vg] bn
  let Q : Vg := bnr ⟶[Vg] Z
  let U : Vg := X ⟶[Vg] Y
  let W' : Vg := Y ⟶[Vg] Z
  let f : H ⟶ P := (fixedRightTensor d n).map a b
  let p : P ⟶ (anr ⟶[Vg] bnr) := (fixedRightTensor d r).map an bn
  let q : W ⟶ Q := (fixedRightTensor d r).map bn k
  let t : H ⟶ U := (fixedRightTensor d (n ⊗ r)).map a b
  let va : (anr ⟶[Vg] bnr) ⟶ (X ⟶[Vg] bnr) :=
    eHomWhiskerRight Vg (α_ a n r).inv bnr
  let ub : U ⟶ (X ⟶[Vg] bnr) :=
    eHomWhiskerLeft Vg X (α_ b n r).inv
  let vb : Q ⟶ W' := eHomWhiskerRight Vg (α_ b n r).inv Z
  let z : W ⟶ W' := q ≫ vb
  have hBraid : (W ◁ f) ≫ (β_ W P).hom =
      (β_ W H).hom ≫ (f ⊗ₘ 𝟙 W) := by
    simpa only [id_tensorHom] using braiding_naturality (𝟙 W) f
  have hMap : eComp Vg an bn k ≫ (fixedRightTensor d r).map an k =
      (p ⊗ₘ q) ≫ eComp Vg anr bnr Z := by
    simpa only [p, q, anr, bnr, Z] using fixedRightTensor_comp d r an bn k
  have hPre : eComp Vg anr bnr Z ≫
      eHomWhiskerRight Vg (α_ a n r).inv Z =
        (va ▷ Q) ≫ eComp Vg X bnr Z := by
    simpa only [va, Q, X, anr, an] using
      eComp_eHomWhiskerRight Vg (α_ a n r).inv bnr Z
  have hLeft :
      MonoidalClosed.uncurry ((weight d n k).map (op b) (op a)) ≫
          weightShiftMap d r n k a =
        (β_ W H).hom ≫ ((f ≫ p ≫ va) ⊗ₘ q) ≫ eComp Vg X bnr Z := by
    rw [weight_uncurry_map]
    simp only [weightShiftMap, Category.assoc]
    change (W ◁ f) ≫ (β_ W P).hom ≫ eComp Vg an bn k ≫
        (fixedRightTensor d r).map an k ≫
          eHomWhiskerRight Vg (α_ a n r).inv Z = _
    calc
      _ = (β_ W H).hom ≫ (f ⊗ₘ 𝟙 W) ≫
          eComp Vg an bn k ≫ (fixedRightTensor d r).map an k ≫
            eHomWhiskerRight Vg (α_ a n r).inv Z := by
        rw [← Category.assoc (W ◁ f), hBraid]
        simp only [Category.assoc]
      _ = (β_ W H).hom ≫ (f ⊗ₘ 𝟙 W) ≫ (p ⊗ₘ q) ≫
          eComp Vg anr bnr Z ≫ eHomWhiskerRight Vg (α_ a n r).inv Z := by
        rw [← Category.assoc (eComp Vg an bn k), hMap]
        simp only [Category.assoc]
      _ = (β_ W H).hom ≫ ((f ≫ p) ⊗ₘ q) ≫
          eComp Vg anr bnr Z ≫ eHomWhiskerRight Vg (α_ a n r).inv Z := by
        simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]
      _ = (β_ W H).hom ≫ ((f ≫ p) ⊗ₘ q) ≫
          (va ▷ Q) ≫ eComp Vg X bnr Z := by
        rw [hPre]
      _ = _ := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.comp_id, Category.assoc]
  have hPair : (z ⊗ₘ 𝟙 H) ≫ (W' ◁ t) = z ⊗ₘ t := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp]
  have hRight :
      (weightShiftMap d r n k b ⊗ₘ 𝟙 (a ⟶[Vg] b)) ≫
          MonoidalClosed.uncurry
            ((weight d (n ⊗ r) (k ⊗ r)).map (op b) (op a)) =
        (β_ W H).hom ≫ (t ⊗ₘ z) ≫ eComp Vg X Y Z := by
    rw [weight_uncurry_map]
    change (z ⊗ₘ 𝟙 H) ≫ (W' ◁ t) ≫ (β_ W' U).hom ≫
      eComp Vg X Y Z = _
    rw [← Category.assoc (z ⊗ₘ 𝟙 H), hPair]
    simpa only [Category.assoc] using
      congrArg (fun m => m ≫ eComp Vg X Y Z) (braiding_naturality z t)
  have hFirst : f ≫ p ≫ va = t ≫ ub := by
    simpa only [f, p, va, t, ub, an, bn, anr, bnr, X, Y,
      Category.assoc] using (rightTensor_associator_inv d r n a b).symm
  have hMiddle : (ub ▷ Q) ≫ eComp Vg X bnr Z =
      (U ◁ vb) ≫ eComp Vg X Y Z := by
    have h := eHom_whisker_cancel_inv Vg (X := X) (Z := Z) (α_ b n r)
    have ht := congrArg
      (fun m : (U ⊗ W') ⟶ (X ⟶[Vg] Z) => (U ◁ vb) ≫ m) h
    rw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← eHomWhiskerRight_comp, Iso.hom_inv_id, eHomWhiskerRight_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp] at ht
    exact ht
  rw [hLeft, hRight, hFirst]
  have h := congrArg
    (fun m : (U ⊗ Q) ⟶ (X ⟶[Vg] Z) => (β_ W H).hom ≫ (t ⊗ₘ q) ≫ m)
    hMiddle
  simpa only [← tensorHom_id, ← id_tensorHom,
    tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp,
    z, Category.assoc] using h

/-- The complete uncurried weight-action functions agree before any native
Hom input, coefficient or index label is chosen. -/
theorem weightShiftMap_naturality_function (d : EnrichedMonoidalCategoryData Vg A) :
    (fun (r n k a b : A) =>
      MonoidalClosed.uncurry ((weight d n k).map (op b) (op a)) ≫
        weightShiftMap d r n k a) =
      fun (r n k a b : A) =>
        (weightShiftMap d r n k b ⊗ₘ 𝟙 (a ⟶[Vg] b)) ≫
          MonoidalClosed.uncurry
            ((weight d (n ⊗ r) (k ⊗ r)).map (op b) (op a)) := by
  funext r n k a b
  exact weightShiftMap_naturality d r n k a b

/-- The proved full weight naturality constructs an actual unit-graded
transformation on the original opposite index. -/
def weightShift (d : EnrichedMonoidalCategoryData Vg A) (r n k : A) :
    GradedNatTrans ((Center.ofBraided Vg).obj (𝟙_ Vg))
      (weight d n k) (weight d (n ⊗ r) (k ⊗ r)) :=
  GradedNatTrans.unitOfComponents
    (fun a => weightShiftMap d r n k a.unop)
    (fun a b => weightShiftMap_naturality d r n k b.unop a.unop)

/-- Every whole ordinary component is the actual original weight map. -/
theorem weightShift_component (d : EnrichedMonoidalCategoryData Vg A)
    (r n k a : A) :
    (eHomEquiv Vg).symm ((weightShift d r n k).app (op a)) =
      weightShiftMap d r n k a :=
  GradedNatTrans.unitOfComponents_component _ _ _

/-- All original component functions are retained before coend descent. -/
theorem weightShift_component_function (d : EnrichedMonoidalCategoryData Vg A) :
    (fun (r n k a : A) =>
      (eHomEquiv Vg).symm ((weightShift d r n k).app (op a))) =
      fun (r n k a : A) => weightShiftMap d r n k a := by
  funext r n k a
  exact weightShift_component d r n k a

attribute [local instance] Enriched.prodCategory

omit [MonoidalClosed Vg] in
/-- Insert the original fixed left identity in the original enriched product. -/
private def leftTensorProduct (c : A) : EnrichedFunctor Vg A (A × A) where
  obj x := (c, x)
  map x y := (λ_ (x ⟶[Vg] y)).inv ≫ (eId Vg c ⊗ₘ 𝟙 (x ⟶[Vg] y))
  map_id x := by
    change eId Vg x ≫ (λ_ (x ⟶[Vg] x)).inv ≫
        (eId Vg c ⊗ₘ 𝟙 (x ⟶[Vg] x)) =
      (λ_ (𝟙_ Vg)).inv ≫ (eId Vg c ⊗ₘ eId Vg x)
    rw [leftUnitor_inv_naturality_assoc]
    slice_lhs 2 3 =>
      rw [← id_tensorHom, tensorHom_comp_tensorHom]
      simp
  map_comp x y z := by
    have hIdentity : (eId Vg c ⊗ₘ eId Vg c) ≫ eComp Vg c c c =
        (λ_ (𝟙_ Vg)).hom ≫ eId Vg c := by
      rw [← cancel_epi (λ_ (𝟙_ Vg)).inv]
      simp only [Iso.inv_hom_id_assoc]
      rw [leftUnitor_inv_comp_tensorHom_assoc, e_id_comp, Category.comp_id]
    have hTensorUnit {X Y Z : Vg} (f : (𝟙_ Vg) ⟶ Y) (g : X ⟶ Z) :
        f ⊗ₘ g = (λ_ X).hom ≫ g ≫ (λ_ Z).inv ≫ f ▷ Z := by
      rw [← cancel_epi (λ_ X).inv]
      simp only [Iso.inv_hom_id_assoc]
      exact leftUnitor_inv_comp_tensorHom f g
    change eComp Vg x y z ≫ (λ_ (x ⟶[Vg] z)).inv ≫
        (eId Vg c ⊗ₘ 𝟙 (x ⟶[Vg] z)) =
      (((λ_ (x ⟶[Vg] y)).inv ≫ (eId Vg c ⊗ₘ 𝟙 (x ⟶[Vg] y))) ⊗ₘ
        ((λ_ (y ⟶[Vg] z)).inv ≫ (eId Vg c ⊗ₘ 𝟙 (y ⟶[Vg] z)))) ≫
        tensorμ (c ⟶[Vg] c) (x ⟶[Vg] y) (c ⟶[Vg] c) (y ⟶[Vg] z) ≫
        (eComp Vg c c c ⊗ₘ eComp Vg x y z)
    rw [← cancel_epi (λ_ ((x ⟶[Vg] y) ⊗ (y ⟶[Vg] z))).hom]
    nth_rewrite 2 [MonoidalCategory.tensor_left_unitality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [tensorμ_natural_assoc, tensorHom_comp_tensorHom]
    simp only [id_tensorHom_id, Category.id_comp]
    rw [hIdentity]
    nth_rewrite 2 [← Category.id_comp (eComp Vg x y z)]
    rw [← tensorHom_comp_tensorHom]
    simp only [tensorHom_id]
    rw [hTensorUnit, ← MonoidalCategory.leftUnitor_monoidal_assoc,
      ← MonoidalCategory.tensor_left_unitality_assoc]

omit [MonoidalClosed Vg] in
/-- The proof uses the original index-generator tensor expression as a genuine
functor built from the original product and selected enriched tensor. -/
private def leftTensor (d : EnrichedMonoidalCategoryData Vg A) (c : A) :
    EnrichedFunctor Vg A A :=
  (leftTensorProduct (Vg := Vg) c).comp Vg d.tensorEnrichedFunctor

omit [MonoidalClosed Vg] in
private theorem leftTensor_map (d : EnrichedMonoidalCategoryData Vg A)
    (c x y : A) :
    (leftTensor d c).map x y = (λ_ (x ⟶[Vg] y)).inv ≫
      (eId Vg c ⊗ₘ 𝟙 (x ⟶[Vg] y)) ≫ d.tensorMap c c x y := by
  change ((λ_ (x ⟶[Vg] y)).inv ≫
    (eId Vg c ⊗ₘ 𝟙 (x ⟶[Vg] y))) ≫ d.tensorMap c c x y = _
  exact Category.assoc _ _ _

omit [MonoidalClosed Vg] in
set_option backward.isDefEq.respectTransparency false in
/-- The same left tensor map preserves every original ordinary arrow point. -/
private theorem leftTensor_point (d : EnrichedMonoidalCategoryData Vg A)
    (c x y : A) (f : x ⟶ y) :
    eHomEquiv Vg f ≫ (leftTensor d c).map x y = eHomEquiv Vg (c ◁ f) := by
  let H : Vg := x ⟶[Vg] y
  let e : (𝟙_ Vg) ⟶ H := eHomEquiv Vg f
  have hUnit : e ≫ (λ_ H).inv = (λ_ (𝟙_ Vg)).inv ≫ (𝟙_ Vg ◁ e) :=
    leftUnitor_inv_naturality e
  have hPair : (𝟙_ Vg ◁ e) ≫ (eId Vg c ⊗ₘ 𝟙 H) = eId Vg c ⊗ₘ e := by
    simpa only [Category.id_comp, Category.comp_id, id_tensorHom] using
      tensorHom_comp_tensorHom (𝟙 (𝟙_ Vg)) e (eId Vg c) (𝟙 H)
  rw [leftTensor_map]
  change e ≫ (λ_ H).inv ≫ (eId Vg c ⊗ₘ 𝟙 H) ≫ d.tensorMap c c x y = _
  rw [← Category.assoc e, hUnit]
  simp only [Category.assoc]
  rw [← Category.assoc (𝟙_ Vg ◁ e), hPair]
  simpa only [e, eHomEquiv_id, id_tensorHom] using d.tensorMap_eHomEquiv (𝟙 c) f

omit [MonoidalClosed Vg] in
set_option backward.isDefEq.respectTransparency false in
/-- The approved public full-precomposition API applies to the exact original
identity-fixed left tensor expression, using its actual point value. -/
private theorem leftTensor_precomposition (d : EnrichedMonoidalCategoryData Vg A)
    (c x y z : A) (f : x ⟶ y) :
    eHomWhiskerRight Vg f z ≫ (leftTensor d c).map x z =
      (leftTensor d c).map y z ≫ eHomWhiskerRight Vg (c ◁ f) (c ⊗ z) := by
  have hp := leftTensor_point d c x y f
  have hr := congrArg
    (fun p : (𝟙_ Vg) ⟶ ((c ⊗ x) ⟶[Vg] (c ⊗ y)) => (eHomEquiv Vg).symm p) hp
  simp only [Equiv.symm_apply_apply] at hr
  have h := enrichedFunctorFullPrecomposition (leftTensor d c) x y z f
  have hWhisker := congrArg
    (fun j : c ⊗ x ⟶ c ⊗ y => eHomWhiskerRight Vg j (c ⊗ z)) hr
  have hTail := congrArg
    (fun m : ((c ⊗ y) ⟶[Vg] (c ⊗ z)) ⟶ ((c ⊗ x) ⟶[Vg] (c ⊗ z)) =>
      (leftTensor d c).map y z ≫ m) hWhisker
  exact h.trans hTail

omit [MonoidalClosed Vg] in
private theorem leftTensor_obj (d : EnrichedMonoidalCategoryData Vg A) (c x : A) :
    (leftTensor d c).obj x = c ⊗ x := rfl

omit [MonoidalClosed Vg] in
set_option backward.isDefEq.respectTransparency false in
/-- The original associator is natural on the whole middle Hom object when
the first and final factors are fixed by their actual enriched identities. -/
private theorem leftRightTensor_associator (d : EnrichedMonoidalCategoryData Vg A)
    (c r x y : A) :
    ((leftTensor d c).map x y ≫
        (fixedRightTensor d r).map (c ⊗ x) (c ⊗ y)) ≫
        eHomWhiskerLeft Vg ((c ⊗ x) ⊗ r) (α_ c y r).hom =
      ((fixedRightTensor d r).map x y ≫
        (leftTensor d c).map (x ⊗ r) (y ⊗ r)) ≫
        eHomWhiskerRight Vg (α_ c x r).hom (c ⊗ (y ⊗ r)) := by
  let H : Vg := x ⟶[Vg] y
  let C : Vg := c ⟶[Vg] c
  let R : Vg := r ⟶[Vg] r
  let K : Vg := (c ⊗ x) ⟶[Vg] (c ⊗ y)
  let T : Vg := (x ⊗ r) ⟶[Vg] (y ⊗ r)
  let p : (𝟙_ Vg) ⟶ C := eId Vg c
  let e : (𝟙_ Vg) ⟶ R := eId Vg r
  let j : H ⟶ C ⊗ H := (λ_ H).inv ≫ (p ⊗ₘ 𝟙 H)
  let q : H ⟶ (C ⊗ H) ⊗ R :=
    j ≫ (ρ_ (C ⊗ H)).inv ≫ (𝟙 (C ⊗ H) ⊗ₘ e)
  let f : (C ⊗ H) ⊗ R ⟶
      (((c ⊗ x) ⊗ r) ⟶[Vg] ((c ⊗ y) ⊗ r)) :=
    (d.tensorMap c c x y ▷ R) ≫ d.tensorMap (c ⊗ x) (c ⊗ y) r r
  let g : (C ⊗ H) ⊗ R ⟶
      ((c ⊗ (x ⊗ r)) ⟶[Vg] (c ⊗ (y ⊗ r))) :=
    (α_ C H R).hom ≫ (C ◁ d.tensorMap x y r r) ≫
      d.tensorMap c c (x ⊗ r) (y ⊗ r)
  have hNatural : f ≫ eHomWhiskerLeft Vg ((c ⊗ x) ⊗ r) (α_ c y r).hom =
      g ≫ eHomWhiskerRight Vg (α_ c x r).hom (c ⊗ (y ⊗ r)) := by
    apply unitGradedNaturality_eq_whisker
    simpa only [f, g, C, H, R, Category.assoc] using
      d.associatorNaturality c c x y r r
  have hLeft : q ≫ f =
      (leftTensor d c).map x y ≫
        (fixedRightTensor d r).map (c ⊗ x) (c ⊗ y) := by
    have hUnit : (ρ_ (C ⊗ H)).inv ≫ (d.tensorMap c c x y ⊗ₘ e) =
        d.tensorMap c c x y ≫ (ρ_ K).inv ≫ (𝟙 K ⊗ₘ e) := by
      simpa only [id_tensorHom] using
        rightUnitor_inv_comp_tensorHom (d.tensorMap c c x y) e
    calc
      q ≫ f = j ≫ (ρ_ (C ⊗ H)).inv ≫ (d.tensorMap c c x y ⊗ₘ e) ≫
          d.tensorMap (c ⊗ x) (c ⊗ y) r r := by
        simp only [q, f, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.comp_id, Category.id_comp, Category.assoc]
      _ = j ≫ d.tensorMap c c x y ≫ (ρ_ K).inv ≫ (𝟙 K ⊗ₘ e) ≫
          d.tensorMap (c ⊗ x) (c ⊗ y) r r := by
        rw [← Category.assoc (ρ_ (C ⊗ H)).inv, hUnit]
        simp only [Category.assoc]
      _ = _ := by
        simp only [leftTensor_map, fixedRightTensor_map, j, p, e, C, H, K,
          Category.assoc]
  have hPrefix : q ≫ (α_ C H R).hom =
      (ρ_ H).inv ≫ (𝟙 H ⊗ₘ e) ≫ (λ_ (H ⊗ R)).inv ≫
        (p ⊗ₘ 𝟙 (H ⊗ R)) := by
    have hMove : j ≫ (ρ_ (C ⊗ H)).inv =
        (ρ_ H).inv ≫ (j ▷ (𝟙_ Vg)) := rightUnitor_inv_naturality j
    have hPair : (j ▷ (𝟙_ Vg)) ≫ (𝟙 (C ⊗ H) ⊗ₘ e) = j ⊗ₘ e := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom,
        Category.comp_id, Category.id_comp]
    have hSplit : j ⊗ₘ e = ((λ_ H).inv ▷ (𝟙_ Vg)) ≫
        ((p ⊗ₘ 𝟙 H) ⊗ₘ e) := by
      simpa only [j, Category.id_comp, tensorHom_id] using
        (tensorHom_comp_tensorHom (λ_ H).inv (𝟙 (𝟙_ Vg)) (p ⊗ₘ 𝟙 H) e).symm
    have hAssoc : ((p ⊗ₘ 𝟙 H) ⊗ₘ e) ≫ (α_ C H R).hom =
        (α_ (𝟙_ Vg) H (𝟙_ Vg)).hom ≫ (p ⊗ₘ (𝟙 H ⊗ₘ e)) :=
      associator_naturality p (𝟙 H) e
    have hUnit : ((λ_ H).inv ▷ (𝟙_ Vg)) ≫
        (α_ (𝟙_ Vg) H (𝟙_ Vg)).hom = (λ_ (H ⊗ (𝟙_ Vg))).inv := by
      monoidal
    calc
      q ≫ (α_ C H R).hom = (ρ_ H).inv ≫ (j ⊗ₘ e) ≫ (α_ C H R).hom := by
        simp only [q, Category.assoc]
        rw [← Category.assoc j, hMove]
        simp only [Category.assoc]
        rw [← Category.assoc (j ▷ (𝟙_ Vg)), hPair]
      _ = (ρ_ H).inv ≫ ((λ_ H).inv ▷ (𝟙_ Vg)) ≫
          ((p ⊗ₘ 𝟙 H) ⊗ₘ e) ≫ (α_ C H R).hom := by
        rw [hSplit]
        simp only [Category.assoc]
      _ = (ρ_ H).inv ≫ ((λ_ H).inv ▷ (𝟙_ Vg)) ≫
          (α_ (𝟙_ Vg) H (𝟙_ Vg)).hom ≫ (p ⊗ₘ (𝟙 H ⊗ₘ e)) := by
        rw [hAssoc]
      _ = (ρ_ H).inv ≫ (λ_ (H ⊗ (𝟙_ Vg))).inv ≫
          (p ⊗ₘ (𝟙 H ⊗ₘ e)) := by
        rw [← Category.assoc ((λ_ H).inv ▷ (𝟙_ Vg)), hUnit]
      _ = _ := by
        simpa only [Category.assoc, tensorHom_id] using congrArg
          (fun m => (ρ_ H).inv ≫ m) (leftUnitor_inv_comp_tensorHom p (𝟙 H ⊗ₘ e))
  have hInsert : (λ_ (H ⊗ R)).inv ≫ (p ⊗ₘ 𝟙 (H ⊗ R)) ≫
      (C ◁ d.tensorMap x y r r) =
        d.tensorMap x y r r ≫ (λ_ T).inv ≫ (p ⊗ₘ 𝟙 T) := by
    calc
      _ = (λ_ (H ⊗ R)).inv ≫ (p ⊗ₘ d.tensorMap x y r r) := by
        simp only [← id_tensorHom, tensorHom_comp_tensorHom,
          Category.comp_id, Category.id_comp]
      _ = _ := by
        simpa only [T, tensorHom_id] using
          leftUnitor_inv_comp_tensorHom p (d.tensorMap x y r r)
  have hRight : q ≫ g = (fixedRightTensor d r).map x y ≫
      (leftTensor d c).map (x ⊗ r) (y ⊗ r) := by
    calc
      q ≫ g = (q ≫ (α_ C H R).hom) ≫ (C ◁ d.tensorMap x y r r) ≫
          d.tensorMap c c (x ⊗ r) (y ⊗ r) := by
        simp only [g, Category.assoc]
      _ = (ρ_ H).inv ≫ (𝟙 H ⊗ₘ e) ≫
          ((λ_ (H ⊗ R)).inv ≫ (p ⊗ₘ 𝟙 (H ⊗ R)) ≫ (C ◁ d.tensorMap x y r r)) ≫
          d.tensorMap c c (x ⊗ r) (y ⊗ r) := by
        rw [hPrefix]
        simp only [Category.assoc]
      _ = (ρ_ H).inv ≫ (𝟙 H ⊗ₘ e) ≫ d.tensorMap x y r r ≫
          (λ_ T).inv ≫ (p ⊗ₘ 𝟙 T) ≫ d.tensorMap c c (x ⊗ r) (y ⊗ r) := by
        rw [hInsert]
        simp only [Category.assoc]
      _ = _ := by
        simp only [fixedRightTensor_map, leftTensor_map, p, e, H, T, Category.assoc]
  have h := congrArg (fun m => q ≫ m) hNatural
  simpa only [← Category.assoc, hLeft, hRight] using h

omit [MonoidalClosed Vg] in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse middle associator equation also retains the complete Hom. -/
private theorem leftRightTensor_associator_inv (d : EnrichedMonoidalCategoryData Vg A)
    (c r x y : A) :
    ((fixedRightTensor d r).map x y ≫
        (leftTensor d c).map (x ⊗ r) (y ⊗ r)) ≫
        eHomWhiskerLeft Vg (c ⊗ (x ⊗ r)) (α_ c y r).inv =
      ((leftTensor d c).map x y ≫
        (fixedRightTensor d r).map (c ⊗ x) (c ⊗ y)) ≫
        eHomWhiskerRight Vg (α_ c x r).inv ((c ⊗ y) ⊗ r) := by
  have h := congrArg
    (fun m => m ≫ eHomWhiskerRight Vg (α_ c x r).inv (c ⊗ (y ⊗ r)) ≫
      eHomWhiskerLeft Vg (c ⊗ (x ⊗ r)) (α_ c y r).inv)
    (leftRightTensor_associator d c r x y)
  simpa only [fixedRightTensor_obj, leftTensor_obj, Category.assoc,
    eHom_whisker_exchange_assoc, ← eHomWhiskerLeft_comp, ← eHomWhiskerRight_comp,
    ← eHomWhiskerLeft_comp_assoc, ← eHomWhiskerRight_comp_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, eHomWhiskerLeft_id,
    eHomWhiskerRight_id, Category.comp_id, Category.id_comp] using h.symm

omit [MonoidalClosed Vg] in
set_option backward.isDefEq.respectTransparency false in
private theorem rightTensor_precomposition (d : EnrichedMonoidalCategoryData Vg A)
    (r x y z : A) (f : x ⟶ y) :
    eHomWhiskerRight Vg f z ≫ (fixedRightTensor d r).map x z =
      (fixedRightTensor d r).map y z ≫ eHomWhiskerRight Vg (f ▷ r) (z ⊗ r) := by
  have hp := fixedRightTensor_point d r f
  have hr := congrArg
    (fun p : (𝟙_ Vg) ⟶ ((x ⊗ r) ⟶[Vg] (y ⊗ r)) => (eHomEquiv Vg).symm p) hp
  simp only [Equiv.symm_apply_apply] at hr
  have h := enrichedFunctorFullPrecomposition (fixedRightTensor d r) x y z f
  have hWhisker := congrArg
    (fun j : x ⊗ r ⟶ y ⊗ r => eHomWhiskerRight Vg j (z ⊗ r)) hr
  have hTail := congrArg
    (fun m : ((y ⊗ r) ⟶[Vg] (z ⊗ r)) ⟶ ((x ⊗ r) ⟶[Vg] (z ⊗ r)) =>
      (fixedRightTensor d r).map y z ≫ m) hWhisker
  exact h.trans hTail

omit [MonoidalClosed Vg] in
set_option backward.isDefEq.respectTransparency false in
private theorem indexGenerator_leftTensor (d : EnrichedMonoidalCategoryData Vg A)
    (n k l a b : A) :
    indexGenerator d n k l a b =
      ((leftTensor d b).map (a ⊗ n) k ⊗ₘ 𝟙 ((b ⊗ k) ⟶[Vg] l)) ≫
        eComp Vg (b ⊗ (a ⊗ n)) (b ⊗ k) l ≫
        eHomWhiskerRight Vg (α_ b a n).hom l := by
  simp only [indexGenerator, leftTensor_map, eHomWhiskerRight,
    tensorHom_id, Category.assoc]

omit [MonoidalClosed Vg] in
set_option backward.isDefEq.respectTransparency false in
/-- The complete original index-generator map commutes with the actual weight
shift. Both enriched weight Hom factors and the source pentagon are retained. -/
theorem indexGenerator_shift (d : EnrichedMonoidalCategoryData Vg A)
    (r n k l a b : A) :
    indexGenerator d n k l a b ≫ weightShiftMap d r n l (b ⊗ a) =
      (weightShiftMap d r n k a ⊗ₘ weightShiftMap d r k l b) ≫
        indexGenerator d (n ⊗ r) (k ⊗ r) (l ⊗ r) a b := by
  let A0 : A := a ⊗ n
  let B0 : A := b ⊗ A0
  let B1 : A := b ⊗ k
  let C0 : A := (b ⊗ a) ⊗ n
  let Ar : A := A0 ⊗ r
  let Br : A := B0 ⊗ r
  let B1r : A := B1 ⊗ r
  let K : A := k ⊗ r
  let X : A := b ⊗ Ar
  let Y : A := b ⊗ K
  let Z : A := l ⊗ r
  let A' : A := a ⊗ (n ⊗ r)
  let B' : A := b ⊗ A'
  let C' : A := (b ⊗ a) ⊗ (n ⊗ r)
  let H : Vg := A0 ⟶[Vg] k
  let W : Vg := B1 ⟶[Vg] l
  let U : Vg := X ⟶[Vg] Y
  let Q : Vg := B1r ⟶[Vg] Z
  let f : H ⟶ (Br ⟶[Vg] B1r) :=
    (leftTensor d b).map A0 k ≫ (fixedRightTensor d r).map B0 B1
  let p : H ⟶ U :=
    (fixedRightTensor d r).map A0 k ≫ (leftTensor d b).map Ar K
  let q : W ⟶ Q := (fixedRightTensor d r).map B1 l
  let u : U ⟶ (X ⟶[Vg] B1r) := eHomWhiskerLeft Vg X (α_ b k r).inv
  let v : Q ⟶ (Y ⟶[Vg] Z) := eHomWhiskerRight Vg (α_ b k r).inv Z
  let q' : W ⟶ (Y ⟶[Vg] Z) := q ≫ v
  let s : C' ⟶ X := (α_ b a (n ⊗ r)).hom ≫ b ◁ (α_ a n r).inv
  let sl : C' ⟶ Br :=
    (α_ (b ⊗ a) n r).inv ≫ ((α_ b a n).hom ▷ r)
  have hPath : sl = s ≫ (α_ b A0 r).inv := by
    have h := congrArg
      (fun m => (α_ (b ⊗ a) n r).inv ≫ m ≫
        (b ◁ (α_ a n r).inv) ≫ (α_ b (a ⊗ n) r).inv)
      (MonoidalCategory.pentagon b a n r)
    simpa only [sl, s, A0, tensorHom_id, Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.comp_id,
      Iso.inv_hom_id_assoc] using h
  have hPrePath : eHomWhiskerRight Vg ((α_ b a n).hom ▷ r) Z ≫
      eHomWhiskerRight Vg (α_ (b ⊗ a) n r).inv Z =
        eHomWhiskerRight Vg (α_ b A0 r).inv Z ≫ eHomWhiskerRight Vg s Z := by
    simpa only [sl, eHomWhiskerRight_comp] using
      congrArg (fun m : C' ⟶ Br => eHomWhiskerRight Vg m Z) hPath
  have hFirst : f ≫ eHomWhiskerRight Vg (α_ b A0 r).inv B1r = p ≫ u := by
    simpa only [f, p, u, A0, B0, B1, Ar, Br, B1r, K, X,
      Category.assoc] using (leftRightTensor_associator_inv d b r A0 k).symm
  have hMiddle : (u ▷ Q) ≫ eComp Vg X B1r Z =
      (U ◁ v) ≫ eComp Vg X Y Z := by
    have h := eHom_whisker_cancel_inv Vg (X := X) (Z := Z) (α_ b k r)
    have ht := congrArg
      (fun m : (U ⊗ (Y ⟶[Vg] Z)) ⟶ (X ⟶[Vg] Z) => (U ◁ v) ≫ m) h
    rw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← eHomWhiskerRight_comp, Iso.hom_inv_id, eHomWhiskerRight_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp] at ht
    exact ht
  have hMiddlePair : ((p ≫ u) ⊗ₘ q) ≫ eComp Vg X B1r Z =
      (p ⊗ₘ q') ≫ eComp Vg X Y Z := by
    have h := congrArg
      (fun m : (U ⊗ Q) ⟶ (X ⟶[Vg] Z) => (p ⊗ₘ q) ≫ m) hMiddle
    simpa only [← tensorHom_id, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp, q'] using h
  have hLeftRaw : indexGenerator d n k l a b ≫ weightShiftMap d r n l (b ⊗ a) =
      (f ⊗ₘ q) ≫ eComp Vg Br B1r Z ≫
        eHomWhiskerRight Vg ((α_ b a n).hom ▷ r) Z ≫
          eHomWhiskerRight Vg (α_ (b ⊗ a) n r).inv Z := by
    rw [indexGenerator_leftTensor]
    simp only [weightShiftMap, Category.assoc]
    change ((leftTensor d b).map A0 k ⊗ₘ 𝟙 W) ≫
        eComp Vg B0 B1 l ≫ eHomWhiskerRight Vg (α_ b a n).hom l ≫
          (fixedRightTensor d r).map C0 l ≫
            eHomWhiskerRight Vg (α_ (b ⊗ a) n r).inv Z = _
    rw [← Category.assoc (eHomWhiskerRight Vg (α_ b a n).hom l),
      rightTensor_precomposition d r C0 B0 l (α_ b a n).hom]
    simp only [Category.assoc]
    rw [← Category.assoc (eComp Vg B0 B1 l), fixedRightTensor_comp]
    simp only [f, q, Br, B1r, Z, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.assoc]
  have hLeft : indexGenerator d n k l a b ≫ weightShiftMap d r n l (b ⊗ a) =
      (p ⊗ₘ q') ≫ eComp Vg X Y Z ≫ eHomWhiskerRight Vg s Z := by
    rw [hLeftRaw]
    rw [hPrePath, eComp_eHomWhiskerRight_assoc]
    simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc]
    rw [hFirst]
    have hqId : q ≫ 𝟙 (B1r ⟶[Vg] Z) = q := by
      change q ≫ 𝟙 Q = q
      exact Category.comp_id q
    rw [hqId]
    simpa only [Category.assoc] using congrArg
      (fun m => m ≫ eHomWhiskerRight Vg s Z) hMiddlePair
  have hLeftPre := leftTensor_precomposition d b A' Ar K (α_ a n r).inv
  have hSource :
      ((p ≫ eHomWhiskerRight Vg (b ◁ (α_ a n r).inv) Y) ⊗ₘ q') ≫
          eComp Vg B' Y Z =
        (p ⊗ₘ q') ≫ eComp Vg X Y Z ≫
          eHomWhiskerRight Vg (b ◁ (α_ a n r).inv) Z := by
    have h := congrArg
      (fun m : ((X ⟶[Vg] Y) ⊗ (Y ⟶[Vg] Z)) ⟶ (B' ⟶[Vg] Z) =>
        (p ⊗ₘ q') ≫ m)
      (eComp_eHomWhiskerRight Vg (b ◁ (α_ a n r).inv) Y Z).symm
    simpa only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, B', X, Ar, A'] using h
  have hRight :
      (weightShiftMap d r n k a ⊗ₘ weightShiftMap d r k l b) ≫
          indexGenerator d (n ⊗ r) (k ⊗ r) (l ⊗ r) a b =
        (p ⊗ₘ q') ≫ eComp Vg X Y Z ≫ eHomWhiskerRight Vg s Z := by
    rw [indexGenerator_leftTensor]
    simp only [weightShiftMap]
    change (((fixedRightTensor d r).map A0 k ≫
        eHomWhiskerRight Vg (α_ a n r).inv K) ⊗ₘ q') ≫
          ((leftTensor d b).map A' K ⊗ₘ 𝟙 (Y ⟶[Vg] Z)) ≫
            eComp Vg B' Y Z ≫ eHomWhiskerRight Vg (α_ b a (n ⊗ r)).hom Z = _
    simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.assoc]
    rw [hLeftPre]
    rw [← Category.assoc ((fixedRightTensor d r).map A0 k)]
    change ((p ≫ eHomWhiskerRight Vg (b ◁ (α_ a n r).inv) Y) ⊗ₘ q') ≫
        eComp Vg B' Y Z ≫ eHomWhiskerRight Vg (α_ b a (n ⊗ r)).hom Z = _
    rw [← Category.assoc (_ ⊗ₘ q'), hSource]
    simp only [s, eHomWhiskerRight_comp, Category.assoc]
  exact hLeft.trans hRight.symm

omit [MonoidalClosed Vg] in
/-- The full index-generator right-shift functions agree at every original
index and both complete coefficient Hom objects. -/
theorem indexGenerator_shift_function (d : EnrichedMonoidalCategoryData Vg A) :
    (fun (r n k l a b : A) =>
      indexGenerator d n k l a b ≫ weightShiftMap d r n l (b ⊗ a)) =
      fun (r n k l a b : A) =>
        (weightShiftMap d r n k a ⊗ₘ weightShiftMap d r k l b) ≫
          indexGenerator d (n ⊗ r) (k ⊗ r) (l ⊗ r) a b := by
  funext r n k l a b
  exact indexGenerator_shift d r n k l a b

omit [MonoidalClosed Vg] in
/-- The actual inverse tensor permutation is natural on all four factors.
Its proof uses the original tensor-mu naturality and both inverse equations. -/
private theorem tensorδ_naturalForShift
    {X₁ X₂ Y₁ Y₂ X₁' X₂' Y₁' Y₂' : Vg}
    (f₁ : X₁ ⟶ X₁') (f₂ : X₂ ⟶ X₂')
    (g₁ : Y₁ ⟶ Y₁') (g₂ : Y₂ ⟶ Y₂') :
    ((f₁ ⊗ₘ g₁) ⊗ₘ (f₂ ⊗ₘ g₂)) ≫ tensorδ X₁' X₂' Y₁' Y₂' =
      tensorδ X₁ X₂ Y₁ Y₂ ≫ ((f₁ ⊗ₘ f₂) ⊗ₘ (g₁ ⊗ₘ g₂)) := by
  have h := congrArg
    (fun m => tensorδ X₁ X₂ Y₁ Y₂ ≫ m ≫ tensorδ X₁' X₂' Y₁' Y₂')
    (tensorμ_natural f₁ f₂ g₁ g₂)
  simpa only [Category.assoc, tensorδ_tensorμ_assoc, tensorμ_tensorδ,
    Category.comp_id] using h.symm

section Coend

variable (d : EnrichedMonoidalCategoryData Vg A) (S : EnrichedFunctor Vg A Vg)
  [∀ n k : A, HasCoproduct (Enriched.weightedCoend.relations (weight d n k) S)]
  [∀ n k : A, HasCoproduct (Enriched.weightedCoend.objects (weight d n k) S)]
  [∀ n k : A, HasCoequalizer (Enriched.weightedCoend.leftMap (weight d n k) S)
    (Enriched.weightedCoend.rightMap (weight d n k) S)]

/-- The general Hom shift is the actual map of the original weighted coends,
using their original full object and relation coproducts and coequalizers. -/
def hom (r n k : A) : Hom d S n k ⟶ Hom d S (n ⊗ r) (k ⊗ r) :=
  Enriched.weightedCoend.mapWeightGraded S (weightShift d r n k)

set_option backward.isDefEq.respectTransparency false in
/-- The complete coend generator characteristic retains the whole weight
map and the unchanged original coefficient factor. -/
theorem hom_ι (r n k a : A) :
    Enriched.weightedCoend.ι (weight d n k) S a ≫ hom d S r n k =
      (weightShiftMap d r n k a ⊗ₘ 𝟙 (S.obj a)) ≫
        Enriched.weightedCoend.ι (weight d (n ⊗ r) (k ⊗ r)) S a := by
  simpa only [hom, weightShift_component] using
    Enriched.weightedCoend.mapWeightGraded_ι S (weightShift d r n k) a

/-- The complete characteristic functions agree at all original index and
coefficient objects before a native generator is substituted. -/
theorem hom_ι_function :
    (fun (r n k a : A) =>
      Enriched.weightedCoend.ι (weight d n k) S a ≫ hom d S r n k) =
      fun (r n k a : A) =>
        (weightShiftMap d r n k a ⊗ₘ 𝟙 (S.obj a)) ≫
          Enriched.weightedCoend.ι (weight d (n ⊗ r) (k ⊗ r)) S a := by
  funext r n k a
  exact hom_ι d S r n k a

set_option backward.isDefEq.respectTransparency false in
/-- Every entire source-point generator keeps its original coefficient
and the exact source associator and final-factor extension. -/
theorem hom_point_generator (r n k a : A) (f : a ⊗ n ⟶ k) :
    (eHomEquiv Vg f ⊗ₘ 𝟙 (S.obj a)) ≫
        Enriched.weightedCoend.ι (weight d n k) S a ≫ hom d S r n k =
      (eHomEquiv Vg (label r n k a f) ⊗ₘ 𝟙 (S.obj a)) ≫
        Enriched.weightedCoend.ι (weight d (n ⊗ r) (k ⊗ r)) S a := by
  rw [hom_ι, tensorHom_comp_tensorHom_assoc, weightShiftMap_point,
    Category.comp_id]

variable (L : EnrichedFunctor.LaxMonoidalData d
  (MonoidalClosed.enrichedMonoidalCategoryDataSelf Vg) S)

set_option backward.isDefEq.respectTransparency false in
/-- The actual original epsilon and left-unitor generator are preserved by
the general coend shift; no operator identity law is an input. -/
theorem hom_identity (r n : A) :
    identityGenerator d S L n ≫ hom d S r n n =
      identityGenerator d S L (n ⊗ r) := by
  simp only [identityGenerator, Category.assoc]
  rw [hom_ι, tensorHom_comp_tensorHom_assoc, weightShiftMap_unit_point,
    Category.comp_id]

/-- The entire original enriched identity functions agree for every shift. -/
theorem hom_identity_function :
    (fun (r n : A) => identityGenerator d S L n ≫ hom d S r n n) =
      fun (r n : A) => identityGenerator d S L (n ⊗ r) := by
  funext r n
  exact hom_identity d S L r n

set_option backward.isDefEq.respectTransparency false in
/-- The actual complete index-generator equation and tensor-delta naturality
preserve every full pair of original coend coefficient objects. -/
theorem compositionGenerator_shift (r n k l a b : A) :
    compositionGenerator d S L n k l a b ≫ hom d S r n l =
      ((weightShiftMap d r n k a ⊗ₘ 𝟙 (S.obj a)) ⊗ₘ
        (weightShiftMap d r k l b ⊗ₘ 𝟙 (S.obj b))) ≫
        compositionGenerator d S L (n ⊗ r) (k ⊗ r) (l ⊗ r) a b := by
  simp only [compositionGenerator, Category.assoc]
  rw [hom_ι]
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
  rw [indexGenerator_shift]
  have hδ := tensorδ_naturalForShift (weightShiftMap d r n k a)
    (weightShiftMap d r k l b) (𝟙 (S.obj a)) (𝟙 (S.obj b))
  rw [← Category.assoc
    ((weightShiftMap d r n k a ⊗ₘ 𝟙 (S.obj a)) ⊗ₘ
      (weightShiftMap d r k l b ⊗ₘ 𝟙 (S.obj b))), hδ]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc,
    id_tensorHom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The Hom shift preserves the actual original composition after both full
coend extensionality scopes. No operator coherence law is an input. -/
theorem hom_composition (r n k l : A) :
    composition d S L n k l ≫ hom d S r n l =
      (hom d S r n k ⊗ₘ hom d S r k l) ≫
        composition d S L (n ⊗ r) (k ⊗ r) (l ⊗ r) := by
  apply Enriched.weightedCoend.Mapped.hom_ext (weight d k l) S
    (tensorLeft (Hom d S n k))
  intro b
  apply Enriched.weightedCoend.Mapped.hom_ext (weight d n k) S
    (tensorRight (Enriched.weightedCoend.objects (weight d k l) S b))
  intro a
  change (Enriched.weightedCoend.ι (weight d n k) S a ▷
      Enriched.weightedCoend.objects (weight d k l) S b) ≫
        (Hom d S n k ◁ Enriched.weightedCoend.ι (weight d k l) S b) ≫
          (composition d S L n k l ≫ hom d S r n l) =
    (Enriched.weightedCoend.ι (weight d n k) S a ▷
      Enriched.weightedCoend.objects (weight d k l) S b) ≫
        (Hom d S n k ◁ Enriched.weightedCoend.ι (weight d k l) S b) ≫
          ((hom d S r n k ⊗ₘ hom d S r k l) ≫
            composition d S L (n ⊗ r) (k ⊗ r) (l ⊗ r))
  simp only [← tensorHom_def_assoc]
  have hPair :
      (Enriched.weightedCoend.ι (weight d n k) S a ⊗ₘ
        Enriched.weightedCoend.ι (weight d k l) S b) ≫
          (hom d S r n k ⊗ₘ hom d S r k l) =
      ((weightShiftMap d r n k a ⊗ₘ 𝟙 (S.obj a)) ⊗ₘ
        (weightShiftMap d r k l b ⊗ₘ 𝟙 (S.obj b))) ≫
        (Enriched.weightedCoend.ι (weight d (n ⊗ r) (k ⊗ r)) S a ⊗ₘ
          Enriched.weightedCoend.ι (weight d (k ⊗ r) (l ⊗ r)) S b) := by
    rw [tensorHom_comp_tensorHom, hom_ι, hom_ι, ← tensorHom_comp_tensorHom]
  calc
    _ = compositionGenerator d S L n k l a b ≫ hom d S r n l := by
      rw [← Category.assoc, composition_generator]
    _ = ((weightShiftMap d r n k a ⊗ₘ 𝟙 (S.obj a)) ⊗ₘ
          (weightShiftMap d r k l b ⊗ₘ 𝟙 (S.obj b))) ≫
        compositionGenerator d S L (n ⊗ r) (k ⊗ r) (l ⊗ r) a b :=
      compositionGenerator_shift d S L r n k l a b
    _ = _ := by
      rw [← Category.assoc
        (Enriched.weightedCoend.ι (weight d n k) S a ⊗ₘ
          Enriched.weightedCoend.ι (weight d k l) S b), hPair]
      rw [Category.assoc, composition_generator]

/-- Every complete composition function is preserved on the original
two-coend Hom objects before any native world or label is substituted. -/
theorem hom_composition_function :
    (fun (r n k l : A) => composition d S L n k l ≫ hom d S r n l) =
      fun (r n k l : A) =>
        (hom d S r n k ⊗ₘ hom d S r k l) ≫
          composition d S L (n ⊗ r) (k ⊗ r) (l ⊗ r) := by
  funext r n k l
  exact hom_composition d S L r n k l

/-- The proved unit and composition equations construct the actual enriched
right shift on the original operator index with its fixed d, S and L data. -/
def indexShift (r : A) :
    EnrichedFunctor Vg (OperatorIndex d S L) (OperatorIndex d S L) where
  obj X := ⟨X.asIndex ⊗ r⟩
  map X Y := hom d S r X.asIndex Y.asIndex
  map_id X := hom_identity d S L r X.asIndex
  map_comp X Y Z := hom_composition d S L r X.asIndex Y.asIndex Z.asIndex

end Coend

end GenericRightTensor

end CategoryTheory.Enriched
