/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCategory
public import MathlibExt.CategoryTheory.Enriched.Restriction

/-!
# The full unit-coefficient map into the operator index

The source is the original full enriched Hom object. Its map is the unit
coefficient coend generator after precomposition by the source left unitor.
Identity and full composition preservation follow from the original unitor
naturality, tensor interchange, actual coefficient unit and coend relation.
Restriction is then the existing enriched precomposition functor.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Limits Opposite

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

omit [BraidedCategory V] [MonoidalClosed V] [MonoidalCategory I] in
private theorem precompositionPointForProof {x y z : I}
    (f : x ⟶ y) (g : y ⟶ z) :
    eHomEquiv V g ≫ eHomWhiskerRight V f z = eHomEquiv V (f ≫ g) := by
  let H : V := y ⟶[V] z
  let p : (𝟙_ V) ⟶ (x ⟶[V] y) := eHomEquiv V f
  let q : (𝟙_ V) ⟶ H := eHomEquiv V g
  have hTensor : ((𝟙_ V) ◁ q) ≫ (p ⊗ₘ 𝟙 H) = p ⊗ₘ q := by
    simpa only [MonoidalCategory.id_tensorHom, Category.id_comp,
      Category.comp_id] using
      (MonoidalCategory.tensorHom_comp_tensorHom
        (𝟙 (𝟙_ V)) q p (𝟙 H))
  calc
    _ = (λ_ (𝟙_ V)).inv ≫
        (((𝟙_ V) ◁ q) ≫ (p ⊗ₘ 𝟙 H)) ≫ eComp V x y z := by
      dsimp only [eHomWhiskerRight, p, q, H]
      rw [MonoidalCategory.leftUnitor_inv_naturality_assoc]
      simp only [MonoidalCategory.tensorHom_id, Category.assoc]
    _ = (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ q) ≫ eComp V x y z :=
      congrArg (fun t : (𝟙_ V) ⊗ (𝟙_ V) ⟶ (x ⟶[V] y) ⊗ H =>
        (λ_ (𝟙_ V)).inv ≫ t ≫ eComp V x y z) hTensor
    _ = _ := (eHomEquiv_comp (V := V) f g).symm

omit [BraidedCategory V] [MonoidalClosed V] [MonoidalCategory I] in
private theorem middleIsoTransportForProof
    {x y y' z : I} {H : V} (c : y ≅ y') (f : H ⟶ (x ⟶[V] y)) :
    (f ⊗ₘ eHomWhiskerRight V c.hom z) ≫ eComp V x y z =
      ((f ≫ eHomWhiskerLeft V x c.hom) ⊗ₘ 𝟙 (y' ⟶[V] z)) ≫
        eComp V x y' z := by
  let K : V := y' ⟶[V] z
  have hRetraction :
      (f ≫ eHomWhiskerLeft V x c.hom) ≫ eHomWhiskerLeft V x c.inv = f := by
    rw [Category.assoc, ← eHomWhiskerLeft_comp, Iso.hom_inv_id,
      eHomWhiskerLeft_id, Category.comp_id]
  have hPair :
      ((f ≫ eHomWhiskerLeft V x c.hom) ⊗ₘ 𝟙 K) ≫
          (eHomWhiskerLeft V x c.inv ▷ K) = f ▷ K := by
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
      hRetraction, MonoidalCategory.tensorHom_id]
  have hCancel :
      (eHomWhiskerLeft V x c.inv ▷ K) ≫
          ((x ⟶[V] y) ◁ eHomWhiskerRight V c.hom z) ≫
          eComp V x y z = eComp V x y' z :=
    eHom_whisker_cancel_inv (V := V) c
  symm
  calc
    _ = ((f ≫ eHomWhiskerLeft V x c.hom) ⊗ₘ 𝟙 K) ≫
        (eHomWhiskerLeft V x c.inv ▷ K) ≫
        ((x ⟶[V] y) ◁ eHomWhiskerRight V c.hom z) ≫ eComp V x y z := by
      simpa only [Category.assoc] using congrArg
        (fun q : (x ⟶[V] y') ⊗ K ⟶ (x ⟶[V] z) =>
          ((f ≫ eHomWhiskerLeft V x c.hom) ⊗ₘ 𝟙 K) ≫ q) hCancel.symm
    _ = (f ▷ K) ≫ ((x ⟶[V] y) ◁ eHomWhiskerRight V c.hom z) ≫
        eComp V x y z := by
      simpa only [Category.assoc] using congrArg
        (fun q : H ⊗ K ⟶ (x ⟶[V] y) ⊗ K =>
          q ≫ ((x ⟶[V] y) ◁ eHomWhiskerRight V c.hom z) ≫
            eComp V x y z) hPair
    _ = _ := by
      dsimp only [K]
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]

omit [MonoidalClosed V] in
private theorem unitIndexCompositeForProof
    (d : EnrichedMonoidalCategoryData V I) (n k l : I) :
    (eHomWhiskerRight V (λ_ n).hom k ⊗ₘ
        eHomWhiskerRight V (λ_ k).hom l) ≫
        indexGenerator d n k l (𝟙_ I) (𝟙_ I) =
      eComp V n k l ≫
        eHomWhiskerRight V (((λ_ (𝟙_ I)).hom ⊗ₘ 𝟙 n) ≫ (λ_ n).hom) l := by
  let U : I := (𝟙_ I) ⊗ n
  let X : I := (𝟙_ I) ⊗ U
  let Y : I := (𝟙_ I) ⊗ k
  let Z : I := ((𝟙_ I) ⊗ (𝟙_ I)) ⊗ n
  let H : V := n ⟶[V] k
  let K : V := k ⟶[V] l
  let W : V := U ⟶[V] k
  let P : V := Y ⟶[V] l
  let p : H ⟶ W := eHomWhiskerRight V (λ_ n).hom k
  let q : K ⟶ P := eHomWhiskerRight V (λ_ k).hom l
  let j : W ⟶ (X ⟶[V] Y) :=
    (λ_ W).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 W) ≫
      d.tensorMap (𝟙_ I) (𝟙_ I) U k
  let r : X ⟶ n := (λ_ U).hom ≫ (λ_ n).hom
  let a : Z ⟶ X := (α_ (𝟙_ I) (𝟙_ I) n).hom
  have hUnitor :
      j ≫ eHomWhiskerLeft V X (λ_ k).hom =
        eHomWhiskerRight V (λ_ U).hom k := by
    have ht := unitGradedNaturality_eq_whisker j (𝟙 W)
      (λ_ U).hom (λ_ k).hom
      (by simpa only [j, U, X, Y, W] using d.leftUnitorNaturality U k)
    simpa only [Category.id_comp] using ht
  have hRaw : indexGenerator d n k l (𝟙_ I) (𝟙_ I) =
      (j ⊗ₘ 𝟙 P) ≫ eComp V X Y l ≫ eHomWhiskerRight V a l := by
    simp only [indexGenerator, j, U, X, Y, Z, W, P, a,
      eHomWhiskerRight, MonoidalCategory.tensorHom_id, Category.assoc]
  have hSplit : (p ⊗ₘ q) ≫ (j ⊗ₘ 𝟙 P) = (p ≫ j) ⊗ₘ q := by
    simpa only [Category.comp_id] using
      MonoidalCategory.tensorHom_comp_tensorHom p q j (𝟙 P)
  have hMiddle :
      ((p ≫ j) ⊗ₘ q) ≫ eComp V X Y l =
        ((p ≫ j ≫ eHomWhiskerLeft V X (λ_ k).hom) ⊗ₘ 𝟙 K) ≫
          eComp V X k l := by
    have h := middleIsoTransportForProof
      (x := X) (y := Y) (y' := k) (z := l) (λ_ k) (p ≫ j)
    dsimp only [p, q, j, K, Y] at h ⊢
    simpa only [Category.assoc] using h
  have hPre : p ≫ j ≫ eHomWhiskerLeft V X (λ_ k).hom =
      eHomWhiskerRight V r k := by
    calc
      _ = p ≫ eHomWhiskerRight V (λ_ U).hom k :=
        congrArg (fun t : W ⟶ (X ⟶[V] k) => p ≫ t) hUnitor
      _ = _ := by
        dsimp only [p, r, U, X]
        exact (eHomWhiskerRight_comp (V := V)
          (λ_ ((𝟙_ I) ⊗ n)).hom (λ_ n).hom k).symm
  have hPreComp :
      (eHomWhiskerRight V r k ⊗ₘ 𝟙 K) ≫ eComp V X k l =
        eComp V n k l ≫ eHomWhiskerRight V r l := by
    simpa only [MonoidalCategory.tensorHom_id] using
      (eComp_eHomWhiskerRight (V := V) r k l).symm
  have hUnit : a ≫ r = ((λ_ (𝟙_ I)).hom ⊗ₘ 𝟙 n) ≫ (λ_ n).hom := by
    dsimp only [a, r, U, X, Z]
    monoidal
  calc
    _ = ((p ≫ j) ⊗ₘ q) ≫ eComp V X Y l ≫ eHomWhiskerRight V a l := by
      rw [hRaw]
      simpa only [Category.assoc] using congrArg
        (fun t : H ⊗ K ⟶ (X ⟶[V] Y) ⊗ P =>
          t ≫ eComp V X Y l ≫ eHomWhiskerRight V a l) hSplit
    _ = ((p ≫ j ≫ eHomWhiskerLeft V X (λ_ k).hom) ⊗ₘ 𝟙 K) ≫
        eComp V X k l ≫ eHomWhiskerRight V a l := by
      simpa only [Category.assoc] using congrArg
        (fun t : H ⊗ K ⟶ (X ⟶[V] l) => t ≫ eHomWhiskerRight V a l) hMiddle
    _ = (eHomWhiskerRight V r k ⊗ₘ 𝟙 K) ≫
        eComp V X k l ≫ eHomWhiskerRight V a l :=
      congrArg (fun t : H ⟶ (X ⟶[V] k) =>
        (t ⊗ₘ 𝟙 K) ≫ eComp V X k l ≫ eHomWhiskerRight V a l) hPre
    _ = eComp V n k l ≫ eHomWhiskerRight V r l ≫
        eHomWhiskerRight V a l := by
      simpa only [Category.assoc] using congrArg
        (fun t : H ⊗ K ⟶ (X ⟶[V] l) => t ≫ eHomWhiskerRight V a l) hPreComp
    _ = eComp V n k l ≫ eHomWhiskerRight V (a ≫ r) l :=
      congrArg (fun t : (n ⟶[V] l) ⟶ (Z ⟶[V] l) => eComp V n k l ≫ t)
        (eHomWhiskerRight_comp (V := V) a r l).symm
    _ = _ := congrArg
      (fun t : Z ⟶ n => eComp V n k l ≫ eHomWhiskerRight V t l) hUnit

omit [MonoidalClosed V] in
private theorem tensorUnitCoefficientPairForProof (W Z A : V)
    (e : (𝟙_ V) ⟶ A) :
    (((ρ_ W).inv ≫ (𝟙 W ⊗ₘ e)) ⊗ₘ
        ((ρ_ Z).inv ≫ (𝟙 Z ⊗ₘ e))) ≫
        tensorδ W Z A A ≫ (𝟙 (W ⊗ Z) ⊗ₘ (β_ A A).hom) =
      (ρ_ (W ⊗ Z)).inv ≫
        (𝟙 (W ⊗ Z) ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ e))) := by
  let U : V := 𝟙_ V
  let P : V := W ⊗ Z
  let δ₀ := tensorδ W Z U U
  let μ₀ := tensorμ W Z U U
  let i : P ⟶ (W ⊗ U) ⊗ (Z ⊗ U) := (ρ_ W).inv ⊗ₘ (ρ_ Z).inv
  let o : (W ⊗ U) ⊗ (Z ⊗ U) ⟶ P := (ρ_ W).hom ⊗ₘ (ρ_ Z).hom
  have hNaturality :
      ((𝟙 W ⊗ₘ e) ⊗ₘ (𝟙 Z ⊗ₘ e)) ≫ tensorδ W Z A A =
        δ₀ ≫ (𝟙 P ⊗ₘ (e ⊗ₘ e)) := by
    have h := Functor.OplaxMonoidal.δ_natural (MonoidalCategory.tensor V)
      (show (W, Z) ⟶ (W, Z) from (𝟙 W, 𝟙 Z))
      (show (U, U) ⟶ (A, A) from (e, e))
    simp only [MonoidalCategory.tensor_δ] at h
    change δ₀ ≫ ((𝟙 W ⊗ₘ 𝟙 Z) ⊗ₘ (e ⊗ₘ e)) =
      ((𝟙 W ⊗ₘ e) ⊗ₘ (𝟙 Z ⊗ₘ e)) ≫ tensorδ W Z A A at h
    simpa only [MonoidalCategory.id_tensorHom_id] using h.symm
  have hPair : o ≫ i = 𝟙 ((W ⊗ U) ⊗ (Z ⊗ U)) := by
    dsimp only [o, i, U]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id, MonoidalCategory.id_tensorHom_id]
  have hPairTail : o ≫ i ≫ δ₀ = δ₀ :=
    (Category.assoc o i δ₀).symm.trans
      ((congrArg (fun t => t ≫ δ₀) hPair).trans (Category.id_comp δ₀))
  have hUnit : i ≫ δ₀ = (ρ_ P).inv ≫ (𝟙 P ⊗ₘ (λ_ U).inv) := by
    have hUnitor : (ρ_ P).hom =
        (𝟙 P ⊗ₘ (λ_ U).inv) ≫ μ₀ ≫ o := by
      simpa only [P, U, μ₀, o, MonoidalCategory.id_tensorHom] using
        tensor_right_unitality W Z
    have hu := congrArg
      (fun t : P ⊗ U ⟶ P => (ρ_ P).inv ≫ t ≫ i ≫ δ₀)
      hUnitor
    have hCancel : μ₀ ≫ δ₀ = 𝟙 (P ⊗ (U ⊗ U)) := tensorμ_tensorδ W Z U U
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hPairTail, hCancel] at hu
    dsimp only [P, U] at hu ⊢
    simpa only [Category.comp_id] using hu
  have hCross : (e ⊗ₘ e) ≫ (β_ A A).hom = e ⊗ₘ e := by
    simpa only [CategoryTheory.braiding_tensorUnit_left,
      MonoidalCategory.unitors_equal, Iso.hom_inv_id,
      Category.id_comp] using (BraidedCategory.braiding_naturality e e)
  have hCrossTensor :
      (𝟙 P ⊗ₘ (e ⊗ₘ e)) ≫ (𝟙 P ⊗ₘ (β_ A A).hom) =
        𝟙 P ⊗ₘ (e ⊗ₘ e) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, hCross]
  have hInsertion :
      (((ρ_ W).inv ≫ (𝟙 W ⊗ₘ e)) ⊗ₘ
          ((ρ_ Z).inv ≫ (𝟙 Z ⊗ₘ e))) =
        i ≫ ((𝟙 W ⊗ₘ e) ⊗ₘ (𝟙 Z ⊗ₘ e)) :=
    (MonoidalCategory.tensorHom_comp_tensorHom
      (ρ_ W).inv (ρ_ Z).inv (𝟙 W ⊗ₘ e) (𝟙 Z ⊗ₘ e)).symm
  have hLast :
      (𝟙 P ⊗ₘ (λ_ U).inv) ≫ (𝟙 P ⊗ₘ (e ⊗ₘ e)) =
        𝟙 P ⊗ₘ ((λ_ U).inv ≫ (e ⊗ₘ e)) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  calc
    _ = i ≫ ((𝟙 W ⊗ₘ e) ⊗ₘ (𝟙 Z ⊗ₘ e)) ≫
        tensorδ W Z A A ≫ (𝟙 P ⊗ₘ (β_ A A).hom) := by
      simpa only [P, Category.assoc] using congrArg
        (fun t : P ⟶ (W ⊗ A) ⊗ (Z ⊗ A) =>
          t ≫ tensorδ W Z A A ≫ (𝟙 P ⊗ₘ (β_ A A).hom)) hInsertion
    _ = i ≫ δ₀ ≫ (𝟙 P ⊗ₘ (e ⊗ₘ e)) ≫
        (𝟙 P ⊗ₘ (β_ A A).hom) := by
      simpa only [Category.assoc] using congrArg
        (fun t : (W ⊗ U) ⊗ (Z ⊗ U) ⟶ P ⊗ (A ⊗ A) =>
          i ≫ t ≫ (𝟙 P ⊗ₘ (β_ A A).hom)) hNaturality
    _ = i ≫ δ₀ ≫ (𝟙 P ⊗ₘ (e ⊗ₘ e)) := by
      rw [hCrossTensor]
    _ = (ρ_ P).inv ≫ (𝟙 P ⊗ₘ (λ_ U).inv) ≫
        (𝟙 P ⊗ₘ (e ⊗ₘ e)) := by
      simpa only [Category.assoc] using congrArg
        (fun t : P ⟶ P ⊗ (U ⊗ U) => t ≫ (𝟙 P ⊗ₘ (e ⊗ₘ e))) hUnit
    _ = _ := by
      simpa only [P, U, Category.assoc] using congrArg
        (fun t : P ⊗ U ⟶ P ⊗ (A ⊗ A) => (ρ_ P).inv ≫ t) hLast

variable (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

omit [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)] in
private theorem coefficientUnitPairForProof :
    (λ_ (𝟙_ V)).inv ≫ (L.epsilon ⊗ₘ L.epsilon) ≫
        L.mu (𝟙_ I) (𝟙_ I) ≫
        (ρ_ (S.obj ((𝟙_ I) ⊗ (𝟙_ I)))).inv ≫
        S.obj ((𝟙_ I) ⊗ (𝟙_ I)) ◁ eHomEquiv V (λ_ (𝟙_ I)).hom ≫
        MonoidalClosed.uncurry (S.map ((𝟙_ I) ⊗ (𝟙_ I)) (𝟙_ I)) =
      L.epsilon := by
  let U : I := 𝟙_ I
  let A : V := S.obj U
  let B : V := S.obj (U ⊗ U)
  let e : (𝟙_ V) ⟶ A := L.epsilon
  let m : A ⊗ A ⟶ B := L.mu U U
  let r : U ⊗ U ⟶ U := (λ_ U).hom
  let E : (𝟙_ V) ⟶ ((U ⊗ U) ⟶[V] U) := eHomEquiv V r
  let s : B ⟶ A := (eHomEquiv V (C := V) (X := B) (Y := A)).symm
    (E ≫ S.map (U ⊗ U) U)
  have hAction : s = (ρ_ B).inv ≫ B ◁ E ≫
      MonoidalClosed.uncurry (S.map (U ⊗ U) U) := by
    dsimp only [s]
    rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
    dsimp only [MonoidalClosed.uncurry']
    rw [MonoidalClosed.uncurry_natural_left]
  have hLeft : (λ_ A).hom = e ▷ A ≫ m ≫ s := (L.unit U).1
  have hProduct : (e ⊗ₘ e) ≫ m ≫ s = (λ_ (𝟙_ V)).hom ≫ e := by
    calc
      _ = ((𝟙_ V) ◁ e) ≫ (e ▷ A) ≫ m ≫ s := by
        simp only [MonoidalCategory.tensorHom_def', Category.assoc]
      _ = ((𝟙_ V) ◁ e) ≫ (λ_ A).hom := by
        simpa only [Category.assoc] using congrArg
          (fun t : (𝟙_ V) ⊗ A ⟶ A => ((𝟙_ V) ◁ e) ≫ t) hLeft.symm
      _ = _ := MonoidalCategory.leftUnitor_naturality e
  have hSquare : (λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ e) ≫ m ≫ s = e := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun t : (𝟙_ V) ⊗ (𝟙_ V) ⟶ A => (λ_ (𝟙_ V)).inv ≫ t) hProduct
  rw [hAction] at hSquare
  simpa only [U, A, B, e, m, r, E, Category.assoc] using hSquare

private theorem unitPairTargetRelationForProof (n k : I) :
    (eHomWhiskerRight V ((λ_ (𝟙_ I)).hom ⊗ₘ 𝟙 n) k ⊗ₘ
        𝟙 (S.obj ((𝟙_ I) ⊗ (𝟙_ I)))) ≫
        weightedCoend.ι (weight d n k) S ((𝟙_ I) ⊗ (𝟙_ I)) =
      (𝟙 (((𝟙_ I) ⊗ n) ⟶[V] k) ⊗ₘ
        ((ρ_ (S.obj ((𝟙_ I) ⊗ (𝟙_ I)))).inv ≫
          S.obj ((𝟙_ I) ⊗ (𝟙_ I)) ◁ eHomEquiv V (λ_ (𝟙_ I)).hom ≫
          MonoidalClosed.uncurry
            (S.map ((𝟙_ I) ⊗ (𝟙_ I)) (𝟙_ I)))) ≫
        weightedCoend.ι (weight d n k) S (𝟙_ I) := by
  have h := CategoryTheory.Enriched.weightedCoend.condition_unitPoint
    (weight d n k) S ((𝟙_ I) ⊗ (𝟙_ I)) (𝟙_ I)
    (eHomEquiv V (λ_ (𝟙_ I)).hom)
  rw [weight_point_pre] at h
  exact h

/-- Insert the complete original index Hom using the actual coefficient unit. -/
def indexHom (n k : I) : (n ⟶[V] k) ⟶ Hom d S n k :=
  eHomWhiskerRight V (λ_ n).hom k ≫
    (ρ_ (((𝟙_ I) ⊗ n) ⟶[V] k)).inv ≫
    (𝟙 (((𝟙_ I) ⊗ n) ⟶[V] k) ⊗ₘ L.epsilon) ≫
    weightedCoend.ι (weight d n k) S (𝟙_ I)

/-- Original arrows are inserted at their literal unitor-composite generator. -/
theorem indexHom_point {n k : I} (f : n ⟶ k) :
    eHomEquiv V f ≫ indexHom d S L n k =
      (λ_ (𝟙_ V)).inv ≫
        (eHomEquiv V ((λ_ n).hom ≫ f) ⊗ₘ L.epsilon) ≫
        weightedCoend.ι (weight d n k) S (𝟙_ I) := by
  let W : V := ((𝟙_ I) ⊗ n) ⟶[V] k
  let p : (𝟙_ V) ⟶ W := eHomEquiv V ((λ_ n).hom ≫ f)
  have hPoint : eHomEquiv V f ≫ eHomWhiskerRight V (λ_ n).hom k = p :=
    precompositionPointForProof (λ_ n).hom f
  have hUnit : p ≫ (ρ_ W).inv ≫ (𝟙 W ⊗ₘ L.epsilon) =
      (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ L.epsilon) := by
    simpa only [MonoidalCategory.id_tensorHom,
      MonoidalCategory.unitors_inv_equal, Category.assoc] using
      (MonoidalCategory.rightUnitor_inv_comp_tensorHom p L.epsilon).symm
  calc
    _ = (eHomEquiv V f ≫ eHomWhiskerRight V (λ_ n).hom k) ≫
        (ρ_ W).inv ≫ (𝟙 W ⊗ₘ L.epsilon) ≫
        weightedCoend.ι (weight d n k) S (𝟙_ I) := by
      dsimp only [indexHom, W]
      simp only [Category.assoc]
    _ = p ≫ (ρ_ W).inv ≫ (𝟙 W ⊗ₘ L.epsilon) ≫
        weightedCoend.ι (weight d n k) S (𝟙_ I) :=
      congrArg (fun t : (𝟙_ V) ⟶ W =>
        t ≫ (ρ_ W).inv ≫ (𝟙 W ⊗ₘ L.epsilon) ≫
          weightedCoend.ι (weight d n k) S (𝟙_ I)) hPoint
    _ = (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ L.epsilon) ≫
        weightedCoend.ι (weight d n k) S (𝟙_ I) := by
      let i : W ⊗ S.obj (𝟙_ I) ⟶ Hom d S n k :=
        weightedCoend.ι (weight d n k) S (𝟙_ I)
      have h := congrArg
        (fun t : (𝟙_ V) ⟶ W ⊗ S.obj (𝟙_ I) => t ≫ i) hUnit
      have hLeft : p ≫ (ρ_ W).inv ≫ (𝟙 W ⊗ₘ L.epsilon) ≫ i =
          (p ≫ (ρ_ W).inv ≫ (𝟙 W ⊗ₘ L.epsilon)) ≫ i :=
        (congrArg (fun t : W ⟶ Hom d S n k => p ≫ t)
          (Category.assoc (ρ_ W).inv (𝟙 W ⊗ₘ L.epsilon) i).symm).trans
            (Category.assoc p ((ρ_ W).inv ≫ (𝟙 W ⊗ₘ L.epsilon)) i).symm
      have hRight : ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ L.epsilon)) ≫ i =
          (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ L.epsilon) ≫ i :=
        Category.assoc (λ_ (𝟙_ V)).inv (p ⊗ₘ L.epsilon) i
      change p ≫ (ρ_ W).inv ≫ (𝟙 W ⊗ₘ L.epsilon) ≫ i =
        (λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ L.epsilon) ≫ i
      exact hLeft.trans (h.trans hRight)
    _ = _ := rfl

/-- The complete source identity maps to the already-derived operator identity. -/
theorem indexHom_id (n : I) :
    eId V n ≫ indexHom d S L n n = identityGenerator d S L n := by
  simpa only [eHomEquiv_id, Category.comp_id, identityGenerator] using
    (indexHom_point d S L (𝟙 n))

/-- Both full source Hom factors map to the actual two-coend composition. -/
theorem indexHom_comp (n k l : I) :
    eComp V n k l ≫ indexHom d S L n l =
      (indexHom d S L n k ⊗ₘ indexHom d S L k l) ≫ composition d S L n k l := by
  let U : I := 𝟙_ I
  let H : V := n ⟶[V] k
  let K : V := k ⟶[V] l
  let W : V := (U ⊗ n) ⟶[V] k
  let Z : V := (U ⊗ k) ⟶[V] l
  let T : V := (U ⊗ n) ⟶[V] l
  let Q : V := ((U ⊗ U) ⊗ n) ⟶[V] l
  let A : V := S.obj U
  let B : V := S.obj (U ⊗ U)
  let p : H ⟶ W := eHomWhiskerRight V (λ_ n).hom k
  let q : K ⟶ Z := eHomWhiskerRight V (λ_ k).hom l
  let t : (n ⟶[V] l) ⟶ T := eHomWhiskerRight V (λ_ n).hom l
  let w : T ⟶ Q := eHomWhiskerRight V ((λ_ U).hom ⊗ₘ 𝟙 n) l
  let e : (𝟙_ V) ⟶ A := L.epsilon
  let νW : W ⟶ W ⊗ A := (ρ_ W).inv ≫ (𝟙 W ⊗ₘ e)
  let νZ : Z ⟶ Z ⊗ A := (ρ_ Z).inv ≫ (𝟙 Z ⊗ₘ e)
  let i₁ : W ⊗ A ⟶ Hom d S n k := weightedCoend.ι (weight d n k) S U
  let i₂ : Z ⊗ A ⟶ Hom d S k l := weightedCoend.ι (weight d k l) S U
  let i₃ : Q ⊗ B ⟶ Hom d S n l := weightedCoend.ι (weight d n l) S (U ⊗ U)
  let i₀ : T ⊗ A ⟶ Hom d S n l := weightedCoend.ι (weight d n l) S U
  let γ : W ⊗ Z ⟶ Q := indexGenerator d n k l U U
  let m : A ⊗ A ⟶ B := L.mu U U
  let v : (𝟙_ V) ⟶ A ⊗ A := (λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ e)
  let s : B ⟶ A := (ρ_ B).inv ≫ B ◁ eHomEquiv V (λ_ U).hom ≫
    MonoidalClosed.uncurry (S.map (U ⊗ U) U)
  let f : H ⊗ K ⟶ T := eComp V n k l ≫ t
  have hEntry : (indexHom d S L n k ⊗ₘ indexHom d S L k l) =
      ((p ⊗ₘ q) ≫ (νW ⊗ₘ νZ)) ≫ (i₁ ⊗ₘ i₂) := by
    have h₁ : indexHom d S L n k = (p ≫ νW) ≫ i₁ := by
      change p ≫ (ρ_ W).inv ≫ (𝟙 W ⊗ₘ e) ≫ i₁ =
        (p ≫ ((ρ_ W).inv ≫ (𝟙 W ⊗ₘ e))) ≫ i₁
      exact ((Category.assoc p ((ρ_ W).inv ≫ (𝟙 W ⊗ₘ e)) i₁).trans
        (congrArg (fun t : W ⟶ Hom d S n k => p ≫ t)
          (Category.assoc (ρ_ W).inv (𝟙 W ⊗ₘ e) i₁))).symm
    have h₂ : indexHom d S L k l = (q ≫ νZ) ≫ i₂ := by
      change q ≫ (ρ_ Z).inv ≫ (𝟙 Z ⊗ₘ e) ≫ i₂ =
        (q ≫ ((ρ_ Z).inv ≫ (𝟙 Z ⊗ₘ e))) ≫ i₂
      exact ((Category.assoc q ((ρ_ Z).inv ≫ (𝟙 Z ⊗ₘ e)) i₂).trans
        (congrArg (fun t : Z ⟶ Hom d S k l => q ≫ t)
          (Category.assoc (ρ_ Z).inv (𝟙 Z ⊗ₘ e) i₂))).symm
    calc
      _ = (((p ≫ νW) ≫ i₁) ⊗ₘ ((q ≫ νZ) ≫ i₂)) :=
        congrArg₂ (fun a : H ⟶ Hom d S n k =>
          fun b : K ⟶ Hom d S k l => a ⊗ₘ b) h₁ h₂
      _ = ((p ≫ νW) ⊗ₘ (q ≫ νZ)) ≫ (i₁ ⊗ₘ i₂) :=
        (MonoidalCategory.tensorHom_comp_tensorHom
          (p ≫ νW) (q ≫ νZ) i₁ i₂).symm
      _ = _ := congrArg
        (fun a : H ⊗ K ⟶ (W ⊗ A) ⊗ (Z ⊗ A) => a ≫ (i₁ ⊗ₘ i₂))
        (MonoidalCategory.tensorHom_comp_tensorHom p q νW νZ).symm
  have hGenerator : (i₁ ⊗ₘ i₂) ≫ composition d S L n k l =
      compositionGenerator d S L n k l U U :=
    composition_generator d S L n k l U U
  have hLiteral : compositionGenerator d S L n k l U U =
      tensorδ W Z A A ≫ (𝟙 (W ⊗ Z) ⊗ₘ (β_ A A).hom) ≫ (γ ⊗ₘ m) ≫ i₃ := rfl
  have hPadding : (νW ⊗ₘ νZ) ≫ tensorδ W Z A A ≫
      (𝟙 (W ⊗ Z) ⊗ₘ (β_ A A).hom) =
        (ρ_ (W ⊗ Z)).inv ≫ (𝟙 (W ⊗ Z) ⊗ₘ v) :=
    tensorUnitCoefficientPairForProof W Z A e
  have hPull : (p ⊗ₘ q) ≫ (ρ_ (W ⊗ Z)).inv =
      (ρ_ (H ⊗ K)).inv ≫ ((p ⊗ₘ q) ⊗ₘ 𝟙 (𝟙_ V)) := by
    simpa only [MonoidalCategory.tensorHom_id] using
      MonoidalCategory.rightUnitor_inv_naturality (p ⊗ₘ q)
  have hTensor :
      ((p ⊗ₘ q) ⊗ₘ 𝟙 (𝟙_ V)) ≫ (𝟙 (W ⊗ Z) ⊗ₘ v) ≫ (γ ⊗ₘ m) =
        (((p ⊗ₘ q) ≫ γ) ⊗ₘ (v ≫ m)) := by
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  have hIndex : (p ⊗ₘ q) ≫ γ = f ≫ w := by
    simpa only [p, q, γ, f, t, w, U,
      eHomWhiskerRight_comp, Category.assoc] using
      unitIndexCompositeForProof d n k l
  have hRelation : (w ⊗ₘ 𝟙 B) ≫ i₃ = (𝟙 T ⊗ₘ s) ≫ i₀ :=
    unitPairTargetRelationForProof d S n l
  have hCoefficient : v ≫ m ≫ s = e := by
    dsimp only [v, m, s, e, A, B, U]
    simpa only [Category.assoc] using coefficientUnitPairForProof d S L
  have hFirst : ((f ≫ w) ⊗ₘ (v ≫ m)) =
      (f ⊗ₘ (v ≫ m)) ≫ (w ⊗ₘ 𝟙 B) := by
    simpa only [Category.comp_id] using
      (MonoidalCategory.tensorHom_comp_tensorHom f (v ≫ m) w (𝟙 B)).symm
  have hAfter : (f ⊗ₘ (v ≫ m)) ≫ (𝟙 T ⊗ₘ s) = f ⊗ₘ e := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
    simpa only [Category.assoc] using congrArg
      (fun z : (𝟙_ V) ⟶ A => f ⊗ₘ z) hCoefficient
  have hTarget : (((p ⊗ₘ q) ≫ γ) ⊗ₘ (v ≫ m)) ≫ i₃ =
      (f ⊗ₘ e) ≫ i₀ := by
    calc
      _ = ((f ≫ w) ⊗ₘ (v ≫ m)) ≫ i₃ :=
        congrArg (fun z : H ⊗ K ⟶ Q => (z ⊗ₘ (v ≫ m)) ≫ i₃) hIndex
      _ = (f ⊗ₘ (v ≫ m)) ≫ (w ⊗ₘ 𝟙 B) ≫ i₃ := by
        simpa only [Category.assoc] using congrArg
          (fun z : (H ⊗ K) ⊗ (𝟙_ V) ⟶ Q ⊗ B => z ≫ i₃) hFirst
      _ = (f ⊗ₘ (v ≫ m)) ≫ (𝟙 T ⊗ₘ s) ≫ i₀ :=
        congrArg (fun z : T ⊗ B ⟶ Hom d S n l => (f ⊗ₘ (v ≫ m)) ≫ z) hRelation
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun z : (H ⊗ K) ⊗ (𝟙_ V) ⟶ T ⊗ A => z ≫ i₀) hAfter
  have hLast : (ρ_ (H ⊗ K)).inv ≫ (f ⊗ₘ e) ≫ i₀ =
      eComp V n k l ≫ indexHom d S L n l := by
    have h := congrArg
      (fun z : H ⊗ K ⟶ T ⊗ A => z ≫ i₀)
      (MonoidalCategory.rightUnitor_inv_comp_tensorHom f e)
    rw [← MonoidalCategory.id_tensorHom T e] at h
    have hRight : (f ≫ (ρ_ T).inv ≫ (𝟙 T ⊗ₘ e)) ≫ i₀ =
        eComp V n k l ≫ t ≫ (ρ_ T).inv ≫ (𝟙 T ⊗ₘ e) ≫ i₀ :=
      (Category.assoc f ((ρ_ T).inv ≫ (𝟙 T ⊗ₘ e)) i₀).trans
        ((congrArg (fun z : T ⟶ Hom d S n l => f ≫ z)
          (Category.assoc (ρ_ T).inv (𝟙 T ⊗ₘ e) i₀)).trans
            (Category.assoc (eComp V n k l) t
              ((ρ_ T).inv ≫ (𝟙 T ⊗ₘ e) ≫ i₀)))
    change (ρ_ (H ⊗ K)).inv ≫ (f ⊗ₘ e) ≫ i₀ =
      eComp V n k l ≫ t ≫ (ρ_ T).inv ≫ (𝟙 T ⊗ₘ e) ≫ i₀
    exact (Category.assoc (ρ_ (H ⊗ K)).inv (f ⊗ₘ e) i₀).symm.trans
      (h.trans hRight)
  symm
  calc
    _ = ((p ⊗ₘ q) ≫ (νW ⊗ₘ νZ)) ≫ (i₁ ⊗ₘ i₂) ≫
        composition d S L n k l := by
      simpa only [Category.assoc] using congrArg
        (fun z : H ⊗ K ⟶ Hom d S n k ⊗ Hom d S k l =>
          z ≫ composition d S L n k l) hEntry
    _ = (p ⊗ₘ q) ≫ (νW ⊗ₘ νZ) ≫ compositionGenerator d S L n k l U U := by
      rw [hGenerator]
      exact Category.assoc (p ⊗ₘ q) (νW ⊗ₘ νZ)
        (compositionGenerator d S L n k l U U)
    _ = (p ⊗ₘ q) ≫ (νW ⊗ₘ νZ) ≫ tensorδ W Z A A ≫
        (𝟙 (W ⊗ Z) ⊗ₘ (β_ A A).hom) ≫ (γ ⊗ₘ m) ≫ i₃ := by
      rw [hLiteral]
    _ = (p ⊗ₘ q) ≫ (ρ_ (W ⊗ Z)).inv ≫
        (𝟙 (W ⊗ Z) ⊗ₘ v) ≫ (γ ⊗ₘ m) ≫ i₃ := by
      simpa only [Category.assoc] using congrArg
        (fun z : W ⊗ Z ⟶ (W ⊗ Z) ⊗ (A ⊗ A) =>
          (p ⊗ₘ q) ≫ z ≫ (γ ⊗ₘ m) ≫ i₃) hPadding
    _ = (ρ_ (H ⊗ K)).inv ≫ ((p ⊗ₘ q) ⊗ₘ 𝟙 (𝟙_ V)) ≫
        (𝟙 (W ⊗ Z) ⊗ₘ v) ≫ (γ ⊗ₘ m) ≫ i₃ := by
      simpa only [Category.assoc] using congrArg
        (fun z : H ⊗ K ⟶ (W ⊗ Z) ⊗ (𝟙_ V) =>
          z ≫ (𝟙 (W ⊗ Z) ⊗ₘ v) ≫ (γ ⊗ₘ m) ≫ i₃) hPull
    _ = (ρ_ (H ⊗ K)).inv ≫ (((p ⊗ₘ q) ≫ γ) ⊗ₘ (v ≫ m)) ≫ i₃ := by
      simpa only [Category.assoc] using congrArg
        (fun z : (H ⊗ K) ⊗ (𝟙_ V) ⟶ Q ⊗ B => (ρ_ (H ⊗ K)).inv ≫ z ≫ i₃)
        hTensor
    _ = (ρ_ (H ⊗ K)).inv ≫ (f ⊗ₘ e) ≫ i₀ := by
      simpa only [Category.assoc] using congrArg
        (fun z : (H ⊗ K) ⊗ (𝟙_ V) ⟶ Hom d S n l => (ρ_ (H ⊗ K)).inv ≫ z) hTarget
    _ = _ := hLast

/-- The unit coefficient defines an enriched functor into the operator category. -/
def indexUnitFunctor : EnrichedFunctor V I (OperatorIndex d S L) where
  obj n := ⟨n⟩
  map n k := indexHom d S L n k
  map_id n := by exact indexHom_id d S L n
  map_comp n k l := by exact indexHom_comp d S L n k l

/-- Restriction precomposes with the full unit-coefficient enriched functor. -/
def indexRestriction : EnrichedFunctorCat V (OperatorIndex d S L) ⥤
    EnrichedFunctorCat V I :=
  EnrichedFunctorCat.restriction (indexUnitFunctor d S L)

/-- Restriction keeps the same indexed object, through the tagged index. -/
theorem indexRestriction_obj (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n : I) :
    ((indexRestriction d S L).obj F).toEnrichedFunctor.obj n =
      F.toEnrichedFunctor.obj ⟨n⟩ := rfl

/-- The entire restricted index action is precomposition by the full unit Hom map. -/
theorem indexRestriction_fullMap
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (n k : I) :
    ((indexRestriction d S L).obj F).toEnrichedFunctor.map n k =
      indexHom d S L n k ≫ F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩ := rfl

end CategoryTheory.Enriched.SphereOperator
