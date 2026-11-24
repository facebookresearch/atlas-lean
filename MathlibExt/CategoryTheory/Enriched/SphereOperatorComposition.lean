/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Functor
public import MathlibExt.CategoryTheory.Enriched.Monoidal.ExternalTensor
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorHom
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendMapped
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI vI

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator

open Opposite BraidedCategory Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

/-- The complete ordered index map, including the selected source associator. -/
def indexGenerator (d : EnrichedMonoidalCategoryData V I)
    (n k l a b : I) :
    ((a ⊗ n) ⟶[V] k) ⊗ ((b ⊗ k) ⟶[V] l) ⟶
      (((b ⊗ a) ⊗ n) ⟶[V] l) :=
  ((((λ_ ((a ⊗ n) ⟶[V] k)).inv ≫
      (eId V b ⊗ₘ 𝟙 ((a ⊗ n) ⟶[V] k)) ≫
        d.tensorMap b b (a ⊗ n) k) ⊗ₘ 𝟙 ((b ⊗ k) ⟶[V] l)) ≫
    eComp V (b ⊗ (a ⊗ n)) (b ⊗ k) l) ≫
    (λ_ ((b ⊗ (a ⊗ n)) ⟶[V] l)).inv ≫
    (eHomEquiv V (α_ b a n).hom ⊗ₘ
      𝟙 ((b ⊗ (a ⊗ n)) ⟶[V] l)) ≫
    eComp V ((b ⊗ a) ⊗ n) (b ⊗ (a ⊗ n)) l

/-- Combine full index and coefficient factors into the actual target generator. -/
def compositionGenerator
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n k l a b : I)
    [HasCoproduct (weightedCoend.relations (weight d n l) S)]
    [HasCoproduct (weightedCoend.objects (weight d n l) S)]
    [HasCoequalizer (weightedCoend.leftMap (weight d n l) S)
      (weightedCoend.rightMap (weight d n l) S)] :
    ((((a ⊗ n) ⟶[V] k) ⊗ S.obj a) ⊗
      (((b ⊗ k) ⟶[V] l) ⊗ S.obj b)) ⟶ Hom d S n l :=
  MonoidalCategory.tensorδ ((a ⊗ n) ⟶[V] k) ((b ⊗ k) ⟶[V] l)
      (S.obj a) (S.obj b) ≫
    ((𝟙 (((a ⊗ n) ⟶[V] k) ⊗ ((b ⊗ k) ⟶[V] l))) ⊗ₘ
      (β_ (S.obj a) (S.obj b)).hom) ≫
    (indexGenerator d n k l a b ⊗ₘ L.mu b a) ≫
    weightedCoend.ι (weight d n l) S (b ⊗ a)


/-- Proof-local full tensorator action certificate for both operator balances. -/
private theorem fullTensoratorActionNaturality
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (a a' b b' : I) :
    MonoidalClosed.uncurry
        ((S.map a a' ⊗ₘ S.map b b') ≫
          (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
            (S.obj a) (S.obj a') (S.obj b) (S.obj b')) ≫ L.mu a' b' =
      (L.mu a b ⊗ₘ 𝟙 ((a ⟶[V] a') ⊗ (b ⟶[V] b'))) ≫
        MonoidalClosed.uncurry
          (d.tensorMap a a' b b' ≫ S.map (a ⊗ b) (a' ⊗ b')) := by
  let H : V := (a ⟶[V] a') ⊗ (b ⟶[V] b')
  let P : V := S.obj a ⊗ S.obj b
  let P' : V := S.obj a' ⊗ S.obj b'
  let Q : V := S.obj (a ⊗ b)
  let Q' : V := S.obj (a' ⊗ b')
  let f : H ⟶ (ihom P).obj P' :=
    (S.map a a' ⊗ₘ S.map b b') ≫
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
        (S.obj a) (S.obj a') (S.obj b) (S.obj b')
  let g : H ⟶ (ihom Q).obj Q' :=
    d.tensorMap a a' b b' ≫ S.map (a ⊗ b) (a' ⊗ b')
  have hWhole : f ≫ eHomWhiskerLeft V P (L.mu a' b') =
      g ≫ eHomWhiskerRight V (L.mu a b) Q' := by
    simpa only [f, g, P, P', Q, Q', H, Category.assoc] using
      L.mu_naturality a a' b b'
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight] at hWhole
  have hUncurry :
      MonoidalClosed.uncurry (f ≫ (ihom P).map (L.mu a' b')) =
        MonoidalClosed.uncurry (g ≫ (MonoidalClosed.pre (L.mu a b)).app Q') :=
    congrArg (fun z : H ⟶ (ihom P).obj Q' => MonoidalClosed.uncurry z) hWhole
  have hPost :
      MonoidalClosed.uncurry (f ≫ (ihom P).map (L.mu a' b')) =
        MonoidalClosed.uncurry f ≫ L.mu a' b' :=
    MonoidalClosed.uncurry_natural_right (C := V) f (L.mu a' b')
  have hPre :
      MonoidalClosed.uncurry (g ≫ (MonoidalClosed.pre (L.mu a b)).app Q') =
        (L.mu a b ▷ H) ≫ MonoidalClosed.uncurry g :=
    MonoidalClosed.uncurry_pre_app (C := V) Q' g (L.mu a b)
  have hFull := hPost.symm.trans (hUncurry.trans hPre)
  simpa only [f, g, P, P', Q, Q', H, tensorHom_id] using hFull

/-- The actual full tensorator square with the first coefficient fixed by its identity. -/
private theorem tensorator_left_fixed_action
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (b a a' : I) :
    (α_ (S.obj b) (S.obj a) (a ⟶[V] a')).hom ≫
        S.obj b ◁ MonoidalClosed.uncurry (S.map a a') ≫ L.mu b a' =
      (L.mu b a ▷ (a ⟶[V] a')) ≫ MonoidalClosed.uncurry
        (((λ_ (a ⟶[V] a')).inv ≫
          (eId V b ⊗ₘ 𝟙 (a ⟶[V] a')) ≫ d.tensorMap b b a a') ≫
            S.map (b ⊗ a) (b ⊗ a')) := by
  let H : V := a ⟶[V] a'
  let B : V := b ⟶[V] b
  let K : V := B ⊗ H
  let P : V := S.obj b ⊗ S.obj a
  let P' : V := S.obj b ⊗ S.obj a'
  let Q : V := S.obj (b ⊗ a)
  let Q' : V := S.obj (b ⊗ a')
  let q : H ⟶ K := (λ_ H).inv ≫ (eId V b ⊗ₘ 𝟙 H)
  let f : K ⟶ (ihom P).obj P' :=
    (S.map b b ⊗ₘ S.map a a') ≫
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
        (S.obj b) (S.obj b) (S.obj a) (S.obj a')
  let g : K ⟶ (ihom Q).obj Q' :=
    d.tensorMap b b a a' ≫ S.map (b ⊗ a) (b ⊗ a')
  have hFull : MonoidalClosed.uncurry f ≫ L.mu b a' =
      (L.mu b a ▷ K) ≫ MonoidalClosed.uncurry g := by
    simpa only [f, g, K, B, H, tensorHom_id] using
      fullTensoratorActionNaturality d S L b b a a'
  have hExternal : MonoidalClosed.uncurry f =
      MonoidalCategory.tensorμ (S.obj b) (S.obj a) B H ≫
        (MonoidalClosed.uncurry (S.map b b) ⊗ₘ
          MonoidalClosed.uncurry (S.map a a')) := by
    dsimp only [f, P, P', K, B, H]
    rw [MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.enrichedMonoidalCategoryDataSelf_tensorMap,
      MonoidalClosed.uncurry_curry]
    rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq]
    have hTensor := MonoidalCategory.tensorμ_natural_right_assoc
      (S.obj b) (S.obj a) (S.map b b) (S.map a a')
      ((ihom.ev (S.obj b)).app (S.obj b) ⊗ₘ
        (ihom.ev (S.obj a)).app (S.obj a'))
    calc
      _ = MonoidalCategory.tensorμ (S.obj b) (S.obj a) B H ≫
          ((S.obj b ◁ S.map b b ⊗ₘ S.obj a ◁ S.map a a') ≫
            ((ihom.ev (S.obj b)).app (S.obj b) ⊗ₘ
              (ihom.ev (S.obj a)).app (S.obj a'))) := hTensor
      _ = _ := by rw [tensorHom_comp_tensorHom]
  have hIdentity : MonoidalClosed.uncurry (eId V b ≫ S.map b b) =
      (ρ_ (S.obj b)).hom := by
    rw [S.map_id, MonoidalClosed.enrichedCategorySelf_id,
      MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry]
  have hUnit :
      P ◁ (λ_ H).inv ≫ MonoidalCategory.tensorμ (S.obj b) (S.obj a) (𝟙_ V) H ≫
        ((ρ_ (S.obj b)).hom ⊗ₘ 𝟙 (S.obj a ⊗ H)) =
      (α_ (S.obj b) (S.obj a) H).hom := by
    dsimp only [P, MonoidalCategory.tensorμ]
    rw [CategoryTheory.braiding_tensorUnit_right]
    monoidal
  have hNormalized : P ◁ q ≫ MonoidalClosed.uncurry f =
      (α_ (S.obj b) (S.obj a) H).hom ≫
        S.obj b ◁ MonoidalClosed.uncurry (S.map a a') := by
    have hTail :
        (ρ_ (S.obj b)).hom ⊗ₘ MonoidalClosed.uncurry (S.map a a') =
      ((ρ_ (S.obj b)).hom ⊗ₘ 𝟙 (S.obj a ⊗ H)) ≫
        (𝟙 (S.obj b) ⊗ₘ MonoidalClosed.uncurry (S.map a a')) := by
      rw [tensorHom_comp_tensorHom]
      simp only [Category.comp_id, Category.id_comp]
    calc
      _ = P ◁ (λ_ H).inv ≫
          MonoidalCategory.tensorμ (S.obj b) (S.obj a) (𝟙_ V) H ≫
          (((S.obj b ◁ eId V b) ≫ MonoidalClosed.uncurry (S.map b b)) ⊗ₘ
            MonoidalClosed.uncurry (S.map a a')) := by
        dsimp only [q]
        rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, hExternal,
          MonoidalCategory.tensorμ_natural_right_assoc, tensorHom_comp_tensorHom]
        simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
      _ = P ◁ (λ_ H).inv ≫
          MonoidalCategory.tensorμ (S.obj b) (S.obj a) (𝟙_ V) H ≫
          ((ρ_ (S.obj b)).hom ⊗ₘ MonoidalClosed.uncurry (S.map a a')) := by
        rw [← MonoidalClosed.uncurry_natural_left, hIdentity]
      _ = _ := by
        rw [hTail]
        simpa only [Category.assoc, id_tensorHom] using congrArg
          (fun z : P ⊗ H ⟶ S.obj b ⊗ (S.obj a ⊗ H) =>
            z ≫ S.obj b ◁ MonoidalClosed.uncurry (S.map a a')) hUnit
  calc
    _ = (P ◁ q ≫ MonoidalClosed.uncurry f) ≫ L.mu b a' := by
      simpa only [H, Category.assoc] using congrArg
        (fun z : P ⊗ H ⟶ P' => z ≫ L.mu b a') hNormalized.symm
    _ = P ◁ q ≫ (L.mu b a ▷ K) ≫ MonoidalClosed.uncurry g := by
      rw [Category.assoc, hFull]
    _ = (L.mu b a ▷ H) ≫ Q ◁ q ≫ MonoidalClosed.uncurry g := by
      rw [← whisker_exchange_assoc]
    _ = (L.mu b a ▷ H) ≫ MonoidalClosed.uncurry (q ≫ g) := by
      exact congrArg
        (fun z : Q ⊗ H ⟶ Q' => (L.mu b a ▷ H) ≫ z)
        (MonoidalClosed.uncurry_natural_left (C := V) q g).symm
    _ = _ := by simp only [q, g, H, Category.assoc]

/-- The actual full tensorator square with the second coefficient fixed by its identity. -/
private theorem tensorator_right_fixed_action
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (b b' a : I) :
    (α_ (S.obj b) (S.obj a) (b ⟶[V] b')).hom ≫
        S.obj b ◁ (β_ (S.obj a) (b ⟶[V] b')).hom ≫
        (α_ (S.obj b) (b ⟶[V] b') (S.obj a)).inv ≫
        (MonoidalClosed.uncurry (S.map b b') ▷ S.obj a) ≫ L.mu b' a =
      (L.mu b a ▷ (b ⟶[V] b')) ≫ MonoidalClosed.uncurry
        ((fixedRightTensor d a).map b b' ≫ S.map (b ⊗ a) (b' ⊗ a)) := by
  let H : V := b ⟶[V] b'
  let A : V := a ⟶[V] a
  let K : V := H ⊗ A
  let P : V := S.obj b ⊗ S.obj a
  let P' : V := S.obj b' ⊗ S.obj a
  let Q : V := S.obj (b ⊗ a)
  let Q' : V := S.obj (b' ⊗ a)
  let q : H ⟶ K := (ρ_ H).inv ≫ (𝟙 H ⊗ₘ eId V a)
  let f : K ⟶ (ihom P).obj P' :=
    (S.map b b' ⊗ₘ S.map a a) ≫
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V).tensorMap
        (S.obj b) (S.obj b') (S.obj a) (S.obj a)
  let g : K ⟶ (ihom Q).obj Q' :=
    d.tensorMap b b' a a ≫ S.map (b ⊗ a) (b' ⊗ a)
  have hFull : MonoidalClosed.uncurry f ≫ L.mu b' a =
      (L.mu b a ▷ K) ≫ MonoidalClosed.uncurry g := by
    simpa only [f, g, K, A, H, tensorHom_id] using
      fullTensoratorActionNaturality d S L b b' a a
  have hExternal : MonoidalClosed.uncurry f =
      MonoidalCategory.tensorμ (S.obj b) (S.obj a) H A ≫
        (MonoidalClosed.uncurry (S.map b b') ⊗ₘ
          MonoidalClosed.uncurry (S.map a a)) := by
    dsimp only [f, P, P', K, H, A]
    rw [MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.enrichedMonoidalCategoryDataSelf_tensorMap,
      MonoidalClosed.uncurry_curry]
    rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq]
    have hTensor := MonoidalCategory.tensorμ_natural_right_assoc
      (S.obj b) (S.obj a) (S.map b b') (S.map a a)
      ((ihom.ev (S.obj b)).app (S.obj b') ⊗ₘ
        (ihom.ev (S.obj a)).app (S.obj a))
    calc
      _ = MonoidalCategory.tensorμ (S.obj b) (S.obj a) H A ≫
          ((S.obj b ◁ S.map b b' ⊗ₘ S.obj a ◁ S.map a a) ≫
            ((ihom.ev (S.obj b)).app (S.obj b') ⊗ₘ
              (ihom.ev (S.obj a)).app (S.obj a))) := hTensor
      _ = _ := by rw [tensorHom_comp_tensorHom]
  have hIdentity : MonoidalClosed.uncurry (eId V a ≫ S.map a a) =
      (ρ_ (S.obj a)).hom := by
    rw [S.map_id, MonoidalClosed.enrichedCategorySelf_id,
      MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry]
  have hUnit :
      P ◁ (ρ_ H).inv ≫ MonoidalCategory.tensorμ (S.obj b) (S.obj a) H (𝟙_ V) ≫
        (𝟙 (S.obj b ⊗ H) ⊗ₘ (ρ_ (S.obj a)).hom) =
      (α_ (S.obj b) (S.obj a) H).hom ≫ S.obj b ◁ (β_ (S.obj a) H).hom ≫
        (α_ (S.obj b) H (S.obj a)).inv := by
    dsimp only [P, MonoidalCategory.tensorμ]
    monoidal
  have hNormalized : P ◁ q ≫ MonoidalClosed.uncurry f =
      (α_ (S.obj b) (S.obj a) H).hom ≫ S.obj b ◁ (β_ (S.obj a) H).hom ≫
        (α_ (S.obj b) H (S.obj a)).inv ≫
        (MonoidalClosed.uncurry (S.map b b') ▷ S.obj a) := by
    have hTail :
        MonoidalClosed.uncurry (S.map b b') ⊗ₘ (ρ_ (S.obj a)).hom =
      (𝟙 (S.obj b ⊗ H) ⊗ₘ (ρ_ (S.obj a)).hom) ≫
        (MonoidalClosed.uncurry (S.map b b') ⊗ₘ 𝟙 (S.obj a)) := by
      rw [tensorHom_comp_tensorHom]
      simp only [Category.comp_id, Category.id_comp]
    calc
      _ = P ◁ (ρ_ H).inv ≫
          MonoidalCategory.tensorμ (S.obj b) (S.obj a) H (𝟙_ V) ≫
          (MonoidalClosed.uncurry (S.map b b') ⊗ₘ
            ((S.obj a ◁ eId V a) ≫ MonoidalClosed.uncurry (S.map a a))) := by
        dsimp only [q]
        rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, hExternal,
          MonoidalCategory.tensorμ_natural_right_assoc, tensorHom_comp_tensorHom]
        simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp]
      _ = P ◁ (ρ_ H).inv ≫
          MonoidalCategory.tensorμ (S.obj b) (S.obj a) H (𝟙_ V) ≫
          (MonoidalClosed.uncurry (S.map b b') ⊗ₘ (ρ_ (S.obj a)).hom) := by
        rw [← MonoidalClosed.uncurry_natural_left, hIdentity]
      _ = _ := by
        rw [hTail]
        simpa only [Category.assoc, tensorHom_id] using congrArg
          (fun z : P ⊗ H ⟶ (S.obj b ⊗ H) ⊗ S.obj a =>
            z ≫ (MonoidalClosed.uncurry (S.map b b') ▷ S.obj a)) hUnit
  calc
    _ = (P ◁ q ≫ MonoidalClosed.uncurry f) ≫ L.mu b' a := by
      simpa only [H, Category.assoc] using congrArg
        (fun z : P ⊗ H ⟶ P' => z ≫ L.mu b' a) hNormalized.symm
    _ = P ◁ q ≫ (L.mu b a ▷ K) ≫ MonoidalClosed.uncurry g := by
      rw [Category.assoc, hFull]
    _ = (L.mu b a ▷ H) ≫ Q ◁ q ≫ MonoidalClosed.uncurry g := by
      rw [← whisker_exchange_assoc]
    _ = (L.mu b a ▷ H) ≫ MonoidalClosed.uncurry (q ≫ g) := by
      exact congrArg
        (fun z : Q ⊗ H ⟶ Q' => (L.mu b a ▷ H) ≫ z)
        (MonoidalClosed.uncurry_natural_left (C := V) q g).symm
    _ = _ := by
      have hArgs : q ≫ g =
          (fixedRightTensor d a).map b b' ≫ S.map (b ⊗ a) (b' ⊗ a) := by
        have hMap : (fixedRightTensor d a).map b b' =
            q ≫ d.tensorMap b b' a a := by
          exact (fixedRightTensor_map d a b b').trans
            (Category.assoc (ρ_ H).inv (𝟙 H ⊗ₘ eId V a)
              (d.tensorMap b b' a a)).symm
        have hPost := congrArg
          (fun f : H ⟶ ((b ⊗ a) ⟶[V] (b' ⊗ a)) =>
            f ≫ S.map (b ⊗ a) (b' ⊗ a)) hMap
        exact (Category.assoc q (d.tensorMap b b' a a)
          (S.map (b ⊗ a) (b' ⊗ a))).symm.trans hPost.symm
      exact congrArg
        (fun f : H ⟶ (ihom Q).obj Q' =>
          (L.mu b a ▷ H) ≫ MonoidalClosed.uncurry f) hArgs

attribute [local instance] Enriched.prodCategory

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The proof-local left identity insertion keeps the full varying Hom object. -/
private def fixedLeftProductForProof (b : I) : EnrichedFunctor V I (I × I) where
  obj a := (b, a)
  map a a' := (λ_ (a ⟶[V] a')).inv ≫
    (eId V b ⊗ₘ 𝟙 (a ⟶[V] a'))
  map_id a := by
    change eId V a ≫ (λ_ (a ⟶[V] a)).inv ≫
        (eId V b ⊗ₘ 𝟙 (a ⟶[V] a)) =
      (λ_ (𝟙_ V)).inv ≫ (eId V b ⊗ₘ eId V a)
    rw [leftUnitor_inv_naturality_assoc]
    slice_lhs 2 3 =>
      rw [← id_tensorHom, tensorHom_comp_tensorHom]
      simp
  map_comp a a' a'' := by
    have hIdentity : (eId V b ⊗ₘ eId V b) ≫ eComp V b b b =
        (λ_ (𝟙_ V)).hom ≫ eId V b := by
      rw [← cancel_epi (λ_ (𝟙_ V)).inv]
      simp only [Iso.inv_hom_id_assoc]
      rw [leftUnitor_inv_comp_tensorHom_assoc, e_id_comp, Category.comp_id]
    have hTensorUnit {X Y Z : V} (f : 𝟙_ V ⟶ Y) (g : X ⟶ Z) :
        f ⊗ₘ g = (λ_ X).hom ≫ g ≫ (λ_ Z).inv ≫ f ▷ Z := by
      rw [← cancel_epi (λ_ X).inv]
      simp only [Iso.inv_hom_id_assoc]
      exact leftUnitor_inv_comp_tensorHom f g
    change eComp V a a' a'' ≫ (λ_ (a ⟶[V] a'')).inv ≫
        (eId V b ⊗ₘ 𝟙 (a ⟶[V] a'')) =
      (((λ_ (a ⟶[V] a')).inv ≫ (eId V b ⊗ₘ 𝟙 (a ⟶[V] a'))) ⊗ₘ
        ((λ_ (a' ⟶[V] a'')).inv ≫ (eId V b ⊗ₘ 𝟙 (a' ⟶[V] a'')))) ≫
        MonoidalCategory.tensorμ (b ⟶[V] b) (a ⟶[V] a')
          (b ⟶[V] b) (a' ⟶[V] a'') ≫
        (eComp V b b b ⊗ₘ eComp V a a' a'')
    rw [← cancel_epi (λ_ ((a ⟶[V] a') ⊗ (a' ⟶[V] a''))).hom]
    nth_rewrite 2 [MonoidalCategory.tensor_left_unitality]
    simp only [Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Iso.hom_inv_id_assoc]
    rw [MonoidalCategory.tensorμ_natural_assoc, tensorHom_comp_tensorHom]
    simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]
    rw [hIdentity]
    nth_rewrite 2 [← Category.id_comp (eComp V a a' a'')]
    rw [← tensorHom_comp_tensorHom]
    simp only [tensorHom_id]
    rw [hTensorUnit, ← MonoidalCategory.leftUnitor_monoidal_assoc,
      ← MonoidalCategory.tensor_left_unitality_assoc]

omit [MonoidalClosed V] in
/-- The selected left tensor functor used only to prove the full index-weight certificate. -/
private def fixedLeftTensorForProof (d : EnrichedMonoidalCategoryData V I) (b : I) :
    EnrichedFunctor V I I :=
  (fixedLeftProductForProof (V := V) b).comp V d.tensorEnrichedFunctor

omit [MonoidalClosed V] in
private theorem fixedLeftTensor_mapForProof
    (d : EnrichedMonoidalCategoryData V I) (b a a' : I) :
    (fixedLeftTensorForProof d b).map a a' =
      (λ_ (a ⟶[V] a')).inv ≫ (eId V b ⊗ₘ 𝟙 (a ⟶[V] a')) ≫
        d.tensorMap b b a a' := by
  change ((λ_ (a ⟶[V] a')).inv ≫ (eId V b ⊗ₘ 𝟙 (a ⟶[V] a'))) ≫
    d.tensorMap b b a a' = _
  exact Category.assoc _ _ _

omit [MonoidalClosed V] in
/-- The complete selected associator square, before either identity specialization. -/
private theorem associator_full_hom_whisker
    (d : EnrichedMonoidalCategoryData V I) (b b' a a' n n' : I) :
    ((d.tensorMap b b' a a' ▷ (n ⟶[V] n')) ≫
        d.tensorMap (b ⊗ a) (b' ⊗ a') n n') ≫
      eHomWhiskerLeft V ((b ⊗ a) ⊗ n) (α_ b' a' n').hom =
    ((α_ (b ⟶[V] b') (a ⟶[V] a') (n ⟶[V] n')).hom ≫
        (b ⟶[V] b') ◁ d.tensorMap a a' n n' ≫
        d.tensorMap b b' (a ⊗ n) (a' ⊗ n')) ≫
      eHomWhiskerRight V (α_ b a n).hom (b' ⊗ (a' ⊗ n')) := by
  exact unitGradedNaturality_eq_whisker
    (f := (d.tensorMap b b' a a' ▷ (n ⟶[V] n')) ≫
      d.tensorMap (b ⊗ a) (b' ⊗ a') n n')
    (g := (α_ (b ⟶[V] b') (a ⟶[V] a') (n ⟶[V] n')).hom ≫
      (b ⟶[V] b') ◁ d.tensorMap a a' n n' ≫
      d.tensorMap b b' (a ⊗ n) (a' ⊗ n'))
    (a := (α_ b a n).hom) (b := (α_ b' a' n').hom)
    (h := d.associatorNaturality b b' a a' n n')


omit [MonoidalClosed V] [MonoidalCategory I] [BraidedCategory V] in
/-- Move the actual middle index isomorphism across the entire enriched composition. -/
private theorem eComp_middle_iso_transportForProof
    (X Y Y' Z : I) (e : Y ≅ Y') :
    (eHomWhiskerLeft V X e.hom ▷ (Y' ⟶[V] Z)) ≫ eComp V X Y' Z =
      (X ⟶[V] Y) ◁ eHomWhiskerRight V e.hom Z ≫ eComp V X Y Z := by
  have h := eHom_whisker_cancel V (X := X) (Z := Z) e
  have ht := congrArg
    (fun f : ((X ⟶[V] Y) ⊗ (Y ⟶[V] Z)) ⟶ (X ⟶[V] Z) =>
      ((X ⟶[V] Y) ◁ eHomWhiskerRight V e.hom Z) ≫ f) h
  rw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← eHomWhiskerRight_comp, e.inv_hom_id, eHomWhiskerRight_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp] at ht
  exact ht


omit [MonoidalClosed V] [MonoidalCategory I] [BraidedCategory V] in
private theorem inserted_left_identity_compForProof (X Y : I) :
    (eId V X ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ eComp V X X Y =
      (λ_ (X ⟶[V] Y)).hom := by
  rw [← cancel_epi (λ_ (X ⟶[V] Y)).inv]
  simp only [tensorHom_id, e_id_comp,
    Iso.inv_hom_id]

omit [MonoidalClosed V] [MonoidalCategory I] [BraidedCategory V] in
private theorem inserted_right_identity_compForProof (X Y : I) :
    (𝟙 (X ⟶[V] Y) ⊗ₘ eId V Y) ≫ eComp V X Y Y =
      (ρ_ (X ⟶[V] Y)).hom := by
  rw [← cancel_epi (ρ_ (X ⟶[V] Y)).inv]
  simp only [id_tensorHom, e_comp_id,
    Iso.inv_hom_id]

omit [MonoidalClosed V] in
/-- The full crossing left by two opposite unit insertions is positive. -/
private theorem tensor_unit_exchange_leftForProof (H B : V) :
    ((λ_ H).inv ⊗ₘ (ρ_ B).inv) ≫
      MonoidalCategory.tensorμ (𝟙_ V) H B (𝟙_ V) ≫
      ((λ_ B).hom ⊗ₘ (ρ_ H).hom) = (β_ H B).hom := by
  let X : V := H ⊗ B
  let Y : V := B ⊗ H
  let f : X ⟶ Y := (β_ H B).hom
  have hPre :
      ((λ_ H).inv ⊗ₘ (ρ_ B).inv) ≫
        (α_ (𝟙_ V) H (B ⊗ (𝟙_ V))).hom ≫
        (𝟙_ V) ◁ (α_ H B (𝟙_ V)).inv =
      (λ_ X).inv ≫ (𝟙_ V) ◁ (ρ_ X).inv := by
    dsimp only [X]
    monoidal
  have hPost :
      (𝟙_ V) ◁ (α_ B H (𝟙_ V)).hom ≫
        (α_ (𝟙_ V) B (H ⊗ (𝟙_ V))).inv ≫
        ((λ_ B).hom ⊗ₘ (ρ_ H).hom) =
      (𝟙_ V) ◁ (ρ_ Y).hom ≫ (λ_ Y).hom := by
    dsimp only [Y]
    monoidal
  have hRight :
      (ρ_ X).inv ≫ (f ▷ (𝟙_ V)) ≫ (ρ_ Y).hom = f := by
    rw [rightUnitor_naturality]
    simp only [Iso.inv_hom_id_assoc]
  have hLeft :
      (λ_ X).inv ≫ (𝟙_ V) ◁ f ≫ (λ_ Y).hom = f := by
    rw [leftUnitor_naturality]
    simp only [Iso.inv_hom_id_assoc]
  calc
    _ = (((λ_ H).inv ⊗ₘ (ρ_ B).inv) ≫
        (α_ (𝟙_ V) H (B ⊗ (𝟙_ V))).hom ≫
        (𝟙_ V) ◁ (α_ H B (𝟙_ V)).inv) ≫
      (𝟙_ V) ◁ (f ▷ (𝟙_ V)) ≫
      ((𝟙_ V) ◁ (α_ B H (𝟙_ V)).hom ≫
        (α_ (𝟙_ V) B (H ⊗ (𝟙_ V))).inv ≫
        ((λ_ B).hom ⊗ₘ (ρ_ H).hom)) := by
      simp only [MonoidalCategory.tensorμ, f, Category.assoc]
    _ = ((λ_ X).inv ≫ (𝟙_ V) ◁ (ρ_ X).inv) ≫
        (𝟙_ V) ◁ (f ▷ (𝟙_ V)) ≫
        ((𝟙_ V) ◁ (ρ_ Y).hom ≫ (λ_ Y).hom) := by
      rw [hPre, hPost]
    _ = (λ_ X).inv ≫
        (𝟙_ V) ◁ ((ρ_ X).inv ≫ (f ▷ (𝟙_ V)) ≫ (ρ_ Y).hom) ≫
        (λ_ Y).hom := by
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    _ = f := by rw [hRight]; exact hLeft
    _ = _ := rfl

omit [MonoidalClosed V] in
/-- The other product path crosses only the tensor unit. -/
private theorem tensor_unit_exchange_rightForProof (B H : V) :
    ((ρ_ B).inv ⊗ₘ (λ_ H).inv) ≫
      MonoidalCategory.tensorμ B (𝟙_ V) (𝟙_ V) H ≫
      ((ρ_ B).hom ⊗ₘ (λ_ H).hom) = 𝟙 (B ⊗ H) := by
  dsimp only [MonoidalCategory.tensorμ]
  rw [CategoryTheory.braiding_tensorUnit_left]
  monoidal

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The complete two product paths differ by the positive whole Hom crossing. -/
private theorem product_full_exchangeForProof (b b' x y : I) :
    (((fixedLeftProductForProof (V := V) b).map x y) ⊗ₘ
        (fixedRightProduct (V := V) y).map b b') ≫
      (Enriched.prodCategory V I I).comp (b, x) (b, y) (b', y) =
    (β_ (x ⟶[V] y) (b ⟶[V] b')).hom ≫
      (((fixedRightProduct (V := V) x).map b b') ⊗ₘ
        (fixedLeftProductForProof (V := V) b').map x y) ≫
      (Enriched.prodCategory V I I).comp (b, x) (b', x) (b', y) := by
  let H : V := x ⟶[V] y
  let B : V := b ⟶[V] b'
  have hL :
      (((fixedLeftProductForProof (V := V) b).map x y) ⊗ₘ
          (fixedRightProduct (V := V) y).map b b') ≫
        (Enriched.prodCategory V I I).comp (b, x) (b, y) (b', y) =
      (β_ H B).hom := by
    dsimp only [fixedLeftProductForProof, fixedRightProduct]
    rw [Enriched.prodEComp]
    rw [← tensorHom_comp_tensorHom_assoc, MonoidalCategory.tensorμ_natural_assoc,
      tensorHom_comp_tensorHom]
    simp only [tensorHom_id, id_tensorHom]
    have hB : (eId V b ▷ B) ≫ eComp V b b b' = (λ_ B).hom := by
      simpa only [B, tensorHom_id] using
        inserted_left_identity_compForProof (V := V) b b'
    have hH : (H ◁ eId V y) ≫ eComp V x y y = (ρ_ H).hom := by
      simpa only [H, id_tensorHom] using
        inserted_right_identity_compForProof (V := V) x y
    rw [hB, hH]
    exact tensor_unit_exchange_leftForProof H B
  have hR :
      (((fixedRightProduct (V := V) x).map b b') ⊗ₘ
          (fixedLeftProductForProof (V := V) b').map x y) ≫
        (Enriched.prodCategory V I I).comp (b, x) (b', x) (b', y) =
      𝟙 (B ⊗ H) := by
    dsimp only [fixedLeftProductForProof, fixedRightProduct]
    rw [Enriched.prodEComp]
    rw [← tensorHom_comp_tensorHom_assoc, MonoidalCategory.tensorμ_natural_assoc,
      tensorHom_comp_tensorHom]
    simp only [tensorHom_id, id_tensorHom]
    have hB : (B ◁ eId V b') ≫ eComp V b b' b' = (ρ_ B).hom := by
      simpa only [B, id_tensorHom] using
        inserted_right_identity_compForProof (V := V) b b'
    have hH : (eId V x ▷ H) ≫ eComp V x x y = (λ_ H).hom := by
      simpa only [H, tensorHom_id] using
        inserted_left_identity_compForProof (V := V) x y
    rw [hB, hH]
    exact tensor_unit_exchange_rightForProof B H
  rw [hL]
  change (β_ H B).hom = (β_ H B).hom ≫ _
  rw [hR, Category.comp_id]

omit [MonoidalClosed V] in
/-- The full selected tensor inherits the product exchange, with no index braiding. -/
private theorem tensor_full_exchangeForProof
    (d : EnrichedMonoidalCategoryData V I) (b b' x y : I) :
    (((fixedLeftTensorForProof d b).map x y) ⊗ₘ
        (fixedRightTensor d y).map b b') ≫
      eComp V (b ⊗ x) (b ⊗ y) (b' ⊗ y) =
    (β_ (x ⟶[V] y) (b ⟶[V] b')).hom ≫
      (((fixedRightTensor d x).map b b') ⊗ₘ
        (fixedLeftTensorForProof d b').map x y) ≫
      eComp V (b ⊗ x) (b' ⊗ x) (b' ⊗ y) := by
  have hL :
      (((fixedLeftTensorForProof d b).map x y) ⊗ₘ
          (fixedRightTensor d y).map b b') ≫
        eComp V (b ⊗ x) (b ⊗ y) (b' ⊗ y) =
      ((((fixedLeftProductForProof (V := V) b).map x y) ⊗ₘ
          (fixedRightProduct (V := V) y).map b b') ≫
        (Enriched.prodCategory V I I).comp (b, x) (b, y) (b', y)) ≫
        d.tensorMap b b' x y := by
    let p : (x ⟶[V] y) ⟶ (b ⟶[V] b) ⊗ (x ⟶[V] y) :=
      (λ_ (x ⟶[V] y)).inv ≫ (eId V b ⊗ₘ 𝟙 (x ⟶[V] y))
    let q : (b ⟶[V] b') ⟶ (b ⟶[V] b') ⊗ (y ⟶[V] y) :=
      (ρ_ (b ⟶[V] b')).inv ≫ (𝟙 (b ⟶[V] b') ⊗ₘ eId V y)
    change ((p ≫ d.tensorMap b b x y) ⊗ₘ (q ≫ d.tensorMap b b' y y)) ≫
        eComp V (b ⊗ x) (b ⊗ y) (b' ⊗ y) =
      ((p ⊗ₘ q) ≫ (Enriched.prodCategory V I I).comp
        (b, x) (b, y) (b', y)) ≫ d.tensorMap b b' x y
    calc
      _ = ((p ⊗ₘ q) ≫
          (d.tensorMap b b x y ⊗ₘ d.tensorMap b b' y y)) ≫
          eComp V (b ⊗ x) (b ⊗ y) (b' ⊗ y) :=
        congrArg (fun h => h ≫ eComp V (b ⊗ x) (b ⊗ y) (b' ⊗ y))
          (tensorHom_comp_tensorHom p q
            (d.tensorMap b b x y) (d.tensorMap b b' y y)).symm
      _ = (p ⊗ₘ q) ≫
          ((d.tensorMap b b x y ⊗ₘ d.tensorMap b b' y y) ≫
            eComp V (b ⊗ x) (b ⊗ y) (b' ⊗ y)) := Category.assoc _ _ _
      _ = (p ⊗ₘ q) ≫ ((Enriched.prodCategory V I I).comp
          (b, x) (b, y) (b', y) ≫ d.tensorMap b b' x y) :=
        congrArg (fun h => (p ⊗ₘ q) ≫ h) (d.tensorMap_comp b b b' x y y).symm
      _ = _ := (Category.assoc _ _ _).symm
  have hR :
      (((fixedRightTensor d x).map b b') ⊗ₘ
          (fixedLeftTensorForProof d b').map x y) ≫
        eComp V (b ⊗ x) (b' ⊗ x) (b' ⊗ y) =
      ((((fixedRightProduct (V := V) x).map b b') ⊗ₘ
          (fixedLeftProductForProof (V := V) b').map x y) ≫
        (Enriched.prodCategory V I I).comp (b, x) (b', x) (b', y)) ≫
        d.tensorMap b b' x y := by
    let p : (b ⟶[V] b') ⟶ (b ⟶[V] b') ⊗ (x ⟶[V] x) :=
      (ρ_ (b ⟶[V] b')).inv ≫ (𝟙 (b ⟶[V] b') ⊗ₘ eId V x)
    let q : (x ⟶[V] y) ⟶ (b' ⟶[V] b') ⊗ (x ⟶[V] y) :=
      (λ_ (x ⟶[V] y)).inv ≫ (eId V b' ⊗ₘ 𝟙 (x ⟶[V] y))
    change ((p ≫ d.tensorMap b b' x x) ⊗ₘ (q ≫ d.tensorMap b' b' x y)) ≫
        eComp V (b ⊗ x) (b' ⊗ x) (b' ⊗ y) =
      ((p ⊗ₘ q) ≫ (Enriched.prodCategory V I I).comp
        (b, x) (b', x) (b', y)) ≫ d.tensorMap b b' x y
    calc
      _ = ((p ⊗ₘ q) ≫
          (d.tensorMap b b' x x ⊗ₘ d.tensorMap b' b' x y)) ≫
          eComp V (b ⊗ x) (b' ⊗ x) (b' ⊗ y) :=
        congrArg (fun h => h ≫ eComp V (b ⊗ x) (b' ⊗ x) (b' ⊗ y))
          (tensorHom_comp_tensorHom p q
            (d.tensorMap b b' x x) (d.tensorMap b' b' x y)).symm
      _ = (p ⊗ₘ q) ≫
          ((d.tensorMap b b' x x ⊗ₘ d.tensorMap b' b' x y) ≫
            eComp V (b ⊗ x) (b' ⊗ x) (b' ⊗ y)) := Category.assoc _ _ _
      _ = (p ⊗ₘ q) ≫ ((Enriched.prodCategory V I I).comp
          (b, x) (b', x) (b', y) ≫ d.tensorMap b b' x y) :=
        congrArg (fun h => (p ⊗ₘ q) ≫ h) (d.tensorMap_comp b b' b' x x y).symm
      _ = _ := (Category.assoc _ _ _).symm
  calc
    _ = _ := hL
    _ = ((β_ (x ⟶[V] y) (b ⟶[V] b')).hom ≫
        (((fixedRightProduct (V := V) x).map b b') ⊗ₘ
          (fixedLeftProductForProof (V := V) b').map x y) ≫
        (Enriched.prodCategory V I I).comp (b, x) (b', x) (b', y)) ≫
        d.tensorMap b b' x y := congrArg
      (fun f => f ≫ d.tensorMap b b' x y)
      (product_full_exchangeForProof (V := V) b b' x y)
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => (β_ (x ⟶[V] y) (b ⟶[V] b')).hom ≫ f) hR.symm


omit [MonoidalClosed V] in
private theorem fixedLeftTensor_objForExport
    (d : EnrichedMonoidalCategoryData V I) (b x : I) :
    (fixedLeftTensorForProof d b).obj x = b ⊗ x := rfl

omit [MonoidalClosed V] in
set_option backward.isDefEq.respectTransparency false in
/-- The two full independent Hom actions commute through the actual product braid. -/
public theorem tensor_full_exchange
    (d : EnrichedMonoidalCategoryData V I) (b b' x y : I) :
    (((λ_ (x ⟶[V] y)).inv ≫
          (eId V b ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap b b x y) ⊗ₘ
        (fixedRightTensor d y).map b b') ≫
      eComp V (b ⊗ x) (b ⊗ y) (b' ⊗ y) =
    (β_ (x ⟶[V] y) (b ⟶[V] b')).hom ≫
      ((fixedRightTensor d x).map b b' ⊗ₘ
        ((λ_ (x ⟶[V] y)).inv ≫
          (eId V b' ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap b' b' x y)) ≫
      eComp V (b ⊗ x) (b' ⊗ x) (b' ⊗ y) := by
  simpa only [fixedLeftTensor_mapForProof, Category.assoc] using
    tensor_full_exchangeForProof d b b' x y


omit [MonoidalClosed V] in
set_option backward.isDefEq.respectTransparency false in
/-- Fixing the first index retains the entire enriched identity of the second index. -/
public theorem tensor_left_id
    (d : EnrichedMonoidalCategoryData V I) (b x : I) :
    eId V x ≫ (λ_ (x ⟶[V] x)).inv ≫
        (eId V b ⊗ₘ 𝟙 (x ⟶[V] x)) ≫ d.tensorMap b b x x =
      eId V (b ⊗ x) := by
  simpa only [fixedLeftTensor_mapForProof, fixedLeftTensor_objForExport, Category.assoc] using
    (fixedLeftTensorForProof d b).map_id x

omit [MonoidalClosed V] in
set_option backward.isDefEq.respectTransparency false in
/-- Fixing the first index retains composition on both full remaining Hom objects. -/
public theorem tensor_left_comp
    (d : EnrichedMonoidalCategoryData V I) (b x y z : I) :
    eComp V x y z ≫ (λ_ (x ⟶[V] z)).inv ≫
        (eId V b ⊗ₘ 𝟙 (x ⟶[V] z)) ≫ d.tensorMap b b x z =
      (((λ_ (x ⟶[V] y)).inv ≫
          (eId V b ⊗ₘ 𝟙 (x ⟶[V] y)) ≫ d.tensorMap b b x y) ⊗ₘ
        ((λ_ (y ⟶[V] z)).inv ≫
          (eId V b ⊗ₘ 𝟙 (y ⟶[V] z)) ≫ d.tensorMap b b y z)) ≫
      eComp V (b ⊗ x) (b ⊗ y) (b ⊗ z) := by
  simpa only [fixedLeftTensor_mapForProof, fixedLeftTensor_objForExport, Category.assoc] using
    (fixedLeftTensorForProof d b).map_comp x y z

omit [MonoidalClosed V] [BraidedCategory V] in
private theorem rightIdentityInsertion_after_mapForProof
    {X Y N : V} (f : X ⟶ Y) (e : 𝟙_ V ⟶ N) :
    (ρ_ X).inv ≫ (f ⊗ₘ e) =
      f ≫ (ρ_ Y).inv ≫ (𝟙 Y ⊗ₘ e) := by
  simpa only [id_tensorHom] using rightUnitor_inv_comp_tensorHom f e

omit [MonoidalClosed V] [BraidedCategory V] in
private theorem leftIdentityInsertion_after_mapForProof
    {X Y B : V} (f : X ⟶ Y) (e : 𝟙_ V ⟶ B) :
    (λ_ X).inv ≫ (e ⊗ₘ f) =
      f ≫ (λ_ Y).inv ≫ (e ⊗ₘ 𝟙 Y) := by
  simpa only [tensorHom_id] using leftUnitor_inv_comp_tensorHom e f

omit [MonoidalClosed V] [BraidedCategory V] in
/-- Two literal identity insertions reassociate without any braiding. -/
private theorem leftRightIdentityInsertion_reassociateForProof
    (H B N : V) (e : 𝟙_ V ⟶ B) (r : 𝟙_ V ⟶ N) :
    ((λ_ H).inv ≫ (e ⊗ₘ 𝟙 H)) ≫
        ((ρ_ (B ⊗ H)).inv ≫ (𝟙 (B ⊗ H) ⊗ₘ r)) ≫
        (α_ B H N).hom =
      ((ρ_ H).inv ≫ (𝟙 H ⊗ₘ r)) ≫
        (λ_ (H ⊗ N)).inv ≫ (e ⊗ₘ 𝟙 (H ⊗ N)) := by
  have hPadding :
      (λ_ H).inv ≫ (ρ_ ((𝟙_ V) ⊗ H)).inv ≫
          (α_ (𝟙_ V) H (𝟙_ V)).hom =
        (ρ_ H).inv ≫ (λ_ (H ⊗ (𝟙_ V))).inv := by
    monoidal
  calc
    _ = (λ_ H).inv ≫ (ρ_ ((𝟙_ V) ⊗ H)).inv ≫
        ((e ⊗ₘ 𝟙 H) ⊗ₘ r) ≫ (α_ B H N).hom := by
      simp only [Category.assoc]
      rw [rightUnitor_inv_naturality_assoc]
      rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc]
      simp only [Category.comp_id, Category.id_comp]
    _ = (λ_ H).inv ≫ (ρ_ ((𝟙_ V) ⊗ H)).inv ≫
        (α_ (𝟙_ V) H (𝟙_ V)).hom ≫
        (e ⊗ₘ (𝟙 H ⊗ₘ r)) := by
      rw [associator_naturality]
    _ = (ρ_ H).inv ≫ (λ_ (H ⊗ (𝟙_ V))).inv ≫
        (e ⊗ₘ (𝟙 H ⊗ₘ r)) := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ (e ⊗ₘ (𝟙 H ⊗ₘ r))) hPadding
    _ = _ := by
      rw [leftIdentityInsertion_after_mapForProof]
      simp only [Category.assoc]

omit [MonoidalClosed V] [BraidedCategory V] in
/-- Reassociate the two original right identities into the product identity. -/
private theorem rightRightIdentityInsertion_reassociateForProof
    (H A N : V) (e : 𝟙_ V ⟶ A) (r : 𝟙_ V ⟶ N) :
    ((ρ_ H).inv ≫ (𝟙 H ⊗ₘ e)) ≫
        ((ρ_ (H ⊗ A)).inv ≫ (𝟙 (H ⊗ A) ⊗ₘ r)) ≫
        (α_ H A N).hom =
      (ρ_ H).inv ≫
        (𝟙 H ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (e ⊗ₘ r))) := by
  have hPadding :
      (ρ_ (H ⊗ (𝟙_ V))).inv ≫
          (α_ H (𝟙_ V) (𝟙_ V)).hom =
        H ◁ (λ_ (𝟙_ V)).inv := by
    monoidal
  calc
    _ = (ρ_ H).inv ≫ (ρ_ (H ⊗ (𝟙_ V))).inv ≫
        ((𝟙 H ⊗ₘ e) ⊗ₘ r) ≫ (α_ H A N).hom := by
      simp only [Category.assoc]
      rw [rightUnitor_inv_naturality_assoc]
      rw [← tensorHom_id, tensorHom_comp_tensorHom_assoc]
      simp only [Category.comp_id, Category.id_comp]
    _ = (ρ_ H).inv ≫ (ρ_ (H ⊗ (𝟙_ V))).inv ≫
        (α_ H (𝟙_ V) (𝟙_ V)).hom ≫
        (𝟙 H ⊗ₘ (e ⊗ₘ r)) := by
      rw [associator_naturality]
    _ = (ρ_ H).inv ≫
        H ◁ (λ_ (𝟙_ V)).inv ≫ (𝟙 H ⊗ₘ (e ⊗ₘ r)) := by
      simpa only [Category.assoc] using congrArg
        (fun z : (H ⊗ (𝟙_ V)) ⟶ H ⊗ ((𝟙_ V) ⊗ (𝟙_ V)) =>
          (ρ_ H).inv ≫ z ≫ (𝟙 H ⊗ₘ (e ⊗ₘ r))) hPadding
    _ = _ := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom]
      simp only [Category.id_comp]

omit [MonoidalClosed V] in
/-- Specialize the selected full associator only at the identities of b and n. -/
private theorem associator_firstVaryingForProof
    (d : EnrichedMonoidalCategoryData V I) (b a a' n : I) :
    ((fixedLeftTensorForProof d b).map a a' ≫
        (fixedRightTensor d n).map (b ⊗ a) (b ⊗ a')) ≫
        eHomWhiskerLeft V ((b ⊗ a) ⊗ n) (α_ b a' n).hom =
      ((fixedRightTensor d n).map a a' ≫
        (fixedLeftTensorForProof d b).map (a ⊗ n) (a' ⊗ n)) ≫
        eHomWhiskerRight V (α_ b a n).hom (b ⊗ (a' ⊗ n)) := by
  let H : V := a ⟶[V] a'
  let B : V := b ⟶[V] b
  let N : V := n ⟶[V] n
  let qB : H ⟶ B ⊗ H :=
    (λ_ H).inv ≫ (eId V b ⊗ₘ 𝟙 H)
  let qN (X : V) : X ⟶ X ⊗ N :=
    (ρ_ X).inv ≫ (𝟙 X ⊗ₘ eId V n)
  let q : H ⟶ (B ⊗ H) ⊗ N := qB ≫ qN (B ⊗ H)
  let f : (B ⊗ H) ⊗ N ⟶
      (((b ⊗ a) ⊗ n) ⟶[V] ((b ⊗ a') ⊗ n)) :=
    (d.tensorMap b b a a' ▷ N) ≫
      d.tensorMap (b ⊗ a) (b ⊗ a') n n
  let g : (B ⊗ H) ⊗ N ⟶
      ((b ⊗ (a ⊗ n)) ⟶[V] (b ⊗ (a' ⊗ n))) :=
    (α_ B H N).hom ≫ B ◁ d.tensorMap a a' n n ≫
      d.tensorMap b b (a ⊗ n) (a' ⊗ n)
  have hLeftPadding :
      qN (B ⊗ H) ≫ (d.tensorMap b b a a' ▷ N) =
        d.tensorMap b b a a' ≫ qN ((b ⊗ a) ⟶[V] (b ⊗ a')) := by
    calc
      _ = (ρ_ (B ⊗ H)).inv ≫
          ((B ⊗ H) ◁ eId V n ≫ (d.tensorMap b b a a' ▷ N)) := by
        simp only [qN, id_tensorHom, Category.assoc]
      _ = (ρ_ (B ⊗ H)).inv ≫ (d.tensorMap b b a a' ⊗ₘ eId V n) :=
        congrArg
          (fun z : ((B ⊗ H) ⊗ (𝟙_ V)) ⟶
              (((b ⊗ a) ⟶[V] (b ⊗ a')) ⊗ N) =>
            (ρ_ (B ⊗ H)).inv ≫ z)
          (tensorHom_def' (d.tensorMap b b a a') (eId V n)).symm
      _ = _ := by
        simpa only [qN] using rightIdentityInsertion_after_mapForProof
          (d.tensorMap b b a a') (eId V n)
  have hLeft :
      q ≫ f = (fixedLeftTensorForProof d b).map a a' ≫
        (fixedRightTensor d n).map (b ⊗ a) (b ⊗ a') := by
    calc
      _ = qB ≫ (qN (B ⊗ H) ≫ (d.tensorMap b b a a' ▷ N)) ≫
          d.tensorMap (b ⊗ a) (b ⊗ a') n n := by
        simp only [q, f, Category.assoc]
      _ = qB ≫ d.tensorMap b b a a' ≫
          qN ((b ⊗ a) ⟶[V] (b ⊗ a')) ≫
          d.tensorMap (b ⊗ a) (b ⊗ a') n n := by
        rw [hLeftPadding]
        simp only [Category.assoc]
      _ = _ := by
        have hB : (fixedLeftTensorForProof d b).map a a' =
            qB ≫ d.tensorMap b b a a' := by
          exact (fixedLeftTensor_mapForProof d b a a').trans
            (Category.assoc (λ_ H).inv (eId V b ⊗ₘ 𝟙 H)
              (d.tensorMap b b a a')).symm
        have hN : (fixedRightTensor d n).map (b ⊗ a) (b ⊗ a') =
            qN ((b ⊗ a) ⟶[V] (b ⊗ a')) ≫
              d.tensorMap (b ⊗ a) (b ⊗ a') n n := by
          exact (fixedRightTensor_map d n (b ⊗ a) (b ⊗ a')).trans
            (Category.assoc (ρ_ ((b ⊗ a) ⟶[V] (b ⊗ a'))).inv
              (𝟙 ((b ⊗ a) ⟶[V] (b ⊗ a')) ⊗ₘ eId V n)
              (d.tensorMap (b ⊗ a) (b ⊗ a') n n)).symm
        have hMaps := congrArg₂
          (fun (s : H ⟶ ((b ⊗ a) ⟶[V] (b ⊗ a')))
              (t : ((b ⊗ a) ⟶[V] (b ⊗ a')) ⟶
                (((b ⊗ a) ⊗ n) ⟶[V] ((b ⊗ a') ⊗ n))) => s ≫ t) hB hN
        exact (Category.assoc qB (d.tensorMap b b a a')
          (qN ((b ⊗ a) ⟶[V] (b ⊗ a')) ≫
            d.tensorMap (b ⊗ a) (b ⊗ a') n n)).symm.trans hMaps.symm
  have hReassociate :
      q ≫ (α_ B H N).hom =
        qN H ≫ (λ_ (H ⊗ N)).inv ≫
          (eId V b ⊗ₘ 𝟙 (H ⊗ N)) := by
    simpa only [q, qB, qN, H, B, N, Category.assoc] using
      leftRightIdentityInsertion_reassociateForProof
        H B N (eId V b) (eId V n)
  have hRightPadding :
      (λ_ (H ⊗ N)).inv ≫ (eId V b ⊗ₘ 𝟙 (H ⊗ N)) ≫
          B ◁ d.tensorMap a a' n n =
        d.tensorMap a a' n n ≫
          (λ_ ((a ⊗ n) ⟶[V] (a' ⊗ n))).inv ≫
          (eId V b ⊗ₘ 𝟙 ((a ⊗ n) ⟶[V] (a' ⊗ n))) := by
    calc
      _ = (λ_ (H ⊗ N)).inv ≫
          (eId V b ▷ (H ⊗ N) ≫ B ◁ d.tensorMap a a' n n) := by
        simp only [tensorHom_id]
      _ = (λ_ (H ⊗ N)).inv ≫ (eId V b ⊗ₘ d.tensorMap a a' n n) :=
        congrArg
          (fun z : ((𝟙_ V) ⊗ (H ⊗ N)) ⟶
              (B ⊗ ((a ⊗ n) ⟶[V] (a' ⊗ n))) =>
            (λ_ (H ⊗ N)).inv ≫ z)
          (tensorHom_def (eId V b) (d.tensorMap a a' n n)).symm
      _ = _ := leftIdentityInsertion_after_mapForProof
        (d.tensorMap a a' n n) (eId V b)
  have hRight :
      q ≫ g = (fixedRightTensor d n).map a a' ≫
        (fixedLeftTensorForProof d b).map (a ⊗ n) (a' ⊗ n) := by
    calc
      _ = (q ≫ (α_ B H N).hom) ≫
          B ◁ d.tensorMap a a' n n ≫
          d.tensorMap b b (a ⊗ n) (a' ⊗ n) := by
        simp only [g, Category.assoc]
      _ = qN H ≫
          ((λ_ (H ⊗ N)).inv ≫ (eId V b ⊗ₘ 𝟙 (H ⊗ N)) ≫
            B ◁ d.tensorMap a a' n n) ≫
          d.tensorMap b b (a ⊗ n) (a' ⊗ n) := by
        rw [hReassociate]
        simp only [Category.assoc]
      _ = qN H ≫
          (d.tensorMap a a' n n ≫
            (λ_ ((a ⊗ n) ⟶[V] (a' ⊗ n))).inv ≫
            (eId V b ⊗ₘ 𝟙 ((a ⊗ n) ⟶[V] (a' ⊗ n)))) ≫
          d.tensorMap b b (a ⊗ n) (a' ⊗ n) :=
        congrArg
          (fun z : (H ⊗ N) ⟶
              (B ⊗ ((a ⊗ n) ⟶[V] (a' ⊗ n))) =>
            qN H ≫ z ≫ d.tensorMap b b (a ⊗ n) (a' ⊗ n)) hRightPadding
      _ = _ := by
        let Y : V := (a ⊗ n) ⟶[V] (a' ⊗ n)
        let qBY : Y ⟶ B ⊗ Y := (λ_ Y).inv ≫ (eId V b ⊗ₘ 𝟙 Y)
        have hN : (fixedRightTensor d n).map a a' =
            qN H ≫ d.tensorMap a a' n n := by
          exact (fixedRightTensor_map d n a a').trans
            (Category.assoc (ρ_ H).inv (𝟙 H ⊗ₘ eId V n)
              (d.tensorMap a a' n n)).symm
        have hB : (fixedLeftTensorForProof d b).map (a ⊗ n) (a' ⊗ n) =
            qBY ≫ d.tensorMap b b (a ⊗ n) (a' ⊗ n) := by
          exact (fixedLeftTensor_mapForProof d b (a ⊗ n) (a' ⊗ n)).trans
            (Category.assoc (λ_ Y).inv (eId V b ⊗ₘ 𝟙 Y)
              (d.tensorMap b b (a ⊗ n) (a' ⊗ n))).symm
        have hMaps := congrArg₂
          (fun (s : H ⟶ Y) (t : Y ⟶
              ((b ⊗ (a ⊗ n)) ⟶[V] (b ⊗ (a' ⊗ n)))) => s ≫ t) hN hB
        have hAssoc := congrArg
          (fun z : (H ⊗ N) ⟶
              ((b ⊗ (a ⊗ n)) ⟶[V] (b ⊗ (a' ⊗ n))) => qN H ≫ z)
          (Category.assoc (d.tensorMap a a' n n) qBY
            (d.tensorMap b b (a ⊗ n) (a' ⊗ n)))
        exact hAssoc.trans ((Category.assoc (qN H) (d.tensorMap a a' n n)
          (qBY ≫ d.tensorMap b b (a ⊗ n) (a' ⊗ n))).symm.trans hMaps.symm)
  have hWhole := congrArg
    (fun z => q ≫ z)
    (associator_full_hom_whisker d b b a a' n n)
  have hPre :
      (q ≫ f) ≫
        eHomWhiskerLeft V ((b ⊗ a) ⊗ n) (α_ b a' n).hom =
      (q ≫ g) ≫
        eHomWhiskerRight V (α_ b a n).hom (b ⊗ (a' ⊗ n)) := by
    simpa only [f, g, H, B, N, Category.assoc] using hWhole
  rw [hLeft, hRight] at hPre
  exact hPre

omit [MonoidalClosed V] in
/-- Specialize the same full associator at the identities of a and n. -/
private theorem associator_secondVaryingForProof
    (d : EnrichedMonoidalCategoryData V I) (b b' a n : I) :
    ((fixedRightTensor d a).map b b' ≫
        (fixedRightTensor d n).map (b ⊗ a) (b' ⊗ a)) ≫
        eHomWhiskerLeft V ((b ⊗ a) ⊗ n) (α_ b' a n).hom =
      (fixedRightTensor d (a ⊗ n)).map b b' ≫
        eHomWhiskerRight V (α_ b a n).hom (b' ⊗ (a ⊗ n)) := by
  let H : V := b ⟶[V] b'
  let A : V := a ⟶[V] a
  let N : V := n ⟶[V] n
  let qA : H ⟶ H ⊗ A :=
    (ρ_ H).inv ≫ (𝟙 H ⊗ₘ eId V a)
  let qN (X : V) : X ⟶ X ⊗ N :=
    (ρ_ X).inv ≫ (𝟙 X ⊗ₘ eId V n)
  let q : H ⟶ (H ⊗ A) ⊗ N := qA ≫ qN (H ⊗ A)
  let f : (H ⊗ A) ⊗ N ⟶
      (((b ⊗ a) ⊗ n) ⟶[V] ((b' ⊗ a) ⊗ n)) :=
    (d.tensorMap b b' a a ▷ N) ≫
      d.tensorMap (b ⊗ a) (b' ⊗ a) n n
  let g : (H ⊗ A) ⊗ N ⟶
      ((b ⊗ (a ⊗ n)) ⟶[V] (b' ⊗ (a ⊗ n))) :=
    (α_ H A N).hom ≫ H ◁ d.tensorMap a a n n ≫
      d.tensorMap b b' (a ⊗ n) (a ⊗ n)
  have hLeftPadding :
      qN (H ⊗ A) ≫ (d.tensorMap b b' a a ▷ N) =
        d.tensorMap b b' a a ≫ qN ((b ⊗ a) ⟶[V] (b' ⊗ a)) := by
    calc
      _ = (ρ_ (H ⊗ A)).inv ≫
          ((H ⊗ A) ◁ eId V n ≫ (d.tensorMap b b' a a ▷ N)) := by
        simp only [qN, id_tensorHom, Category.assoc]
      _ = (ρ_ (H ⊗ A)).inv ≫ (d.tensorMap b b' a a ⊗ₘ eId V n) :=
        congrArg
          (fun z : ((H ⊗ A) ⊗ (𝟙_ V)) ⟶
              (((b ⊗ a) ⟶[V] (b' ⊗ a)) ⊗ N) =>
            (ρ_ (H ⊗ A)).inv ≫ z)
          (tensorHom_def' (d.tensorMap b b' a a) (eId V n)).symm
      _ = _ := by
        simpa only [qN] using rightIdentityInsertion_after_mapForProof
          (d.tensorMap b b' a a) (eId V n)
  have hLeft :
      q ≫ f = (fixedRightTensor d a).map b b' ≫
        (fixedRightTensor d n).map (b ⊗ a) (b' ⊗ a) := by
    calc
      _ = qA ≫ (qN (H ⊗ A) ≫ (d.tensorMap b b' a a ▷ N)) ≫
          d.tensorMap (b ⊗ a) (b' ⊗ a) n n := by
        simp only [q, f, Category.assoc]
      _ = qA ≫ d.tensorMap b b' a a ≫
          qN ((b ⊗ a) ⟶[V] (b' ⊗ a)) ≫
          d.tensorMap (b ⊗ a) (b' ⊗ a) n n := by
        rw [hLeftPadding]
        simp only [Category.assoc]
      _ = _ := by
        have hA : (fixedRightTensor d a).map b b' =
            qA ≫ d.tensorMap b b' a a := by
          exact (fixedRightTensor_map d a b b').trans
            (Category.assoc (ρ_ H).inv (𝟙 H ⊗ₘ eId V a)
              (d.tensorMap b b' a a)).symm
        have hN : (fixedRightTensor d n).map (b ⊗ a) (b' ⊗ a) =
            qN ((b ⊗ a) ⟶[V] (b' ⊗ a)) ≫
              d.tensorMap (b ⊗ a) (b' ⊗ a) n n := by
          exact (fixedRightTensor_map d n (b ⊗ a) (b' ⊗ a)).trans
            (Category.assoc (ρ_ ((b ⊗ a) ⟶[V] (b' ⊗ a))).inv
              (𝟙 ((b ⊗ a) ⟶[V] (b' ⊗ a)) ⊗ₘ eId V n)
              (d.tensorMap (b ⊗ a) (b' ⊗ a) n n)).symm
        have hMaps := congrArg₂
          (fun (s : H ⟶ ((b ⊗ a) ⟶[V] (b' ⊗ a)))
              (t : ((b ⊗ a) ⟶[V] (b' ⊗ a)) ⟶
                (((b ⊗ a) ⊗ n) ⟶[V] ((b' ⊗ a) ⊗ n))) => s ≫ t) hA hN
        exact (Category.assoc qA (d.tensorMap b b' a a)
          (qN ((b ⊗ a) ⟶[V] (b' ⊗ a)) ≫
            d.tensorMap (b ⊗ a) (b' ⊗ a) n n)).symm.trans hMaps.symm
  have hReassociate :
      q ≫ (α_ H A N).hom =
        (ρ_ H).inv ≫
          (𝟙 H ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (eId V a ⊗ₘ eId V n))) := by
    simpa only [q, qA, qN, H, A, N, Category.assoc] using
      rightRightIdentityInsertion_reassociateForProof
        H A N (eId V a) (eId V n)
  let j : (𝟙_ V) ⟶ A ⊗ N :=
    (λ_ (𝟙_ V)).inv ≫ (eId V a ⊗ₘ eId V n)
  have hIdentity : j ≫ d.tensorMap a a n n = eId V (a ⊗ n) := by
    simpa only [j, Enriched.prodEId] using d.tensorMap_id a n
  have hRight :
      q ≫ g = (fixedRightTensor d (a ⊗ n)).map b b' := by
    have hMap : (fixedRightTensor d (a ⊗ n)).map b b' =
        (ρ_ H).inv ≫ (𝟙 H ⊗ₘ eId V (a ⊗ n)) ≫
          d.tensorMap b b' (a ⊗ n) (a ⊗ n) :=
      fixedRightTensor_map d (a ⊗ n) b b'
    rw [hMap]
    calc
      q ≫ g = (q ≫ (α_ H A N).hom) ≫
          H ◁ d.tensorMap a a n n ≫
          d.tensorMap b b' (a ⊗ n) (a ⊗ n) := by
        simp only [g, Category.assoc]
      _ = ((ρ_ H).inv ≫ (𝟙 H ⊗ₘ j)) ≫
          H ◁ d.tensorMap a a n n ≫
          d.tensorMap b b' (a ⊗ n) (a ⊗ n) := by
        exact congrArg
          (fun z : H ⟶ H ⊗ (A ⊗ N) =>
            z ≫ H ◁ d.tensorMap a a n n ≫
              d.tensorMap b b' (a ⊗ n) (a ⊗ n)) hReassociate
      _ = (ρ_ H).inv ≫ (𝟙 H ⊗ₘ (j ≫ d.tensorMap a a n n)) ≫
          d.tensorMap b b' (a ⊗ n) (a ⊗ n) := by
        simpa only [Category.assoc] using congrArg
          (fun z : (H ⊗ (𝟙_ V)) ⟶
              (H ⊗ ((a ⊗ n) ⟶[V] (a ⊗ n))) =>
            (ρ_ H).inv ≫ z ≫ d.tensorMap b b' (a ⊗ n) (a ⊗ n))
          (tensorHom_comp_whiskerLeft (𝟙 H) j (d.tensorMap a a n n))
      _ = (ρ_ H).inv ≫ (𝟙 H ⊗ₘ eId V (a ⊗ n)) ≫
          d.tensorMap b b' (a ⊗ n) (a ⊗ n) :=
        congrArg
          (fun z : (𝟙_ V) ⟶ ((a ⊗ n) ⟶[V] (a ⊗ n)) =>
            (ρ_ H).inv ≫ (𝟙 H ⊗ₘ z) ≫
              d.tensorMap b b' (a ⊗ n) (a ⊗ n)) hIdentity
  have hWhole := congrArg
    (fun z => q ≫ z)
    (associator_full_hom_whisker d b b' a a n n)
  have hPre :
      (q ≫ f) ≫
        eHomWhiskerLeft V ((b ⊗ a) ⊗ n) (α_ b' a n).hom =
      (q ≫ g) ≫
        eHomWhiskerRight V (α_ b a n).hom (b' ⊗ (a ⊗ n)) := by
    simpa only [f, g, H, A, N, Category.assoc] using hWhole
  rw [hLeft, hRight] at hPre
  exact hPre

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The inverse middle crossing cancels exactly the positive full hexagon. -/
private theorem inverseMiddleWeightReorder_hexagonForProof (B H Z : V) :
    ((α_ B H Z).hom ≫ B ◁ (β_ Z H).inv ≫ (α_ B Z H).inv) ≫
        (β_ (B ⊗ Z) H).hom =
      (β_ B H).hom ▷ Z ≫ (α_ H B Z).hom := by
  rw [braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The entire enriched composition satisfies the A weight exchange.
The negative Z/H crossing is retained before the final positive weight action. -/
private theorem enrichedComposition_firstWeightExchangeForProof (x x' y z : I) :
    ((β_ (x' ⟶[V] y) (x ⟶[V] x')).hom ▷ (y ⟶[V] z)) ≫
        (eComp V x x' y ▷ (y ⟶[V] z)) ≫ eComp V x y z =
      ((α_ (x' ⟶[V] y) (x ⟶[V] x') (y ⟶[V] z)).hom ≫
        (x' ⟶[V] y) ◁ (β_ (y ⟶[V] z) (x ⟶[V] x')).inv ≫
        (α_ (x' ⟶[V] y) (y ⟶[V] z) (x ⟶[V] x')).inv) ≫
        (eComp V x' y z ▷ (x ⟶[V] x')) ≫
        (β_ (x' ⟶[V] z) (x ⟶[V] x')).hom ≫ eComp V x x' z := by
  let B : V := x' ⟶[V] y
  let H : V := x ⟶[V] x'
  let Z : V := y ⟶[V] z
  let s : (B ⊗ H) ⊗ Z ⟶ (B ⊗ Z) ⊗ H :=
    (α_ B H Z).hom ≫ B ◁ (β_ Z H).inv ≫ (α_ B Z H).inv
  have hHex : s ≫ (β_ (B ⊗ Z) H).hom =
      (β_ B H).hom ▷ Z ≫ (α_ H B Z).hom :=
    inverseMiddleWeightReorder_hexagonForProof B H Z
  have hNaturality :
      (eComp V x' y z ▷ H) ≫ (β_ (x' ⟶[V] z) H).hom =
        (β_ (B ⊗ Z) H).hom ≫ H ◁ eComp V x' y z := by
    simpa only [B, H, Z, tensorHom_id, id_tensorHom] using
      (braiding_naturality (eComp V x' y z) (𝟙 H))
  symm
  calc
    _ = s ≫ (β_ (B ⊗ Z) H).hom ≫
        H ◁ eComp V x' y z ≫ eComp V x x' z := by
      simpa only [s, B, H, Z, Category.assoc] using congrArg
        (fun k : (B ⊗ Z) ⊗ H ⟶ H ⊗ (x' ⟶[V] z) =>
          s ≫ k ≫ eComp V x x' z) hNaturality
    _ = (β_ B H).hom ▷ Z ≫ (α_ H B Z).hom ≫
        H ◁ eComp V x' y z ≫ eComp V x x' z := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ H ◁ eComp V x' y z ≫ eComp V x x' z) hHex
    _ = _ := by
      simpa only [B, H, Z, Category.assoc] using congrArg
        (fun f => ((β_ B H).hom ▷ Z) ≫ f)
        (e_assoc' V x x' y z)


omit [MonoidalClosed V] [MonoidalCategory I] in
private abbrev firstWeightReorderForProof (B H Z : V) :
    (B ⊗ H) ⊗ Z ⟶ (B ⊗ Z) ⊗ H :=
  (α_ B H Z).hom ≫ B ◁ (β_ Z H).inv ≫ (α_ B Z H).inv

omit [MonoidalClosed V] [MonoidalCategory I] in
private theorem firstWeightReorder_naturalityForProof
    {B H Z B' H' Z' : V} (g : B ⟶ B') (p : H ⟶ H') (h : Z ⟶ Z') :
    ((g ⊗ₘ p) ⊗ₘ h) ≫ firstWeightReorderForProof B' H' Z' =
      firstWeightReorderForProof B H Z ≫ ((g ⊗ₘ h) ⊗ₘ p) := by
  have hMiddle :
      (g ⊗ₘ (p ⊗ₘ h)) ≫ B' ◁ (β_ Z' H').inv =
        B ◁ (β_ Z H).inv ≫ (g ⊗ₘ (h ⊗ₘ p)) := by
    calc
      _ = g ⊗ₘ ((p ⊗ₘ h) ≫ (β_ Z' H').inv) := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
      _ = g ⊗ₘ ((β_ Z H).inv ≫ (h ⊗ₘ p)) := by
        rw [braiding_inv_naturality p h]
      _ = _ := by
        rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  calc
    _ = (α_ B H Z).hom ≫ (g ⊗ₘ (p ⊗ₘ h)) ≫
        B' ◁ (β_ Z' H').inv ≫ (α_ B' Z' H').inv := by
      dsimp only [firstWeightReorderForProof]
      rw [associator_naturality_assoc]
    _ = (α_ B H Z).hom ≫ B ◁ (β_ Z H).inv ≫
        (g ⊗ₘ (h ⊗ₘ p)) ≫ (α_ B' Z' H').inv := by
      simpa only [Category.assoc] using congrArg
        (fun k : B ⊗ (H ⊗ Z) ⟶ B' ⊗ (Z' ⊗ H') =>
          (α_ B H Z).hom ≫ k ≫ (α_ B' Z' H').inv) hMiddle
    _ = _ := by
      rw [associator_inv_naturality]
      simp only [firstWeightReorderForProof, Category.assoc]

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- Arbitrary full parameter maps may be substituted into the first weight exchange. -/
private theorem enrichedComposition_firstWeightExchange_mappedForProof
    (x x' y z : I) {B H Z : V}
    (g : B ⟶ (x' ⟶[V] y)) (p : H ⟶ (x ⟶[V] x'))
    (h : Z ⟶ (y ⟶[V] z)) :
    ((((g ⊗ₘ p) ≫ (β_ (x' ⟶[V] y) (x ⟶[V] x')).hom ≫
        eComp V x x' y) ⊗ₘ h) ≫ eComp V x y z) =
      firstWeightReorderForProof B H Z ≫
        (((g ⊗ₘ h) ≫ eComp V x' y z) ⊗ₘ p) ≫
        (β_ (x' ⟶[V] z) (x ⟶[V] x')).hom ≫ eComp V x x' z := by
  let input := (g ⊗ₘ p) ⊗ₘ h
  have hReorder :
      input ≫ firstWeightReorderForProof
          (x' ⟶[V] y) (x ⟶[V] x') (y ⟶[V] z) =
        firstWeightReorderForProof B H Z ≫ ((g ⊗ₘ h) ⊗ₘ p) :=
    firstWeightReorder_naturalityForProof g p h
  calc
    _ = input ≫
        ((β_ (x' ⟶[V] y) (x ⟶[V] x')).hom ▷ (y ⟶[V] z)) ≫
        (eComp V x x' y ▷ (y ⟶[V] z)) ≫ eComp V x y z := by
      simpa only [input, tensorHom_id, Category.comp_id,
        comp_whiskerRight, Category.assoc] using congrArg
        (fun k : (B ⊗ H) ⊗ Z ⟶ (x ⟶[V] y) ⊗ (y ⟶[V] z) =>
          k ≫ eComp V x y z)
        (tensorHom_comp_tensorHom (g ⊗ₘ p) h
          ((β_ (x' ⟶[V] y) (x ⟶[V] x')).hom ≫ eComp V x x' y)
          (𝟙 (y ⟶[V] z))).symm
    _ = input ≫
        firstWeightReorderForProof
          (x' ⟶[V] y) (x ⟶[V] x') (y ⟶[V] z) ≫
        (eComp V x' y z ▷ (x ⟶[V] x')) ≫
        (β_ (x' ⟶[V] z) (x ⟶[V] x')).hom ≫ eComp V x x' z := by
      simpa only [firstWeightReorderForProof, Category.assoc] using congrArg
        (fun f => input ≫ f)
        (enrichedComposition_firstWeightExchangeForProof (V := V) x x' y z)
    _ = firstWeightReorderForProof B H Z ≫ ((g ⊗ₘ h) ⊗ₘ p) ≫
        (eComp V x' y z ▷ (x ⟶[V] x')) ≫
        (β_ (x' ⟶[V] z) (x ⟶[V] x')).hom ≫ eComp V x x' z := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ (eComp V x' y z ▷ (x ⟶[V] x')) ≫
          (β_ (x' ⟶[V] z) (x ⟶[V] x')).hom ≫ eComp V x x' z) hReorder
    _ = _ := by
      simpa only [tensorHom_id, Category.comp_id, Category.assoc] using congrArg
        (fun k : (B ⊗ Z) ⊗ H ⟶ (x' ⟶[V] z) ⊗ (x ⟶[V] x') =>
          firstWeightReorderForProof B H Z ≫ k ≫
            (β_ (x' ⟶[V] z) (x ⟶[V] x')).hom ≫ eComp V x x' z)
        (tensorHom_comp_tensorHom (g ⊗ₘ h) p
          (eComp V x' y z) (𝟙 (x ⟶[V] x')))

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- Enriched functoriality supplies the entire first index-weight exchange. -/
private theorem enrichedFunctor_firstWeightExchangeForProof
    (F : EnrichedFunctor V I I) (x x' y z : I) {H : V}
    (p : H ⟶ (x ⟶[V] x')) :
    ((((x' ⟶[V] y) ◁ p ≫
        (β_ (x' ⟶[V] y) (x ⟶[V] x')).hom ≫
        eComp V x x' y ≫ F.map x y) ⊗ₘ 𝟙 (F.obj y ⟶[V] z)) ≫
        eComp V (F.obj x) (F.obj y) z) =
      firstWeightReorderForProof (x' ⟶[V] y) H (F.obj y ⟶[V] z) ≫
        (((F.map x' y ⊗ₘ 𝟙 (F.obj y ⟶[V] z)) ≫
            eComp V (F.obj x') (F.obj y) z) ⊗ₘ (p ≫ F.map x x')) ≫
        (β_ (F.obj x' ⟶[V] z) (F.obj x ⟶[V] F.obj x')).hom ≫
        eComp V (F.obj x) (F.obj x') z := by
  have hFront :
      (x' ⟶[V] y) ◁ p ≫
          (β_ (x' ⟶[V] y) (x ⟶[V] x')).hom ≫
          eComp V x x' y ≫ F.map x y =
        (F.map x' y ⊗ₘ (p ≫ F.map x x')) ≫
          (β_ (F.obj x' ⟶[V] F.obj y) (F.obj x ⟶[V] F.obj x')).hom ≫
          eComp V (F.obj x) (F.obj x') (F.obj y) := by
    calc
      _ = (x' ⟶[V] y) ◁ p ≫
          (β_ (x' ⟶[V] y) (x ⟶[V] x')).hom ≫
          (F.map x x' ⊗ₘ F.map x' y) ≫
          eComp V (F.obj x) (F.obj x') (F.obj y) := by
        rw [F.map_comp]
      _ = (x' ⟶[V] y) ◁ p ≫
          (F.map x' y ⊗ₘ F.map x x') ≫
          (β_ (F.obj x' ⟶[V] F.obj y) (F.obj x ⟶[V] F.obj x')).hom ≫
          eComp V (F.obj x) (F.obj x') (F.obj y) := by
        rw [← braiding_naturality_assoc]
      _ = _ := by
        simpa only [id_tensorHom, Category.id_comp, Category.assoc] using congrArg
          (fun k : (x' ⟶[V] y) ⊗ H ⟶
              (F.obj x' ⟶[V] F.obj y) ⊗ (F.obj x ⟶[V] F.obj x') =>
            k ≫ (β_ (F.obj x' ⟶[V] F.obj y) (F.obj x ⟶[V] F.obj x')).hom ≫
              eComp V (F.obj x) (F.obj x') (F.obj y))
          (tensorHom_comp_tensorHom (𝟙 (x' ⟶[V] y)) p
            (F.map x' y) (F.map x x'))
  rw [hFront]
  exact enrichedComposition_firstWeightExchange_mappedForProof
    (F.obj x) (F.obj x') (F.obj y) z (F.map x' y) (p ≫ F.map x x')
    (𝟙 (F.obj y ⟶[V] z))

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- Transport the complete weight action through an actual source isomorphism square.
The naturality certificate is derived from the selected full associator at each use. -/
private theorem isoWeightAction_transportForProof
    (w w' x x' z : I) (u : w ≅ x) (v : w' ≅ x')
    {B H : V} (g : B ⟶ (x' ⟶[V] z)) (p : H ⟶ (x ⟶[V] x'))
    (q : H ⟶ (w ⟶[V] w'))
    (hNatural : q ≫ eHomWhiskerLeft V w v.hom =
      p ≫ eHomWhiskerRight V u.hom x') :
    (((g ⊗ₘ p) ≫ (β_ (x' ⟶[V] z) (x ⟶[V] x')).hom ≫
        eComp V x x' z) ≫ eHomWhiskerRight V u.hom z) =
      ((g ≫ eHomWhiskerRight V v.hom z) ⊗ₘ q) ≫
        (β_ (w' ⟶[V] z) (w ⟶[V] w')).hom ≫ eComp V w w' z := by
  have hMiddle := eComp_middle_iso_transportForProof (V := V) w w' x' z v
  calc
    _ = (β_ B H).hom ≫ (p ⊗ₘ g) ≫
        eComp V x x' z ≫ eHomWhiskerRight V u.hom z := by
      rw [braiding_naturality_assoc]
      simp only [Category.assoc]
    _ = (β_ B H).hom ≫
        ((p ≫ eHomWhiskerRight V u.hom x') ⊗ₘ g) ≫
        eComp V w x' z := by
      rw [eComp_eHomWhiskerRight]
      simpa only [tensorHom_id, Category.comp_id, Category.assoc] using congrArg
        (fun k : H ⊗ B ⟶ (w ⟶[V] x') ⊗ (x' ⟶[V] z) =>
          (β_ B H).hom ≫ k ≫ eComp V w x' z)
        (tensorHom_comp_tensorHom p g
          (eHomWhiskerRight V u.hom x') (𝟙 (x' ⟶[V] z)))
    _ = (β_ B H).hom ≫
        ((q ≫ eHomWhiskerLeft V w v.hom) ⊗ₘ g) ≫
        eComp V w x' z := by
      rw [← hNatural]
    _ = (β_ B H).hom ≫ (q ⊗ₘ g) ≫
        (eHomWhiskerLeft V w v.hom ▷ (x' ⟶[V] z)) ≫
        eComp V w x' z := by
      simpa only [tensorHom_id, Category.comp_id, Category.assoc] using congrArg
        (fun k : H ⊗ B ⟶ (w ⟶[V] x') ⊗ (x' ⟶[V] z) =>
          (β_ B H).hom ≫ k ≫ eComp V w x' z)
        (tensorHom_comp_tensorHom q g
          (eHomWhiskerLeft V w v.hom) (𝟙 (x' ⟶[V] z))).symm
    _ = (β_ B H).hom ≫ (q ⊗ₘ g) ≫
        (w ⟶[V] w') ◁ eHomWhiskerRight V v.hom z ≫
        eComp V w w' z := by
      rw [hMiddle]
    _ = (β_ B H).hom ≫
        (q ⊗ₘ (g ≫ eHomWhiskerRight V v.hom z)) ≫
        eComp V w w' z := by
      simpa only [id_tensorHom, Category.comp_id, Category.assoc] using congrArg
        (fun k : H ⊗ B ⟶ (w ⟶[V] w') ⊗ (w' ⟶[V] z) =>
          (β_ B H).hom ≫ k ≫ eComp V w w' z)
        (tensorHom_comp_tensorHom q g
          (𝟙 (w ⟶[V] w')) (eHomWhiskerRight V v.hom z))
    _ = _ := by
      rw [← braiding_naturality_assoc]

omit [MonoidalClosed V] [MonoidalCategory I] in
private theorem secondWeightReorder_hexagonForProof (W Z H : V) :
    W ◁ (β_ Z H).hom ≫ (α_ W H Z).inv ≫
        (β_ W H).hom ▷ Z ≫ (α_ H W Z).hom =
      (α_ W Z H).inv ≫ (β_ (W ⊗ Z) H).hom := by
  rw [braiding_tensor_left_hom]
  simp only [Iso.inv_hom_id_assoc]

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The full second weight exchange follows from the actual tensor exchange square. -/
private theorem enrichedComposition_secondWeightExchangeForProof
    (x y y' x' z : I) {W H : V}
    (g : W ⟶ (x ⟶[V] y)) (h : H ⟶ (y ⟶[V] y'))
    (r : H ⟶ (x ⟶[V] x')) (g' : W ⟶ (x' ⟶[V] y'))
    (hSquare : (g ⊗ₘ h) ≫ eComp V x y y' =
      (β_ W H).hom ≫ (r ⊗ₘ g') ≫ eComp V x x' y') :
    (g ⊗ₘ
        ((y' ⟶[V] z) ◁ h ≫ (β_ (y' ⟶[V] z) (y ⟶[V] y')).hom ≫
          eComp V y y' z)) ≫ eComp V x y z =
      (α_ W (y' ⟶[V] z) H).inv ≫
        (((g' ⊗ₘ 𝟙 (y' ⟶[V] z)) ≫ eComp V x' y' z) ⊗ₘ r) ≫
        (β_ (x' ⟶[V] z) (x ⟶[V] x')).hom ≫ eComp V x x' z := by
  let Z : V := y' ⟶[V] z
  let t : W ⊗ Z ⟶ (x' ⟶[V] z) :=
    (g' ⊗ₘ 𝟙 Z) ≫ eComp V x' y' z
  have hAction :
      Z ◁ h ≫ (β_ Z (y ⟶[V] y')).hom =
        (β_ Z H).hom ≫ (h ⊗ₘ 𝟙 Z) := by
    simpa only [id_tensorHom] using
      (braiding_naturality (𝟙 Z) h)
  have hActionPost :
      Z ◁ h ≫ (β_ Z (y ⟶[V] y')).hom ≫ eComp V y y' z =
        (β_ Z H).hom ≫ (h ⊗ₘ 𝟙 Z) ≫ eComp V y y' z := by
    simpa only [Category.assoc] using congrArg
      (fun k : Z ⊗ H ⟶ (y ⟶[V] y') ⊗ Z =>
        k ≫ eComp V y y' z) hAction
  have hTensorPre :
      (W ◁ (β_ Z H).hom) ≫ (g ⊗ₘ (h ⊗ₘ 𝟙 Z)) =
        g ⊗ₘ ((β_ Z H).hom ≫ (h ⊗ₘ 𝟙 Z)) := by
    simpa only [id_tensorHom, Category.id_comp] using
      (tensorHom_comp_tensorHom (𝟙 W) (β_ Z H).hom g (h ⊗ₘ 𝟙 Z))
  have hTensorPost :
      (g ⊗ₘ ((β_ Z H).hom ≫ (h ⊗ₘ 𝟙 Z))) ≫
          (x ⟶[V] y) ◁ eComp V y y' z =
        g ⊗ₘ ((β_ Z H).hom ≫ (h ⊗ₘ 𝟙 Z) ≫ eComp V y y' z) := by
    simpa only [id_tensorHom, Category.comp_id, Category.assoc] using
      (tensorHom_comp_tensorHom g ((β_ Z H).hom ≫ (h ⊗ₘ 𝟙 Z))
        (𝟙 (x ⟶[V] y)) (eComp V y y' z))
  have hTensorAction :
      g ⊗ₘ (Z ◁ h ≫ (β_ Z (y ⟶[V] y')).hom ≫ eComp V y y' z) =
        (W ◁ (β_ Z H).hom) ≫
          (g ⊗ₘ (h ⊗ₘ 𝟙 Z)) ≫ (x ⟶[V] y) ◁ eComp V y y' z := by
    calc
      _ = g ⊗ₘ ((β_ Z H).hom ≫ (h ⊗ₘ 𝟙 Z) ≫ eComp V y y' z) :=
        congrArg (fun k : Z ⊗ H ⟶ (y ⟶[V] z) => g ⊗ₘ k) hActionPost
      _ = (g ⊗ₘ ((β_ Z H).hom ≫ (h ⊗ₘ 𝟙 Z))) ≫
          (x ⟶[V] y) ◁ eComp V y y' z := hTensorPost.symm
      _ = (W ◁ (β_ Z H).hom) ≫
          (g ⊗ₘ (h ⊗ₘ 𝟙 Z)) ≫ (x ⟶[V] y) ◁ eComp V y y' z := by
        simpa only [Category.assoc] using congrArg
          (fun k : W ⊗ (Z ⊗ H) ⟶ (x ⟶[V] y) ⊗ ((y ⟶[V] y') ⊗ Z) =>
            k ≫ (x ⟶[V] y) ◁ eComp V y y' z) hTensorPre.symm
  have hAssoc :
      ((g ⊗ₘ (h ⊗ₘ 𝟙 Z)) ≫
          (x ⟶[V] y) ◁ eComp V y y' z) ≫ eComp V x y z =
        (α_ W H Z).inv ≫
          (((g ⊗ₘ h) ≫ eComp V x y y') ▷ Z) ≫ eComp V x y' z := by
    calc
      _ = (g ⊗ₘ (h ⊗ₘ 𝟙 Z)) ≫
          (α_ (x ⟶[V] y) (y ⟶[V] y') Z).inv ≫
          (eComp V x y y' ▷ Z) ≫ eComp V x y' z := by
        simpa only [Category.assoc] using congrArg
          (fun k : (x ⟶[V] y) ⊗ ((y ⟶[V] y') ⊗ Z) ⟶ (x ⟶[V] z) =>
            (g ⊗ₘ (h ⊗ₘ 𝟙 Z)) ≫ k) (e_assoc V x y y' z).symm
      _ = (α_ W H Z).inv ≫ ((g ⊗ₘ h) ▷ Z) ≫
          (eComp V x y y' ▷ Z) ≫ eComp V x y' z := by
        simpa only [tensorHom_id, Category.assoc] using congrArg
          (fun k : W ⊗ (H ⊗ Z) ⟶ ((x ⟶[V] y) ⊗ (y ⟶[V] y')) ⊗ Z =>
            k ≫ (eComp V x y y' ▷ Z) ≫ eComp V x y' z)
          (associator_inv_naturality g h (𝟙 Z))
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k : (W ⊗ H) ⊗ Z ⟶ (x ⟶[V] y') ⊗ Z =>
            (α_ W H Z).inv ≫ k ≫ eComp V x y' z)
          (comp_whiskerRight (g ⊗ₘ h) (eComp V x y y') Z).symm
  have hJoin :
      (r ⊗ₘ (g' ⊗ₘ 𝟙 Z)) ≫
          (x ⟶[V] x') ◁ eComp V x' y' z =
        r ⊗ₘ t := by
    simpa only [id_tensorHom, Category.comp_id, t] using
      (tensorHom_comp_tensorHom r (g' ⊗ₘ 𝟙 Z)
        (𝟙 (x ⟶[V] x')) (eComp V x' y' z))
  have hRightAssoc :
      (((r ⊗ₘ g') ≫ eComp V x x' y') ▷ Z) ≫ eComp V x y' z =
        (α_ H W Z).hom ≫ (r ⊗ₘ t) ≫ eComp V x x' z := by
    calc
      _ = ((r ⊗ₘ g') ▷ Z) ≫ (eComp V x x' y' ▷ Z) ≫
          eComp V x y' z := by
        simpa only [Category.assoc] using congrArg
          (fun k : (H ⊗ W) ⊗ Z ⟶ (x ⟶[V] y') ⊗ Z =>
            k ≫ eComp V x y' z)
          (comp_whiskerRight (r ⊗ₘ g') (eComp V x x' y') Z)
      _ = ((r ⊗ₘ g') ▷ Z) ≫
          (α_ (x ⟶[V] x') (x' ⟶[V] y') Z).hom ≫
          (x ⟶[V] x') ◁ eComp V x' y' z ≫ eComp V x x' z := by
        simpa only [Category.assoc] using congrArg
          (fun k : ((x ⟶[V] x') ⊗ (x' ⟶[V] y')) ⊗ Z ⟶ (x ⟶[V] z) =>
            ((r ⊗ₘ g') ▷ Z) ≫ k) (e_assoc' V x x' y' z).symm
      _ = (α_ H W Z).hom ≫ (r ⊗ₘ (g' ⊗ₘ 𝟙 Z)) ≫
          (x ⟶[V] x') ◁ eComp V x' y' z ≫ eComp V x x' z := by
        simpa only [tensorHom_id, Category.assoc] using congrArg
          (fun k : (H ⊗ W) ⊗ Z ⟶ (x ⟶[V] x') ⊗ ((x' ⟶[V] y') ⊗ Z) =>
            k ≫ (x ⟶[V] x') ◁ eComp V x' y' z ≫ eComp V x x' z)
          (associator_naturality r g' (𝟙 Z))
      _ = _ := by
        simpa only [Category.assoc] using congrArg
          (fun k : H ⊗ (W ⊗ Z) ⟶ (x ⟶[V] x') ⊗ (x' ⟶[V] z) =>
            (α_ H W Z).hom ≫ k ≫ eComp V x x' z) hJoin
  have hSquareRight :
      (((g ⊗ₘ h) ≫ eComp V x y y') ▷ Z) =
        ((β_ W H).hom ▷ Z) ≫
          (((r ⊗ₘ g') ≫ eComp V x x' y') ▷ Z) :=
    (congrArg (fun k : W ⊗ H ⟶ (x ⟶[V] y') => k ▷ Z) hSquare).trans
      (comp_whiskerRight (β_ W H).hom
        ((r ⊗ₘ g') ≫ eComp V x x' y') Z)
  have hBraid :
      (β_ (W ⊗ Z) H).hom ≫ (r ⊗ₘ t) =
        (t ⊗ₘ r) ≫ (β_ (x' ⟶[V] z) (x ⟶[V] x')).hom :=
    (braiding_naturality t r).symm
  calc
    _ = (W ◁ (β_ Z H).hom) ≫
        ((g ⊗ₘ (h ⊗ₘ 𝟙 Z)) ≫
          (x ⟶[V] y) ◁ eComp V y y' z) ≫ eComp V x y z := by
      simpa only [Z, Category.assoc] using congrArg
        (fun k : W ⊗ (Z ⊗ H) ⟶ (x ⟶[V] y) ⊗ (y ⟶[V] z) =>
          k ≫ eComp V x y z) hTensorAction
    _ = W ◁ (β_ Z H).hom ≫ (α_ W H Z).inv ≫
        (((g ⊗ₘ h) ≫ eComp V x y y') ▷ Z) ≫ eComp V x y' z := by
      simpa only [Category.assoc] using congrArg
        (fun k : W ⊗ (H ⊗ Z) ⟶ (x ⟶[V] z) =>
          (W ◁ (β_ Z H).hom) ≫ k) hAssoc
    _ = W ◁ (β_ Z H).hom ≫ (α_ W H Z).inv ≫
        ((β_ W H).hom ▷ Z) ≫
        (((r ⊗ₘ g') ≫ eComp V x x' y') ▷ Z) ≫ eComp V x y' z := by
      simpa only [Category.assoc] using congrArg
        (fun k : (W ⊗ H) ⊗ Z ⟶ (x ⟶[V] y') ⊗ Z =>
          (W ◁ (β_ Z H).hom) ≫ (α_ W H Z).inv ≫ k ≫ eComp V x y' z)
        hSquareRight
    _ = W ◁ (β_ Z H).hom ≫ (α_ W H Z).inv ≫
        ((β_ W H).hom ▷ Z) ≫
        (α_ H W Z).hom ≫ (r ⊗ₘ t) ≫ eComp V x x' z := by
      simpa only [Category.assoc] using congrArg
        (fun k : (H ⊗ W) ⊗ Z ⟶ (x ⟶[V] z) =>
          (W ◁ (β_ Z H).hom) ≫ (α_ W H Z).inv ≫
            ((β_ W H).hom ▷ Z) ≫ k) hRightAssoc
    _ = (α_ W Z H).inv ≫ (β_ (W ⊗ Z) H).hom ≫
        (r ⊗ₘ t) ≫ eComp V x x' z := by
      simpa only [Category.assoc] using congrArg
        (fun k : W ⊗ (Z ⊗ H) ⟶ H ⊗ (W ⊗ Z) =>
          k ≫ (r ⊗ₘ t) ≫ eComp V x x' z)
        (secondWeightReorder_hexagonForProof W Z H)
    _ = _ := by
      simpa only [Z, t, Category.assoc] using congrArg
        (fun k : (W ⊗ Z) ⊗ H ⟶ (x ⟶[V] x') ⊗ (x' ⟶[V] z) =>
          (α_ W Z H).inv ≫ k ≫ eComp V x x' z) hBraid


omit [MonoidalClosed V] in
/-- This is the full original ordered generator with its actual selected fixed-left map. -/
private theorem indexGenerator_selectedForProof
    (d : EnrichedMonoidalCategoryData V I) (n k l a b : I) :
    indexGenerator d n k l a b =
      (((fixedLeftTensorForProof d b).map (a ⊗ n) k ⊗ₘ
          𝟙 ((b ⊗ k) ⟶[V] l)) ≫
        eComp V (b ⊗ (a ⊗ n)) (b ⊗ k) l) ≫
        eHomWhiskerRight V (α_ b a n).hom l := by
  let W : V := (a ⊗ n) ⟶[V] k
  let Z : V := (b ⊗ k) ⟶[V] l
  let T : V := (b ⊗ (a ⊗ n)) ⟶[V] (b ⊗ k)
  let R : V := (b ⊗ (a ⊗ n)) ⟶[V] l
  let U : V := ((b ⊗ a) ⊗ n) ⟶[V] l
  let j : W ⟶ T :=
    (λ_ W).inv ≫ (eId V b ⊗ₘ 𝟙 W) ≫ d.tensorMap b b (a ⊗ n) k
  have hMap : (fixedLeftTensorForProof d b).map (a ⊗ n) k = j :=
    fixedLeftTensor_mapForProof d b (a ⊗ n) k
  have hPre : eHomWhiskerRight V (α_ b a n).hom l =
      (λ_ R).inv ≫ (eHomEquiv V (α_ b a n).hom ⊗ₘ 𝟙 R) ≫
        eComp V ((b ⊗ a) ⊗ n) (b ⊗ (a ⊗ n)) l := by
    dsimp only [R]
    simp only [eHomWhiskerRight, tensorHom_id]
  calc
    _ = ((j ⊗ₘ 𝟙 Z) ≫ eComp V (b ⊗ (a ⊗ n)) (b ⊗ k) l) ≫
        ((λ_ R).inv ≫ (eHomEquiv V (α_ b a n).hom ⊗ₘ 𝟙 R) ≫
          eComp V ((b ⊗ a) ⊗ n) (b ⊗ (a ⊗ n)) l) := rfl
    _ = ((j ⊗ₘ 𝟙 Z) ≫ eComp V (b ⊗ (a ⊗ n)) (b ⊗ k) l) ≫
        eHomWhiskerRight V (α_ b a n).hom l :=
      congrArg
        (fun f : R ⟶ U =>
          ((j ⊗ₘ 𝟙 Z) ≫ eComp V (b ⊗ (a ⊗ n)) (b ⊗ k) l) ≫ f) hPre.symm
    _ = _ := congrArg
      (fun f : W ⟶ T =>
        ((f ⊗ₘ 𝟙 Z) ≫ eComp V (b ⊗ (a ⊗ n)) (b ⊗ k) l) ≫
          eHomWhiskerRight V (α_ b a n).hom l) hMap.symm


/-- The full A index-weight certificate at the original I(a,a') Hom object. -/
private theorem indexGenerator_firstWeightForProof
    (d : EnrichedMonoidalCategoryData V I) (n k l a a' b : I) :
    (MonoidalClosed.uncurry ((weight d n k).map (op a') (op a)) ⊗ₘ
        𝟙 ((b ⊗ k) ⟶[V] l)) ≫ indexGenerator d n k l a b =
      firstWeightReorderForProof ((a' ⊗ n) ⟶[V] k)
          (a ⟶[V] a') ((b ⊗ k) ⟶[V] l) ≫
        (indexGenerator d n k l a' b ⊗ₘ
          (fixedLeftTensorForProof d b).map a a') ≫
        MonoidalClosed.uncurry
          ((weight d n l).map (op (b ⊗ a')) (op (b ⊗ a))) := by
  let W : V := (a' ⊗ n) ⟶[V] k
  let H : V := a ⟶[V] a'
  let Z : V := (b ⊗ k) ⟶[V] l
  let x : I := b ⊗ (a ⊗ n)
  let x' : I := b ⊗ (a' ⊗ n)
  let y : I := b ⊗ k
  let u : ((b ⊗ a) ⊗ n) ≅ x := α_ b a n
  let v : ((b ⊗ a') ⊗ n) ≅ x' := α_ b a' n
  let f (c : I) : ((c ⊗ n) ⟶[V] k) ⟶
      ((b ⊗ (c ⊗ n)) ⟶[V] (b ⊗ k)) :=
    (fixedLeftTensorForProof d b).map (c ⊗ n) k
  let t (c : I) : (((c ⊗ n) ⟶[V] k) ⊗ Z) ⟶
      ((b ⊗ (c ⊗ n)) ⟶[V] l) :=
    (f c ⊗ₘ 𝟙 Z) ≫ eComp V (b ⊗ (c ⊗ n)) (b ⊗ k) l
  let p : H ⟶ (x ⟶[V] x') :=
    (fixedRightTensor d n).map a a' ≫
      (fixedLeftTensorForProof d b).map (a ⊗ n) (a' ⊗ n)
  let q : H ⟶ (((b ⊗ a) ⊗ n) ⟶[V] ((b ⊗ a') ⊗ n)) :=
    (fixedLeftTensorForProof d b).map a a' ≫
      (fixedRightTensor d n).map (b ⊗ a) (b ⊗ a')
  let s : (W ⊗ H) ⊗ Z ⟶ (W ⊗ Z) ⊗ H := firstWeightReorderForProof W H Z
  let w : W ⊗ H ⟶ ((a ⊗ n) ⟶[V] k) :=
    MonoidalClosed.uncurry ((weight d n k).map (op a') (op a))
  have hNatural :
      q ≫ eHomWhiskerLeft V ((b ⊗ a) ⊗ n) v.hom =
        p ≫ eHomWhiskerRight V u.hom x' :=
    associator_firstVaryingForProof d b a a' n
  have hSplit : (w ⊗ₘ 𝟙 Z) ≫ t a = ((w ≫ f a) ⊗ₘ 𝟙 Z) ≫ eComp V x y l := by
    have hTensor := tensorHom_comp_tensorHom w (𝟙 Z) (f a) (𝟙 Z)
    have hIdentity : ((w ≫ f a) ⊗ₘ (𝟙 Z ≫ 𝟙 Z)) = (w ≫ f a) ⊗ₘ 𝟙 Z :=
      congrArg (fun q : Z ⟶ Z => (w ≫ f a) ⊗ₘ q) (Category.comp_id (𝟙 Z))
    exact (Category.assoc (w ⊗ₘ 𝟙 Z) (f a ⊗ₘ 𝟙 Z) (eComp V x y l)).symm.trans
      (congrArg (fun q : (W ⊗ H) ⊗ Z ⟶ (x ⟶[V] y) ⊗ Z => q ≫ eComp V x y l)
        (hTensor.trans hIdentity))
  have hWeightMap : w = W ◁ (fixedRightTensor d n).map a a' ≫
      (β_ W ((a ⊗ n) ⟶[V] (a' ⊗ n))).hom ≫ eComp V (a ⊗ n) (a' ⊗ n) k :=
    weight_uncurry_map d n k a a'
  have hWeight := congrArg
    (fun q : W ⊗ H ⟶ ((a ⊗ n) ⟶[V] k) => ((q ≫ f a) ⊗ₘ 𝟙 Z) ≫ eComp V x y l)
    hWeightMap
  have hFull :
      (((W ◁ (fixedRightTensor d n).map a a' ≫
          (β_ W ((a ⊗ n) ⟶[V] (a' ⊗ n))).hom ≫
          eComp V (a ⊗ n) (a' ⊗ n) k) ≫
        f a) ⊗ₘ 𝟙 Z) ≫ eComp V x y l =
        s ≫ (t a' ⊗ₘ p) ≫
          (β_ (x' ⟶[V] l) (x ⟶[V] x')).hom ≫ eComp V x x' l := by
    have hTransport :
        ((W ◁ (fixedRightTensor d n).map a a' ≫
            (β_ W ((a ⊗ n) ⟶[V] (a' ⊗ n))).hom ≫
            eComp V (a ⊗ n) (a' ⊗ n) k ≫ f a) ⊗ₘ 𝟙 Z) ≫
          eComp V x y l =
        s ≫ (t a' ⊗ₘ p) ≫
          (β_ (x' ⟶[V] l) (x ⟶[V] x')).hom ≫ eComp V x x' l :=
      enrichedFunctor_firstWeightExchangeForProof
        (fixedLeftTensorForProof d b) (a ⊗ n) (a' ⊗ n) k l
        ((fixedRightTensor d n).map a a')
    have hInput :
        (W ◁ (fixedRightTensor d n).map a a' ≫
          ((β_ W ((a ⊗ n) ⟶[V] (a' ⊗ n))).hom ≫ eComp V (a ⊗ n) (a' ⊗ n) k)) ≫ f a =
        W ◁ (fixedRightTensor d n).map a a' ≫
          (β_ W ((a ⊗ n) ⟶[V] (a' ⊗ n))).hom ≫ eComp V (a ⊗ n) (a' ⊗ n) k ≫ f a :=
      (Category.assoc (W ◁ (fixedRightTensor d n).map a a')
        ((β_ W ((a ⊗ n) ⟶[V] (a' ⊗ n))).hom ≫ eComp V (a ⊗ n) (a' ⊗ n) k) (f a)).trans
        (congrArg (fun q => W ◁ (fixedRightTensor d n).map a a' ≫ q)
          (Category.assoc (β_ W ((a ⊗ n) ⟶[V] (a' ⊗ n))).hom
            (eComp V (a ⊗ n) (a' ⊗ n) k) (f a)))
    exact (congrArg
      (fun q : W ⊗ H ⟶ (x ⟶[V] y) => (q ⊗ₘ 𝟙 Z) ≫ eComp V x y l) hInput).trans hTransport
  have hFirst :
      (w ⊗ₘ 𝟙 Z) ≫ t a =
        s ≫ (t a' ⊗ₘ p) ≫
          (β_ (x' ⟶[V] l) (x ⟶[V] x')).hom ≫ eComp V x x' l :=
    hSplit.trans (hWeight.trans hFull)
  have hTransport := isoWeightAction_transportForProof
    ((b ⊗ a) ⊗ n) ((b ⊗ a') ⊗ n) x x' l u v (t a') p q hNatural
  have hIndex (c : I) : indexGenerator d n k l c b =
      t c ≫ eHomWhiskerRight V (α_ b c n).hom l :=
    indexGenerator_selectedForProof d n k l c b
  have hLast :
      ((t a' ≫ eHomWhiskerRight V v.hom l) ⊗ₘ q) ≫
          (β_ (((b ⊗ a') ⊗ n) ⟶[V] l)
            (((b ⊗ a) ⊗ n) ⟶[V] ((b ⊗ a') ⊗ n))).hom ≫
          eComp V ((b ⊗ a) ⊗ n) ((b ⊗ a') ⊗ n) l =
        (indexGenerator d n k l a' b ⊗ₘ (fixedLeftTensorForProof d b).map a a') ≫
          MonoidalClosed.uncurry
            ((weight d n l).map (op (b ⊗ a')) (op (b ⊗ a))) := by
    let T : V := ((b ⊗ a') ⊗ n) ⟶[V] l
    let R : V := ((b ⊗ a) ⊗ n) ⟶[V] ((b ⊗ a') ⊗ n)
    let tail : T ⊗ R ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) :=
      (β_ T R).hom ≫ eComp V ((b ⊗ a) ⊗ n) ((b ⊗ a') ⊗ n) l
    let q₁ : H ⟶ ((b ⊗ a) ⟶[V] (b ⊗ a')) := (fixedLeftTensorForProof d b).map a a'
    let q₂ : ((b ⊗ a) ⟶[V] (b ⊗ a')) ⟶ R := (fixedRightTensor d n).map (b ⊗ a) (b ⊗ a')
    let gamma : W ⊗ Z ⟶ T := indexGenerator d n k l a' b
    let out : T ⊗ ((b ⊗ a) ⟶[V] (b ⊗ a')) ⟶
        (((b ⊗ a) ⊗ n) ⟶[V] l) :=
      MonoidalClosed.uncurry ((weight d n l).map (op (b ⊗ a')) (op (b ⊗ a)))
    have hQ : q = q₁ ≫ q₂ := rfl
    have hIndexT : t a' ≫ eHomWhiskerRight V v.hom l = gamma := (hIndex a').symm
    have hJoin : (gamma ⊗ₘ q₁) ≫ T ◁ q₂ = gamma ⊗ₘ (q₁ ≫ q₂) :=
      tensorHom_comp_whiskerLeft gamma q₁ q₂
    have hOutputWeight : out = T ◁ q₂ ≫ tail :=
      weight_uncurry_map d n l (b ⊗ a) (b ⊗ a')
    have hFirst : ((t a' ≫ eHomWhiskerRight V v.hom l) ⊗ₘ q) ≫ tail =
        (gamma ⊗ₘ q) ≫ tail :=
      congrArg (fun f : W ⊗ Z ⟶ T => (f ⊗ₘ q) ≫ tail) hIndexT
    have hSecond : (gamma ⊗ₘ q) ≫ tail =
        ((gamma ⊗ₘ q₁) ≫ T ◁ q₂) ≫ tail :=
      congrArg (fun f : (W ⊗ Z) ⊗ H ⟶ T ⊗ R => f ≫ tail)
        ((congrArg (fun f : H ⟶ R => gamma ⊗ₘ f) hQ).trans hJoin.symm)
    have hThird : ((gamma ⊗ₘ q₁) ≫ T ◁ q₂) ≫ tail =
        (gamma ⊗ₘ q₁) ≫ (T ◁ q₂ ≫ tail) :=
      Category.assoc (gamma ⊗ₘ q₁) (T ◁ q₂) tail
    have hFourth : (gamma ⊗ₘ q₁) ≫ (T ◁ q₂ ≫ tail) =
        (gamma ⊗ₘ q₁) ≫ out :=
      congrArg (fun f : T ⊗ ((b ⊗ a) ⟶[V] (b ⊗ a')) ⟶
          (((b ⊗ a) ⊗ n) ⟶[V] l) => (gamma ⊗ₘ q₁) ≫ f) hOutputWeight.symm
    exact hFirst.trans (hSecond.trans (hThird.trans hFourth))
  let pullU : (x ⟶[V] l) ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) :=
    eHomWhiskerRight V u.hom l
  let pullV : (x' ⟶[V] l) ⟶ (((b ⊗ a') ⊗ n) ⟶[V] l) :=
    eHomWhiskerRight V v.hom l
  let middle : (W ⊗ Z) ⊗ H ⟶ (x ⟶[V] l) :=
    (t a' ⊗ₘ p) ≫ (β_ (x' ⟶[V] l) (x ⟶[V] x')).hom ≫ eComp V x x' l
  let transported : (W ⊗ Z) ⊗ H ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) :=
    ((t a' ≫ pullV) ⊗ₘ q) ≫
      (β_ (((b ⊗ a') ⊗ n) ⟶[V] l)
        (((b ⊗ a) ⊗ n) ⟶[V] ((b ⊗ a') ⊗ n))).hom ≫
      eComp V ((b ⊗ a) ⊗ n) ((b ⊗ a') ⊗ n) l
  let startMap : (((a ⊗ n) ⟶[V] k) ⊗ Z) ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) :=
    indexGenerator d n k l a b
  let output : (W ⊗ Z) ⊗ H ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) :=
    (indexGenerator d n k l a' b ⊗ₘ (fixedLeftTensorForProof d b).map a a') ≫
      MonoidalClosed.uncurry ((weight d n l).map (op (b ⊗ a')) (op (b ⊗ a)))
  have hStartMap : startMap = t a ≫ pullU := hIndex a
  have hFirstT : (w ⊗ₘ 𝟙 Z) ≫ t a = s ≫ middle := hFirst
  have hTransportT : middle ≫ pullU = transported := hTransport
  have hOutputT : transported = output := hLast
  have hStart : (w ⊗ₘ 𝟙 Z) ≫ startMap = ((w ⊗ₘ 𝟙 Z) ≫ t a) ≫ pullU :=
    (congrArg (fun f : (((a ⊗ n) ⟶[V] k) ⊗ Z) ⟶
        (((b ⊗ a) ⊗ n) ⟶[V] l) => (w ⊗ₘ 𝟙 Z) ≫ f) hStartMap).trans
      (Category.assoc (w ⊗ₘ 𝟙 Z) (t a) pullU).symm
  have hApply : ((w ⊗ₘ 𝟙 Z) ≫ t a) ≫ pullU = (s ≫ middle) ≫ pullU :=
    congrArg (fun f : (W ⊗ H) ⊗ Z ⟶ (x ⟶[V] l) => f ≫ pullU) hFirstT
  have hAssociate : (s ≫ middle) ≫ pullU = s ≫ (middle ≫ pullU) :=
    Category.assoc s middle pullU
  have hTransported : s ≫ (middle ≫ pullU) = s ≫ transported :=
    congrArg (fun f : (W ⊗ Z) ⊗ H ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) => s ≫ f) hTransportT
  have hFinish : s ≫ transported = s ≫ output :=
    congrArg (fun f : (W ⊗ Z) ⊗ H ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) => s ≫ f) hOutputT
  change (w ⊗ₘ 𝟙 Z) ≫ startMap = s ≫ output
  exact hStart.trans (hApply.trans (hAssociate.trans (hTransported.trans hFinish)))


/-- The full B index-weight certificate at the original I(b,b') Hom object. -/
private theorem indexGenerator_secondWeightForProof
    (d : EnrichedMonoidalCategoryData V I) (n k l a b b' : I) :
    (𝟙 ((a ⊗ n) ⟶[V] k) ⊗ₘ
        MonoidalClosed.uncurry ((weight d k l).map (op b') (op b))) ≫
        indexGenerator d n k l a b =
      (α_ ((a ⊗ n) ⟶[V] k) ((b' ⊗ k) ⟶[V] l) (b ⟶[V] b')).inv ≫
        (indexGenerator d n k l a b' ⊗ₘ (fixedRightTensor d a).map b b') ≫
        MonoidalClosed.uncurry
          ((weight d n l).map (op (b' ⊗ a)) (op (b ⊗ a))) := by
  let W : V := (a ⊗ n) ⟶[V] k
  let H : V := b ⟶[V] b'
  let Z : V := (b' ⊗ k) ⟶[V] l
  let x : I := b ⊗ (a ⊗ n)
  let x' : I := b' ⊗ (a ⊗ n)
  let y : I := b ⊗ k
  let y' : I := b' ⊗ k
  let u : ((b ⊗ a) ⊗ n) ≅ x := α_ b a n
  let v : ((b' ⊗ a) ⊗ n) ≅ x' := α_ b' a n
  let g : W ⟶ (x ⟶[V] y) := (fixedLeftTensorForProof d b).map (a ⊗ n) k
  let h : H ⟶ (y ⟶[V] y') := (fixedRightTensor d k).map b b'
  let r : H ⟶ (x ⟶[V] x') := (fixedRightTensor d (a ⊗ n)).map b b'
  let g' : W ⟶ (x' ⟶[V] y') := (fixedLeftTensorForProof d b').map (a ⊗ n) k
  let t : W ⊗ (y ⟶[V] l) ⟶ (x ⟶[V] l) :=
    (g ⊗ₘ 𝟙 (y ⟶[V] l)) ≫ eComp V x y l
  let t' : W ⊗ Z ⟶ (x' ⟶[V] l) := (g' ⊗ₘ 𝟙 Z) ≫ eComp V x' y' l
  let q : H ⟶ (((b ⊗ a) ⊗ n) ⟶[V] ((b' ⊗ a) ⊗ n)) :=
    (fixedRightTensor d a).map b b' ≫
      (fixedRightTensor d n).map (b ⊗ a) (b' ⊗ a)
  let w : Z ⊗ H ⟶ (y ⟶[V] l) :=
    MonoidalClosed.uncurry ((weight d k l).map (op b') (op b))
  have hSquare : (g ⊗ₘ h) ≫ eComp V x y y' =
      (β_ W H).hom ≫ (r ⊗ₘ g') ≫ eComp V x x' y' :=
    tensor_full_exchangeForProof d b b' (a ⊗ n) k
  have hNatural :
      q ≫ eHomWhiskerLeft V ((b ⊗ a) ⊗ n) v.hom =
        r ≫ eHomWhiskerRight V u.hom x' :=
    associator_secondVaryingForProof d b b' a n
  have hSplit : (𝟙 W ⊗ₘ w) ≫ t = (g ⊗ₘ w) ≫ eComp V x y l := by
    have hTensor := tensorHom_comp_tensorHom (𝟙 W) w g (𝟙 (y ⟶[V] l))
    have hIdentity : ((𝟙 W ≫ g) ⊗ₘ (w ≫ 𝟙 (y ⟶[V] l))) = g ⊗ₘ w :=
      congrArg₂
        (fun (p : W ⟶ (x ⟶[V] y)) (q : Z ⊗ H ⟶ (y ⟶[V] l)) => p ⊗ₘ q)
        (Category.id_comp g) (Category.comp_id w)
    exact (Category.assoc (𝟙 W ⊗ₘ w) (g ⊗ₘ 𝟙 (y ⟶[V] l)) (eComp V x y l)).symm.trans
      (congrArg
        (fun q : W ⊗ (Z ⊗ H) ⟶ (x ⟶[V] y) ⊗ (y ⟶[V] l) => q ≫ eComp V x y l)
        (hTensor.trans hIdentity))
  have hWeightMap : w = Z ◁ h ≫ (β_ Z (y ⟶[V] y')).hom ≫ eComp V y y' l :=
    weight_uncurry_map d k l b b'
  have hWeight := congrArg
    (fun q : Z ⊗ H ⟶ (y ⟶[V] l) => (g ⊗ₘ q) ≫ eComp V x y l) hWeightMap
  have hFull :
      (g ⊗ₘ
        (Z ◁ h ≫ (β_ Z (y ⟶[V] y')).hom ≫ eComp V y y' l)) ≫
          eComp V x y l =
        (α_ W Z H).inv ≫ (t' ⊗ₘ r) ≫
          (β_ (x' ⟶[V] l) (x ⟶[V] x')).hom ≫ eComp V x x' l :=
    enrichedComposition_secondWeightExchangeForProof x y y' x' l g h r g' hSquare
  have hSecond :
      (𝟙 W ⊗ₘ w) ≫ t =
        (α_ W Z H).inv ≫ (t' ⊗ₘ r) ≫
          (β_ (x' ⟶[V] l) (x ⟶[V] x')).hom ≫ eComp V x x' l :=
    hSplit.trans (hWeight.trans hFull)
  have hTransport := isoWeightAction_transportForProof
    ((b ⊗ a) ⊗ n) ((b' ⊗ a) ⊗ n) x x' l u v t' r q hNatural
  have hIndex : indexGenerator d n k l a b = t ≫ eHomWhiskerRight V u.hom l :=
    indexGenerator_selectedForProof d n k l a b
  have hIndex' : t' ≫ eHomWhiskerRight V v.hom l = indexGenerator d n k l a b' :=
    (indexGenerator_selectedForProof d n k l a b').symm
  have hLast :
      ((t' ≫ eHomWhiskerRight V v.hom l) ⊗ₘ q) ≫
          (β_ (((b' ⊗ a) ⊗ n) ⟶[V] l)
            (((b ⊗ a) ⊗ n) ⟶[V] ((b' ⊗ a) ⊗ n))).hom ≫
          eComp V ((b ⊗ a) ⊗ n) ((b' ⊗ a) ⊗ n) l =
        (indexGenerator d n k l a b' ⊗ₘ (fixedRightTensor d a).map b b') ≫
          MonoidalClosed.uncurry
            ((weight d n l).map (op (b' ⊗ a)) (op (b ⊗ a))) := by
    let T : V := ((b' ⊗ a) ⊗ n) ⟶[V] l
    let R : V := ((b ⊗ a) ⊗ n) ⟶[V] ((b' ⊗ a) ⊗ n)
    let tail : T ⊗ R ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) :=
      (β_ T R).hom ≫ eComp V ((b ⊗ a) ⊗ n) ((b' ⊗ a) ⊗ n) l
    let q₁ : H ⟶ ((b ⊗ a) ⟶[V] (b' ⊗ a)) := (fixedRightTensor d a).map b b'
    let q₂ : ((b ⊗ a) ⟶[V] (b' ⊗ a)) ⟶ R := (fixedRightTensor d n).map (b ⊗ a) (b' ⊗ a)
    let gamma : W ⊗ Z ⟶ T := indexGenerator d n k l a b'
    let out : T ⊗ ((b ⊗ a) ⟶[V] (b' ⊗ a)) ⟶
        (((b ⊗ a) ⊗ n) ⟶[V] l) :=
      MonoidalClosed.uncurry ((weight d n l).map (op (b' ⊗ a)) (op (b ⊗ a)))
    have hQ : q = q₁ ≫ q₂ := rfl
    have hIndexT : t' ≫ eHomWhiskerRight V v.hom l = gamma := hIndex'
    have hJoin : (gamma ⊗ₘ q₁) ≫ T ◁ q₂ = gamma ⊗ₘ (q₁ ≫ q₂) :=
      tensorHom_comp_whiskerLeft gamma q₁ q₂
    have hOutputWeight : out = T ◁ q₂ ≫ tail :=
      weight_uncurry_map d n l (b ⊗ a) (b' ⊗ a)
    have hFirst : ((t' ≫ eHomWhiskerRight V v.hom l) ⊗ₘ q) ≫ tail =
        (gamma ⊗ₘ q) ≫ tail :=
      congrArg (fun f : W ⊗ Z ⟶ T => (f ⊗ₘ q) ≫ tail) hIndexT
    have hSecond : (gamma ⊗ₘ q) ≫ tail =
        ((gamma ⊗ₘ q₁) ≫ T ◁ q₂) ≫ tail :=
      congrArg (fun f : (W ⊗ Z) ⊗ H ⟶ T ⊗ R => f ≫ tail)
        ((congrArg (fun f : H ⟶ R => gamma ⊗ₘ f) hQ).trans hJoin.symm)
    have hThird : ((gamma ⊗ₘ q₁) ≫ T ◁ q₂) ≫ tail =
        (gamma ⊗ₘ q₁) ≫ (T ◁ q₂ ≫ tail) :=
      Category.assoc (gamma ⊗ₘ q₁) (T ◁ q₂) tail
    have hFourth : (gamma ⊗ₘ q₁) ≫ (T ◁ q₂ ≫ tail) =
        (gamma ⊗ₘ q₁) ≫ out :=
      congrArg (fun f : T ⊗ ((b ⊗ a) ⟶[V] (b' ⊗ a)) ⟶
          (((b ⊗ a) ⊗ n) ⟶[V] l) => (gamma ⊗ₘ q₁) ≫ f) hOutputWeight.symm
    exact hFirst.trans (hSecond.trans (hThird.trans hFourth))
  let pullU : (x ⟶[V] l) ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) :=
    eHomWhiskerRight V u.hom l
  let pullV : (x' ⟶[V] l) ⟶ (((b' ⊗ a) ⊗ n) ⟶[V] l) :=
    eHomWhiskerRight V v.hom l
  let front : W ⊗ (Z ⊗ H) ⟶ (W ⊗ Z) ⊗ H := (α_ W Z H).inv
  let middle : (W ⊗ Z) ⊗ H ⟶ (x ⟶[V] l) :=
    (t' ⊗ₘ r) ≫ (β_ (x' ⟶[V] l) (x ⟶[V] x')).hom ≫ eComp V x x' l
  let transported : (W ⊗ Z) ⊗ H ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) :=
    ((t' ≫ pullV) ⊗ₘ q) ≫
      (β_ (((b' ⊗ a) ⊗ n) ⟶[V] l)
        (((b ⊗ a) ⊗ n) ⟶[V] ((b' ⊗ a) ⊗ n))).hom ≫
      eComp V ((b ⊗ a) ⊗ n) ((b' ⊗ a) ⊗ n) l
  let startMap : W ⊗ (y ⟶[V] l) ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) :=
    indexGenerator d n k l a b
  let output : (W ⊗ Z) ⊗ H ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) :=
    (indexGenerator d n k l a b' ⊗ₘ (fixedRightTensor d a).map b b') ≫
      MonoidalClosed.uncurry ((weight d n l).map (op (b' ⊗ a)) (op (b ⊗ a)))
  have hStartMap : startMap = t ≫ pullU := hIndex
  have hSecondT : (𝟙 W ⊗ₘ w) ≫ t = front ≫ middle := hSecond
  have hTransportT : middle ≫ pullU = transported := hTransport
  have hOutputT : transported = output := hLast
  have hStart : (𝟙 W ⊗ₘ w) ≫ startMap = ((𝟙 W ⊗ₘ w) ≫ t) ≫ pullU :=
    (congrArg (fun f : W ⊗ (y ⟶[V] l) ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) =>
        (𝟙 W ⊗ₘ w) ≫ f) hStartMap).trans
      (Category.assoc (𝟙 W ⊗ₘ w) t pullU).symm
  have hApply : ((𝟙 W ⊗ₘ w) ≫ t) ≫ pullU = (front ≫ middle) ≫ pullU :=
    congrArg (fun f : W ⊗ (Z ⊗ H) ⟶ (x ⟶[V] l) => f ≫ pullU) hSecondT
  have hAssociate : (front ≫ middle) ≫ pullU = front ≫ (middle ≫ pullU) :=
    Category.assoc front middle pullU
  have hTransported : front ≫ (middle ≫ pullU) = front ≫ transported :=
    congrArg (fun f : (W ⊗ Z) ⊗ H ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) => front ≫ f) hTransportT
  have hFinish : front ≫ transported = front ≫ output :=
    congrArg (fun f : (W ⊗ Z) ⊗ H ⟶ (((b ⊗ a) ⊗ n) ⟶[V] l) => front ≫ f) hOutputT
  change (𝟙 W ⊗ₘ w) ≫ startMap = front ≫ output
  exact hStart.trans (hApply.trans (hAssociate.trans (hTransported.trans hFinish)))


omit [MonoidalClosed V] [MonoidalCategory I] in
/-- Use the existing full oplax naturality of the canonical tensor functor. -/
private theorem tensorDelta_naturalityForProof
    {W W' Z Z' A A' B B' : V}
    (f : W ⟶ W') (g : Z ⟶ Z') (p : A ⟶ A') (q : B ⟶ B') :
    ((f ⊗ₘ p) ⊗ₘ (g ⊗ₘ q)) ≫ tensorδ W' Z' A' B' =
      tensorδ W Z A B ≫ ((f ⊗ₘ g) ⊗ₘ (p ⊗ₘ q)) := by
  have h := Functor.OplaxMonoidal.δ_natural (MonoidalCategory.tensor V)
    (show (W, Z) ⟶ (W', Z') from (f, g))
    (show (A, B) ⟶ (A', B') from (p, q))
  simp only [MonoidalCategory.tensor_δ] at h
  change tensorδ W Z A B ≫ ((f ⊗ₘ g) ⊗ₘ (p ⊗ₘ q)) =
    ((f ⊗ₘ p) ⊗ₘ (g ⊗ₘ q)) ≫ tensorδ W' Z' A' B' at h
  exact h.symm

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The full A weight-face rewire is the inverse hexagon of the mixed crossing. -/
private theorem firstWeightFace_rewireForProof (W H Z A B : V) :
    ((α_ W H A).inv ⊗ₘ 𝟙 (Z ⊗ B)) ≫
        tensorδ (W ⊗ H) Z A B ≫
        (𝟙 ((W ⊗ H) ⊗ Z) ⊗ₘ (β_ A B).hom) ≫
        (firstWeightReorderForProof W H Z ⊗ₘ 𝟙 (B ⊗ A)) =
      tensorδ W Z (H ⊗ A) B ≫
        (𝟙 (W ⊗ Z) ⊗ₘ (α_ H A B).hom) ≫
        (𝟙 (W ⊗ Z) ⊗ₘ H ◁ (β_ A B).hom) ≫
        (α_ (W ⊗ Z) H (B ⊗ A)).inv := by
  let source : V := (W ⊗ (H ⊗ A)) ⊗ (Z ⊗ B)
  let target : V := ((W ⊗ Z) ⊗ H) ⊗ (B ⊗ A)
  let p : source ⟶ W ⊗ ((H ⊗ Z) ⊗ (A ⊗ B)) :=
    (α_ W (H ⊗ A) (Z ⊗ B)).hom ≫ W ◁ tensorδ H Z A B
  let s : W ⊗ ((Z ⊗ H) ⊗ (B ⊗ A)) ⟶ target :=
    W ◁ (α_ Z H (B ⊗ A)).hom ≫
      (α_ W Z (H ⊗ (B ⊗ A))).inv ≫ (α_ (W ⊗ Z) H (B ⊗ A)).inv
  let f : H ⊗ Z ⟶ Z ⊗ H := (β_ Z H).inv
  let g : A ⊗ B ⟶ B ⊗ A := (β_ A B).hom
  have hL :
      ((α_ W H A).inv ⊗ₘ 𝟙 (Z ⊗ B)) ≫
          tensorδ (W ⊗ H) Z A B ≫
          (𝟙 ((W ⊗ H) ⊗ Z) ⊗ₘ (β_ A B).hom) ≫
          (firstWeightReorderForProof W H Z ⊗ₘ 𝟙 (B ⊗ A)) =
        p ≫ W ◁ ((H ⊗ Z) ◁ g ≫ f ▷ (B ⊗ A)) ≫ s := by
    dsimp only [p, s, f, g, source, target, tensorδ, firstWeightReorderForProof]
    monoidal
  have hR :
      tensorδ W Z (H ⊗ A) B ≫
          (𝟙 (W ⊗ Z) ⊗ₘ (α_ H A B).hom) ≫
          (𝟙 (W ⊗ Z) ⊗ₘ H ◁ (β_ A B).hom) ≫
          (α_ (W ⊗ Z) H (B ⊗ A)).inv =
        p ≫ W ◁ (f ▷ (A ⊗ B) ≫ (Z ⊗ H) ◁ g) ≫ s := by
    dsimp only [p, s, f, g, source, target, tensorδ]
    rw [braiding_tensor_right_inv Z H A]
    monoidal
  have hExchange :
      (H ⊗ Z) ◁ g ≫ f ▷ (B ⊗ A) =
        f ▷ (A ⊗ B) ≫ (Z ⊗ H) ◁ g := whisker_exchange f g
  calc
    _ = _ := hL
    _ = p ≫ W ◁ (f ▷ (A ⊗ B) ≫ (Z ⊗ H) ◁ g) ≫ s :=
      congrArg
        (fun z : (H ⊗ Z) ⊗ (A ⊗ B) ⟶ (Z ⊗ H) ⊗ (B ⊗ A) =>
          p ≫ W ◁ z ≫ s) hExchange
    _ = _ := hR.symm

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The full B weight-face rewire keeps the inverse H/A crossing. -/
private theorem secondWeightFace_rewireForProof (W Z H A B : V) :
    (𝟙 (W ⊗ A) ⊗ₘ (α_ Z H B).inv) ≫
        tensorδ W (Z ⊗ H) A B ≫
        (𝟙 (W ⊗ (Z ⊗ H)) ⊗ₘ (β_ A B).hom) ≫
        ((α_ W Z H).inv ⊗ₘ 𝟙 (B ⊗ A)) =
      tensorδ W Z A (H ⊗ B) ≫
        (𝟙 (W ⊗ Z) ⊗ₘ (α_ A H B).inv) ≫
        (𝟙 (W ⊗ Z) ⊗ₘ ((β_ H A).inv ▷ B)) ≫
        (𝟙 (W ⊗ Z) ⊗ₘ (α_ H A B).hom) ≫
        (𝟙 (W ⊗ Z) ⊗ₘ H ◁ (β_ A B).hom) ≫
        (α_ (W ⊗ Z) H (B ⊗ A)).inv := by
  dsimp only [tensorδ]
  rw [braiding_tensor_left_inv Z H A]
  monoidal

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The A diagram face uses the positive full Yang-Baxter equation. -/
private theorem firstDiagramFace_rewireForProof (H A B : V) :
    ((β_ H A).hom ▷ B) ≫ (β_ (A ⊗ H) B).hom =
      (α_ H A B).hom ≫ H ◁ (β_ A B).hom ≫
        (β_ H (B ⊗ A)).hom ≫ (α_ B A H).hom := by
  have h := congrArg (fun f => (α_ H A B).hom ≫ f)
    (yang_baxter H A B)
  rw [braiding_tensor_left_hom A H B,
    braiding_tensor_right_hom H B A]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Iso.hom_inv_id, Category.comp_id] using h

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The B diagram face cancels inverse H/A against the positive target braid.
The remaining A/H crossing is positive even when V is not symmetric. -/
private theorem secondDiagramFace_rewireForProof (H A B : V) :
    (α_ A H B).inv ≫ ((β_ H A).inv ▷ B) ≫
        (α_ H A B).hom ≫ H ◁ (β_ A B).hom ≫
        (β_ H (B ⊗ A)).hom ≫ (α_ B A H).hom ≫
        B ◁ (β_ A H).hom ≫ (α_ B H A).inv =
      A ◁ (β_ H B).hom ≫ (β_ A (B ⊗ H)).hom := by
  have hSwap :
      (β_ (A ⊗ H) B).hom ≫ B ◁ (β_ A H).hom =
        ((β_ A H).hom ▷ B) ≫ (β_ (H ⊗ A) B).hom := by
    simpa only [tensorHom_id, id_tensorHom] using
      (braiding_naturality (β_ A H).hom (𝟙 B)).symm
  have hHex :
      (α_ A H B).inv ≫ ((β_ A H).hom ▷ B) ≫
          (β_ (H ⊗ A) B).hom ≫ (α_ B H A).inv =
        (β_ A (H ⊗ B)).hom ≫ ((β_ H B).hom ▷ A) := by
    rw [braiding_tensor_left_hom H A B,
      braiding_tensor_right_hom A H B]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = (α_ A H B).inv ≫ ((β_ H A).inv ▷ B) ≫
        ((β_ H A).hom ▷ B) ≫ (β_ (A ⊗ H) B).hom ≫
        B ◁ (β_ A H).hom ≫ (α_ B H A).inv := by
      simpa only [Category.assoc] using congrArg
        (fun z : (H ⊗ A) ⊗ B ⟶ B ⊗ (A ⊗ H) =>
          (α_ A H B).inv ≫ ((β_ H A).inv ▷ B) ≫ z ≫
            B ◁ (β_ A H).hom ≫ (α_ B H A).inv)
        (firstDiagramFace_rewireForProof H A B).symm
    _ = (α_ A H B).inv ≫
        (β_ (A ⊗ H) B).hom ≫ B ◁ (β_ A H).hom ≫
        (α_ B H A).inv := by
      simp only [← comp_whiskerRight_assoc,
        Iso.inv_hom_id, MonoidalCategory.id_whiskerRight,
        Category.id_comp]
    _ = (α_ A H B).inv ≫ ((β_ A H).hom ▷ B) ≫
        (β_ (H ⊗ A) B).hom ≫ (α_ B H A).inv := by
      simpa only [Category.assoc] using congrArg
        (fun z : (A ⊗ H) ⊗ B ⟶ B ⊗ (H ⊗ A) =>
          (α_ A H B).inv ≫ z ≫ (α_ B H A).inv) hSwap
    _ = (β_ A (H ⊗ B)).hom ≫ ((β_ H B).hom ▷ A) := hHex
    _ = _ := by
      simpa only [id_tensorHom, tensorHom_id] using
        (braiding_naturality (𝟙 A) (β_ H B).hom).symm


omit [MonoidalClosed V] [MonoidalCategory I] in
private abbrev rawCompositionForProof
    {W Z A B T C : V} (t : W ⊗ Z ⟶ T) (m : B ⊗ A ⟶ C) :
    (W ⊗ A) ⊗ (Z ⊗ B) ⟶ T ⊗ C :=
  tensorδ W Z A B ≫ (𝟙 (W ⊗ Z) ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ m)

omit [MonoidalClosed V] [MonoidalCategory I] in
private abbrev firstRelationInsertionForProof
    {W H Z A B T K C : V}
    (t : W ⊗ Z ⟶ T) (r : H ⟶ K) (m : B ⊗ A ⟶ C) :
    (W ⊗ (H ⊗ A)) ⊗ (Z ⊗ B) ⟶ T ⊗ (K ⊗ C) :=
  tensorδ W Z (H ⊗ A) B ≫
    (𝟙 (W ⊗ Z) ⊗ₘ (α_ H A B).hom) ≫
    (𝟙 (W ⊗ Z) ⊗ₘ H ◁ (β_ A B).hom) ≫
    (t ⊗ₘ (r ⊗ₘ m))

omit [MonoidalClosed V] [MonoidalCategory I] in
private abbrev secondRelationInsertionForProof
    {W H Z A B T K C : V}
    (t : W ⊗ Z ⟶ T) (r : H ⟶ K) (m : B ⊗ A ⟶ C) :
    (W ⊗ A) ⊗ (Z ⊗ (H ⊗ B)) ⟶ T ⊗ (K ⊗ C) :=
  tensorδ W Z A (H ⊗ B) ≫
    (𝟙 (W ⊗ Z) ⊗ₘ (α_ A H B).inv) ≫
    (𝟙 (W ⊗ Z) ⊗ₘ ((β_ H A).inv ▷ B)) ≫
    (𝟙 (W ⊗ Z) ⊗ₘ (α_ H A B).hom) ≫
    (𝟙 (W ⊗ Z) ⊗ₘ H ◁ (β_ A B).hom) ≫
    (t ⊗ₘ (r ⊗ₘ m))

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- Apply the already-derived whole index equation to the actual A weight face.
The index equation is a proof-local lemma input, never a constructor premise. -/
private theorem firstWeightFace_transportForProof
    {W W' H Z A B T T' K C : V}
    (p : W' ⊗ H ⟶ W) (t : W ⊗ Z ⟶ T) (t' : W' ⊗ Z ⟶ T')
    (r : H ⟶ K) (q : T' ⊗ K ⟶ T) (m : B ⊗ A ⟶ C)
    (hIndex : (p ⊗ₘ 𝟙 Z) ≫ t =
      firstWeightReorderForProof W' H Z ≫ (t' ⊗ₘ r) ≫ q) :
    (((α_ W' H A).inv ≫ (p ⊗ₘ 𝟙 A)) ⊗ₘ 𝟙 (Z ⊗ B)) ≫
        rawCompositionForProof t m =
      firstRelationInsertionForProof t' r m ≫
        (α_ T' K C).inv ≫ (q ⊗ₘ 𝟙 C) := by
  let sourceFront :
      (W' ⊗ (H ⊗ A)) ⊗ (Z ⊗ B) ⟶
        (((W' ⊗ H) ⊗ Z) ⊗ (B ⊗ A)) :=
    ((α_ W' H A).inv ⊗ₘ 𝟙 (Z ⊗ B)) ≫
      tensorδ (W' ⊗ H) Z A B ≫
      (𝟙 ((W' ⊗ H) ⊗ Z) ⊗ₘ (β_ A B).hom)
  let targetPrefix :
      (W' ⊗ (H ⊗ A)) ⊗ (Z ⊗ B) ⟶
        (((W' ⊗ Z) ⊗ H) ⊗ (B ⊗ A)) :=
    tensorδ W' Z (H ⊗ A) B ≫
      (𝟙 (W' ⊗ Z) ⊗ₘ (α_ H A B).hom) ≫
      (𝟙 (W' ⊗ Z) ⊗ₘ H ◁ (β_ A B).hom) ≫
      (α_ (W' ⊗ Z) H (B ⊗ A)).inv
  have hDelta :
      ((p ⊗ₘ 𝟙 A) ⊗ₘ 𝟙 (Z ⊗ B)) ≫ tensorδ W Z A B =
        tensorδ (W' ⊗ H) Z A B ≫
          ((p ⊗ₘ 𝟙 Z) ⊗ₘ 𝟙 (A ⊗ B)) := by
    simpa only [MonoidalCategory.id_tensorHom_id] using
      tensorDelta_naturalityForProof p (𝟙 Z) (𝟙 A) (𝟙 B)
  have hSplit :
      (((α_ W' H A).inv ≫ (p ⊗ₘ 𝟙 A)) ⊗ₘ 𝟙 (Z ⊗ B)) =
        ((α_ W' H A).inv ⊗ₘ 𝟙 (Z ⊗ B)) ≫
          ((p ⊗ₘ 𝟙 A) ⊗ₘ 𝟙 (Z ⊗ B)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hFront :
      (((α_ W' H A).inv ≫ (p ⊗ₘ 𝟙 A)) ⊗ₘ 𝟙 (Z ⊗ B)) ≫
          rawCompositionForProof t m =
        sourceFront ≫ (((p ⊗ₘ 𝟙 Z) ≫ t) ⊗ₘ m) := by
    dsimp only [rawCompositionForProof]
    rw [hSplit]
    have h := congrArg
      (fun f => ((α_ W' H A).inv ⊗ₘ 𝟙 (Z ⊗ B)) ≫ f ≫
        (𝟙 (W ⊗ Z) ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ m)) hDelta
    simpa only [sourceFront, tensorHom_comp_tensorHom_assoc,
      tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
      Category.assoc] using h
  have hRewire :
      sourceFront ≫ (firstWeightReorderForProof W' H Z ⊗ₘ 𝟙 (B ⊗ A)) =
        targetPrefix := by
    simpa only [sourceFront, targetPrefix, Category.assoc] using
      firstWeightFace_rewireForProof W' H Z A B
  have hTarget :
      firstRelationInsertionForProof t' r m ≫
          (α_ T' K C).inv ≫ (q ⊗ₘ 𝟙 C) =
        targetPrefix ≫ (((t' ⊗ₘ r) ≫ q) ⊗ₘ m) := by
    have h := congrArg
      (fun f =>
        (tensorδ W' Z (H ⊗ A) B ≫
          (𝟙 (W' ⊗ Z) ⊗ₘ (α_ H A B).hom) ≫
          (𝟙 (W' ⊗ Z) ⊗ₘ H ◁ (β_ A B).hom)) ≫
          f ≫ (q ⊗ₘ 𝟙 C))
      (associator_inv_naturality t' r m)
    simpa only [firstRelationInsertionForProof, targetPrefix,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, Category.assoc] using h
  calc
    _ = sourceFront ≫ (((p ⊗ₘ 𝟙 Z) ≫ t) ⊗ₘ m) := hFront
    _ = sourceFront ≫ (firstWeightReorderForProof W' H Z ⊗ₘ 𝟙 (B ⊗ A)) ≫
        (((t' ⊗ₘ r) ≫ q) ⊗ₘ m) := by
      rw [hIndex]
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.assoc]
    _ = targetPrefix ≫ (((t' ⊗ₘ r) ≫ q) ⊗ₘ m) := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ (((t' ⊗ₘ r) ≫ q) ⊗ₘ m)) hRewire
    _ = _ := hTarget.symm

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- Apply the actual full second index-weight equation to the B face. -/
private theorem secondWeightFace_transportForProof
    {W Z Z' H A B T T' K C : V}
    (p : Z' ⊗ H ⟶ Z) (t : W ⊗ Z ⟶ T) (t' : W ⊗ Z' ⟶ T')
    (r : H ⟶ K) (q : T' ⊗ K ⟶ T) (m : B ⊗ A ⟶ C)
    (hIndex : (𝟙 W ⊗ₘ p) ≫ t =
      (α_ W Z' H).inv ≫ (t' ⊗ₘ r) ≫ q) :
    (𝟙 (W ⊗ A) ⊗ₘ
        ((α_ Z' H B).inv ≫ (p ⊗ₘ 𝟙 B))) ≫
        rawCompositionForProof t m =
      secondRelationInsertionForProof t' r m ≫
        (α_ T' K C).inv ≫ (q ⊗ₘ 𝟙 C) := by
  let sourceFront :
      (W ⊗ A) ⊗ (Z' ⊗ (H ⊗ B)) ⟶
        ((W ⊗ (Z' ⊗ H)) ⊗ (B ⊗ A)) :=
    (𝟙 (W ⊗ A) ⊗ₘ (α_ Z' H B).inv) ≫
      tensorδ W (Z' ⊗ H) A B ≫
      (𝟙 (W ⊗ (Z' ⊗ H)) ⊗ₘ (β_ A B).hom)
  let targetPrefix :
      (W ⊗ A) ⊗ (Z' ⊗ (H ⊗ B)) ⟶
        (((W ⊗ Z') ⊗ H) ⊗ (B ⊗ A)) :=
    tensorδ W Z' A (H ⊗ B) ≫
      (𝟙 (W ⊗ Z') ⊗ₘ (α_ A H B).inv) ≫
      (𝟙 (W ⊗ Z') ⊗ₘ ((β_ H A).inv ▷ B)) ≫
      (𝟙 (W ⊗ Z') ⊗ₘ (α_ H A B).hom) ≫
      (𝟙 (W ⊗ Z') ⊗ₘ H ◁ (β_ A B).hom) ≫
      (α_ (W ⊗ Z') H (B ⊗ A)).inv
  have hDelta :
      (𝟙 (W ⊗ A) ⊗ₘ (p ⊗ₘ 𝟙 B)) ≫ tensorδ W Z A B =
        tensorδ W (Z' ⊗ H) A B ≫
          ((𝟙 W ⊗ₘ p) ⊗ₘ 𝟙 (A ⊗ B)) := by
    simpa only [MonoidalCategory.id_tensorHom_id] using
      tensorDelta_naturalityForProof (𝟙 W) p (𝟙 A) (𝟙 B)
  have hSplit :
      (𝟙 (W ⊗ A) ⊗ₘ ((α_ Z' H B).inv ≫ (p ⊗ₘ 𝟙 B))) =
        (𝟙 (W ⊗ A) ⊗ₘ (α_ Z' H B).inv) ≫
          (𝟙 (W ⊗ A) ⊗ₘ (p ⊗ₘ 𝟙 B)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hFront :
      (𝟙 (W ⊗ A) ⊗ₘ ((α_ Z' H B).inv ≫ (p ⊗ₘ 𝟙 B))) ≫
          rawCompositionForProof t m =
        sourceFront ≫ (((𝟙 W ⊗ₘ p) ≫ t) ⊗ₘ m) := by
    dsimp only [rawCompositionForProof]
    rw [hSplit]
    have h := congrArg
      (fun f => (𝟙 (W ⊗ A) ⊗ₘ (α_ Z' H B).inv) ≫ f ≫
        (𝟙 (W ⊗ Z) ⊗ₘ (β_ A B).hom) ≫ (t ⊗ₘ m)) hDelta
    simpa only [sourceFront, tensorHom_comp_tensorHom_assoc,
      tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
      Category.assoc] using h
  have hRewire :
      sourceFront ≫ ((α_ W Z' H).inv ⊗ₘ 𝟙 (B ⊗ A)) = targetPrefix := by
    simpa only [sourceFront, targetPrefix, Category.assoc] using
      secondWeightFace_rewireForProof W Z' H A B
  have hTarget :
      secondRelationInsertionForProof t' r m ≫
          (α_ T' K C).inv ≫ (q ⊗ₘ 𝟙 C) =
        targetPrefix ≫ (((t' ⊗ₘ r) ≫ q) ⊗ₘ m) := by
    have h := congrArg
      (fun f =>
        (tensorδ W Z' A (H ⊗ B) ≫
          (𝟙 (W ⊗ Z') ⊗ₘ (α_ A H B).inv) ≫
          (𝟙 (W ⊗ Z') ⊗ₘ ((β_ H A).inv ▷ B)) ≫
          (𝟙 (W ⊗ Z') ⊗ₘ (α_ H A B).hom) ≫
          (𝟙 (W ⊗ Z') ⊗ₘ H ◁ (β_ A B).hom)) ≫
          f ≫ (q ⊗ₘ 𝟙 C))
      (associator_inv_naturality t' r m)
    simpa only [secondRelationInsertionForProof, targetPrefix,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, Category.assoc] using h
  calc
    _ = sourceFront ≫ (((𝟙 W ⊗ₘ p) ≫ t) ⊗ₘ m) := hFront
    _ = sourceFront ≫ ((α_ W Z' H).inv ⊗ₘ 𝟙 (B ⊗ A)) ≫
        (((t' ⊗ₘ r) ≫ q) ⊗ₘ m) := by
      rw [hIndex]
      simp only [tensorHom_comp_tensorHom, Category.id_comp]
    _ = targetPrefix ≫ (((t' ⊗ₘ r) ≫ q) ⊗ₘ m) := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ (((t' ⊗ₘ r) ≫ q) ⊗ₘ m)) hRewire
    _ = _ := hTarget.symm


omit [MonoidalClosed V] [MonoidalCategory I] in
/-- Convert the actual first coefficient square into the entire A diagram face. -/
private theorem firstDiagramFace_transportForProof
    {W Z H A A' B T K C C' : V}
    (t : W ⊗ Z ⟶ T) (r : H ⟶ K)
    (p : A ⊗ H ⟶ A') (m : B ⊗ A ⟶ C) (m' : B ⊗ A' ⟶ C')
    (q : C ⊗ K ⟶ C')
    (hCoefficient : (m ⊗ₘ r) ≫ q =
      (α_ B A H).hom ≫ B ◁ p ≫ m') :
    ((W ◁ ((β_ H A).hom ≫ p)) ⊗ₘ 𝟙 (Z ⊗ B)) ≫
        rawCompositionForProof t m' =
      firstRelationInsertionForProof t r m ≫
        T ◁ ((β_ K C).hom ≫ q) := by
  let leftCoefficient : (H ⊗ A) ⊗ B ⟶ C' :=
    (((β_ H A).hom ≫ p) ⊗ₘ 𝟙 B) ≫ (β_ A' B).hom ≫ m'
  let rightCoefficient : (H ⊗ A) ⊗ B ⟶ C' :=
    (α_ H A B).hom ≫ H ◁ (β_ A B).hom ≫
      (r ⊗ₘ m) ≫ (β_ K C).hom ≫ q
  have hMove :
      (β_ (A ⊗ H) B).hom ≫ B ◁ p =
        (p ⊗ₘ 𝟙 B) ≫ (β_ A' B).hom := by
    simpa only [id_tensorHom] using
      (braiding_naturality p (𝟙 B)).symm
  have hCoefficientRewire : rightCoefficient = leftCoefficient := by
    calc
      _ = (α_ H A B).hom ≫ H ◁ (β_ A B).hom ≫
          (β_ H (B ⊗ A)).hom ≫ (m ⊗ₘ r) ≫ q := by
        dsimp only [rightCoefficient]
        rw [braiding_naturality_assoc]
      _ = (α_ H A B).hom ≫ H ◁ (β_ A B).hom ≫
          (β_ H (B ⊗ A)).hom ≫ (α_ B A H).hom ≫ B ◁ p ≫ m' := by
        rw [hCoefficient]
      _ = ((β_ H A).hom ▷ B) ≫
          (β_ (A ⊗ H) B).hom ≫ B ◁ p ≫ m' := by
        simpa only [Category.assoc] using congrArg
          (fun f => f ≫ B ◁ p ≫ m')
          (firstDiagramFace_rewireForProof H A B).symm
      _ = ((β_ H A).hom ▷ B) ≫
          (p ⊗ₘ 𝟙 B) ≫ (β_ A' B).hom ≫ m' := by
        simpa only [Category.assoc] using congrArg
          (fun f => ((β_ H A).hom ▷ B) ≫ f ≫ m') hMove
      _ = _ := by
        simp only [leftCoefficient, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc, Category.comp_id]
  have hDelta :
      ((W ◁ ((β_ H A).hom ≫ p)) ⊗ₘ 𝟙 (Z ⊗ B)) ≫
          tensorδ W Z A' B =
        tensorδ W Z (H ⊗ A) B ≫
          (𝟙 (W ⊗ Z) ⊗ₘ (((β_ H A).hom ≫ p) ⊗ₘ 𝟙 B)) := by
    simpa only [id_tensorHom, MonoidalCategory.id_tensorHom_id,
      MonoidalCategory.whiskerLeft_id] using
      tensorDelta_naturalityForProof (𝟙 W) (𝟙 Z)
        ((β_ H A).hom ≫ p) (𝟙 B)
  have hLeft :
      ((W ◁ ((β_ H A).hom ≫ p)) ⊗ₘ 𝟙 (Z ⊗ B)) ≫
          rawCompositionForProof t m' =
        tensorδ W Z (H ⊗ A) B ≫ (t ⊗ₘ leftCoefficient) := by
    have h := congrArg
      (fun f => f ≫ (𝟙 (W ⊗ Z) ⊗ₘ (β_ A' B).hom) ≫ (t ⊗ₘ m')) hDelta
    simpa only [rawCompositionForProof, leftCoefficient,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, Category.assoc] using h
  have hRight :
      firstRelationInsertionForProof t r m ≫
          T ◁ ((β_ K C).hom ≫ q) =
        tensorδ W Z (H ⊗ A) B ≫ (t ⊗ₘ rightCoefficient) := by
    simp only [firstRelationInsertionForProof, rightCoefficient,
      ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
      Category.assoc]
  rw [hLeft, hRight]
  exact congrArg
    (fun f => tensorδ W Z (H ⊗ A) B ≫ (t ⊗ₘ f)) hCoefficientRewire.symm

omit [MonoidalClosed V] [MonoidalCategory I] in
/-- The second full coefficient square supplies the B diagram face.
No replacement of inverse H/A by inverse A/H is used. -/
private theorem secondDiagramFace_transportForProof
    {W Z H A B B' T K C C' : V}
    (t : W ⊗ Z ⟶ T) (r : H ⟶ K)
    (p : B ⊗ H ⟶ B') (m : B ⊗ A ⟶ C) (m' : B' ⊗ A ⟶ C')
    (q : C ⊗ K ⟶ C')
    (hCoefficient : (m ⊗ₘ r) ≫ q =
      (α_ B A H).hom ≫ B ◁ (β_ A H).hom ≫
        (α_ B H A).inv ≫ (p ▷ A) ≫ m') :
    (𝟙 (W ⊗ A) ⊗ₘ Z ◁ ((β_ H B).hom ≫ p)) ≫
        rawCompositionForProof t m' =
      secondRelationInsertionForProof t r m ≫
        T ◁ ((β_ K C).hom ≫ q) := by
  let leftCoefficient : A ⊗ (H ⊗ B) ⟶ C' :=
    A ◁ ((β_ H B).hom ≫ p) ≫ (β_ A B').hom ≫ m'
  let rightCoefficient : A ⊗ (H ⊗ B) ⟶ C' :=
    (α_ A H B).inv ≫ ((β_ H A).inv ▷ B) ≫
      (α_ H A B).hom ≫ H ◁ (β_ A B).hom ≫
      (r ⊗ₘ m) ≫ (β_ K C).hom ≫ q
  have hMove :
      (β_ A (B ⊗ H)).hom ≫ (p ▷ A) =
        A ◁ p ≫ (β_ A B').hom := by
    simpa only [id_tensorHom, tensorHom_id] using
      (braiding_naturality (𝟙 A) p).symm
  have hCoefficientRewire : rightCoefficient = leftCoefficient := by
    calc
      _ = (α_ A H B).inv ≫ ((β_ H A).inv ▷ B) ≫
          (α_ H A B).hom ≫ H ◁ (β_ A B).hom ≫
          (β_ H (B ⊗ A)).hom ≫ (m ⊗ₘ r) ≫ q := by
        dsimp only [rightCoefficient]
        rw [braiding_naturality_assoc]
      _ = (α_ A H B).inv ≫ ((β_ H A).inv ▷ B) ≫
          (α_ H A B).hom ≫ H ◁ (β_ A B).hom ≫
          (β_ H (B ⊗ A)).hom ≫ (α_ B A H).hom ≫
          B ◁ (β_ A H).hom ≫ (α_ B H A).inv ≫ (p ▷ A) ≫ m' := by
        rw [hCoefficient]
      _ = A ◁ (β_ H B).hom ≫
          (β_ A (B ⊗ H)).hom ≫ (p ▷ A) ≫ m' := by
        simpa only [Category.assoc] using congrArg
          (fun f => f ≫ (p ▷ A) ≫ m')
          (secondDiagramFace_rewireForProof H A B)
      _ = A ◁ (β_ H B).hom ≫ A ◁ p ≫ (β_ A B').hom ≫ m' := by
        simpa only [Category.assoc] using congrArg
          (fun f => A ◁ (β_ H B).hom ≫ f ≫ m') hMove
      _ = _ := by
        simp only [leftCoefficient, MonoidalCategory.whiskerLeft_comp,
          Category.assoc]
  have hDelta :
      (𝟙 (W ⊗ A) ⊗ₘ Z ◁ ((β_ H B).hom ≫ p)) ≫
          tensorδ W Z A B' =
        tensorδ W Z A (H ⊗ B) ≫
          (𝟙 (W ⊗ Z) ⊗ₘ A ◁ ((β_ H B).hom ≫ p)) := by
    simpa only [id_tensorHom, MonoidalCategory.id_tensorHom_id,
      MonoidalCategory.whiskerLeft_id] using
      tensorDelta_naturalityForProof (𝟙 W) (𝟙 Z) (𝟙 A)
        ((β_ H B).hom ≫ p)
  have hLeft :
      (𝟙 (W ⊗ A) ⊗ₘ Z ◁ ((β_ H B).hom ≫ p)) ≫
          rawCompositionForProof t m' =
        tensorδ W Z A (H ⊗ B) ≫ (t ⊗ₘ leftCoefficient) := by
    have h := congrArg
      (fun f => f ≫ (𝟙 (W ⊗ Z) ⊗ₘ (β_ A B').hom) ≫ (t ⊗ₘ m')) hDelta
    simpa only [rawCompositionForProof, leftCoefficient, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id, Category.assoc] using h
  have hRight :
      secondRelationInsertionForProof t r m ≫
          T ◁ ((β_ K C).hom ≫ q) =
        tensorδ W Z A (H ⊗ B) ≫ (t ⊗ₘ rightCoefficient) := by
    simp only [secondRelationInsertionForProof, rightCoefficient,
      ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
      Category.assoc]
  rw [hLeft, hRight]
  exact congrArg
    (fun f => tensorδ W Z A (H ⊗ B) ≫ (t ⊗ₘ f)) hCoefficientRewire.symm

/-- The complete A-relation insertion into the target operator coend relation.
This proof-local map retains the entire I(a,a') parameter. -/
private def compositionRelationOneMap
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n k l a a' b : I) :
    (weightedCoend.relations (weight d n k) S (a, a')) ⊗
        (weightedCoend.objects (weight d k l) S b) ⟶
      weightedCoend.relations (weight d n l) S (b ⊗ a, b ⊗ a') :=
  MonoidalCategory.tensorδ ((a' ⊗ n) ⟶[V] k) ((b ⊗ k) ⟶[V] l)
      ((a ⟶[V] a') ⊗ S.obj a) (S.obj b) ≫
    (𝟙 (((a' ⊗ n) ⟶[V] k) ⊗ ((b ⊗ k) ⟶[V] l)) ⊗ₘ
      (α_ (a ⟶[V] a') (S.obj a) (S.obj b)).hom) ≫
    (𝟙 (((a' ⊗ n) ⟶[V] k) ⊗ ((b ⊗ k) ⟶[V] l)) ⊗ₘ
      ((a ⟶[V] a') ◁ (β_ (S.obj a) (S.obj b)).hom)) ≫
    (indexGenerator d n k l a' b ⊗ₘ
      (((λ_ (a ⟶[V] a')).inv ≫
        (eId V b ⊗ₘ 𝟙 (a ⟶[V] a')) ≫ d.tensorMap b b a a') ⊗ₘ L.mu b a))

/-- The complete B-relation insertion into the target operator coend relation.
The mixed crossing is inverse and the coefficient crossing remains positive. -/
private def compositionRelationTwoMap
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n k l a b b' : I) :
    (weightedCoend.objects (weight d n k) S a) ⊗
        (weightedCoend.relations (weight d k l) S (b, b')) ⟶
      weightedCoend.relations (weight d n l) S (b ⊗ a, b' ⊗ a) :=
  MonoidalCategory.tensorδ ((a ⊗ n) ⟶[V] k) ((b' ⊗ k) ⟶[V] l)
      (S.obj a) ((b ⟶[V] b') ⊗ S.obj b) ≫
    (𝟙 (((a ⊗ n) ⟶[V] k) ⊗ ((b' ⊗ k) ⟶[V] l)) ⊗ₘ
      (α_ (S.obj a) (b ⟶[V] b') (S.obj b)).inv) ≫
    (𝟙 (((a ⊗ n) ⟶[V] k) ⊗ ((b' ⊗ k) ⟶[V] l)) ⊗ₘ
      ((β_ (b ⟶[V] b') (S.obj a)).inv ▷ S.obj b)) ≫
    (𝟙 (((a ⊗ n) ⟶[V] k) ⊗ ((b' ⊗ k) ⟶[V] l)) ⊗ₘ
      (α_ (b ⟶[V] b') (S.obj a) (S.obj b)).hom) ≫
    (𝟙 (((a ⊗ n) ⟶[V] k) ⊗ ((b' ⊗ k) ⟶[V] l)) ⊗ₘ
      ((b ⟶[V] b') ◁ (β_ (S.obj a) (S.obj b)).hom)) ≫
    (indexGenerator d n k l a b' ⊗ₘ
      ((fixedRightTensor d a).map b b' ⊗ₘ L.mu b a))


private abbrev operatorWeightFaceForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (n k a a' : I) :
    weightedCoend.relations (weight d n k) S (a, a') ⟶
      weightedCoend.objects (weight d n k) S a :=
  (α_ ((a' ⊗ n) ⟶[V] k) (a ⟶[V] a') (S.obj a)).inv ≫
    (MonoidalClosed.uncurry ((weight d n k).map (op a') (op a)) ⊗ₘ
      𝟙 (S.obj a))

private abbrev operatorDiagramFaceForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (n k a a' : I) :
    weightedCoend.relations (weight d n k) S (a, a') ⟶
      weightedCoend.objects (weight d n k) S a' :=
  ((a' ⊗ n) ⟶[V] k) ◁
    ((β_ (a ⟶[V] a') (S.obj a)).hom ≫
      MonoidalClosed.uncurry (S.map a a'))

private abbrev rawOperatorGeneratorForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n k l a b : I) :
    weightedCoend.objects (weight d n k) S a ⊗
        weightedCoend.objects (weight d k l) S b ⟶
      weightedCoend.objects (weight d n l) S (b ⊗ a) :=
  rawCompositionForProof (indexGenerator d n k l a b) (L.mu b a)

private theorem compositionRelationOneMap_genericForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n k l a a' b : I) :
    compositionRelationOneMap d S L n k l a a' b =
      firstRelationInsertionForProof (indexGenerator d n k l a' b)
        ((fixedLeftTensorForProof d b).map a a') (L.mu b a) := by
  exact congrArg
    (fun f : (a ⟶[V] a') ⟶ ((b ⊗ a) ⟶[V] (b ⊗ a')) =>
      firstRelationInsertionForProof (indexGenerator d n k l a' b) f (L.mu b a))
    (fixedLeftTensor_mapForProof d b a a').symm


private theorem compositionRelationTwoMap_genericForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n k l a b b' : I) :
    compositionRelationTwoMap d S L n k l a b b' =
      secondRelationInsertionForProof (indexGenerator d n k l a b')
        ((fixedRightTensor d a).map b b') (L.mu b a) := by
  rfl

private theorem coefficientFirstSquareForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (b a a' : I) :
    (L.mu b a ⊗ₘ (fixedLeftTensorForProof d b).map a a') ≫
        MonoidalClosed.uncurry (S.map (b ⊗ a) (b ⊗ a')) =
      (α_ (S.obj b) (S.obj a) (a ⟶[V] a')).hom ≫
        S.obj b ◁ MonoidalClosed.uncurry (S.map a a') ≫ L.mu b a' := by
  let H : V := a ⟶[V] a'
  let K : V := (b ⊗ a) ⟶[V] (b ⊗ a')
  let P : V := S.obj b ⊗ S.obj a
  let Q : V := S.obj (b ⊗ a)
  let Q' : V := S.obj (b ⊗ a')
  let r : H ⟶ K := (fixedLeftTensorForProof d b).map a a'
  let r₀ : H ⟶ K :=
    ((λ_ H).inv ≫ (eId V b ⊗ₘ 𝟙 H)) ≫ d.tensorMap b b a a'
  have hMap : r = r₀ := by
    exact (fixedLeftTensor_mapForProof d b a a').trans
      (Category.assoc (λ_ H).inv (eId V b ⊗ₘ 𝟙 H)
        (d.tensorMap b b a a')).symm
  have hArgs := congrArg
    (fun f : H ⟶ K => f ≫ S.map (b ⊗ a) (b ⊗ a')) hMap
  calc
    _ = (L.mu b a ▷ H) ≫ Q ◁ r ≫
        MonoidalClosed.uncurry (S.map (b ⊗ a) (b ⊗ a')) := by
      exact (congrArg
        (fun f : P ⊗ H ⟶ Q ⊗ K =>
          f ≫ MonoidalClosed.uncurry (S.map (b ⊗ a) (b ⊗ a')))
        (tensorHom_def (L.mu b a) r)).trans
        (Category.assoc (L.mu b a ▷ H) (Q ◁ r)
          (MonoidalClosed.uncurry (S.map (b ⊗ a) (b ⊗ a'))))
    _ = (L.mu b a ▷ H) ≫
        MonoidalClosed.uncurry (r ≫ S.map (b ⊗ a) (b ⊗ a')) :=
      congrArg
        (fun f : Q ⊗ H ⟶ Q' => (L.mu b a ▷ H) ≫ f)
        (MonoidalClosed.uncurry_natural_left (C := V) r
          (S.map (b ⊗ a) (b ⊗ a'))).symm
    _ = (L.mu b a ▷ H) ≫
        MonoidalClosed.uncurry (r₀ ≫ S.map (b ⊗ a) (b ⊗ a')) :=
      congrArg
        (fun f : H ⟶ (ihom Q).obj Q' =>
          (L.mu b a ▷ H) ≫ MonoidalClosed.uncurry f) hArgs
    _ = (L.mu b a ▷ H) ≫ MonoidalClosed.uncurry
        (((λ_ H).inv ≫ (eId V b ⊗ₘ 𝟙 H) ≫ d.tensorMap b b a a') ≫
          S.map (b ⊗ a) (b ⊗ a')) :=
      congrArg
        (fun f : H ⟶ (ihom Q).obj Q' =>
          (L.mu b a ▷ H) ≫ MonoidalClosed.uncurry f)
        (congrArg
          (fun f : H ⟶ K => f ≫ S.map (b ⊗ a) (b ⊗ a'))
          (Category.assoc (λ_ H).inv (eId V b ⊗ₘ 𝟙 H)
            (d.tensorMap b b a a')))
    _ = (α_ (S.obj b) (S.obj a) H).hom ≫
        S.obj b ◁ MonoidalClosed.uncurry (S.map a a') ≫ L.mu b a' :=
      (tensorator_left_fixed_action d S L b a a').symm


private theorem coefficientSecondSquareForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (b b' a : I) :
    (L.mu b a ⊗ₘ (fixedRightTensor d a).map b b') ≫
        MonoidalClosed.uncurry (S.map (b ⊗ a) (b' ⊗ a)) =
      (α_ (S.obj b) (S.obj a) (b ⟶[V] b')).hom ≫
        S.obj b ◁ (β_ (S.obj a) (b ⟶[V] b')).hom ≫
        (α_ (S.obj b) (b ⟶[V] b') (S.obj a)).inv ≫
        (MonoidalClosed.uncurry (S.map b b') ▷ S.obj a) ≫ L.mu b' a := by
  let H : V := b ⟶[V] b'
  let K : V := (b ⊗ a) ⟶[V] (b' ⊗ a)
  let P : V := S.obj b ⊗ S.obj a
  let Q : V := S.obj (b ⊗ a)
  let Q' : V := S.obj (b' ⊗ a)
  let r : H ⟶ K := (fixedRightTensor d a).map b b'
  calc
    _ = (L.mu b a ▷ H) ≫ Q ◁ r ≫
        MonoidalClosed.uncurry (S.map (b ⊗ a) (b' ⊗ a)) := by
      exact (congrArg
        (fun f : P ⊗ H ⟶ Q ⊗ K =>
          f ≫ MonoidalClosed.uncurry (S.map (b ⊗ a) (b' ⊗ a)))
        (tensorHom_def (L.mu b a) r)).trans
        (Category.assoc (L.mu b a ▷ H) (Q ◁ r)
          (MonoidalClosed.uncurry (S.map (b ⊗ a) (b' ⊗ a))))
    _ = (L.mu b a ▷ H) ≫
        MonoidalClosed.uncurry (r ≫ S.map (b ⊗ a) (b' ⊗ a)) :=
      congrArg
        (fun f : Q ⊗ H ⟶ Q' => (L.mu b a ▷ H) ≫ f)
        (MonoidalClosed.uncurry_natural_left (C := V) r
          (S.map (b ⊗ a) (b' ⊗ a))).symm
    _ = _ := (tensorator_right_fixed_action d S L b b' a).symm


/-- The actual A weight face reaches the first face of the original target relation. -/
private theorem compositionFirstWeightFaceForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n k l a a' b : I) :
    (operatorWeightFaceForProof d S n k a a' ⊗ₘ
        𝟙 (weightedCoend.objects (weight d k l) S b)) ≫
        rawOperatorGeneratorForProof d S L n k l a b =
      compositionRelationOneMap d S L n k l a a' b ≫
        operatorWeightFaceForProof d S n l (b ⊗ a) (b ⊗ a') := by
  have h :=
    firstWeightFace_transportForProof
      (W := (a ⊗ n) ⟶[V] k) (W' := (a' ⊗ n) ⟶[V] k)
      (H := a ⟶[V] a') (Z := (b ⊗ k) ⟶[V] l)
      (A := S.obj a) (B := S.obj b)
      (T := ((b ⊗ a) ⊗ n) ⟶[V] l) (T' := ((b ⊗ a') ⊗ n) ⟶[V] l)
      (K := (b ⊗ a) ⟶[V] (b ⊗ a')) (C := S.obj (b ⊗ a))
      (MonoidalClosed.uncurry ((weight d n k).map (op a') (op a)))
      (indexGenerator d n k l a b) (indexGenerator d n k l a' b)
      ((fixedLeftTensorForProof d b).map a a')
      (MonoidalClosed.uncurry
        ((weight d n l).map (op (b ⊗ a')) (op (b ⊗ a))))
      (L.mu b a) (indexGenerator_firstWeightForProof d n k l a a' b)
  exact h.trans (congrArg
    (fun f : (weightedCoend.relations (weight d n k) S (a, a')) ⊗
          weightedCoend.objects (weight d k l) S b ⟶
        weightedCoend.relations (weight d n l) S (b ⊗ a, b ⊗ a') =>
      f ≫ operatorWeightFaceForProof d S n l (b ⊗ a) (b ⊗ a'))
    (compositionRelationOneMap_genericForProof d S L n k l a a' b).symm)


/-- The actual A diagram face reaches the second face of the same full target relation. -/
private theorem compositionFirstDiagramFaceForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n k l a a' b : I) :
    (operatorDiagramFaceForProof d S n k a a' ⊗ₘ
        𝟙 (weightedCoend.objects (weight d k l) S b)) ≫
        rawOperatorGeneratorForProof d S L n k l a' b =
      compositionRelationOneMap d S L n k l a a' b ≫
        operatorDiagramFaceForProof d S n l (b ⊗ a) (b ⊗ a') := by
  have h :=
    firstDiagramFace_transportForProof
      (W := (a' ⊗ n) ⟶[V] k) (Z := (b ⊗ k) ⟶[V] l)
      (H := a ⟶[V] a') (A := S.obj a) (A' := S.obj a') (B := S.obj b)
      (T := ((b ⊗ a') ⊗ n) ⟶[V] l) (K := (b ⊗ a) ⟶[V] (b ⊗ a'))
      (C := S.obj (b ⊗ a)) (C' := S.obj (b ⊗ a'))
      (indexGenerator d n k l a' b) ((fixedLeftTensorForProof d b).map a a')
      (MonoidalClosed.uncurry (S.map a a')) (L.mu b a) (L.mu b a')
      (MonoidalClosed.uncurry (S.map (b ⊗ a) (b ⊗ a')))
      (coefficientFirstSquareForProof d S L b a a')
  exact h.trans (congrArg
    (fun f : (weightedCoend.relations (weight d n k) S (a, a')) ⊗
          weightedCoend.objects (weight d k l) S b ⟶
        weightedCoend.relations (weight d n l) S (b ⊗ a, b ⊗ a') =>
      f ≫ operatorDiagramFaceForProof d S n l (b ⊗ a) (b ⊗ a'))
    (compositionRelationOneMap_genericForProof d S L n k l a a' b).symm)


/-- The actual B weight face reaches the first face of its original target relation. -/
private theorem compositionSecondWeightFaceForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n k l a b b' : I) :
    (𝟙 (weightedCoend.objects (weight d n k) S a) ⊗ₘ
        operatorWeightFaceForProof d S k l b b') ≫
        rawOperatorGeneratorForProof d S L n k l a b =
      compositionRelationTwoMap d S L n k l a b b' ≫
        operatorWeightFaceForProof d S n l (b ⊗ a) (b' ⊗ a) := by
  have h :=
    secondWeightFace_transportForProof
      (W := (a ⊗ n) ⟶[V] k) (Z := (b ⊗ k) ⟶[V] l)
      (Z' := (b' ⊗ k) ⟶[V] l) (H := b ⟶[V] b')
      (A := S.obj a) (B := S.obj b)
      (T := ((b ⊗ a) ⊗ n) ⟶[V] l) (T' := ((b' ⊗ a) ⊗ n) ⟶[V] l)
      (K := (b ⊗ a) ⟶[V] (b' ⊗ a)) (C := S.obj (b ⊗ a))
      (MonoidalClosed.uncurry ((weight d k l).map (op b') (op b)))
      (indexGenerator d n k l a b) (indexGenerator d n k l a b')
      ((fixedRightTensor d a).map b b')
      (MonoidalClosed.uncurry
        ((weight d n l).map (op (b' ⊗ a)) (op (b ⊗ a))))
      (L.mu b a) (indexGenerator_secondWeightForProof d n k l a b b')
  exact h.trans (congrArg
    (fun f : weightedCoend.objects (weight d n k) S a ⊗
          weightedCoend.relations (weight d k l) S (b, b') ⟶
        weightedCoend.relations (weight d n l) S (b ⊗ a, b' ⊗ a) =>
      f ≫ operatorWeightFaceForProof d S n l (b ⊗ a) (b' ⊗ a))
    (compositionRelationTwoMap_genericForProof d S L n k l a b b').symm)


/-- The actual B diagram face reaches the other face with the full right tensor map. -/
private theorem compositionSecondDiagramFaceForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n k l a b b' : I) :
    (𝟙 (weightedCoend.objects (weight d n k) S a) ⊗ₘ
        operatorDiagramFaceForProof d S k l b b') ≫
        rawOperatorGeneratorForProof d S L n k l a b' =
      compositionRelationTwoMap d S L n k l a b b' ≫
        operatorDiagramFaceForProof d S n l (b ⊗ a) (b' ⊗ a) := by
  have h :=
    secondDiagramFace_transportForProof
      (W := (a ⊗ n) ⟶[V] k) (Z := (b' ⊗ k) ⟶[V] l)
      (H := b ⟶[V] b') (A := S.obj a) (B := S.obj b) (B' := S.obj b')
      (T := ((b' ⊗ a) ⊗ n) ⟶[V] l) (K := (b ⊗ a) ⟶[V] (b' ⊗ a))
      (C := S.obj (b ⊗ a)) (C' := S.obj (b' ⊗ a))
      (indexGenerator d n k l a b') ((fixedRightTensor d a).map b b')
      (MonoidalClosed.uncurry (S.map b b')) (L.mu b a) (L.mu b' a)
      (MonoidalClosed.uncurry (S.map (b ⊗ a) (b' ⊗ a)))
      (coefficientSecondSquareForProof d S L b b' a)
  exact h.trans (congrArg
    (fun f : weightedCoend.objects (weight d n k) S a ⊗
          weightedCoend.relations (weight d k l) S (b, b') ⟶
        weightedCoend.relations (weight d n l) S (b ⊗ a, b' ⊗ a) =>
      f ≫ operatorDiagramFaceForProof d S n l (b ⊗ a) (b' ⊗ a))
    (compositionRelationTwoMap_genericForProof d S L n k l a b b').symm)


section TargetCoend

variable (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (n k l : I)

variable [HasCoproduct (weightedCoend.relations (weight d n l) S)]
  [HasCoproduct (weightedCoend.objects (weight d n l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n l) S)
    (weightedCoend.rightMap (weight d n l) S)]

private theorem operatorFaces_conditionForProof (c c' : I) :
    operatorWeightFaceForProof d S n l c c' ≫ weightedCoend.ι (weight d n l) S c =
      operatorDiagramFaceForProof d S n l c c' ≫
        weightedCoend.ι (weight d n l) S c' := by
  exact weightedCoend.condition (weight d n l) S c c'

private theorem compositionGenerator_rawForProof (a b : I) :
    compositionGenerator d S L n k l a b =
      rawOperatorGeneratorForProof d S L n k l a b ≫
        weightedCoend.ι (weight d n l) S (b ⊗ a) := by
  let W : V := (a ⊗ n) ⟶[V] k
  let Z : V := (b ⊗ k) ⟶[V] l
  let U : V := (((b ⊗ a) ⊗ n) ⟶[V] l) ⊗ S.obj (b ⊗ a)
  let delta : ((W ⊗ S.obj a) ⊗ (Z ⊗ S.obj b)) ⟶
      (W ⊗ Z) ⊗ (S.obj a ⊗ S.obj b) := tensorδ W Z (S.obj a) (S.obj b)
  let cross : ((W ⊗ Z) ⊗ (S.obj a ⊗ S.obj b)) ⟶
      (W ⊗ Z) ⊗ (S.obj b ⊗ S.obj a) :=
    𝟙 (W ⊗ Z) ⊗ₘ (β_ (S.obj a) (S.obj b)).hom
  let action : ((W ⊗ Z) ⊗ (S.obj b ⊗ S.obj a)) ⟶ U :=
    indexGenerator d n k l a b ⊗ₘ L.mu b a
  let gen : U ⟶ Hom d S n l := weightedCoend.ι (weight d n l) S (b ⊗ a)
  exact (congrArg (fun f => delta ≫ f)
    (Category.assoc cross action gen).symm).trans
    (Category.assoc delta (cross ≫ action) gen).symm

/-- Both literal A relation faces give a genuine tensor-preserved coend balance. -/
private theorem compositionGenerator_firstBalancedForProof (b : I) :
    weightedCoend.Mapped.Balanced (weight d n k) S
      (tensorRight (weightedCoend.objects (weight d k l) S b))
      (fun a => compositionGenerator d S L n k l a b) := by
  intro a a'
  let U : V := weightedCoend.objects (weight d k l) S b
  let q := compositionRelationOneMap d S L n k l a a' b
  have hTarget := congrArg (fun f => q ≫ f)
    (operatorFaces_conditionForProof d S n l (b ⊗ a) (b ⊗ a'))
  change (operatorWeightFaceForProof d S n k a a' ▷ U) ≫
      compositionGenerator d S L n k l a b =
    (operatorDiagramFaceForProof d S n k a a' ▷ U) ≫
      compositionGenerator d S L n k l a' b
  calc
    _ = ((operatorWeightFaceForProof d S n k a a' ⊗ₘ 𝟙 U) ≫
          rawOperatorGeneratorForProof d S L n k l a b) ≫
        weightedCoend.ι (weight d n l) S (b ⊗ a) := by
      simp only [compositionGenerator_rawForProof, tensorHom_id,
        Category.assoc]
    _ = (q ≫ operatorWeightFaceForProof d S n l (b ⊗ a) (b ⊗ a')) ≫
        weightedCoend.ι (weight d n l) S (b ⊗ a) := by
      simpa only [q, U, Category.assoc] using congrArg
        (fun f => f ≫ weightedCoend.ι (weight d n l) S (b ⊗ a))
        (compositionFirstWeightFaceForProof d S L n k l a a' b)
    _ = (q ≫ operatorDiagramFaceForProof d S n l (b ⊗ a) (b ⊗ a')) ≫
        weightedCoend.ι (weight d n l) S (b ⊗ a') := by
      simpa only [Category.assoc] using hTarget
    _ = ((operatorDiagramFaceForProof d S n k a a' ⊗ₘ 𝟙 U) ≫
          rawOperatorGeneratorForProof d S L n k l a' b) ≫
        weightedCoend.ι (weight d n l) S (b ⊗ a') := by
      simpa only [q, U, Category.assoc] using congrArg
        (fun f => f ≫ weightedCoend.ι (weight d n l) S (b ⊗ a'))
        (compositionFirstDiagramFaceForProof d S L n k l a a' b).symm
    _ = _ := by
      simp only [compositionGenerator_rawForProof, tensorHom_id,
        Category.assoc]

/-- The literal B relation faces balance over the entire original I(b,b') Hom. -/
private theorem compositionGenerator_secondBalancedForProof (a : I) :
    weightedCoend.Mapped.Balanced (weight d k l) S
      (tensorLeft (weightedCoend.objects (weight d n k) S a))
      (fun b => compositionGenerator d S L n k l a b) := by
  intro b b'
  let U : V := weightedCoend.objects (weight d n k) S a
  let q := compositionRelationTwoMap d S L n k l a b b'
  have hTarget := congrArg (fun f => q ≫ f)
    (operatorFaces_conditionForProof d S n l (b ⊗ a) (b' ⊗ a))
  change (U ◁ operatorWeightFaceForProof d S k l b b') ≫
      compositionGenerator d S L n k l a b =
    (U ◁ operatorDiagramFaceForProof d S k l b b') ≫
      compositionGenerator d S L n k l a b'
  calc
    _ = ((𝟙 U ⊗ₘ operatorWeightFaceForProof d S k l b b') ≫
          rawOperatorGeneratorForProof d S L n k l a b) ≫
        weightedCoend.ι (weight d n l) S (b ⊗ a) := by
      simp only [compositionGenerator_rawForProof, id_tensorHom,
        Category.assoc]
    _ = (q ≫ operatorWeightFaceForProof d S n l (b ⊗ a) (b' ⊗ a)) ≫
        weightedCoend.ι (weight d n l) S (b ⊗ a) := by
      simpa only [q, U, Category.assoc] using congrArg
        (fun f => f ≫ weightedCoend.ι (weight d n l) S (b ⊗ a))
        (compositionSecondWeightFaceForProof d S L n k l a b b')
    _ = (q ≫ operatorDiagramFaceForProof d S n l (b ⊗ a) (b' ⊗ a)) ≫
        weightedCoend.ι (weight d n l) S (b' ⊗ a) := by
      simpa only [Category.assoc] using hTarget
    _ = ((𝟙 U ⊗ₘ operatorDiagramFaceForProof d S k l b b') ≫
          rawOperatorGeneratorForProof d S L n k l a b') ≫
        weightedCoend.ι (weight d n l) S (b' ⊗ a) := by
      simpa only [q, U, Category.assoc] using congrArg
        (fun f => f ≫ weightedCoend.ι (weight d n l) S (b' ⊗ a))
        (compositionSecondDiagramFaceForProof d S L n k l a b b').symm
    _ = _ := by
      simp only [compositionGenerator_rawForProof, id_tensorHom,
        Category.assoc]

section FirstSourceCoend

variable [HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

private theorem compositionFirstDesc_generatorForProof (a b : I) :
    (weightedCoend.ι (weight d n k) S a ▷
        weightedCoend.objects (weight d k l) S b) ≫
        (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S b))
          (fun a => compositionGenerator d S L n k l a b)
          (compositionGenerator_firstBalancedForProof d S L n k l b)) =
      compositionGenerator d S L n k l a b := by
  exact
    weightedCoend.Mapped.gen_desc (weight d n k) S
      (tensorRight (weightedCoend.objects (weight d k l) S b))
      (fun c => compositionGenerator d S L n k l c b)
      (compositionGenerator_firstBalancedForProof d S L n k l b) a

/-- Mapped hom-extensionality derives the second descent's full balance from the B faces. -/
private theorem compositionFirstDesc_secondBalancedForProof :
    weightedCoend.Mapped.Balanced (weight d k l) S (tensorLeft (Hom d S n k))
      (fun b => (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S b))
          (fun a => compositionGenerator d S L n k l a b)
          (compositionGenerator_firstBalancedForProof d S L n k l b))) := by
  intro b b'
  let R : V := weightedCoend.relations (weight d k l) S (b, b')
  let u (a : I) : V := weightedCoend.objects (weight d n k) S a
  let v (c : I) : V := weightedCoend.objects (weight d k l) S c
  let wf : R ⟶ v b := operatorWeightFaceForProof d S k l b b'
  let df : R ⟶ v b' := operatorDiagramFaceForProof d S k l b b'
  change (Hom d S n k ◁ wf) ≫ (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S b))
          (fun a => compositionGenerator d S L n k l a b)
          (compositionGenerator_firstBalancedForProof d S L n k l b)) =
    (Hom d S n k ◁ df) ≫ (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S b'))
          (fun a => compositionGenerator d S L n k l a b')
          (compositionGenerator_firstBalancedForProof d S L n k l b'))
  apply weightedCoend.Mapped.hom_ext (weight d n k) S (tensorRight R)
  intro a
  change (weightedCoend.ι (weight d n k) S a ▷ R) ≫
      ((Hom d S n k ◁ wf) ≫
        weightedCoend.Mapped.desc (weight d n k) S (tensorRight (v b))
          (fun a => compositionGenerator d S L n k l a b)
          (compositionGenerator_firstBalancedForProof d S L n k l b)) =
    (weightedCoend.ι (weight d n k) S a ▷ R) ≫
      ((Hom d S n k ◁ df) ≫
        weightedCoend.Mapped.desc (weight d n k) S (tensorRight (v b'))
          (fun a => compositionGenerator d S L n k l a b')
          (compositionGenerator_firstBalancedForProof d S L n k l b'))
  have hL :
      (weightedCoend.ι (weight d n k) S a ▷ R) ≫ (Hom d S n k ◁ wf) =
        (u a ◁ wf) ≫ (weightedCoend.ι (weight d n k) S a ▷ v b) := by
    exact (whisker_exchange (weightedCoend.ι (weight d n k) S a) wf).symm
  have hR :
      (weightedCoend.ι (weight d n k) S a ▷ R) ≫ (Hom d S n k ◁ df) =
        (u a ◁ df) ≫ (weightedCoend.ι (weight d n k) S a ▷ v b') := by
    exact (whisker_exchange (weightedCoend.ι (weight d n k) S a) df).symm
  have hFullB :
      (u a ◁ wf) ≫ compositionGenerator d S L n k l a b =
        (u a ◁ df) ≫ compositionGenerator d S L n k l a b' := by
    exact compositionGenerator_secondBalancedForProof d S L n k l a b b'
  calc
    _ = (u a ◁ wf) ≫
        ((weightedCoend.ι (weight d n k) S a ▷ v b) ≫
          (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S b))
          (fun a => compositionGenerator d S L n k l a b)
          (compositionGenerator_firstBalancedForProof d S L n k l b))) := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S b))
          (fun a => compositionGenerator d S L n k l a b)
          (compositionGenerator_firstBalancedForProof d S L n k l b))) hL
    _ = (u a ◁ wf) ≫ compositionGenerator d S L n k l a b := by
      rw [compositionFirstDesc_generatorForProof]
    _ = (u a ◁ df) ≫ compositionGenerator d S L n k l a b' := hFullB
    _ = (u a ◁ df) ≫
        ((weightedCoend.ι (weight d n k) S a ▷ v b') ≫
          (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S b'))
          (fun a => compositionGenerator d S L n k l a b')
          (compositionGenerator_firstBalancedForProof d S L n k l b'))) := by
      rw [compositionFirstDesc_generatorForProof]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S b'))
          (fun a => compositionGenerator d S L n k l a b')
          (compositionGenerator_firstBalancedForProof d S L n k l b'))) hR.symm

section SecondSourceCoend

variable [HasCoproduct (weightedCoend.relations (weight d k l) S)]
  [HasCoproduct (weightedCoend.objects (weight d k l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d k l) S)
    (weightedCoend.rightMap (weight d k l) S)]

/-- The actual sphere-operator composition descends through both original weighted coends. -/
def composition : Hom d S n k ⊗ Hom d S k l ⟶ Hom d S n l :=
  weightedCoend.Mapped.desc (weight d k l) S (tensorLeft (Hom d S n k))
    (fun b => (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S b))
          (fun a => compositionGenerator d S L n k l a b)
          (by exact compositionGenerator_firstBalancedForProof d S L n k l b)))
    (by exact compositionFirstDesc_secondBalancedForProof d S L n k l)

private theorem composition_secondGeneratorForProof (b : I) :
    (Hom d S n k ◁ weightedCoend.ι (weight d k l) S b) ≫
        composition d S L n k l =
      (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S b))
          (fun a => compositionGenerator d S L n k l a b)
          (compositionGenerator_firstBalancedForProof d S L n k l b)) := by
  exact
    weightedCoend.Mapped.gen_desc (weight d k l) S (tensorLeft (Hom d S n k))
      (fun c => (weightedCoend.Mapped.desc (weight d n k) S
          (tensorRight (weightedCoend.objects (weight d k l) S c))
          (fun a => compositionGenerator d S L n k l a c)
          (compositionGenerator_firstBalancedForProof d S L n k l c)))
      (compositionFirstDesc_secondBalancedForProof d S L n k l) b

/-- The characteristic equality retains both entire original coend generators. -/
theorem composition_generator (a b : I) :
    (weightedCoend.ι (weight d n k) S a ⊗ₘ
        weightedCoend.ι (weight d k l) S b) ≫ composition d S L n k l =
      compositionGenerator d S L n k l a b := by
  rw [tensorHom_def, Category.assoc, composition_secondGeneratorForProof,
    compositionFirstDesc_generatorForProof]

omit [HasCoproduct (weightedCoend.relations (weight d n l) S)]
  [HasCoproduct (weightedCoend.objects (weight d n l) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n l) S)
    (weightedCoend.rightMap (weight d n l) S)] in
/-- Joint extensionality follows from the two complete preserved coend universal properties. -/
private theorem compositionSource_hom_extForProof {X : V}
    {f g : Hom d S n k ⊗ Hom d S k l ⟶ X}
    (h : ∀ a b, (weightedCoend.ι (weight d n k) S a ⊗ₘ
      weightedCoend.ι (weight d k l) S b) ≫ f =
        (weightedCoend.ι (weight d n k) S a ⊗ₘ
          weightedCoend.ι (weight d k l) S b) ≫ g) : f = g := by
  apply weightedCoend.Mapped.hom_ext (weight d k l) S (tensorLeft (Hom d S n k))
  intro b
  apply weightedCoend.Mapped.hom_ext (weight d n k) S
    (tensorRight (weightedCoend.objects (weight d k l) S b))
  intro a
  change (weightedCoend.ι (weight d n k) S a ▷
      weightedCoend.objects (weight d k l) S b) ≫
        (Hom d S n k ◁ weightedCoend.ι (weight d k l) S b) ≫ f =
    (weightedCoend.ι (weight d n k) S a ▷
      weightedCoend.objects (weight d k l) S b) ≫
        (Hom d S n k ◁ weightedCoend.ι (weight d k l) S b) ≫ g
  simpa only [tensorHom_def, Category.assoc] using h a b

end SecondSourceCoend
end FirstSourceCoend
end TargetCoend

end CategoryTheory.Enriched.SphereOperator
