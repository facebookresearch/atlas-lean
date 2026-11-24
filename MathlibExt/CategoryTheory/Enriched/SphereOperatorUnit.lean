/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorComposition
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedCoendPoint

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uA uI vI

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonoidalClosed


namespace CategoryTheory.Enriched.SphereOperator

open Limits BraidedCategory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

/-- The original epsilon and source left unitor select the actual unit coend generator.
No unit law, balance certificate, category structure, or model is an input. -/
def identityGenerator
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
    (n : I)
    [HasCoproduct (weightedCoend.relations (weight d n n) S)]
    [HasCoproduct (weightedCoend.objects (weight d n n) S)]
    [HasCoequalizer (weightedCoend.leftMap (weight d n n) S)
      (weightedCoend.rightMap (weight d n n) S)] : (𝟙_ V) ⟶ Hom d S n n :=
  (λ_ (𝟙_ V)).inv ≫
    (eHomEquiv V (λ_ n).hom ⊗ₘ L.epsilon) ≫
    weightedCoend.ι (weight d n n) S (𝟙_ I)

omit [MonoidalClosed V] in
private theorem identityFirstIndexForProof
    (d : EnrichedMonoidalCategoryData V I) (n k b : I) :
    (eHomEquiv V (λ_ n).hom ⊗ₘ 𝟙 ((b ⊗ n) ⟶[V] k)) ≫
        indexGenerator d n n k (𝟙_ I) b =
      (λ_ ((b ⊗ n) ⟶[V] k)).hom ≫
        eHomWhiskerRight V ((ρ_ b).hom ⊗ₘ 𝟙 n) k := by
  let H : V := (b ⊗ n) ⟶[V] k
  let W : V := ((𝟙_ I) ⊗ n) ⟶[V] n
  let X : I := b ⊗ ((𝟙_ I) ⊗ n)
  let Y : I := b ⊗ n
  let Z : I := (b ⊗ (𝟙_ I)) ⊗ n
  let p : (𝟙_ V) ⟶ W := eHomEquiv V (λ_ n).hom
  let f : X ⟶ Y := 𝟙 b ⊗ₘ (λ_ n).hom
  let g : Z ⟶ X := (α_ b (𝟙_ I) n).hom
  let j : W ⟶ (X ⟶[V] Y) :=
    (λ_ W).inv ≫ (eId V b ⊗ₘ 𝟙 W) ≫ d.tensorMap b b ((𝟙_ I) ⊗ n) n
  have hPoint : p ≫ j = eHomEquiv V f := by
    have hTensor :
      ((𝟙_ V) ◁ p) ≫ (eId V b ⊗ₘ 𝟙 W) = eId V b ⊗ₘ p := by
      simpa only [id_tensorHom, Category.id_comp, Category.comp_id] using
        tensorHom_comp_tensorHom (𝟙 (𝟙_ V)) p (eId V b) (𝟙 W)
    calc
      p ≫ j = (λ_ (𝟙_ V)).inv ≫
          (((𝟙_ V) ◁ p) ≫ (eId V b ⊗ₘ 𝟙 W)) ≫
          d.tensorMap b b ((𝟙_ I) ⊗ n) n := by
        dsimp only [j]
        rw [leftUnitor_inv_naturality_assoc]
        simp only [Category.assoc]
      _ = (λ_ (𝟙_ V)).inv ≫ (eId V b ⊗ₘ p) ≫
          d.tensorMap b b ((𝟙_ I) ⊗ n) n :=
        congrArg (fun t : (𝟙_ V) ⊗ (𝟙_ V) ⟶ (b ⟶[V] b) ⊗ W =>
          (λ_ (𝟙_ V)).inv ≫ t ≫ d.tensorMap b b ((𝟙_ I) ⊗ n) n) hTensor
      _ = eHomEquiv V f := by
        simpa only [p, f, eHomEquiv_id] using
          d.tensorMap_eHomEquiv (𝟙 b) (λ_ n).hom
  have hRaw : indexGenerator d n n k (𝟙_ I) b =
      ((j ⊗ₘ 𝟙 H) ≫ eComp V X Y k) ≫ eHomWhiskerRight V g k := by
    simp only [indexGenerator, j, g, W, H, X, Y, Z, eHomWhiskerRight,
      tensorHom_id, Category.assoc]
  have hPull : (eHomEquiv V f ⊗ₘ 𝟙 H) ≫ eComp V X Y k =
      (λ_ H).hom ≫ eHomWhiskerRight V f k := by
    dsimp only [H, Y]
    simp only [eHomWhiskerRight, MonoidalCategory.tensorHom_id,
      Iso.hom_inv_id_assoc]
  have hTriangle : g ≫ f = (ρ_ b).hom ⊗ₘ 𝟙 n := by
    dsimp only [g, f, X, Y, Z]
    monoidal
  have hSplit : (p ⊗ₘ 𝟙 H) ≫ (j ⊗ₘ 𝟙 H) = (p ≫ j) ⊗ₘ 𝟙 H := by
    simpa only [Category.comp_id] using
      tensorHom_comp_tensorHom p (𝟙 H) j (𝟙 H)
  calc
    _ = ((p ≫ j) ⊗ₘ 𝟙 H) ≫ eComp V X Y k ≫ eHomWhiskerRight V g k := by
      rw [hRaw]
      simpa only [Category.assoc] using congrArg
        (fun t : (𝟙_ V) ⊗ H ⟶ (X ⟶[V] Y) ⊗ H =>
          t ≫ eComp V X Y k ≫ eHomWhiskerRight V g k) hSplit
    _ = (eHomEquiv V f ⊗ₘ 𝟙 H) ≫ eComp V X Y k ≫ eHomWhiskerRight V g k :=
      congrArg (fun t : (𝟙_ V) ⟶ (X ⟶[V] Y) =>
        (t ⊗ₘ 𝟙 H) ≫ eComp V X Y k ≫ eHomWhiskerRight V g k) hPoint
    _ = (λ_ H).hom ≫ (eHomWhiskerRight V f k ≫ eHomWhiskerRight V g k) := by
      simpa only [Category.assoc] using congrArg
        (fun t : (𝟙_ V) ⊗ H ⟶ (X ⟶[V] k) => t ≫ eHomWhiskerRight V g k) hPull
    _ = (λ_ H).hom ≫ eHomWhiskerRight V (g ≫ f) k :=
      congrArg (fun t : H ⟶ (Z ⟶[V] k) => (λ_ H).hom ≫ t)
        (eHomWhiskerRight_comp (V := V) g f k).symm
    _ = _ :=
      congrArg (fun t : Z ⟶ Y => (λ_ H).hom ≫ eHomWhiskerRight V t k) hTriangle

omit [MonoidalClosed V] in
private theorem identitySecondIndexForProof
    (d : EnrichedMonoidalCategoryData V I) (n k a : I) :
    (𝟙 ((a ⊗ n) ⟶[V] k) ⊗ₘ eHomEquiv V (λ_ k).hom) ≫
        indexGenerator d n k k a (𝟙_ I) =
      (ρ_ ((a ⊗ n) ⟶[V] k)).hom ≫
        eHomWhiskerRight V ((λ_ a).hom ⊗ₘ 𝟙 n) k := by
  let H : V := (a ⊗ n) ⟶[V] k
  let X : I := (𝟙_ I) ⊗ (a ⊗ n)
  let Y : I := (𝟙_ I) ⊗ k
  let Z : I := ((𝟙_ I) ⊗ a) ⊗ n
  let P : V := Y ⟶[V] k
  let j : H ⟶ (X ⟶[V] Y) :=
    (λ_ H).inv ≫ (eId V (𝟙_ I) ⊗ₘ 𝟙 H) ≫
      d.tensorMap (𝟙_ I) (𝟙_ I) (a ⊗ n) k
  let p : (𝟙_ V) ⟶ P := eHomEquiv V (λ_ k).hom
  let g : Z ⟶ X := (α_ (𝟙_ I) a n).hom
  have hUnitor : (β_ (𝟙_ V) H).hom ≫ (j ⊗ₘ p) ≫ eComp V X Y k =
      (eHomEquiv V (λ_ (a ⊗ n)).hom ⊗ₘ 𝟙 H) ≫ eComp V X (a ⊗ n) k := by
    exact d.leftUnitorNaturality (a ⊗ n) k
  have hPull : (λ_ H).hom ≫ eHomWhiskerRight V (λ_ (a ⊗ n)).hom k =
      (eHomEquiv V (λ_ (a ⊗ n)).hom ⊗ₘ 𝟙 H) ≫ eComp V X (a ⊗ n) k := by
    dsimp only [H, X]
    simp only [eHomWhiskerRight, MonoidalCategory.tensorHom_id,
      Iso.hom_inv_id_assoc]
  have hBridge : (β_ (𝟙_ V) H).hom ≫
      ((ρ_ H).hom ≫ eHomWhiskerRight V (λ_ (a ⊗ n)).hom k) =
        (eHomEquiv V (λ_ (a ⊗ n)).hom ⊗ₘ 𝟙 H) ≫ eComp V X (a ⊗ n) k :=
    (Category.assoc (β_ (𝟙_ V) H).hom (ρ_ H).hom
      (eHomWhiskerRight V (λ_ (a ⊗ n)).hom k)).symm.trans
      ((congrArg (fun t : (𝟙_ V) ⊗ H ⟶ H =>
          t ≫ eHomWhiskerRight V (λ_ (a ⊗ n)).hom k)
        (CategoryTheory.braiding_rightUnitor H)).trans hPull)
  have hIndex : (j ⊗ₘ p) ≫ eComp V X Y k =
      (ρ_ H).hom ≫ eHomWhiskerRight V (λ_ (a ⊗ n)).hom k :=
    (cancel_epi (β_ (𝟙_ V) H).hom).1 (hUnitor.trans hBridge.symm)
  have hRaw : indexGenerator d n k k a (𝟙_ I) =
      ((j ⊗ₘ 𝟙 P) ≫ eComp V X Y k) ≫ eHomWhiskerRight V g k := by
    simp only [indexGenerator, j, g, H, P, X, Y, Z,
      eHomWhiskerRight, tensorHom_id, Category.assoc]
  have hSplit : (𝟙 H ⊗ₘ p) ≫ (j ⊗ₘ 𝟙 P) = j ⊗ₘ p := by
    simpa only [Category.id_comp, Category.comp_id] using
      tensorHom_comp_tensorHom (𝟙 H) p j (𝟙 P)
  have hLeftUnit : g ≫ (λ_ (a ⊗ n)).hom = (λ_ a).hom ⊗ₘ 𝟙 n := by
    dsimp only [g, X, Z]
    monoidal
  calc
    _ = (j ⊗ₘ p) ≫ eComp V X Y k ≫ eHomWhiskerRight V g k := by
      rw [hRaw]
      simpa only [Category.assoc] using congrArg
        (fun t : H ⊗ (𝟙_ V) ⟶ (X ⟶[V] Y) ⊗ P =>
          t ≫ eComp V X Y k ≫ eHomWhiskerRight V g k) hSplit
    _ = (ρ_ H).hom ≫ (eHomWhiskerRight V (λ_ (a ⊗ n)).hom k ≫
        eHomWhiskerRight V g k) := by
      simpa only [Category.assoc] using congrArg
        (fun t : H ⊗ (𝟙_ V) ⟶ (X ⟶[V] k) => t ≫ eHomWhiskerRight V g k) hIndex
    _ = (ρ_ H).hom ≫ eHomWhiskerRight V (g ≫ (λ_ (a ⊗ n)).hom) k :=
      congrArg (fun t : H ⟶ (Z ⟶[V] k) => (ρ_ H).hom ≫ t)
        (eHomWhiskerRight_comp (V := V) g (λ_ (a ⊗ n)).hom k).symm
    _ = _ :=
      congrArg (fun t : Z ⟶ (a ⊗ n) => (ρ_ H).hom ≫ eHomWhiskerRight V t k) hLeftUnit

end CategoryTheory.Enriched.SphereOperator

namespace CategoryTheory.Enriched.SphereOperator

open Limits BraidedCategory Opposite

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [MonoidalClosed V]

/-- The entire unit-point action is the original ordinary coefficient arrow. -/
private theorem coefficientPointActionForProof
    (P Q H : V) (e : (𝟙_ V) ⟶ H) (f : H ⟶ (ihom P).obj Q) :
    (eHomEquiv V (C := V) (X := P) (Y := Q)).symm (e ≫ f) =
      (ρ_ P).inv ≫ P ◁ e ≫ MonoidalClosed.uncurry f := by
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
  change (ρ_ P).inv ≫ MonoidalClosed.uncurry (e ≫ f) =
    (ρ_ P).inv ≫ P ◁ e ≫ MonoidalClosed.uncurry f
  exact congrArg (fun t : P ⊗ (𝟙_ V) ⟶ Q => (ρ_ P).inv ≫ t)
    (MonoidalClosed.uncurry_natural_left (C := V) e f)

variable [BraidedCategory V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

/-- The original left coefficient coherence, normalized to a full unit-point action. -/
private theorem coefficientLeftUnitForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S) (a : I) :
    (λ_ (S.obj a)).inv ≫ (L.epsilon ⊗ₘ 𝟙 (S.obj a)) ≫ L.mu (𝟙_ I) a ≫
      (ρ_ (S.obj ((𝟙_ I) ⊗ a))).inv ≫
      S.obj ((𝟙_ I) ⊗ a) ◁ eHomEquiv V (λ_ a).hom ≫
      MonoidalClosed.uncurry (S.map ((𝟙_ I) ⊗ a) a) = 𝟙 (S.obj a) := by
  have h := congrArg
    (fun f : (𝟙_ V) ⊗ S.obj a ⟶ S.obj a => (λ_ (S.obj a)).inv ≫ f)
    (L.unit a).1.symm
  rw [coefficientPointActionForProof] at h
  simpa only [MonoidalCategory.tensorHom_id, Category.assoc,
    Iso.inv_hom_id] using h

/-- The original right coefficient coherence, with no operator-unit premise. -/
private theorem coefficientRightUnitForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S) (a : I) :
    (ρ_ (S.obj a)).inv ≫ (𝟙 (S.obj a) ⊗ₘ L.epsilon) ≫ L.mu a (𝟙_ I) ≫
      (ρ_ (S.obj (a ⊗ (𝟙_ I)))).inv ≫
      S.obj (a ⊗ (𝟙_ I)) ◁ eHomEquiv V (ρ_ a).hom ≫
      MonoidalClosed.uncurry (S.map (a ⊗ (𝟙_ I)) a) = 𝟙 (S.obj a) := by
  have h := congrArg
    (fun f : S.obj a ⊗ (𝟙_ V) ⟶ S.obj a => (ρ_ (S.obj a)).inv ≫ f)
    (L.unit a).2.symm
  rw [coefficientPointActionForProof] at h
  simpa only [MonoidalCategory.id_tensorHom, Category.assoc,
    Iso.inv_hom_id] using h

/-- The whole target coend unit relation at the actual source right unitor. -/
private theorem targetRightUnitRelationForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S) (n k b : I)
    [HasCoproduct (weightedCoend.relations (weight d n k) S)]
    [HasCoproduct (weightedCoend.objects (weight d n k) S)]
    [HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
      (weightedCoend.rightMap (weight d n k) S)] :
    (((ρ_ ((weight d n k).obj (op b))).inv ≫
        (weight d n k).obj (op b) ◁ eHomEquiv V (ρ_ b).hom ≫
        MonoidalClosed.uncurry ((weight d n k).map (op b) (op (b ⊗ (𝟙_ I))))) ⊗ₘ
      ((ρ_ (S.obj b)).inv ≫ (𝟙 (S.obj b) ⊗ₘ L.epsilon) ≫ L.mu b (𝟙_ I))) ≫
        weightedCoend.ι (weight d n k) S (b ⊗ (𝟙_ I)) =
      weightedCoend.ι (weight d n k) S b := by
  let W := weight d n k
  let c : I := b ⊗ (𝟙_ I)
  let e : (𝟙_ V) ⟶ (c ⟶[V] b) := eHomEquiv V (ρ_ b).hom
  let U : V := W.obj (op b)
  let X : V := S.obj c
  let Y : V := S.obj b
  let wa : U ⟶ W.obj (op c) :=
    (ρ_ U).inv ≫ U ◁ e ≫ MonoidalClosed.uncurry (W.map (op b) (op c))
  let fa : X ⟶ Y := (ρ_ X).inv ≫ X ◁ e ≫ MonoidalClosed.uncurry (S.map c b)
  let t : Y ⟶ X := (ρ_ (S.obj b)).inv ≫ (𝟙 (S.obj b) ⊗ₘ L.epsilon) ≫ L.mu b (𝟙_ I)
  have hPoint : (wa ⊗ₘ 𝟙 X) ≫ weightedCoend.ι W S c =
      (𝟙 U ⊗ₘ fa) ≫ weightedCoend.ι W S b :=
    CategoryTheory.Enriched.weightedCoend.condition_unitPoint W S c b e
  have hCoefficient : t ≫ fa = 𝟙 Y := by
    simpa only [t, fa, c, e, X, Y, Category.assoc] using
      coefficientRightUnitForProof d S L b
  have hSplit : (𝟙 U ⊗ₘ t) ≫ (wa ⊗ₘ 𝟙 X) = wa ⊗ₘ t := by
    simpa only [Category.id_comp, Category.comp_id] using
      MonoidalCategory.tensorHom_comp_tensorHom (𝟙 U) t wa (𝟙 X)
  have hPair : (𝟙 U ⊗ₘ t) ≫ (𝟙 U ⊗ₘ fa) = 𝟙 U ⊗ₘ (t ≫ fa) := by
    simpa only [Category.id_comp] using
      MonoidalCategory.tensorHom_comp_tensorHom (𝟙 U) t (𝟙 U) fa
  change (wa ⊗ₘ t) ≫ weightedCoend.ι W S c = weightedCoend.ι W S b
  calc
    _ = ((𝟙 U ⊗ₘ t) ≫ (wa ⊗ₘ 𝟙 X)) ≫ weightedCoend.ι W S c :=
      congrArg (fun f : U ⊗ Y ⟶ W.obj (op c) ⊗ X =>
        f ≫ weightedCoend.ι W S c) hSplit.symm
    _ = (𝟙 U ⊗ₘ t) ≫ ((wa ⊗ₘ 𝟙 X) ≫ weightedCoend.ι W S c) :=
      Category.assoc _ _ _
    _ = (𝟙 U ⊗ₘ t) ≫ ((𝟙 U ⊗ₘ fa) ≫ weightedCoend.ι W S b) :=
      congrArg (fun f : U ⊗ X ⟶ Hom d S n k => (𝟙 U ⊗ₘ t) ≫ f) hPoint
    _ = ((𝟙 U ⊗ₘ t) ≫ (𝟙 U ⊗ₘ fa)) ≫ weightedCoend.ι W S b :=
      (Category.assoc _ _ _).symm
    _ = (𝟙 U ⊗ₘ (t ≫ fa)) ≫ weightedCoend.ι W S b :=
      congrArg (fun f : U ⊗ Y ⟶ U ⊗ Y => f ≫ weightedCoend.ι W S b) hPair
    _ = weightedCoend.ι W S b := by
      rw [hCoefficient]
      simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]

/-- The whole target coend unit relation at the actual source left unitor. -/
private theorem targetLeftUnitRelationForProof
    (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
    (L : EnrichedFunctor.LaxMonoidalData d
      (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S) (n k b : I)
    [HasCoproduct (weightedCoend.relations (weight d n k) S)]
    [HasCoproduct (weightedCoend.objects (weight d n k) S)]
    [HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
      (weightedCoend.rightMap (weight d n k) S)] :
    (((ρ_ ((weight d n k).obj (op b))).inv ≫
        (weight d n k).obj (op b) ◁ eHomEquiv V (λ_ b).hom ≫
        MonoidalClosed.uncurry ((weight d n k).map (op b) (op ((𝟙_ I) ⊗ b)))) ⊗ₘ
      ((λ_ (S.obj b)).inv ≫ (L.epsilon ⊗ₘ 𝟙 (S.obj b)) ≫ L.mu (𝟙_ I) b)) ≫
        weightedCoend.ι (weight d n k) S ((𝟙_ I) ⊗ b) =
      weightedCoend.ι (weight d n k) S b := by
  let W := weight d n k
  let c : I := (𝟙_ I) ⊗ b
  let e : (𝟙_ V) ⟶ (c ⟶[V] b) := eHomEquiv V (λ_ b).hom
  let U : V := W.obj (op b)
  let X : V := S.obj c
  let Y : V := S.obj b
  let wa : U ⟶ W.obj (op c) :=
    (ρ_ U).inv ≫ U ◁ e ≫ MonoidalClosed.uncurry (W.map (op b) (op c))
  let fa : X ⟶ Y := (ρ_ X).inv ≫ X ◁ e ≫ MonoidalClosed.uncurry (S.map c b)
  let t : Y ⟶ X := (λ_ (S.obj b)).inv ≫ (L.epsilon ⊗ₘ 𝟙 (S.obj b)) ≫ L.mu (𝟙_ I) b
  have hPoint : (wa ⊗ₘ 𝟙 X) ≫ weightedCoend.ι W S c =
      (𝟙 U ⊗ₘ fa) ≫ weightedCoend.ι W S b :=
    CategoryTheory.Enriched.weightedCoend.condition_unitPoint W S c b e
  have hCoefficient : t ≫ fa = 𝟙 Y := by
    simpa only [t, fa, c, e, X, Y, Category.assoc] using
      coefficientLeftUnitForProof d S L b
  have hSplit : (𝟙 U ⊗ₘ t) ≫ (wa ⊗ₘ 𝟙 X) = wa ⊗ₘ t := by
    simpa only [Category.id_comp, Category.comp_id] using
      MonoidalCategory.tensorHom_comp_tensorHom (𝟙 U) t wa (𝟙 X)
  have hPair : (𝟙 U ⊗ₘ t) ≫ (𝟙 U ⊗ₘ fa) = 𝟙 U ⊗ₘ (t ≫ fa) := by
    simpa only [Category.id_comp] using
      MonoidalCategory.tensorHom_comp_tensorHom (𝟙 U) t (𝟙 U) fa
  change (wa ⊗ₘ t) ≫ weightedCoend.ι W S c = weightedCoend.ι W S b
  calc
    _ = ((𝟙 U ⊗ₘ t) ≫ (wa ⊗ₘ 𝟙 X)) ≫ weightedCoend.ι W S c :=
      congrArg (fun f : U ⊗ Y ⟶ W.obj (op c) ⊗ X =>
        f ≫ weightedCoend.ι W S c) hSplit.symm
    _ = (𝟙 U ⊗ₘ t) ≫ ((wa ⊗ₘ 𝟙 X) ≫ weightedCoend.ι W S c) :=
      Category.assoc _ _ _
    _ = (𝟙 U ⊗ₘ t) ≫ ((𝟙 U ⊗ₘ fa) ≫ weightedCoend.ι W S b) :=
      congrArg (fun f : U ⊗ X ⟶ Hom d S n k => (𝟙 U ⊗ₘ t) ≫ f) hPoint
    _ = ((𝟙 U ⊗ₘ t) ≫ (𝟙 U ⊗ₘ fa)) ≫ weightedCoend.ι W S b :=
      (Category.assoc _ _ _).symm
    _ = (𝟙 U ⊗ₘ (t ≫ fa)) ≫ weightedCoend.ι W S b :=
      congrArg (fun f : U ⊗ Y ⟶ U ⊗ Y => f ≫ weightedCoend.ι W S b) hPair
    _ = weightedCoend.ι W S b := by
      rw [hCoefficient]
      simp only [MonoidalCategory.id_tensorHom_id, Category.id_comp]

end CategoryTheory.Enriched.SphereOperator

namespace CategoryTheory.Enriched.SphereOperator

open Limits BraidedCategory Opposite

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V]

/-- The actual inverse tensorator is natural in all four factors. -/
private theorem tensorDeltaNaturalityForProof
    {X₁ X₂ Y₁ Y₂ X₁' X₂' Y₁' Y₂' : V}
    (f₁ : X₁ ⟶ X₁') (f₂ : X₂ ⟶ X₂')
    (g₁ : Y₁ ⟶ Y₁') (g₂ : Y₂ ⟶ Y₂') :
    ((f₁ ⊗ₘ g₁) ⊗ₘ (f₂ ⊗ₘ g₂)) ≫
        MonoidalCategory.tensorδ X₁' X₂' Y₁' Y₂' =
      MonoidalCategory.tensorδ X₁ X₂ Y₁ Y₂ ≫
        ((f₁ ⊗ₘ f₂) ⊗ₘ (g₁ ⊗ₘ g₂)) := by
  have h := Functor.OplaxMonoidal.δ_natural (MonoidalCategory.tensor V)
    (show (X₁, X₂) ⟶ (X₁', X₂') from (f₁, f₂))
    (show (Y₁, Y₂) ⟶ (Y₁', Y₂') from (g₁, g₂))
  simp only [MonoidalCategory.tensor_δ] at h
  change MonoidalCategory.tensorδ X₁ X₂ Y₁ Y₂ ≫
      ((f₁ ⊗ₘ f₂) ⊗ₘ (g₁ ⊗ₘ g₂)) =
    ((f₁ ⊗ₘ g₁) ⊗ₘ (f₂ ⊗ₘ g₂)) ≫
      MonoidalCategory.tensorδ X₁' X₂' Y₁' Y₂' at h
  exact h.symm

/-- An arbitrary first unit point crosses the original inverse mixed braid;
the coefficient then uses the positive crossing in the composition generator. -/
private theorem tensorDeltaFirstUnitPaddingForProof
    (C Z A B : V) (p : (𝟙_ V) ⟶ C) (e : (𝟙_ V) ⟶ A) :
    (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ e)) ⊗ₘ 𝟙 (Z ⊗ B)) ≫
        MonoidalCategory.tensorδ C Z A B ≫
        (𝟙 (C ⊗ Z) ⊗ₘ (β_ A B).hom) =
      (λ_ (Z ⊗ B)).hom ≫
        (((λ_ Z).inv ≫ (p ⊗ₘ 𝟙 Z)) ⊗ₘ
          ((ρ_ B).inv ≫ (𝟙 B ⊗ₘ e))) := by
  have hPre : (((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ e)) ⊗ₘ 𝟙 (Z ⊗ B)) =
      ((λ_ (𝟙_ V)).inv ▷ (Z ⊗ B)) ≫
        ((p ⊗ₘ e) ⊗ₘ 𝟙 (Z ⊗ B)) :=
    (whiskerRight_comp_tensorHom (λ_ (𝟙_ V)).inv
      (p ⊗ₘ e) (𝟙 (Z ⊗ B))).symm
  have hNatural : ((p ⊗ₘ e) ⊗ₘ 𝟙 (Z ⊗ B)) ≫
        MonoidalCategory.tensorδ C Z A B =
      MonoidalCategory.tensorδ (𝟙_ V) Z (𝟙_ V) B ≫
        ((p ⊗ₘ 𝟙 Z) ⊗ₘ (e ⊗ₘ 𝟙 B)) := by
    simpa only [MonoidalCategory.id_tensorHom_id] using
      tensorDeltaNaturalityForProof p (𝟙 Z) e (𝟙 B)
  have hUnit : ((λ_ (𝟙_ V)).inv ▷ (Z ⊗ B)) ≫
        MonoidalCategory.tensorδ (𝟙_ V) Z (𝟙_ V) B =
      (λ_ (Z ⊗ B)).hom ≫ ((λ_ Z).inv ⊗ₘ (λ_ B).inv) := by
    dsimp only [MonoidalCategory.tensorδ]
    rw [CategoryTheory.braiding_inv_tensorUnit_right]
    monoidal
  have hCross : ((λ_ B).inv ≫ (e ⊗ₘ 𝟙 B)) ≫ (β_ A B).hom =
      (ρ_ B).inv ≫ (𝟙 B ⊗ₘ e) := by
    simpa only [MonoidalCategory.id_tensorHom, Category.assoc,
      CategoryTheory.braiding_tensorUnit_left, Iso.inv_hom_id_assoc] using
      congrArg (fun f : (𝟙_ V) ⊗ B ⟶ B ⊗ A => (λ_ B).inv ≫ f)
        (braiding_naturality e (𝟙 B))
  have hPair : ((λ_ Z).inv ⊗ₘ (λ_ B).inv) ≫
        ((p ⊗ₘ 𝟙 Z) ⊗ₘ (e ⊗ₘ 𝟙 B)) ≫
        (𝟙 (C ⊗ Z) ⊗ₘ (β_ A B).hom) =
      ((λ_ Z).inv ≫ (p ⊗ₘ 𝟙 Z)) ⊗ₘ
        ((ρ_ B).inv ≫ (𝟙 B ⊗ₘ e)) := by
    simpa only [MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.assoc] using
      congrArg (fun f : B ⟶ B ⊗ A =>
        ((λ_ Z).inv ≫ (p ⊗ₘ 𝟙 Z)) ⊗ₘ f) hCross
  calc
    _ = ((λ_ (𝟙_ V)).inv ▷ (Z ⊗ B)) ≫
        (((p ⊗ₘ e) ⊗ₘ 𝟙 (Z ⊗ B)) ≫
          MonoidalCategory.tensorδ C Z A B) ≫
        (𝟙 (C ⊗ Z) ⊗ₘ (β_ A B).hom) := by
      rw [hPre]
      simp only [Category.assoc]
    _ = ((λ_ (𝟙_ V)).inv ▷ (Z ⊗ B)) ≫
        MonoidalCategory.tensorδ (𝟙_ V) Z (𝟙_ V) B ≫
        ((p ⊗ₘ 𝟙 Z) ⊗ₘ (e ⊗ₘ 𝟙 B)) ≫
        (𝟙 (C ⊗ Z) ⊗ₘ (β_ A B).hom) := by
      simpa only [Category.assoc] using congrArg
        (fun f : ((𝟙_ V) ⊗ (𝟙_ V)) ⊗ (Z ⊗ B) ⟶
            (C ⊗ Z) ⊗ (A ⊗ B) =>
          ((λ_ (𝟙_ V)).inv ▷ (Z ⊗ B)) ≫ f ≫
            (𝟙 (C ⊗ Z) ⊗ₘ (β_ A B).hom)) hNatural
    _ = (λ_ (Z ⊗ B)).hom ≫ ((λ_ Z).inv ⊗ₘ (λ_ B).inv) ≫
        ((p ⊗ₘ 𝟙 Z) ⊗ₘ (e ⊗ₘ 𝟙 B)) ≫
        (𝟙 (C ⊗ Z) ⊗ₘ (β_ A B).hom) := by
      simpa only [Category.assoc] using congrArg
        (fun f : (𝟙_ V) ⊗ (Z ⊗ B) ⟶
            ((𝟙_ V) ⊗ Z) ⊗ ((𝟙_ V) ⊗ B) =>
          f ≫ ((p ⊗ₘ 𝟙 Z) ⊗ₘ (e ⊗ₘ 𝟙 B)) ≫
            (𝟙 (C ⊗ Z) ⊗ₘ (β_ A B).hom)) hUnit
    _ = _ := congrArg
      (fun f : Z ⊗ B ⟶ (C ⊗ Z) ⊗ (B ⊗ A) => (λ_ (Z ⊗ B)).hom ≫ f)
      hPair

/-- The second unit point uses the same actual inverse tensorator and positive
coefficient crossing, with the original left coefficient unit on the output. -/
private theorem tensorDeltaSecondUnitPaddingForProof
    (X Z A B : V) (p : (𝟙_ V) ⟶ Z) (e : (𝟙_ V) ⟶ B) :
    (𝟙 (X ⊗ A) ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ e))) ≫
        MonoidalCategory.tensorδ X Z A B ≫
        (𝟙 (X ⊗ Z) ⊗ₘ (β_ A B).hom) =
      (ρ_ (X ⊗ A)).hom ≫
        (((ρ_ X).inv ≫ (𝟙 X ⊗ₘ p)) ⊗ₘ
          ((λ_ A).inv ≫ (e ⊗ₘ 𝟙 A))) := by
  have hPre : (𝟙 (X ⊗ A) ⊗ₘ ((λ_ (𝟙_ V)).inv ≫ (p ⊗ₘ e))) =
      ((X ⊗ A) ◁ (λ_ (𝟙_ V)).inv) ≫
        (𝟙 (X ⊗ A) ⊗ₘ (p ⊗ₘ e)) := by
    simpa only [Category.id_comp, MonoidalCategory.id_tensorHom] using
      (MonoidalCategory.tensorHom_comp_tensorHom (𝟙 (X ⊗ A))
        (λ_ (𝟙_ V)).inv (𝟙 (X ⊗ A)) (p ⊗ₘ e)).symm
  have hNatural : (𝟙 (X ⊗ A) ⊗ₘ (p ⊗ₘ e)) ≫
        MonoidalCategory.tensorδ X Z A B =
      MonoidalCategory.tensorδ X (𝟙_ V) A (𝟙_ V) ≫
        ((𝟙 X ⊗ₘ p) ⊗ₘ (𝟙 A ⊗ₘ e)) := by
    simpa only [MonoidalCategory.id_tensorHom_id] using
      tensorDeltaNaturalityForProof (𝟙 X) p (𝟙 A) e
  have hUnit : ((X ⊗ A) ◁ (λ_ (𝟙_ V)).inv) ≫
        MonoidalCategory.tensorδ X (𝟙_ V) A (𝟙_ V) =
      (ρ_ (X ⊗ A)).hom ≫ ((ρ_ X).inv ⊗ₘ (ρ_ A).inv) := by
    dsimp only [MonoidalCategory.tensorδ]
    rw [CategoryTheory.braiding_inv_tensorUnit_left]
    monoidal
  have hCross : ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ e)) ≫ (β_ A B).hom =
      (λ_ A).inv ≫ (e ⊗ₘ 𝟙 A) := by
    simpa only [MonoidalCategory.id_tensorHom, Category.assoc,
      CategoryTheory.braiding_tensorUnit_right, Iso.inv_hom_id_assoc] using
      congrArg (fun f : A ⊗ (𝟙_ V) ⟶ B ⊗ A => (ρ_ A).inv ≫ f)
        (braiding_naturality (𝟙 A) e)
  have hPair : ((ρ_ X).inv ⊗ₘ (ρ_ A).inv) ≫
        ((𝟙 X ⊗ₘ p) ⊗ₘ (𝟙 A ⊗ₘ e)) ≫
        (𝟙 (X ⊗ Z) ⊗ₘ (β_ A B).hom) =
      ((ρ_ X).inv ≫ (𝟙 X ⊗ₘ p)) ⊗ₘ
        ((λ_ A).inv ≫ (e ⊗ₘ 𝟙 A)) := by
    simpa only [MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.assoc] using
      congrArg (fun f : A ⟶ B ⊗ A =>
        ((ρ_ X).inv ≫ (𝟙 X ⊗ₘ p)) ⊗ₘ f) hCross
  calc
    _ = ((X ⊗ A) ◁ (λ_ (𝟙_ V)).inv) ≫
        ((𝟙 (X ⊗ A) ⊗ₘ (p ⊗ₘ e)) ≫
          MonoidalCategory.tensorδ X Z A B) ≫
        (𝟙 (X ⊗ Z) ⊗ₘ (β_ A B).hom) := by
      rw [hPre]
      simp only [Category.assoc]
    _ = ((X ⊗ A) ◁ (λ_ (𝟙_ V)).inv) ≫
        MonoidalCategory.tensorδ X (𝟙_ V) A (𝟙_ V) ≫
        ((𝟙 X ⊗ₘ p) ⊗ₘ (𝟙 A ⊗ₘ e)) ≫
        (𝟙 (X ⊗ Z) ⊗ₘ (β_ A B).hom) := by
      simpa only [Category.assoc] using congrArg
        (fun f : (X ⊗ A) ⊗ ((𝟙_ V) ⊗ (𝟙_ V)) ⟶
            (X ⊗ Z) ⊗ (A ⊗ B) =>
          ((X ⊗ A) ◁ (λ_ (𝟙_ V)).inv) ≫ f ≫
            (𝟙 (X ⊗ Z) ⊗ₘ (β_ A B).hom)) hNatural
    _ = (ρ_ (X ⊗ A)).hom ≫ ((ρ_ X).inv ⊗ₘ (ρ_ A).inv) ≫
        ((𝟙 X ⊗ₘ p) ⊗ₘ (𝟙 A ⊗ₘ e)) ≫
        (𝟙 (X ⊗ Z) ⊗ₘ (β_ A B).hom) := by
      simpa only [Category.assoc] using congrArg
        (fun f : (X ⊗ A) ⊗ (𝟙_ V) ⟶
            (X ⊗ (𝟙_ V)) ⊗ (A ⊗ (𝟙_ V)) =>
          f ≫ ((𝟙 X ⊗ₘ p) ⊗ₘ (𝟙 A ⊗ₘ e)) ≫
            (𝟙 (X ⊗ Z) ⊗ₘ (β_ A B).hom)) hUnit
    _ = _ := congrArg
      (fun f : X ⊗ A ⟶ (X ⊗ Z) ⊗ (B ⊗ A) => (ρ_ (X ⊗ A)).hom ≫ f)
      hPair

variable [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]

/-- The full weight action at an ordinary source point is actual precomposition
by the same fixed-factor tensor arrow. -/
theorem weight_point_pre
    (d : EnrichedMonoidalCategoryData V I) (n k c b : I) (r : c ⟶ b) :
    (ρ_ ((weight d n k).obj (op b))).inv ≫
        (weight d n k).obj (op b) ◁ eHomEquiv V r ≫
        MonoidalClosed.uncurry ((weight d n k).map (op b) (op c)) =
      eHomWhiskerRight V (r ⊗ₘ 𝟙 n) k := by
  let H : V := c ⟶[V] b
  let K : V := (c ⊗ n) ⟶[V] (b ⊗ n)
  let e : (𝟙_ V) ⟶ H := eHomEquiv V r
  let p : (𝟙_ V) ⟶ K := eHomEquiv V (r ⊗ₘ 𝟙 n)
  let W : V := (b ⊗ n) ⟶[V] k
  have hTensor : (e ▷ (𝟙_ V)) ≫ (𝟙 H ⊗ₘ eId V n) = e ⊗ₘ eId V n := by
    simpa only [MonoidalCategory.tensorHom_id, Category.comp_id,
      Category.id_comp] using
      MonoidalCategory.tensorHom_comp_tensorHom e (𝟙 (𝟙_ V)) (𝟙 H) (eId V n)
  have hPoint : e ≫ (fixedRightTensor d n).map c b = p := by
    calc
      _ = ((ρ_ (𝟙_ V)).inv ≫ (e ▷ (𝟙_ V))) ≫
          (𝟙 H ⊗ₘ eId V n) ≫ d.tensorMap c b n n := by
        rw [fixedRightTensor_map]
        have hUnit : e ≫ (ρ_ H).inv =
            (ρ_ (𝟙_ V)).inv ≫ (e ▷ (𝟙_ V)) :=
          rightUnitor_inv_naturality e
        exact (Category.assoc e (ρ_ H).inv
          ((𝟙 H ⊗ₘ eId V n) ≫ d.tensorMap c b n n)).symm.trans
            (congrArg
              (fun f : (𝟙_ V) ⟶ H ⊗ (𝟙_ V) =>
                f ≫ (𝟙 H ⊗ₘ eId V n) ≫ d.tensorMap c b n n) hUnit)
      _ = (ρ_ (𝟙_ V)).inv ≫ (e ⊗ₘ eId V n) ≫ d.tensorMap c b n n := by
        simpa only [Category.assoc] using congrArg
          (fun f : (𝟙_ V) ⊗ (𝟙_ V) ⟶ H ⊗ (n ⟶[V] n) =>
            (ρ_ (𝟙_ V)).inv ≫ f ≫ d.tensorMap c b n n) hTensor
      _ = p := by
        simpa only [e, p, eHomEquiv_id, unitors_inv_equal] using
          d.tensorMap_eHomEquiv r (𝟙 n)
  have hMap : W ◁ e ≫ W ◁ (fixedRightTensor d n).map c b = W ◁ p :=
    (MonoidalCategory.whiskerLeft_comp W e ((fixedRightTensor d n).map c b)).symm.trans
      (congrArg (fun f : (𝟙_ V) ⟶ K => W ◁ f) hPoint)
  have hCross : ((ρ_ W).inv ≫ W ◁ p) ≫ (β_ W K).hom =
      (λ_ W).inv ≫ (p ⊗ₘ 𝟙 W) := by
    simpa only [MonoidalCategory.id_tensorHom, Category.assoc,
      CategoryTheory.braiding_tensorUnit_right, Iso.inv_hom_id_assoc] using
      congrArg (fun f : W ⊗ (𝟙_ V) ⟶ K ⊗ W => (ρ_ W).inv ≫ f)
        (braiding_naturality (𝟙 W) p)
  have hWholeMap := congrArg
    (fun f : ((weight d n k).obj (op b)) ⊗ (c ⟶[V] b) ⟶
        (weight d n k).obj (op c) =>
      (ρ_ ((weight d n k).obj (op b))).inv ≫
        (weight d n k).obj (op b) ◁ eHomEquiv V r ≫ f)
    (weight_uncurry_map d n k c b)
  calc
    _ = (ρ_ W).inv ≫
        (W ◁ e ≫ W ◁ (fixedRightTensor d n).map c b) ≫
        (β_ W K).hom ≫ eComp V (c ⊗ n) (b ⊗ n) k := by
      simpa only [H, K, e, W, weight_obj, Category.assoc] using hWholeMap
    _ = (ρ_ W).inv ≫ W ◁ p ≫ (β_ W K).hom ≫
        eComp V (c ⊗ n) (b ⊗ n) k := by
      exact congrArg
        (fun f : W ⊗ (𝟙_ V) ⟶ W ⊗ K =>
          (ρ_ W).inv ≫ f ≫ (β_ W K).hom ≫
            eComp V (c ⊗ n) (b ⊗ n) k) hMap
    _ = (λ_ W).inv ≫ (p ⊗ₘ 𝟙 W) ≫
        eComp V (c ⊗ n) (b ⊗ n) k := by
      simpa only [Category.assoc] using congrArg
        (fun f : W ⟶ K ⊗ W => f ≫ eComp V (c ⊗ n) (b ⊗ n) k) hCross
    _ = _ := by
      simp only [eHomWhiskerRight, MonoidalCategory.tensorHom_id, p, W]

variable (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  (n k : I)
  [HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

/-- The first unit generator reduces through the actual target right-unitor
relation, retaining the complete weight and coefficient maps. -/
private theorem firstUnitRawGeneratorForProof (b : I) :
    (((λ_ (𝟙_ V)).inv ≫
        (eHomEquiv V (λ_ n).hom ⊗ₘ L.epsilon)) ⊗ₘ
        𝟙 (weightedCoend.objects (weight d n k) S b)) ≫
        compositionGenerator d S L n n k (𝟙_ I) b =
      (λ_ (weightedCoend.objects (weight d n k) S b)).hom ≫
        weightedCoend.ι (weight d n k) S b := by
  let C : V := ((𝟙_ I) ⊗ n) ⟶[V] n
  let Z : V := (b ⊗ n) ⟶[V] k
  let A : V := S.obj (𝟙_ I)
  let B : V := S.obj b
  let T : V := ((b ⊗ (𝟙_ I)) ⊗ n) ⟶[V] k
  let p : (𝟙_ V) ⟶ C := eHomEquiv V (λ_ n).hom
  let u : Z ⟶ C ⊗ Z := (λ_ Z).inv ≫ (p ⊗ₘ 𝟙 Z)
  let v : B ⟶ B ⊗ A := (ρ_ B).inv ≫ (𝟙 B ⊗ₘ L.epsilon)
  let wa : Z ⟶ T := (ρ_ Z).inv ≫ Z ◁ eHomEquiv V (ρ_ b).hom ≫
    MonoidalClosed.uncurry ((weight d n k).map (op b) (op (b ⊗ (𝟙_ I))))
  have hIndex : u ≫ indexGenerator d n n k (𝟙_ I) b =
      eHomWhiskerRight V ((ρ_ b).hom ⊗ₘ 𝟙 n) k := by
    simpa only [u, p, Z, Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun f : (𝟙_ V) ⊗ Z ⟶ T => (λ_ Z).inv ≫ f)
        (identityFirstIndexForProof d n k b)
  have hWeight : u ≫ indexGenerator d n n k (𝟙_ I) b = wa :=
    hIndex.trans (weight_point_pre d n k (b ⊗ (𝟙_ I)) b (ρ_ b).hom).symm
  have hPair : (u ⊗ₘ v) ≫
        (indexGenerator d n n k (𝟙_ I) b ⊗ₘ L.mu b (𝟙_ I)) =
      wa ⊗ₘ (v ≫ L.mu b (𝟙_ I)) :=
    (MonoidalCategory.tensorHom_comp_tensorHom u v
      (indexGenerator d n n k (𝟙_ I) b) (L.mu b (𝟙_ I))).trans
      (congrArg (fun f : Z ⟶ T => f ⊗ₘ (v ≫ L.mu b (𝟙_ I))) hWeight)
  have hPadding := tensorDeltaFirstUnitPaddingForProof C Z A B p L.epsilon
  have hTarget : (wa ⊗ₘ (v ≫ L.mu b (𝟙_ I))) ≫
        weightedCoend.ι (weight d n k) S (b ⊗ (𝟙_ I)) =
      weightedCoend.ι (weight d n k) S b := by
    simpa only [wa, v, Z, B, Category.assoc, weight_obj] using
      targetRightUnitRelationForProof d S L n k b
  calc
    _ = (λ_ (Z ⊗ B)).hom ≫ (u ⊗ₘ v) ≫
        (indexGenerator d n n k (𝟙_ I) b ⊗ₘ L.mu b (𝟙_ I)) ≫
        weightedCoend.ι (weight d n k) S (b ⊗ (𝟙_ I)) := by
      dsimp only [compositionGenerator]
      simpa only [C, Z, A, B, p, u, v, Category.assoc, operator_objects] using congrArg
        (fun f : (𝟙_ V) ⊗ (Z ⊗ B) ⟶ (C ⊗ Z) ⊗ (B ⊗ A) =>
          f ≫ (indexGenerator d n n k (𝟙_ I) b ⊗ₘ L.mu b (𝟙_ I)) ≫
            weightedCoend.ι (weight d n k) S (b ⊗ (𝟙_ I))) hPadding
    _ = (λ_ (Z ⊗ B)).hom ≫ (wa ⊗ₘ (v ≫ L.mu b (𝟙_ I))) ≫
        weightedCoend.ι (weight d n k) S (b ⊗ (𝟙_ I)) := by
      exact ((Category.assoc (u ⊗ₘ v)
        (indexGenerator d n n k (𝟙_ I) b ⊗ₘ L.mu b (𝟙_ I))
        (weightedCoend.ι (weight d n k) S (b ⊗ (𝟙_ I)))).symm
        |> congrArg (fun f => (λ_ (Z ⊗ B)).hom ≫ f)).trans
          (congrArg
            (fun f : Z ⊗ B ⟶ T ⊗ S.obj (b ⊗ (𝟙_ I)) =>
              (λ_ (Z ⊗ B)).hom ≫ f ≫
                weightedCoend.ι (weight d n k) S (b ⊗ (𝟙_ I))) hPair)
    _ = _ := congrArg
      (fun f : Z ⊗ B ⟶ Hom d S n k => (λ_ (Z ⊗ B)).hom ≫ f) hTarget

/-- The second unit generator uses the full target left-unitor relation. -/
private theorem secondUnitRawGeneratorForProof (a : I) :
    (𝟙 (weightedCoend.objects (weight d n k) S a) ⊗ₘ
        ((λ_ (𝟙_ V)).inv ≫
          (eHomEquiv V (λ_ k).hom ⊗ₘ L.epsilon))) ≫
        compositionGenerator d S L n k k a (𝟙_ I) =
      (ρ_ (weightedCoend.objects (weight d n k) S a)).hom ≫
        weightedCoend.ι (weight d n k) S a := by
  let X : V := (a ⊗ n) ⟶[V] k
  let Z : V := ((𝟙_ I) ⊗ k) ⟶[V] k
  let A : V := S.obj a
  let B : V := S.obj (𝟙_ I)
  let T : V := (((𝟙_ I) ⊗ a) ⊗ n) ⟶[V] k
  let p : (𝟙_ V) ⟶ Z := eHomEquiv V (λ_ k).hom
  let u : X ⟶ X ⊗ Z := (ρ_ X).inv ≫ (𝟙 X ⊗ₘ p)
  let v : A ⟶ B ⊗ A := (λ_ A).inv ≫ (L.epsilon ⊗ₘ 𝟙 A)
  let wa : X ⟶ T := (ρ_ X).inv ≫ X ◁ eHomEquiv V (λ_ a).hom ≫
    MonoidalClosed.uncurry ((weight d n k).map (op a) (op ((𝟙_ I) ⊗ a)))
  have hIndex : u ≫ indexGenerator d n k k a (𝟙_ I) =
      eHomWhiskerRight V ((λ_ a).hom ⊗ₘ 𝟙 n) k := by
    simpa only [u, p, X, Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun f : X ⊗ (𝟙_ V) ⟶ T => (ρ_ X).inv ≫ f)
        (identitySecondIndexForProof d n k a)
  have hWeight : u ≫ indexGenerator d n k k a (𝟙_ I) = wa :=
    hIndex.trans (weight_point_pre d n k ((𝟙_ I) ⊗ a) a (λ_ a).hom).symm
  have hPair : (u ⊗ₘ v) ≫
        (indexGenerator d n k k a (𝟙_ I) ⊗ₘ L.mu (𝟙_ I) a) =
      wa ⊗ₘ (v ≫ L.mu (𝟙_ I) a) :=
    (MonoidalCategory.tensorHom_comp_tensorHom u v
      (indexGenerator d n k k a (𝟙_ I)) (L.mu (𝟙_ I) a)).trans
      (congrArg (fun f : X ⟶ T => f ⊗ₘ (v ≫ L.mu (𝟙_ I) a)) hWeight)
  have hPadding := tensorDeltaSecondUnitPaddingForProof X Z A B p L.epsilon
  have hTarget : (wa ⊗ₘ (v ≫ L.mu (𝟙_ I) a)) ≫
        weightedCoend.ι (weight d n k) S ((𝟙_ I) ⊗ a) =
      weightedCoend.ι (weight d n k) S a := by
    simpa only [wa, v, X, A, Category.assoc, weight_obj] using
      targetLeftUnitRelationForProof d S L n k a
  calc
    _ = (ρ_ (X ⊗ A)).hom ≫ (u ⊗ₘ v) ≫
        (indexGenerator d n k k a (𝟙_ I) ⊗ₘ L.mu (𝟙_ I) a) ≫
        weightedCoend.ι (weight d n k) S ((𝟙_ I) ⊗ a) := by
      dsimp only [compositionGenerator]
      simpa only [X, Z, A, B, p, u, v, Category.assoc, operator_objects] using congrArg
        (fun f : (X ⊗ A) ⊗ (𝟙_ V) ⟶ (X ⊗ Z) ⊗ (B ⊗ A) =>
          f ≫ (indexGenerator d n k k a (𝟙_ I) ⊗ₘ L.mu (𝟙_ I) a) ≫
            weightedCoend.ι (weight d n k) S ((𝟙_ I) ⊗ a)) hPadding
    _ = (ρ_ (X ⊗ A)).hom ≫ (wa ⊗ₘ (v ≫ L.mu (𝟙_ I) a)) ≫
        weightedCoend.ι (weight d n k) S ((𝟙_ I) ⊗ a) := by
      exact ((Category.assoc (u ⊗ₘ v)
        (indexGenerator d n k k a (𝟙_ I) ⊗ₘ L.mu (𝟙_ I) a)
        (weightedCoend.ι (weight d n k) S ((𝟙_ I) ⊗ a))).symm
        |> congrArg (fun f => (ρ_ (X ⊗ A)).hom ≫ f)).trans
          (congrArg
            (fun f : X ⊗ A ⟶ T ⊗ S.obj ((𝟙_ I) ⊗ a) =>
              (ρ_ (X ⊗ A)).hom ≫ f ≫
                weightedCoend.ι (weight d n k) S ((𝟙_ I) ⊗ a)) hPair)
    _ = _ := congrArg
      (fun f : X ⊗ A ⟶ Hom d S n k => (ρ_ (X ⊗ A)).hom ≫ f) hTarget

section FirstIdentityCoend

variable [HasCoproduct (weightedCoend.relations (weight d n n) S)]
  [HasCoproduct (weightedCoend.objects (weight d n n) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d n n) S)
    (weightedCoend.rightMap (weight d n n) S)]

/-- The first identity law on every entire original coend generator. -/
theorem identity_composition_generator (b : I) :
    (identityGenerator d S L n ⊗ₘ weightedCoend.ι (weight d n k) S b) ≫
        composition d S L n n k =
      (λ_ (weightedCoend.objects (weight d n k) S b)).hom ≫
        weightedCoend.ι (weight d n k) S b := by
  let U : V := weightedCoend.objects (weight d n k) S b
  let p : (𝟙_ V) ⟶ weightedCoend.objects (weight d n n) S (𝟙_ I) :=
    (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V (λ_ n).hom ⊗ₘ L.epsilon)
  have hSplit : (p ⊗ₘ 𝟙 U) ≫
        (weightedCoend.ι (weight d n n) S (𝟙_ I) ⊗ₘ
          weightedCoend.ι (weight d n k) S b) =
      identityGenerator d S L n ⊗ₘ weightedCoend.ι (weight d n k) S b := by
    have h := MonoidalCategory.tensorHom_comp_tensorHom p (𝟙 U)
      (weightedCoend.ι (weight d n n) S (𝟙_ I))
      (weightedCoend.ι (weight d n k) S b)
    simp only [Category.id_comp] at h
    have hId : p ≫ weightedCoend.ι (weight d n n) S (𝟙_ I) =
        identityGenerator d S L n := by
      dsimp only [p, identityGenerator]
      exact Category.assoc _ _ _
    exact h.trans (congrArg
      (fun f => f ⊗ₘ weightedCoend.ι (weight d n k) S b) hId)
  calc
    _ = ((p ⊗ₘ 𝟙 U) ≫
        (weightedCoend.ι (weight d n n) S (𝟙_ I) ⊗ₘ
          weightedCoend.ι (weight d n k) S b)) ≫ composition d S L n n k :=
      congrArg (fun f : (𝟙_ V) ⊗ U ⟶ Hom d S n n ⊗ Hom d S n k =>
        f ≫ composition d S L n n k) hSplit.symm
    _ = (p ⊗ₘ 𝟙 U) ≫ compositionGenerator d S L n n k (𝟙_ I) b := by
      rw [Category.assoc, composition_generator]
    _ = _ := firstUnitRawGeneratorForProof d S L n k b

/-- The first identity is a unit for the whole derived composition. -/
theorem identity_composition :
    (identityGenerator d S L n ⊗ₘ 𝟙 (Hom d S n k)) ≫
        composition d S L n n k = (λ_ (Hom d S n k)).hom := by
  apply weightedCoend.Mapped.hom_ext (weight d n k) S (tensorLeft (𝟙_ V))
  intro b
  let U : V := weightedCoend.objects (weight d n k) S b
  let q : U ⟶ Hom d S n k := weightedCoend.ι (weight d n k) S b
  have hSplit : ((𝟙_ V) ◁ q) ≫
        (identityGenerator d S L n ⊗ₘ 𝟙 (Hom d S n k)) =
      identityGenerator d S L n ⊗ₘ q := by
    simpa only [MonoidalCategory.id_tensorHom, Category.id_comp,
      Category.comp_id] using
      MonoidalCategory.tensorHom_comp_tensorHom (𝟙 (𝟙_ V)) q
        (identityGenerator d S L n) (𝟙 (Hom d S n k))
  change ((𝟙_ V) ◁ q) ≫
      ((identityGenerator d S L n ⊗ₘ 𝟙 (Hom d S n k)) ≫
        composition d S L n n k) = ((𝟙_ V) ◁ q) ≫ (λ_ (Hom d S n k)).hom
  calc
    _ = (identityGenerator d S L n ⊗ₘ q) ≫ composition d S L n n k := by
      exact (Category.assoc ((𝟙_ V) ◁ q)
        (identityGenerator d S L n ⊗ₘ 𝟙 (Hom d S n k))
        (composition d S L n n k)).symm.trans
          (congrArg (fun f : (𝟙_ V) ⊗ U ⟶ Hom d S n n ⊗ Hom d S n k =>
            f ≫ composition d S L n n k) hSplit)
    _ = (λ_ U).hom ≫ q := identity_composition_generator d S L n k b
    _ = _ := (MonoidalCategory.leftUnitor_naturality q).symm

end FirstIdentityCoend

section SecondIdentityCoend

variable [HasCoproduct (weightedCoend.relations (weight d k k) S)]
  [HasCoproduct (weightedCoend.objects (weight d k k) S)]
  [HasCoequalizer (weightedCoend.leftMap (weight d k k) S)
    (weightedCoend.rightMap (weight d k k) S)]

/-- The second identity law retains every entire original coend generator. -/
theorem composition_identity_generator (a : I) :
    (weightedCoend.ι (weight d n k) S a ⊗ₘ identityGenerator d S L k) ≫
        composition d S L n k k =
      (ρ_ (weightedCoend.objects (weight d n k) S a)).hom ≫
        weightedCoend.ι (weight d n k) S a := by
  let U : V := weightedCoend.objects (weight d n k) S a
  let p : (𝟙_ V) ⟶ weightedCoend.objects (weight d k k) S (𝟙_ I) :=
    (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V (λ_ k).hom ⊗ₘ L.epsilon)
  have hSplit : (𝟙 U ⊗ₘ p) ≫
        (weightedCoend.ι (weight d n k) S a ⊗ₘ
          weightedCoend.ι (weight d k k) S (𝟙_ I)) =
      weightedCoend.ι (weight d n k) S a ⊗ₘ identityGenerator d S L k := by
    have h := MonoidalCategory.tensorHom_comp_tensorHom (𝟙 U) p
      (weightedCoend.ι (weight d n k) S a)
      (weightedCoend.ι (weight d k k) S (𝟙_ I))
    simp only [Category.id_comp] at h
    have hId : p ≫ weightedCoend.ι (weight d k k) S (𝟙_ I) =
        identityGenerator d S L k := by
      dsimp only [p, identityGenerator]
      exact Category.assoc _ _ _
    exact h.trans (congrArg
      (fun f => weightedCoend.ι (weight d n k) S a ⊗ₘ f) hId)
  calc
    _ = ((𝟙 U ⊗ₘ p) ≫
        (weightedCoend.ι (weight d n k) S a ⊗ₘ
          weightedCoend.ι (weight d k k) S (𝟙_ I))) ≫ composition d S L n k k :=
      congrArg (fun f : U ⊗ (𝟙_ V) ⟶ Hom d S n k ⊗ Hom d S k k =>
        f ≫ composition d S L n k k) hSplit.symm
    _ = (𝟙 U ⊗ₘ p) ≫ compositionGenerator d S L n k k a (𝟙_ I) := by
      rw [Category.assoc, composition_generator]
    _ = _ := secondUnitRawGeneratorForProof d S L n k a

/-- The second identity is a unit for the whole derived composition. -/
theorem composition_identity :
    (𝟙 (Hom d S n k) ⊗ₘ identityGenerator d S L k) ≫
        composition d S L n k k = (ρ_ (Hom d S n k)).hom := by
  apply weightedCoend.Mapped.hom_ext (weight d n k) S (tensorRight (𝟙_ V))
  intro a
  let U : V := weightedCoend.objects (weight d n k) S a
  let q : U ⟶ Hom d S n k := weightedCoend.ι (weight d n k) S a
  have hSplit : (q ▷ (𝟙_ V)) ≫
        (𝟙 (Hom d S n k) ⊗ₘ identityGenerator d S L k) =
      q ⊗ₘ identityGenerator d S L k := by
    simpa only [MonoidalCategory.tensorHom_id, Category.id_comp,
      Category.comp_id] using
      MonoidalCategory.tensorHom_comp_tensorHom q (𝟙 (𝟙_ V))
        (𝟙 (Hom d S n k)) (identityGenerator d S L k)
  change (q ▷ (𝟙_ V)) ≫
      ((𝟙 (Hom d S n k) ⊗ₘ identityGenerator d S L k) ≫
        composition d S L n k k) = (q ▷ (𝟙_ V)) ≫ (ρ_ (Hom d S n k)).hom
  calc
    _ = (q ⊗ₘ identityGenerator d S L k) ≫ composition d S L n k k := by
      exact (Category.assoc (q ▷ (𝟙_ V))
        (𝟙 (Hom d S n k) ⊗ₘ identityGenerator d S L k)
        (composition d S L n k k)).symm.trans
          (congrArg (fun f : U ⊗ (𝟙_ V) ⟶ Hom d S n k ⊗ Hom d S k k =>
            f ≫ composition d S L n k k) hSplit)
    _ = (ρ_ U).hom ≫ q := composition_identity_generator d S L n k a
    _ = _ := (MonoidalCategory.rightUnitor_naturality q).symm

end SecondIdentityCoend

end CategoryTheory.Enriched.SphereOperator
