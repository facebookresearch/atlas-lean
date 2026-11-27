/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Kernel

/-!
# The enriched output functor of a Day kernel

The output hom acts through the actual kernel generators. Only the particular
kernel coproducts and coequalizer for each output object are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC uD uK uV vV

namespace CategoryTheory.EnrichedDayKernel.Output

open MonoidalCategory BraidedCategory Opposite Limits
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {K : Type uK} [EnrichedCategory V K]

def outputAction (x k k' : K) (Q : V) :
    (k ⟶[V] k') ⊗ ((x ⟶[V] k) ⊗ Q) ⟶
      (x ⟶[V] k') ⊗ Q :=
  (α_ (k ⟶[V] k') (x ⟶[V] k) Q).inv ≫
    ((β_ (k ⟶[V] k') (x ⟶[V] k)).hom ⊗ₘ 𝟙 Q) ≫
    (eComp V x k k' ⊗ₘ 𝟙 Q)

private def precomposeAction
    (x y k : K) {H : V} (t : H ⟶ (x ⟶[V] y)) (Q : V) :
    (y ⟶[V] k) ⊗ (H ⊗ Q) ⟶ (x ⟶[V] k) ⊗ Q :=
  (α_ (y ⟶[V] k) H Q).inv ≫
    ((((y ⟶[V] k) ◁ t) ≫
      (β_ (y ⟶[V] k) (x ⟶[V] y)).hom ≫
      eComp V x y k) ⊗ₘ 𝟙 Q)

private def outputBase (x k k' : K) :
    (k ⟶[V] k') ⊗ (x ⟶[V] k) ⟶ (x ⟶[V] k') :=
  (β_ (k ⟶[V] k') (x ⟶[V] k)).hom ≫ eComp V x k k'

private def precomposeBase
    (x y k : K) {H : V} (t : H ⟶ (x ⟶[V] y)) :
    (y ⟶[V] k) ⊗ H ⟶ (x ⟶[V] k) :=
  ((y ⟶[V] k) ◁ t) ≫
    (β_ (y ⟶[V] k) (x ⟶[V] y)).hom ≫
    eComp V x y k

private theorem outputBase_precompose
    (x y k k' : K) {H : V} (t : H ⟶ (x ⟶[V] y)) :
    (k ⟶[V] k') ◁ precomposeBase x y k t ≫
        outputBase x k k' =
      outputAction y k k' H ≫ precomposeBase x y k' t := by
  let A : V := x ⟶[V] y
  let W : V := y ⟶[V] k
  let R : V := k ⟶[V] k'
  let pre : R ⊗ (W ⊗ H) ⟶ A ⊗ (W ⊗ R) :=
    R ◁ ((W ◁ t) ≫ (β_ W A).hom) ≫
      (β_ R (A ⊗ W)).hom ≫
      (α_ A W R).hom
  have h :
      (α_ A W R).inv ≫ eComp V x y k ▷ R ≫
          eComp V x k k' =
        A ◁ eComp V y k k' ≫ eComp V x y k' := by
    dsimp only [A, W, R]
    exact e_assoc V x y k k'
  calc
    _ = pre ≫
        ((α_ A W R).inv ≫
          eComp V x y k ▷ R ≫ eComp V x k k') := by
      dsimp only [outputBase, outputAction, precomposeBase,
        pre, A, W, R]
      simp only [MonoidalCategory.whiskerLeft_comp,
        Category.assoc, Iso.hom_inv_id_assoc]
      have hb :
          (k ⟶[V] k') ◁ eComp V x y k ≫
              (β_ (k ⟶[V] k') (x ⟶[V] k)).hom =
            (β_ (k ⟶[V] k')
                (((x ⟶[V] y) ⊗ (y ⟶[V] k)))).hom ≫
              eComp V x y k ▷ (k ⟶[V] k') := by
        simpa only [id_tensorHom, tensorHom_id] using
          braiding_naturality (𝟙 (k ⟶[V] k'))
            (eComp V x y k)
      have hb' :
          (k ⟶[V] k') ◁ eComp V x y k ≫
                (β_ (k ⟶[V] k') (x ⟶[V] k)).hom ≫
              eComp V x k k' =
            (β_ (k ⟶[V] k')
                (((x ⟶[V] y) ⊗ (y ⟶[V] k)))).hom ≫
              eComp V x y k ▷ (k ⟶[V] k') ≫
              eComp V x k k' := by
        simpa only [id_tensorHom, tensorHom_id] using
          braiding_naturality_assoc (𝟙 (k ⟶[V] k'))
            (eComp V x y k) (eComp V x k k')
      rw [hb']
    _ = _ := by rw [h]
    _ = _ := by
      dsimp only [outputBase, outputAction, precomposeBase,
        pre, A, W, R]
      simp only [MonoidalCategory.whiskerLeft_comp,
        Category.assoc]
      have hb :
          (k ⟶[V] k') ◁
                (β_ (y ⟶[V] k) (x ⟶[V] y)).hom ≫
              (β_ (k ⟶[V] k')
                ((x ⟶[V] y) ⊗ (y ⟶[V] k))).hom ≫
              (α_ (x ⟶[V] y) (y ⟶[V] k)
                (k ⟶[V] k')).hom ≫
              (x ⟶[V] y) ◁ eComp V y k k' =
            outputAction y k k' (x ⟶[V] y) ≫
              (β_ (y ⟶[V] k') (x ⟶[V] y)).hom := by
        let R' : V := k ⟶[V] k'
        let W' : V := y ⟶[V] k
        let W'' : V := y ⟶[V] k'
        let c : W' ⊗ R' ⟶ W'' := eComp V y k k'
        have hn :
            (c ⊗ₘ 𝟙 (x ⟶[V] y)) ≫
                (β_ W'' (x ⟶[V] y)).hom =
              (β_ (W' ⊗ R') (x ⟶[V] y)).hom ≫
                (𝟙 (x ⟶[V] y) ⊗ₘ c) :=
          braiding_naturality c (𝟙 (x ⟶[V] y))
        have hyb :
            R' ◁ (β_ W' (x ⟶[V] y)).hom ≫
                (β_ R' ((x ⟶[V] y) ⊗ W')).hom ≫
                (α_ (x ⟶[V] y) W' R').hom =
              (α_ R' W' (x ⟶[V] y)).inv ≫
                ((β_ R' W').hom ⊗ₘ 𝟙 (x ⟶[V] y)) ≫
                (β_ (W' ⊗ R') (x ⟶[V] y)).hom := by
          simpa [braiding_tensor_right_hom,
            braiding_tensor_left_hom] using
              (yang_baxter R' W' (x ⟶[V] y)).symm
        dsimp only [outputAction, R', W', W'', c]
        simp only [Category.assoc]
        rw [hn]
        have hyb' := congrArg
          (fun q => q ≫ ((x ⟶[V] y) ◁ eComp V y k k')) hyb
        simpa only [Category.assoc, id_tensorHom] using hyb'
      have hb' := congrArg
        (fun q => q ≫ eComp V x y k') hb
      have hm :
          (k ⟶[V] k') ◁ ((y ⟶[V] k) ◁ t) ≫
              outputAction y k k' (x ⟶[V] y) =
            outputAction y k k' H ≫ ((y ⟶[V] k') ◁ t) := by
        dsimp only [outputAction]
        simp only [Category.assoc, tensorHom_id]
        rw [associator_inv_naturality_right_assoc]
        rw [whisker_exchange_assoc]
        rw [whisker_exchange (eComp V y k k') t]
      have hm' := congrArg
        (fun q => q ≫ (β_ (y ⟶[V] k') (x ⟶[V] y)).hom ≫
          eComp V x y k') hm
      simp only [Category.assoc] at hb' hm' ⊢
      rw [hb', hm']
      dsimp only [outputAction]
      simp only [Category.assoc]

@[reassoc]
private theorem outputAction_precompose
    (x y k k' : K) {H : V} (t : H ⟶ (x ⟶[V] y)) (Q : V) :
    (k ⟶[V] k') ◁ precomposeAction x y k t Q ≫
        outputAction x k k' Q =
      outputAction y k k' (H ⊗ Q) ≫
        precomposeAction x y k' t Q := by
  let R : V := k ⟶[V] k'
  let W : V := y ⟶[V] k
  let reassoc : R ⊗ (W ⊗ (H ⊗ Q)) ⟶
      (R ⊗ (W ⊗ H)) ⊗ Q :=
    R ◁ (α_ W H Q).inv ≫ (α_ R (W ⊗ H) Q).inv
  have h := outputBase_precompose x y k k' t
  have hQ := congrArg (fun q => q ⊗ₘ 𝟙 Q) h
  calc
    _ = reassoc ≫
        (((k ⟶[V] k') ◁ precomposeBase x y k t ≫
          outputBase x k k') ⊗ₘ 𝟙 Q) := by
      dsimp only [reassoc, R, W, precomposeAction,
        outputAction, precomposeBase, outputBase]
      monoidal
    _ = reassoc ≫
        ((outputAction y k k' H ≫
          precomposeBase x y k' t) ⊗ₘ 𝟙 Q) := by
      rw [hQ]
    _ = _ := by
      dsimp only [reassoc, R, W, precomposeAction,
        outputAction, precomposeBase]
      monoidal

@[reassoc]
private theorem outputAction_map
    (x k k' : K) {H Q Q' : V} (s : H ⊗ Q ⟶ Q') :
    (k ⟶[V] k') ◁ ((x ⟶[V] k) ◁ s) ≫
        outputAction x k k' Q' =
      outputAction x k k' (H ⊗ Q) ≫
        ((x ⟶[V] k') ◁ s) := by
  dsimp only [outputAction]
  simp only [Category.assoc, tensorHom_id]
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc]
  rw [whisker_exchange (eComp V x k k') s]

@[reassoc]
private theorem outputAction_id (x k : K) (Q : V) :
    (λ_ ((x ⟶[V] k) ⊗ Q)).inv ≫
        eId V k ▷ ((x ⟶[V] k) ⊗ Q) ≫
        outputAction x k k Q =
      𝟙 ((x ⟶[V] k) ⊗ Q) := by
  let W : V := x ⟶[V] k
  have hBase :
      ((λ_ W).inv ≫ eId V k ▷ W) ≫
          (β_ (k ⟶[V] k) W).hom ≫ eComp V x k k =
        𝟙 W := by
    simp only [Category.assoc]
    slice_lhs 2 3 =>
      rw [← tensorHom_id, braiding_naturality]
    slice_lhs 1 2 =>
      rw [leftUnitor_inv_braiding]
    rw [id_tensorHom]
    simpa only [W, Category.assoc] using e_comp_id V x k
  have hTensor := congrArg (fun q => q ⊗ₘ 𝟙 Q) hBase
  calc
    _ = ((((λ_ W).inv ≫ eId V k ▷ W) ≫
          (β_ (k ⟶[V] k) W).hom ≫ eComp V x k k) ⊗ₘ
        𝟙 Q) := by
      dsimp only [outputAction, W]
      monoidal
    _ = (𝟙 W ⊗ₘ 𝟙 Q) := hTensor
    _ = 𝟙 (W ⊗ Q) := MonoidalCategory.id_tensorHom_id W Q
    _ = 𝟙 ((x ⟶[V] k) ⊗ Q) := rfl

private theorem outputBase_comp (x k k' k'' : K) :
    (eComp V k k' k'' ⊗ₘ 𝟙 (x ⟶[V] k)) ≫
        outputBase x k k'' =
      (α_ (k ⟶[V] k') (k' ⟶[V] k'') (x ⟶[V] k)).hom ≫
        ((k ⟶[V] k') ◁
          (β_ (k' ⟶[V] k'') (x ⟶[V] k)).hom) ≫
        (α_ (k ⟶[V] k') (x ⟶[V] k) (k' ⟶[V] k'')).inv ≫
        (outputBase x k k' ▷ (k' ⟶[V] k'')) ≫
        (β_ (k' ⟶[V] k'') (x ⟶[V] k')).inv ≫
        outputBase x k' k'' := by
  let R : V := k ⟶[V] k'
  let S : V := k' ⟶[V] k''
  let W : V := x ⟶[V] k
  let pre : (R ⊗ S) ⊗ W ⟶ W ⊗ (R ⊗ S) :=
    (β_ (R ⊗ S) W).hom
  have hn := braiding_naturality (eComp V k k' k'') (𝟙 W)
  have ha := e_assoc V x k k' k''
  calc
    _ = pre ≫
        (W ◁ eComp V k k' k'' ≫ eComp V x k k'') := by
      simpa only [outputBase, pre, R, S, W,
        Category.assoc, id_tensorHom, tensorHom_id] using
          braiding_naturality_assoc (eComp V k k' k'')
            (𝟙 W) (eComp V x k k'')
    _ = pre ≫
        ((α_ W R S).inv ≫ eComp V x k k' ▷ S ≫
          eComp V x k' k'') := by
      rw [ha]
    _ = _ := by
      dsimp only [outputBase, pre, R, S, W]
      rw [braiding_tensor_left_hom]
      simp only [e_assoc, Category.assoc, comp_whiskerRight,
        Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
      rw [e_assoc']


variable [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]

attribute [local instance] Enriched.prodCategory

variable (T : EnrichedFunctor V (C × D) K)
  (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)

/-- The actual output hom acts on each actual kernel integrand. -/
def actionGenerator (k k' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k')]
    [HasCoproduct (EnrichedDayKernel.objects T F G k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k')
      (EnrichedDayKernel.rightMap T F G k')] (a : C × D) :
    (k ⟶[V] k') ⊗ EnrichedDayKernel.objects T F G k a ⟶
      EnrichedDayKernel.obj T F G k' :=
  outputAction (T.obj a) k k' ((F.externalTensor G).obj a) ≫
    EnrichedDayKernel.gen T F G k' a

/-- The actual curried output action is balanced over the whole product-enriched hom. -/
theorem actionGenerator_balanced (k k' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k')]
    [HasCoproduct (EnrichedDayKernel.objects T F G k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k')
      (EnrichedDayKernel.rightMap T F G k')] :
    EnrichedDayKernel.Balanced T F G k
      (fun a => MonoidalClosed.curry (actionGenerator T F G k k' a)) := by
  unfold EnrichedDayKernel.Balanced
  intro a b
  apply (MonoidalClosed.uncurry_injective
    (A := k ⟶[V] k')
    (X := EnrichedDayKernel.obj T F G k')
    (Y := EnrichedDayKernel.relations T F G k (a, b)))
  conv_lhs => rw [MonoidalClosed.uncurry_natural_left]
  conv_rhs => rw [MonoidalClosed.uncurry_natural_left]
  dsimp only
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry,
    EnrichedDayKernel.weight_uncurry_map]
  let x : K := T.obj a
  let y : K := T.obj b
  let H : V := a ⟶[V] b
  let Qa : V := (F.externalTensor G).obj a
  let Qb : V := (F.externalTensor G).obj b
  let t : H ⟶ (x ⟶[V] y) := T.map a b
  let s : H ⊗ Qa ⟶ Qb :=
    (β_ H Qa).hom ≫ MonoidalClosed.uncurry ((F.externalTensor G).map a b)
  have hc := EnrichedDayKernel.gen_balanced T F G k' a b
  rw [EnrichedDayKernel.weight_uncurry_map] at hc
  have hcRaw :
      precomposeAction x y k' t Qa ≫ EnrichedDayKernel.gen T F G k' a =
        (y ⟶[V] k') ◁ s ≫ EnrichedDayKernel.gen T F G k' b := by
    simpa only [precomposeAction, x, y, t, s, H, Qa, Qb,
      EnrichedDayKernel.weight_obj, Category.assoc] using hc
  let γa : (x ⟶[V] k') ⊗ Qa ⟶ EnrichedDayKernel.obj T F G k' :=
    EnrichedDayKernel.gen T F G k' a
  let γb : (y ⟶[V] k') ⊗ Qb ⟶ EnrichedDayKernel.obj T F G k' :=
    EnrichedDayKernel.gen T F G k' b
  have hc' : precomposeAction x y k' t Qa ≫ γa =
      (y ⟶[V] k') ◁ s ≫ γb := hcRaw
  change
    (k ⟶[V] k') ◁ precomposeAction x y k t Qa ≫
          outputAction x k k' Qa ≫ γa =
      (k ⟶[V] k') ◁ ((y ⟶[V] k) ◁ s) ≫
          outputAction y k k' Qb ≫ γb
  rw [outputAction_precompose_assoc, hc', ← outputAction_map_assoc]

/-- Curry and descend the full hom-object action through the actual coend. -/
def actionDesc (k k' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)]
    [HasCoproduct (EnrichedDayKernel.relations T F G k')]
    [HasCoproduct (EnrichedDayKernel.objects T F G k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k')
      (EnrichedDayKernel.rightMap T F G k')] :
    EnrichedDayKernel.obj T F G k ⟶
      (ihom (k ⟶[V] k')).obj (EnrichedDayKernel.obj T F G k') :=
  EnrichedDayKernel.desc T F G k
    (fun a => MonoidalClosed.curry (actionGenerator T F G k k' a))
    (actionGenerator_balanced T F G k k')

/-- Descent is characterized on every integrand generator. -/
@[reassoc]
theorem gen_actionDesc (k k' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)]
    [HasCoproduct (EnrichedDayKernel.relations T F G k')]
    [HasCoproduct (EnrichedDayKernel.objects T F G k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k')
      (EnrichedDayKernel.rightMap T F G k')] (a : C × D) :
    EnrichedDayKernel.gen T F G k a ≫ actionDesc T F G k k' =
      MonoidalClosed.curry (actionGenerator T F G k k' a) :=
  EnrichedDayKernel.gen_desc T F G k _ (actionGenerator_balanced T F G k k') a

/-- The literal enriched output map uses the inverse output-hom braid. -/
def map (k k' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)]
    [HasCoproduct (EnrichedDayKernel.relations T F G k')]
    [HasCoproduct (EnrichedDayKernel.objects T F G k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k')
      (EnrichedDayKernel.rightMap T F G k')] :
    (k ⟶[V] k') ⟶
      (ihom (EnrichedDayKernel.obj T F G k)).obj (EnrichedDayKernel.obj T F G k') :=
  MonoidalClosed.curry
    ((β_ (k ⟶[V] k') (EnrichedDayKernel.obj T F G k)).inv ≫
      MonoidalClosed.uncurry (actionDesc T F G k k'))

/-- The uncurried map is the actual inverse-braid composite. -/
theorem map_uncurry (k k' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)]
    [HasCoproduct (EnrichedDayKernel.relations T F G k')]
    [HasCoproduct (EnrichedDayKernel.objects T F G k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k')
      (EnrichedDayKernel.rightMap T F G k')] :
    MonoidalClosed.uncurry (map T F G k k') =
      (β_ (k ⟶[V] k') (EnrichedDayKernel.obj T F G k)).inv ≫
        MonoidalClosed.uncurry (actionDesc T F G k k') := by
  unfold map
  rw [MonoidalClosed.uncurry_curry]

/-- Full output-hom naturality of the actual generator maps. -/
@[reassoc]
theorem gen_naturality (k k' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)]
    [HasCoproduct (EnrichedDayKernel.relations T F G k')]
    [HasCoproduct (EnrichedDayKernel.objects T F G k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k')
      (EnrichedDayKernel.rightMap T F G k')] (a : C × D) :
    (β_ (k ⟶[V] k') (EnrichedDayKernel.objects T F G k a)).hom ≫
        (EnrichedDayKernel.gen T F G k a ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
        MonoidalClosed.uncurry (map T F G k k') =
      actionGenerator T F G k k' a := by
  rw [map_uncurry]
  let R : V := k ⟶[V] k'
  let X : V := EnrichedDayKernel.objects T F G k a
  let E : V := EnrichedDayKernel.obj T F G k
  let g : X ⟶ E := EnrichedDayKernel.gen T F G k a
  have hba := braiding_naturality_assoc (𝟙 R) g (β_ R E).inv
  have hcancel :
      (β_ R X).hom ≫ (g ⊗ₘ 𝟙 R) ≫ (β_ R E).inv = R ◁ g := by
    calc
      _ = (𝟙 R ⊗ₘ g) ≫ (β_ R E).hom ≫ (β_ R E).inv := hba.symm
      _ = R ◁ g := by simp
  have hcancel' := congrArg
    (fun q => q ≫ MonoidalClosed.uncurry (actionDesc T F G k k')) hcancel
  change
    (β_ R X).hom ≫ (g ⊗ₘ 𝟙 R) ≫ (β_ R E).inv ≫
      MonoidalClosed.uncurry (actionDesc T F G k k') =
        actionGenerator T F G k k' a
  calc
    _ = R ◁ g ≫ MonoidalClosed.uncurry (actionDesc T F G k k') := by
      simpa only [Category.assoc] using hcancel'
    _ = MonoidalClosed.uncurry (g ≫ actionDesc T F G k k') :=
      (MonoidalClosed.uncurry_natural_left g (actionDesc T F G k k')).symm
    _ = MonoidalClosed.uncurry
        (MonoidalClosed.curry (actionGenerator T F G k k' a)) := by
      rw [gen_actionDesc]
    _ = actionGenerator T F G k k' a := MonoidalClosed.uncurry_curry _

/-- The literal output map preserves the actual enriched identity. -/
theorem map_id (k : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)] :
    eId V k ≫ map T F G k k = eId V (EnrichedDayKernel.obj T F G k) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, map_uncurry]
  rw [MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry]
  let E : V := EnrichedDayKernel.obj T F G k
  apply (cancel_epi (ρ_ E).inv).1
  rw [Iso.inv_hom_id]
  apply EnrichedDayKernel.hom_ext T F G k
  intro a
  rw [← map_uncurry]
  let X : V := EnrichedDayKernel.objects T F G k a
  let R : V := k ⟶[V] k
  let u : X ⟶ R ⊗ X := (λ_ X).inv ≫ eId V k ▷ X
  have hStart :
      u ≫ (β_ R X).hom ≫ (EnrichedDayKernel.gen T F G k a ⊗ₘ 𝟙 R) =
        EnrichedDayKernel.gen T F G k a ≫ (ρ_ E).inv ≫ E ◁ eId V k := by
    dsimp only [u, R, X, E]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [← tensorHom_id, braiding_naturality]
    slice_lhs 1 2 => rw [leftUnitor_inv_braiding]
    rw [rightUnitor_inv_naturality_assoc]
    slice_lhs 2 3 =>
      rw [tensorHom_comp_tensorHom]
      simp
    slice_rhs 2 3 => rw [← tensorHom_def]
  have hStart' := congrArg
    (fun q => q ≫ MonoidalClosed.uncurry (map T F G k k)) hStart
  calc
    EnrichedDayKernel.gen T F G k a ≫ (ρ_ E).inv ≫ E ◁ eId V k ≫
        MonoidalClosed.uncurry (map T F G k k) =
      u ≫ (β_ R X).hom ≫ (EnrichedDayKernel.gen T F G k a ⊗ₘ 𝟙 R) ≫
        MonoidalClosed.uncurry (map T F G k k) := by
      simpa only [Category.assoc] using hStart'.symm
    _ = u ≫ actionGenerator T F G k k a := by rw [gen_naturality]
    _ = EnrichedDayKernel.gen T F G k a := by
      dsimp only [actionGenerator]
      have h := outputAction_id_assoc (T.obj a) k ((F.externalTensor G).obj a)
        (EnrichedDayKernel.gen T F G k a)
      simpa only [u, R, X, EnrichedDayKernel.objects,
        Enriched.weightedCoend.objects, EnrichedDayKernel.weight_obj,
        Category.assoc] using h
    _ = EnrichedDayKernel.gen T F G k a ≫ 𝟙 E := by rw [Category.comp_id]

/-- The literal output map preserves full enriched source-first composition. -/
theorem map_comp (k k' k'' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)]
    [HasCoproduct (EnrichedDayKernel.relations T F G k')]
    [HasCoproduct (EnrichedDayKernel.objects T F G k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k')
      (EnrichedDayKernel.rightMap T F G k')]
    [HasCoproduct (EnrichedDayKernel.relations T F G k'')]
    [HasCoproduct (EnrichedDayKernel.objects T F G k'')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k'')
      (EnrichedDayKernel.rightMap T F G k'')] :
    eComp V k k' k'' ≫ map T F G k k'' =
      (map T F G k k' ⊗ₘ map T F G k' k'') ≫
        eComp V (EnrichedDayKernel.obj T F G k)
          (EnrichedDayKernel.obj T F G k') (EnrichedDayKernel.obj T F G k'') := by
  let C₀ : V := EnrichedDayKernel.obj T F G k
  let C₁ : V := EnrichedDayKernel.obj T F G k'
  let C₂ : V := EnrichedDayKernel.obj T F G k''
  let R : V := k ⟶[V] k'
  let S : V := k' ⟶[V] k''
  have hUC {A B C H K : V}
      (p : H ⟶ (ihom A).obj B) (q : K ⟶ (ihom B).obj C) :
      MonoidalClosed.uncurry
          ((p ⊗ₘ q) ≫ eComp V A B C) =
        (α_ A H K).inv ≫
          (MonoidalClosed.uncurry p ▷ K) ≫
          MonoidalClosed.uncurry q := by
    simp only [MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.enrichedCategorySelf_comp,
      MonoidalClosed.comp_eq, MonoidalClosed.uncurry_curry,
      MonoidalClosed.compTranspose_eq]
    have hTensor :
        A ◁ (p ⊗ₘ q) ≫
            (α_ A ((ihom A).obj B) ((ihom B).obj C)).inv =
          (α_ A H K).inv ≫
            ((A ◁ p) ▷ K) ≫
            (A ⊗ (ihom A).obj B) ◁ q := by
      simpa only [id_tensorHom, tensorHom_def,
        MonoidalCategory.id_whiskerRight, Category.id_comp,
        comp_whiskerRight] using
          (associator_inv_naturality (𝟙 A) p q)
    rw [← Category.assoc, hTensor]
    simp only [Category.assoc]
    rw [whisker_exchange_assoc]
    rw [← comp_whiskerRight_assoc]
    rw [← MonoidalClosed.uncurry_eq]
    dsimp
    rw [← MonoidalClosed.uncurry_eq]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  rw [hUC]
  apply (cancel_epi (β_ (R ⊗ S) C₀).hom).1
  apply MonoidalClosed.curry_injective
  apply EnrichedDayKernel.hom_ext T F G k
  intro ij
  apply MonoidalClosed.uncurry_injective
  simp only [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  let x : K :=
    T.obj ij
  let Q : V := (F.externalTensor G).obj ij
  let W₀ : V := x ⟶[V] k
  let W₁ : V := x ⟶[V] k'
  let W₂ : V := x ⟶[V] k''
  let X₀ : V := W₀ ⊗ Q
  let X₁ : V := W₁ ⊗ Q
  let X₂ : V := W₂ ⊗ Q
  let R₂ : V := k ⟶[V] k''
  let c : R ⊗ S ⟶ R₂ := eComp V k k' k''
  let γ₀ : X₀ ⟶ C₀ := EnrichedDayKernel.gen T F G k ij
  let γ₁ : X₁ ⟶ C₁ := EnrichedDayKernel.gen T F G k' ij
  let γ₂ : X₂ ⟶ C₂ := EnrichedDayKernel.gen T F G k'' ij
  change
    (R ⊗ S) ◁ γ₀ ≫ (β_ (R ⊗ S) C₀).hom ≫
          C₀ ◁ c ≫ MonoidalClosed.uncurry (map T F G k k'') =
      (R ⊗ S) ◁ γ₀ ≫ (β_ (R ⊗ S) C₀).hom ≫
        (α_ C₀ R S).inv ≫
        (MonoidalClosed.uncurry (map T F G k k') ▷ S) ≫
        MonoidalClosed.uncurry (map T F G k' k'')
  have hMove :
      (R ⊗ S) ◁ γ₀ ≫ (β_ (R ⊗ S) C₀).hom ≫ C₀ ◁ c =
        (c ⊗ₘ 𝟙 X₀) ≫ (β_ R₂ X₀).hom ≫
          (γ₀ ⊗ₘ 𝟙 R₂) := by
    calc
      _ = (𝟙 (R ⊗ S) ⊗ₘ γ₀) ≫
            (β_ (R ⊗ S) C₀).hom ≫ (𝟙 C₀ ⊗ₘ c) := by
          simp only [id_tensorHom]
      _ = (β_ (R ⊗ S) X₀).hom ≫
            (γ₀ ⊗ₘ 𝟙 (R ⊗ S)) ≫ (𝟙 C₀ ⊗ₘ c) := by
          simpa only [Category.assoc] using
            braiding_naturality_assoc (𝟙 (R ⊗ S)) γ₀
              (𝟙 C₀ ⊗ₘ c)
      _ = (β_ (R ⊗ S) X₀).hom ≫ (γ₀ ⊗ₘ c) := by
          rw [tensorHom_comp_tensorHom]
          simp
      _ = (c ⊗ₘ γ₀) ≫ (β_ R₂ C₀).hom := by
          exact (braiding_naturality c γ₀).symm
      _ = (c ⊗ₘ 𝟙 X₀) ≫ (𝟙 R₂ ⊗ₘ γ₀) ≫
            (β_ R₂ C₀).hom := by
          rw [← Category.assoc, tensorHom_comp_tensorHom]
          simp
      _ = _ := by
          have h := braiding_naturality (𝟙 R₂) γ₀
          have h' := congrArg (fun q => (c ⊗ₘ 𝟙 X₀) ≫ q) h
          simpa only [Category.assoc, id_tensorHom,
            tensorHom_id] using h'
  have hL :
      (R ⊗ S) ◁ γ₀ ≫ (β_ (R ⊗ S) C₀).hom ≫
            C₀ ◁ c ≫ MonoidalClosed.uncurry (map T F G k k'') =
        (c ⊗ₘ 𝟙 X₀) ≫ outputAction x k k'' Q ≫ γ₂ := by
    have hMove' := congrArg
      (fun q => q ≫ MonoidalClosed.uncurry (map T F G k k'')) hMove
    have hGN :
        (β_ R₂ X₀).hom ≫ (γ₀ ⊗ₘ 𝟙 R₂) ≫
              MonoidalClosed.uncurry (map T F G k k'') =
          outputAction x k k'' Q ≫ γ₂ := by
      dsimp only [R₂, X₀, W₀, Q, x, γ₀, γ₂, X₂, W₂, C₀, C₂]
      simpa only [actionGenerator, EnrichedDayKernel.objects,
        Enriched.weightedCoend.objects, EnrichedDayKernel.weight_obj,
        EnrichedFunctor.externalTensor_obj] using
          gen_naturality T F G k k'' ij
    have hGN' := congrArg (fun q => (c ⊗ₘ 𝟙 X₀) ≫ q) hGN
    calc
      _ = (c ⊗ₘ 𝟙 X₀) ≫ (β_ R₂ X₀).hom ≫
            (γ₀ ⊗ₘ 𝟙 R₂) ≫
            MonoidalClosed.uncurry (map T F G k k'') := by
          simpa only [Category.assoc] using hMove'
      _ = _ := by simpa only [Category.assoc] using hGN'
  have hGN₀₁ :
      (β_ R X₀).hom ≫ (γ₀ ⊗ₘ 𝟙 R) ≫
            MonoidalClosed.uncurry (map T F G k k') =
        outputAction x k k' Q ≫ γ₁ := by
    dsimp only [R, X₀, W₀, Q, x, γ₀, γ₁, X₁, W₁, C₀, C₁]
    simpa only [actionGenerator, EnrichedDayKernel.objects,
      Enriched.weightedCoend.objects, EnrichedDayKernel.weight_obj,
      EnrichedFunctor.externalTensor_obj] using
        gen_naturality T F G k k' ij
  have hG₀₁ :
      (γ₀ ⊗ₘ 𝟙 R) ≫ MonoidalClosed.uncurry (map T F G k k') =
        (β_ R X₀).inv ≫ outputAction x k k' Q ≫ γ₁ := by
    have h := congrArg (fun q => (β_ R X₀).inv ≫ q) hGN₀₁
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  have hGN₁₂ :
      (β_ S X₁).hom ≫ (γ₁ ⊗ₘ 𝟙 S) ≫
            MonoidalClosed.uncurry (map T F G k' k'') =
        outputAction x k' k'' Q ≫ γ₂ := by
    dsimp only [S, X₁, W₁, Q, x, γ₁, γ₂, X₂, W₂, C₁, C₂]
    simpa only [actionGenerator, EnrichedDayKernel.objects,
      Enriched.weightedCoend.objects, EnrichedDayKernel.weight_obj,
      EnrichedFunctor.externalTensor_obj] using
        gen_naturality T F G k' k'' ij
  have hG₁₂ :
      (γ₁ ⊗ₘ 𝟙 S) ≫ MonoidalClosed.uncurry (map T F G k' k'') =
        (β_ S X₁).inv ≫ outputAction x k' k'' Q ≫ γ₂ := by
    have h := congrArg (fun q => (β_ S X₁).inv ≫ q) hGN₁₂
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  have hBra :
      (R ⊗ S) ◁ γ₀ ≫ (β_ (R ⊗ S) C₀).hom =
        (β_ (R ⊗ S) X₀).hom ≫
          (γ₀ ⊗ₘ 𝟙 (R ⊗ S)) := by
    simpa only [id_tensorHom] using
      braiding_naturality (𝟙 (R ⊗ S)) γ₀
  have hAssoc :
      (γ₀ ⊗ₘ 𝟙 (R ⊗ S)) ≫ (α_ C₀ R S).inv =
        (α_ X₀ R S).inv ≫ ((γ₀ ⊗ₘ 𝟙 R) ⊗ₘ 𝟙 S) := by
    simpa only [id_tensorHom, tensorHom_id,
      MonoidalCategory.id_whiskerRight] using
      associator_inv_naturality γ₀ (𝟙 R) (𝟙 S)
  have hTensorEval :
      ((γ₀ ⊗ₘ 𝟙 R) ⊗ₘ 𝟙 S) ≫
            (MonoidalClosed.uncurry (map T F G k k') ▷ S) =
        (((γ₀ ⊗ₘ 𝟙 R) ≫
          MonoidalClosed.uncurry (map T F G k k')) ⊗ₘ 𝟙 S) := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom]
    simp
  have hStart :
      (R ⊗ S) ◁ γ₀ ≫ (β_ (R ⊗ S) C₀).hom ≫
            (α_ C₀ R S).inv ≫
            (MonoidalClosed.uncurry (map T F G k k') ▷ S) ≫
            MonoidalClosed.uncurry (map T F G k' k'') =
        (β_ (R ⊗ S) X₀).hom ≫ (α_ X₀ R S).inv ≫
            (((γ₀ ⊗ₘ 𝟙 R) ≫
              MonoidalClosed.uncurry (map T F G k k')) ⊗ₘ 𝟙 S) ≫
            MonoidalClosed.uncurry (map T F G k' k'') := by
    slice_lhs 1 2 => rw [hBra]
    slice_lhs 2 3 => rw [hAssoc]
    slice_lhs 3 4 => rw [hTensorEval]
  have hExpand :
      ((((β_ R X₀).inv ≫ outputAction x k k' Q ≫ γ₁) ⊗ₘ 𝟙 S) ≫
          MonoidalClosed.uncurry (map T F G k' k'')) =
        ((β_ R X₀).inv ⊗ₘ 𝟙 S) ≫
          (outputAction x k k' Q ⊗ₘ 𝟙 S) ≫
          (γ₁ ⊗ₘ 𝟙 S) ≫
          MonoidalClosed.uncurry (map T F G k' k'') := by
    symm
    simp only [tensorHom_id]
    rw [comp_whiskerRight, comp_whiskerRight]
    simp only [Category.assoc]
  have hPX :
      (β_ (R ⊗ S) X₀).hom ≫ (α_ X₀ R S).inv ≫
            ((β_ R X₀).inv ⊗ₘ 𝟙 S) =
        (α_ R S X₀).hom ≫ (R ◁ (β_ S X₀).hom) ≫
          (α_ R X₀ S).inv := by
    rw [braiding_tensor_left_hom]
    simp
  have hR :
      (R ⊗ S) ◁ γ₀ ≫ (β_ (R ⊗ S) C₀).hom ≫
            (α_ C₀ R S).inv ≫
            (MonoidalClosed.uncurry (map T F G k k') ▷ S) ≫
            MonoidalClosed.uncurry (map T F G k' k'') =
        (α_ R S X₀).hom ≫ (R ◁ (β_ S X₀).hom) ≫
          (α_ R X₀ S).inv ≫
          (outputAction x k k' Q ⊗ₘ 𝟙 S) ≫
          (β_ S X₁).inv ≫ outputAction x k' k'' Q ≫ γ₂ := by
    calc
      _ = (β_ (R ⊗ S) X₀).hom ≫ (α_ X₀ R S).inv ≫
            (((γ₀ ⊗ₘ 𝟙 R) ≫
              MonoidalClosed.uncurry (map T F G k k')) ⊗ₘ 𝟙 S) ≫
            MonoidalClosed.uncurry (map T F G k' k'') := hStart
      _ = (β_ (R ⊗ S) X₀).hom ≫ (α_ X₀ R S).inv ≫
            ((((β_ R X₀).inv ≫ outputAction x k k' Q ≫ γ₁) ⊗ₘ
              𝟙 S) ≫
            MonoidalClosed.uncurry (map T F G k' k'')) := by
          rw [hG₀₁]
      _ = (β_ (R ⊗ S) X₀).hom ≫ (α_ X₀ R S).inv ≫
            ((β_ R X₀).inv ⊗ₘ 𝟙 S) ≫
            (outputAction x k k' Q ⊗ₘ 𝟙 S) ≫
            (γ₁ ⊗ₘ 𝟙 S) ≫
            MonoidalClosed.uncurry (map T F G k' k'') := by
          rw [hExpand]
      _ = (β_ (R ⊗ S) X₀).hom ≫ (α_ X₀ R S).inv ≫
            ((β_ R X₀).inv ⊗ₘ 𝟙 S) ≫
            (outputAction x k k' Q ⊗ₘ 𝟙 S) ≫
            (β_ S X₁).inv ≫ outputAction x k' k'' Q ≫ γ₂ := by
          rw [hG₁₂]
      _ = _ := by
        slice_lhs 1 3 => rw [hPX]
        simp only [Category.assoc]
  have hBase :
      (c ⊗ₘ 𝟙 W₀) ≫ outputBase x k k'' =
        (α_ R S W₀).hom ≫ (R ◁ (β_ S W₀).hom) ≫
          (α_ R W₀ S).inv ≫
          (outputBase x k k' ▷ S) ≫
          (β_ S W₁).inv ≫ outputBase x k' k'' := by
    dsimp only [c, R, S, W₀, W₁, x]
    exact outputBase_comp
      (T.obj ij) k k' k''
  have hBaseQ := congrArg (fun q => q ⊗ₘ 𝟙 Q) hBase
  have hLiftL :
      (c ⊗ₘ 𝟙 X₀) ≫ outputAction x k k'' Q =
        (α_ (R ⊗ S) W₀ Q).inv ≫
          (((c ⊗ₘ 𝟙 W₀) ≫ outputBase x k k'') ⊗ₘ 𝟙 Q) := by
    dsimp only [outputAction, outputBase, X₀, R₂]
    monoidal
  have hAction (r s : K) (Q' : V) :
      outputAction x r s Q' =
        (α_ (r ⟶[V] s) (x ⟶[V] r) Q').inv ≫
          (outputBase x r s ⊗ₘ 𝟙 Q') := by
    dsimp only [outputAction, outputBase]
    rw [tensorHom_comp_tensorHom]
    simp
  have hCoeff {A B W W' W'' Q' : V}
      (f : A ⊗ W ⟶ W') (g : B ⊗ W' ⟶ W'') :
      (α_ A B (W ⊗ Q')).hom ≫
            (A ◁ (β_ B (W ⊗ Q')).hom) ≫
            (α_ A (W ⊗ Q') B).inv ≫
            (((α_ A W Q').inv ≫ (f ⊗ₘ 𝟙 Q')) ⊗ₘ 𝟙 B) ≫
            (β_ B (W' ⊗ Q')).inv ≫
            (α_ B W' Q').inv ≫ (g ⊗ₘ 𝟙 Q') =
        (α_ (A ⊗ B) W Q').inv ≫
          (((α_ A B W).hom ≫ (A ◁ (β_ B W).hom) ≫
            (α_ A W B).inv ≫ (f ▷ B) ≫
            (β_ B W').inv ≫ g) ⊗ₘ 𝟙 Q') := by
    rw [braiding_tensor_right_hom, braiding_tensor_right_inv]
    have hCancel :
        ((A ⊗ W) ◁ (β_ B Q').hom) ≫
              (f ▷ (Q' ⊗ B)) ≫ (W' ◁ (β_ B Q').inv) =
          f ▷ (B ⊗ Q') := by
      rw [whisker_exchange_assoc]
      simp
    calc
      _ = 𝟙 _ ⊗≫
            (A ◁ (β_ B W).hom ▷ Q') ⊗≫
            (((A ⊗ W) ◁ (β_ B Q').hom) ≫
              (f ▷ (Q' ⊗ B)) ≫
              (W' ◁ (β_ B Q').inv)) ⊗≫
            ((β_ B W').inv ▷ Q') ⊗≫
            (g ▷ Q') ⊗≫ 𝟙 _ := by
          monoidal
      _ = 𝟙 _ ⊗≫
            (A ◁ (β_ B W).hom ▷ Q') ⊗≫
            (f ▷ (B ⊗ Q')) ⊗≫
            ((β_ B W').inv ▷ Q') ⊗≫
            (g ▷ Q') ⊗≫ 𝟙 _ := by
          rw [hCancel]
      _ = _ := by monoidal
  have hLiftR :
      (α_ R S X₀).hom ≫ (R ◁ (β_ S X₀).hom) ≫
            (α_ R X₀ S).inv ≫
            (outputAction x k k' Q ⊗ₘ 𝟙 S) ≫
            (β_ S X₁).inv ≫ outputAction x k' k'' Q =
        (α_ (R ⊗ S) W₀ Q).inv ≫
          (((α_ R S W₀).hom ≫ (R ◁ (β_ S W₀).hom) ≫
            (α_ R W₀ S).inv ≫
            (outputBase x k k' ▷ S) ≫
            (β_ S W₁).inv ≫ outputBase x k' k'') ⊗ₘ 𝟙 Q) := by
    dsimp only [X₀, X₁]
    rw [hAction, hAction]
    exact hCoeff (outputBase x k k') (outputBase x k' k'')
  have hBaseQ' := congrArg
    (fun q => (α_ (R ⊗ S) W₀ Q).inv ≫ q) hBaseQ
  have hOA :
      (c ⊗ₘ 𝟙 X₀) ≫ outputAction x k k'' Q =
        (α_ R S X₀).hom ≫ (R ◁ (β_ S X₀).hom) ≫
          (α_ R X₀ S).inv ≫
          (outputAction x k k' Q ⊗ₘ 𝟙 S) ≫
          (β_ S X₁).inv ≫ outputAction x k' k'' Q := by
    calc
      _ = (α_ (R ⊗ S) W₀ Q).inv ≫
            (((c ⊗ₘ 𝟙 W₀) ≫ outputBase x k k'') ⊗ₘ 𝟙 Q) := hLiftL
      _ = (α_ (R ⊗ S) W₀ Q).inv ≫
            (((α_ R S W₀).hom ≫ (R ◁ (β_ S W₀).hom) ≫
              (α_ R W₀ S).inv ≫
              (outputBase x k k' ▷ S) ≫
              (β_ S W₁).inv ≫ outputBase x k' k'') ⊗ₘ 𝟙 Q) := by
            simpa only [Category.assoc] using hBaseQ'
      _ = _ := hLiftR.symm
  calc
    _ = (c ⊗ₘ 𝟙 X₀) ≫ outputAction x k k'' Q ≫ γ₂ := hL
    _ = (α_ R S X₀).hom ≫ (R ◁ (β_ S X₀).hom) ≫
          (α_ R X₀ S).inv ≫
          (outputAction x k k' Q ⊗ₘ 𝟙 S) ≫
          (β_ S X₁).inv ≫ outputAction x k' k'' Q ≫ γ₂ := by
        have h := congrArg (fun q => q ≫ γ₂) hOA
        simpa only [Category.assoc] using h
    _ = _ := hR.symm

variable
  [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
    (EnrichedDayKernel.rightMap T F G k)]

/-- The fixed-input Day kernel is a genuine enriched functor on the plain output index. -/
abbrev functor : EnrichedFunctor V K V where
  obj k := EnrichedDayKernel.obj T F G k
  map k k' := map T F G k k'
  map_id k := map_id T F G k
  map_comp k k' k'' := map_comp T F G k k' k''

/-- The output functor uses precisely the selected kernel object. -/
@[simp]
theorem functor_obj (k : K) :
    (functor T F G).obj k = EnrichedDayKernel.obj T F G k := rfl

/-- The output functor uses precisely the full enriched hom map above. -/
@[simp]
theorem functor_map (k k' : K) :
    (functor T F G).map k k' = map T F G k k' := rfl

end CategoryTheory.EnrichedDayKernel.Output
