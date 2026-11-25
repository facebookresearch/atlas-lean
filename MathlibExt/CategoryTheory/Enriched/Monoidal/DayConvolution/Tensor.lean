/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Output
public import MathlibExt.CategoryTheory.Enriched.FunctorCategory
public import MathlibExt.CategoryTheory.Enriched.Monoidal.ExternalTensor

/-!
# Genuine input variance of enriched Day kernels

Full unit-graded transformations act on the external tensor and its particular
weighted coends. The output hom square retains the inverse output braid.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC uD uK uV vV

namespace CategoryTheory.EnrichedDayKernel.Input

open MonoidalCategory BraidedCategory Opposite Limits
open scoped MonoidalClosed

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {K : Type uK} [EnrichedCategory V K]

private theorem outputAction_coefficient (x k k' : K) {Q Q' : V} (s : Q ⟶ Q') :
    (k ⟶[V] k') ◁ ((x ⟶[V] k) ◁ s) ≫ Output.outputAction x k k' Q' =
      Output.outputAction x k k' Q ≫ ((x ⟶[V] k') ◁ s) := by
  dsimp only [Output.outputAction]
  simp only [Category.assoc, tensorHom_id]
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc]
  rw [whisker_exchange (eComp V x k k') s]

variable [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C]
  {D : Type uD} [EnrichedCategory V D]

attribute [local instance] Enriched.prodCategory

variable {F₀ F₁ F₂ : EnrichedFunctor V C V}
  {G₀ G₁ G₂ : EnrichedFunctor V D V}

variable (T : EnrichedFunctor V (C × D) K)

/-- The actual diagram map induced on the two particular input kernels. -/
abbrev mapAt
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁) (k : K)
    [HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)] :
    EnrichedDayKernel.obj T F₀ G₀ k ⟶ EnrichedDayKernel.obj T F₁ G₁ k :=
  Enriched.weightedCoend.mapDiagramGraded
    (EnrichedDayKernel.weight T k) (EnrichedFunctor.externalMap a b)

/-- The actual input map acts on a generator by the two actual input components. -/
@[reassoc]
theorem gen_mapAt
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁) (k : K)
    [HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)] (x : C × D) :
    EnrichedDayKernel.gen T F₀ G₀ k x ≫ mapAt T a b k =
      (𝟙 (T.obj x ⟶[V] k) ⊗ₘ
        ((eHomEquiv V).symm (a.app x.1) ⊗ₘ (eHomEquiv V).symm (b.app x.2))) ≫
        EnrichedDayKernel.gen T F₁ G₁ k x := by
  have h := Enriched.weightedCoend.mapDiagramGraded_ι
    (EnrichedDayKernel.weight T k) (EnrichedFunctor.externalMap a b) x
  change EnrichedDayKernel.gen T F₀ G₀ k x ≫ mapAt T a b k =
    (𝟙 (T.obj x ⟶[V] k) ⊗ₘ
      (eHomEquiv V).symm ((EnrichedFunctor.externalMap a b).app x)) ≫
      EnrichedDayKernel.gen T F₁ G₁ k x at h
  rw [EnrichedFunctor.externalMap_component] at h
  exact h

/-- One particular input kernel suffices for the identity input map. -/
theorem mapAt_id (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K)
    [HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)] :
    mapAt T (GradedNatTrans.unitId F) (GradedNatTrans.unitId G) k =
      𝟙 (EnrichedDayKernel.obj T F G k) := by
  dsimp only [mapAt]
  rw [EnrichedFunctor.externalMap_id]
  exact Enriched.weightedCoend.mapDiagramGraded_id
    (EnrichedDayKernel.weight T k) (F.externalTensor G)

/-- Exactly the three actual input kernels suffice for source-first composition. -/
theorem mapAt_comp
    (a₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (a₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂)
    (b₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁)
    (b₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₁ G₂) (k : K)
    [HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₂ G₂ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₂ G₂ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₂ G₂ k)
      (EnrichedDayKernel.rightMap T F₂ G₂ k)] :
    mapAt T (GradedNatTrans.unitComp a₀₁ a₁₂) (GradedNatTrans.unitComp b₀₁ b₁₂) k =
      mapAt T a₀₁ b₀₁ k ≫ mapAt T a₁₂ b₁₂ k := by
  dsimp only [mapAt]
  rw [EnrichedFunctor.externalMap_comp]
  exact Enriched.weightedCoend.mapDiagramGraded_comp
    (EnrichedDayKernel.weight T k)
    (EnrichedFunctor.externalMap a₀₁ b₀₁) (EnrichedFunctor.externalMap a₁₂ b₁₂)

/-- Input maps commute with the full curried output-hom action descent. -/
theorem actionDesc_natural
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁) (k k' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k')]
    [HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k')
      (EnrichedDayKernel.rightMap T F₀ G₀ k')]
    [HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k')]
    [HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k')
      (EnrichedDayKernel.rightMap T F₁ G₁ k')] :
    Output.actionDesc T F₀ G₀ k k' ≫ (ihom (k ⟶[V] k')).map (mapAt T a b k') =
      mapAt T a b k ≫ Output.actionDesc T F₁ G₁ k k' := by
  apply EnrichedDayKernel.hom_ext T F₀ G₀ k
  intro x
  let s : (F₀.obj x.1 ⊗ G₀.obj x.2) ⟶ (F₁.obj x.1 ⊗ G₁.obj x.2) :=
    (eHomEquiv V).symm (a.app x.1) ⊗ₘ (eHomEquiv V).symm (b.app x.2)
  let γ₀ : (T.obj x ⟶[V] k) ⊗ (F₀.obj x.1 ⊗ G₀.obj x.2) ⟶
      EnrichedDayKernel.obj T F₀ G₀ k := EnrichedDayKernel.gen T F₀ G₀ k x
  let γ₀' : (T.obj x ⟶[V] k') ⊗ (F₀.obj x.1 ⊗ G₀.obj x.2) ⟶
      EnrichedDayKernel.obj T F₀ G₀ k' := EnrichedDayKernel.gen T F₀ G₀ k' x
  let γ₁ : (T.obj x ⟶[V] k) ⊗ (F₁.obj x.1 ⊗ G₁.obj x.2) ⟶
      EnrichedDayKernel.obj T F₁ G₁ k := EnrichedDayKernel.gen T F₁ G₁ k x
  let γ₁' : (T.obj x ⟶[V] k') ⊗ (F₁.obj x.1 ⊗ G₁.obj x.2) ⟶
      EnrichedDayKernel.obj T F₁ G₁ k' := EnrichedDayKernel.gen T F₁ G₁ k' x
  let a₀ : (k ⟶[V] k') ⊗ ((T.obj x ⟶[V] k) ⊗ (F₀.obj x.1 ⊗ G₀.obj x.2)) ⟶
      EnrichedDayKernel.obj T F₀ G₀ k' :=
    Output.outputAction (T.obj x) k k' (F₀.obj x.1 ⊗ G₀.obj x.2) ≫ γ₀'
  let a₁ : (k ⟶[V] k') ⊗ ((T.obj x ⟶[V] k) ⊗ (F₁.obj x.1 ⊗ G₁.obj x.2)) ⟶
      EnrichedDayKernel.obj T F₁ G₁ k' :=
    Output.outputAction (T.obj x) k k' (F₁.obj x.1 ⊗ G₁.obj x.2) ≫ γ₁'
  have hm : γ₀ ≫ mapAt T a b k = (𝟙 (T.obj x ⟶[V] k) ⊗ₘ s) ≫ γ₁ :=
    gen_mapAt T a b k x
  have hm' : γ₀' ≫ mapAt T a b k' = (𝟙 (T.obj x ⟶[V] k') ⊗ₘ s) ≫ γ₁' :=
    gen_mapAt T a b k' x
  have hd₀ : γ₀ ≫ Output.actionDesc T F₀ G₀ k k' =
      MonoidalClosed.curry (A := k ⟶[V] k') a₀ :=
    Output.gen_actionDesc T F₀ G₀ k k' x
  have hd₁ : γ₁ ≫ Output.actionDesc T F₁ G₁ k k' =
      MonoidalClosed.curry (A := k ⟶[V] k') a₁ :=
    Output.gen_actionDesc T F₁ G₁ k k' x
  have hc := outputAction_coefficient (T.obj x) k k' s
  have hact : a₀ ≫ mapAt T a b k' =
      (k ⟶[V] k') ◁ (𝟙 (T.obj x ⟶[V] k) ⊗ₘ s) ≫ a₁ := by
    change
      (Output.outputAction (T.obj x) k k' (F₀.obj x.1 ⊗ G₀.obj x.2) ≫ γ₀') ≫ mapAt T a b k' =
      (k ⟶[V] k') ◁ (𝟙 (T.obj x ⟶[V] k) ⊗ₘ s) ≫
        (Output.outputAction (T.obj x) k k' (F₁.obj x.1 ⊗ G₁.obj x.2) ≫ γ₁')
    rw [Category.assoc, hm']
    simpa only [id_tensorHom, Category.assoc] using
      congrArg (fun q => q ≫ γ₁') hc.symm
  change γ₀ ≫ (Output.actionDesc T F₀ G₀ k k' ≫
      (ihom (k ⟶[V] k')).map (mapAt T a b k')) =
    γ₀ ≫ (mapAt T a b k ≫ Output.actionDesc T F₁ G₁ k k')
  calc
    _ = MonoidalClosed.curry (A := k ⟶[V] k') a₀ ≫
        (ihom (k ⟶[V] k')).map (mapAt T a b k') := by
      rw [← Category.assoc, hd₀]
    _ = MonoidalClosed.curry (A := k ⟶[V] k') (a₀ ≫ mapAt T a b k') :=
      (MonoidalClosed.curry_natural_right (A := k ⟶[V] k') a₀ (mapAt T a b k')).symm
    _ = MonoidalClosed.curry (A := k ⟶[V] k')
        ((k ⟶[V] k') ◁ (𝟙 (T.obj x ⟶[V] k) ⊗ₘ s) ≫ a₁) :=
      congrArg (MonoidalClosed.curry (A := k ⟶[V] k')) hact
    _ = (𝟙 (T.obj x ⟶[V] k) ⊗ₘ s) ≫ MonoidalClosed.curry (A := k ⟶[V] k') a₁ :=
      MonoidalClosed.curry_natural_left (A := k ⟶[V] k') (𝟙 (T.obj x ⟶[V] k) ⊗ₘ s) a₁
    _ = ((𝟙 (T.obj x ⟶[V] k) ⊗ₘ s) ≫ γ₁) ≫ Output.actionDesc T F₁ G₁ k k' := by
      rw [Category.assoc, hd₁]
    _ = _ := by rw [← Category.assoc, hm]

/-- The actual uncurried enriched output maps satisfy the full input-variance square. -/
theorem mapAt_natural
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁) (k k' : K)
    [HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k')]
    [HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k')
      (EnrichedDayKernel.rightMap T F₀ G₀ k')]
    [HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)]
    [HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k')]
    [HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k')]
    [HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k')
      (EnrichedDayKernel.rightMap T F₁ G₁ k')] :
    MonoidalClosed.uncurry (Output.map T F₀ G₀ k k') ≫ mapAt T a b k' =
      (mapAt T a b k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
        MonoidalClosed.uncurry (Output.map T F₁ G₁ k k') := by
  have hn := congrArg (MonoidalClosed.uncurry (A := k ⟶[V] k'))
    (actionDesc_natural T a b k k')
  rw [MonoidalClosed.uncurry_natural_right, MonoidalClosed.uncurry_natural_left] at hn
  have hb :
      (β_ (k ⟶[V] k') (EnrichedDayKernel.obj T F₀ G₀ k)).inv ≫
          (k ⟶[V] k') ◁ mapAt T a b k =
        (mapAt T a b k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
          (β_ (k ⟶[V] k') (EnrichedDayKernel.obj T F₁ G₁ k)).inv := by
    simpa only [tensorHom_id] using
      (braiding_inv_naturality_left (mapAt T a b k) (k ⟶[V] k')).symm
  rw [Output.map_uncurry, Output.map_uncurry]
  calc
    _ = (β_ (k ⟶[V] k') (EnrichedDayKernel.obj T F₀ G₀ k)).inv ≫
        (MonoidalClosed.uncurry (Output.actionDesc T F₀ G₀ k k') ≫ mapAt T a b k') :=
      Category.assoc _ _ _
    _ = (β_ (k ⟶[V] k') (EnrichedDayKernel.obj T F₀ G₀ k)).inv ≫
        ((k ⟶[V] k') ◁ mapAt T a b k ≫
          MonoidalClosed.uncurry (Output.actionDesc T F₁ G₁ k k')) := by rw [hn]
    _ = (mapAt T a b k ⊗ₘ 𝟙 (k ⟶[V] k')) ≫
        (β_ (k ⟶[V] k') (EnrichedDayKernel.obj T F₁ G₁ k)).inv ≫
          MonoidalClosed.uncurry (Output.actionDesc T F₁ G₁ k k') := by
      rw [← Category.assoc, hb, Category.assoc]

/-- Genuine input transformations induce a genuine transformation of output functors. -/
abbrev natTrans
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁)
    [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)] :
    GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
      (Output.functor T F₀ G₀) (Output.functor T F₁ G₁) :=
  GradedNatTrans.unitOfComponents (fun k => mapAt T a b k)
    (fun k k' => mapAt_natural T a b k k')

/-- Its ordinary output component is the actual particular coend diagram map. -/
@[simp]
theorem natTrans_component
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁)
    [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)] (k : K) :
    (eHomEquiv V).symm ((natTrans T a b).app k) = mapAt T a b k :=
  GradedNatTrans.unitOfComponents_component _ _ k

/-- Output transformations preserve identity for the actual one-input kernel family. -/
theorem natTrans_id (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V)
    [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
      (EnrichedDayKernel.rightMap T F G k)] :
    natTrans T (GradedNatTrans.unitId F) (GradedNatTrans.unitId G) =
      GradedNatTrans.unitId (Output.functor T F G) := by
  apply GradedNatTrans.ext
  funext k
  apply (eHomEquiv V).symm.injective
  rw [natTrans_component, GradedNatTrans.unitId_component]
  exact mapAt_id T F G k

/-- Output transformations preserve source-first composition for three actual families. -/
theorem natTrans_comp
    (a₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₀ F₁)
    (a₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F₁ F₂)
    (b₀₁ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₀ G₁)
    (b₁₂ : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G₁ G₂)
    [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F₀ G₀ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F₀ G₀ k)]
    [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F₀ G₀ k)
      (EnrichedDayKernel.rightMap T F₀ G₀ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F₁ G₁ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F₁ G₁ k)]
    [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F₁ G₁ k)
      (EnrichedDayKernel.rightMap T F₁ G₁ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.relations T F₂ G₂ k)]
    [∀ k : K, HasCoproduct (EnrichedDayKernel.objects T F₂ G₂ k)]
    [∀ k : K, HasCoequalizer (EnrichedDayKernel.leftMap T F₂ G₂ k)
      (EnrichedDayKernel.rightMap T F₂ G₂ k)] :
    natTrans T (GradedNatTrans.unitComp a₀₁ a₁₂) (GradedNatTrans.unitComp b₀₁ b₁₂) =
      GradedNatTrans.unitComp (natTrans T a₀₁ b₀₁) (natTrans T a₁₂ b₁₂) := by
  apply GradedNatTrans.ext
  funext k
  apply (eHomEquiv V).symm.injective
  rw [natTrans_component, GradedNatTrans.unitComp_component,
    natTrans_component, natTrans_component]
  exact mapAt_comp T a₀₁ a₁₂ b₀₁ b₁₂ k

section WholeBifunctor

variable
    [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
      HasCoproduct (EnrichedDayKernel.relations T F G k)]
    [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
      HasCoproduct (EnrichedDayKernel.objects T F G k)]
    [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : K),
      HasCoequalizer (EnrichedDayKernel.leftMap T F G k)
        (EnrichedDayKernel.rightMap T F G k)]

/-- The Day kernel is functorial in both genuine input-transformation categories. -/
abbrev bifunctor :
    (EnrichedFunctorCat V C × EnrichedFunctorCat V D) ⥤ EnrichedFunctorCat V K where
  obj X := ⟨Output.functor T X.1.toEnrichedFunctor X.2.toEnrichedFunctor⟩
  map a := natTrans T a.1 a.2
  map_id X := natTrans_id T X.1.toEnrichedFunctor X.2.toEnrichedFunctor
  map_comp a b := natTrans_comp T a.1 b.1 a.2 b.2

/-- The bifunctor selects the actual fixed-input output functor. -/
@[simp]
theorem bifunctor_obj (F : EnrichedFunctorCat V C) (G : EnrichedFunctorCat V D) :
    ((bifunctor T).obj (F, G)).toEnrichedFunctor =
      Output.functor T F.toEnrichedFunctor G.toEnrichedFunctor := rfl

/-- The bifunctor's ordinary component is the actual particular coend map. -/
@[simp]
theorem bifunctor_map_component
    {F F' : EnrichedFunctorCat V C} {G G' : EnrichedFunctorCat V D}
    (a : F ⟶ F') (b : G ⟶ G') (k : K) :
    EnrichedFunctorCat.component
        (F := ⟨Output.functor T F.toEnrichedFunctor G.toEnrichedFunctor⟩)
        (G := ⟨Output.functor T F'.toEnrichedFunctor G'.toEnrichedFunctor⟩)
        ((bifunctor T).map (X := (F, G)) (Y := (F', G')) (a, b)) k =
      mapAt T (F₀ := F.toEnrichedFunctor) (F₁ := F'.toEnrichedFunctor)
        (G₀ := G.toEnrichedFunctor) (G₁ := G'.toEnrichedFunctor) a b k :=
  natTrans_component T (F₀ := F.toEnrichedFunctor) (F₁ := F'.toEnrichedFunctor)
    (G₀ := G.toEnrichedFunctor) (G₁ := G'.toEnrichedFunctor) a b k

end WholeBifunctor
end CategoryTheory.EnrichedDayKernel.Input
