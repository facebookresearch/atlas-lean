/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageFlattenReindex

/-!
# Original reindexing in the appended S-direction

The suffix map is the original single-stage reindexing, transported through
the canonical Cons charts. Iterating that same exact map and flattening
retains the original appended tuple operator on the complete original
carrier and morphisms.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original onefold operator, through the unchanged source and target Cons charts. -/
def iteratedStageSingleReindex {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w) :
    IteratedStage C [z.unop.len] ⥤ IteratedStage C [w.unop.len] :=
  (iteratedStageConsEquivalence C z.unop.len []).functor ⋙
    reindexStage (C := IteratedStage C []) f.unop ⋙
      (iteratedStageConsEquivalence C w.unop.len []).inverse

/-- Every original single-direction map retains the original exact reindexing data. -/
theorem iteratedStageSingleReindex_isWaldhausenExact {z w : SimplexCategoryᵒᵖ}
    (f : z ⟶ w) : (iteratedStageSingleReindex C f).IsWaldhausenExact := by
  let _ : HasZeroObject (Stage (IteratedStage C []) z.unop.len) :=
    generalStageHasZeroObject (IteratedStage C []) z.unop.len
  let _ : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C []) z.unop.len) :=
    generalStageWaldhausenCategory (IteratedStage C []) z.unop.len
  let _ : HasZeroObject (Stage (IteratedStage C []) w.unop.len) :=
    generalStageHasZeroObject (IteratedStage C []) w.unop.len
  let _ : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C []) w.unop.len) :=
    generalStageWaldhausenCategory (IteratedStage C []) w.unop.len
  exact ((iteratedStageConsEquivalence_exact C z.unop.len []).1.comp
    (reindexStage_general_isWaldhausenExact (IteratedStage C []) f.unop)).comp
      (iteratedStageConsEquivalence_exact C w.unop.len []).2

/-- Identity in the appended direction is the original onefold identity. -/
theorem iteratedStageSingleReindex_id (z : SimplexCategoryᵒᵖ) :
    iteratedStageSingleReindex C (𝟙 z) = 𝟭 (IteratedStage C [z.unop.len]) := by
  unfold iteratedStageSingleReindex
  rw [unop_id, reindexStage_id, Functor.id_comp]
  exact iteratedStageConsEquivalence_functor_inverse C z.unop.len []

/-- Original source-first suffix composition retains the original single-stage maps. -/
theorem iteratedStageSingleReindex_comp {z w t : SimplexCategoryᵒᵖ}
    (f : z ⟶ w) (g : w ⟶ t) :
    iteratedStageSingleReindex C (f ≫ g) =
      iteratedStageSingleReindex C f ⋙ iteratedStageSingleReindex C g := by
  unfold iteratedStageSingleReindex
  change _ = (iteratedStageConsEquivalence C z.unop.len []).functor ⋙
    reindexStage (C := IteratedStage C []) f.unop ⋙
    ((iteratedStageConsEquivalence C w.unop.len []).inverse ⋙
      (iteratedStageConsEquivalence C w.unop.len []).functor) ⋙
    reindexStage (C := IteratedStage C []) g.unop ⋙
    (iteratedStageConsEquivalence C t.unop.len []).inverse
  rw [iteratedStageConsEquivalence_inverse_functor, Functor.id_comp,
    unop_comp, reindexStage_comp]
  rfl

private theorem consMapZero {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (h : x ⟶ y) : stageTupleConsMap α h 0 = h := by
  unfold stageTupleConsMap
  exact Fin.cases_zero

private theorem consMapSucc {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (h : x ⟶ y) (i : Fin r) :
    stageTupleConsMap α h i.succ = α i := by
  unfold stageTupleConsMap
  exact Fin.cases_succ i

private theorem tupleEqToHomApp {r : ℕ} {a b : StageSimplexTuple r} (h : a = b)
    (i : Fin r) : (eqToHom h : a ⟶ b) i = eqToHom (congrArg (fun t => t i) h) := by
  subst b
  rfl

private theorem transportComp {D : Type} [Category D]
    {A B A' B' A'' B'' : D} (ha : A = A') (hb : B = B')
    (hc : A' = A'') (hd : B' = B'') (h : A ⟶ B) :
    eqToHom hc.symm ≫ (eqToHom ha.symm ≫ h ≫ eqToHom hb) ≫ eqToHom hd =
      eqToHom (ha.trans hc).symm ≫ h ≫ eqToHom (hb.trans hd) := by
  subst A' B' A'' B''
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Both the prefix and the appended map retain their original coordinates
under the actual Cons tuple chart. -/
theorem stageTupleSnocMap_cons_moving {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y z w : SimplexCategoryᵒᵖ} (h : x ⟶ y) (f : z ⟶ w) :
    eqToHom (stageTupleSnoc_cons x a z).symm ≫
        stageTupleSnocMap (stageTupleConsMap α h) f ≫
          eqToHom (stageTupleSnoc_cons y b w) =
      stageTupleConsMap (stageTupleSnocMap α f) h := by
  apply CategoryTheory.Pi.ext
  intro i
  simp only [CategoryTheory.Pi.comp_apply, tupleEqToHomApp]
  cases i using Fin.cases with
  | zero =>
      change @Eq (x ⟶ y) _ h
      exact (stageTupleSnocMap_castSucc (stageTupleConsMap α h) f
        (0 : Fin (r + 1))).trans (consMapZero α h)
  | succ i =>
      cases i using Fin.lastCases with
      | last =>
          let k : Fin (r + 2) := (Fin.last r).succ
          have ha : (Fin.cons x (stageTupleSnoc a z) : StageSimplexTuple (r + 2)) k = z := by
            dsimp only [k]
            change stageTupleSnoc a z (Fin.last r) = z
            exact stageTupleSnoc_last a z
          have hb : (Fin.cons y (stageTupleSnoc b w) : StageSimplexTuple (r + 2)) k = w := by
            dsimp only [k]
            change stageTupleSnoc b w (Fin.last r) = w
            exact stageTupleSnoc_last b w
          apply (cancel_epi (eqToHom ha.symm)).mp
          apply (cancel_mono (eqToHom hb)).mp
          have hLeft := (transportComp
            (congrArg (fun q => q k) (stageTupleSnoc_cons x a z))
            (congrArg (fun q => q k) (stageTupleSnoc_cons y b w)) ha hb
            (stageTupleSnocMap (stageTupleConsMap α h) f k)).trans
              (stageTupleSnocMap_last (stageTupleConsMap α h) f)
          have hRight := (congrArg (fun m => eqToHom ha.symm ≫ m ≫ eqToHom hb)
            (consMapSucc (stageTupleSnocMap α f) h (Fin.last r))).trans
              (stageTupleSnocMap_last α f)
          simpa only [Category.assoc] using hLeft.trans hRight.symm
      | cast i =>
          let k : Fin (r + 2) := i.castSucc.succ
          have ha : (Fin.cons x (stageTupleSnoc a z) : StageSimplexTuple (r + 2)) k = a i := by
            dsimp only [k]
            change stageTupleSnoc a z i.castSucc = a i
            exact stageTupleSnoc_castSucc a z i
          have hb : (Fin.cons y (stageTupleSnoc b w) : StageSimplexTuple (r + 2)) k = b i := by
            dsimp only [k]
            change stageTupleSnoc b w i.castSucc = b i
            exact stageTupleSnoc_castSucc b w i
          apply (cancel_epi (eqToHom ha.symm)).mp
          apply (cancel_mono (eqToHom hb)).mp
          have hLeft := (transportComp
            (congrArg (fun q => q k) (stageTupleSnoc_cons x a z))
            (congrArg (fun q => q k) (stageTupleSnoc_cons y b w)) ha hb
            (stageTupleSnocMap (stageTupleConsMap α h) f k)).trans
              ((stageTupleSnocMap_castSucc (stageTupleConsMap α h) f i.succ).trans
                (consMapSucc α h i))
          have hRight := (congrArg (fun m => eqToHom ha.symm ≫ m ≫ eqToHom hb)
            (consMapSucc (stageTupleSnocMap α f) h i.castSucc)).trans
              (stageTupleSnocMap_castSucc α f i)
          simpa only [Category.assoc] using hLeft.trans hRight.symm

private theorem consMapId {r : ℕ} (a : StageSimplexTuple r) (x : SimplexCategoryᵒᵖ) :
    stageTupleConsMap (𝟙 a) (𝟙 x) = 𝟙 (Fin.cons x a : StageSimplexTuple (r + 1)) := by
  apply CategoryTheory.Pi.ext
  intro i
  cases i using Fin.cases with
  | zero => exact consMapZero (𝟙 a) (𝟙 x)
  | succ i => exact consMapSucc (𝟙 a) (𝟙 x) i

private theorem stageMapEq {A B : Type (max u v)}
    [Category.{v} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {F G : A ⥤ B} (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (h : F = G) (n : ℕ) : hF.mapStage n = hG.mapStage n := by
  subst G
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem tupleConsChartEq {r : ℕ} (x : SimplexCategoryᵒᵖ)
    (a : StageSimplexTuple r) :
    iteratedStageTupleConsEquivalence C x a =
      iteratedStageOfFnSuccEquivalence C (fun i : Fin (r + 1) =>
        ((Fin.cons x a : StageSimplexTuple (r + 1)) i).unop.len) := by
  unfold iteratedStageTupleConsEquivalence iteratedStageOfFnSuccEquivalence
  rfl

private theorem tupleConsChartFunctorInverse {r : ℕ} (x : SimplexCategoryᵒᵖ)
    (a : StageSimplexTuple r) :
    (iteratedStageTupleConsEquivalence C x a).functor ⋙
        (iteratedStageTupleConsEquivalence C x a).inverse =
      𝟭 (StageAtTuple C (Fin.cons x a)) := by
  rw [tupleConsChartEq]
  exact iteratedStageOfFnSuccEquivalence_functor_inverse C
    (fun i : Fin (r + 1) => ((Fin.cons x a : StageSimplexTuple (r + 1)) i).unop.len)

private theorem tupleConsChartInverseFunctor {r : ℕ} (x : SimplexCategoryᵒᵖ)
    (a : StageSimplexTuple r) :
    (iteratedStageTupleConsEquivalence C x a).inverse ⋙
        (iteratedStageTupleConsEquivalence C x a).functor =
      𝟭 (Stage (StageAtTuple C a) x.unop.len) := by
  rw [tupleConsChartEq]
  exact iteratedStageOfFnSuccEquivalence_inverse_functor C
    (fun i : Fin (r + 1) => ((Fin.cons x a : StageSimplexTuple (r + 1)) i).unop.len)

private theorem tupleTransportReindex {r : ℕ}
    {a b a' b' : StageSimplexTuple r} (ha : a = a') (hb : b = b') (α : a ⟶ b) :
    reindexIteratedStage C α ⋙ (iteratedStageTupleEquivalence C hb).functor =
      (iteratedStageTupleEquivalence C ha).functor ⋙
        reindexIteratedStage C (eqToHom ha.symm ≫ α ≫ eqToHom hb) := by
  subst a' b'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    iteratedStageTupleEquivalence, iteratedStageListEquivalence, Equivalence.refl,
    Functor.id_comp, Functor.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem reindexCons {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (h : x ⟶ y) :
    reindexIteratedStage C (stageTupleConsMap α h) =
      (iteratedStageTupleConsEquivalence C x a).functor ⋙
        (reindexStage (C := StageAtTuple C a) h.unop ⋙
          (reindexIteratedStage_isWaldhausenExact C α).mapStage y.unop.len) ⋙
        (iteratedStageTupleConsEquivalence C y b).inverse := by
  simpa +unfoldPartialApp only [stageTupleConsMap, Fin.cons,
    Fin.cases_zero, Fin.cases_succ, tupleConsChartEq] using
    (reindexIteratedStage_succ C (stageTupleConsMap α h))

private theorem snocConsChartFunctorInverse {r : ℕ} (x : SimplexCategoryᵒᵖ)
    (a : StageSimplexTuple r) (z : SimplexCategoryᵒᵖ) :
    (iteratedStageTupleSnocConsEquivalence C x a z).functor ⋙
        (iteratedStageTupleSnocConsEquivalence C x a z).inverse =
      𝟭 (StageAtTuple C (stageTupleSnoc (Fin.cons x a) z)) := by
  change (iteratedStageTupleEquivalence C (stageTupleSnoc_cons x a z)).functor ⋙
      ((iteratedStageTupleConsEquivalence C x (stageTupleSnoc a z)).functor ⋙
        (iteratedStageTupleConsEquivalence C x (stageTupleSnoc a z)).inverse) ⋙
      (iteratedStageTupleEquivalence C (stageTupleSnoc_cons x a z)).inverse = _
  rw [tupleConsChartFunctorInverse]
  exact iteratedStageListEquivalence_functor_inverse C
    (congrArg stageTupleDegrees (stageTupleSnoc_cons x a z))

set_option backward.isDefEq.respectTransparency false in
private theorem reindexSnocConsMoving {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y z w : SimplexCategoryᵒᵖ} (h : x ⟶ y) (f : z ⟶ w) :
    reindexIteratedStage C (stageTupleSnocMap (stageTupleConsMap α h) f) ⋙
        (iteratedStageTupleSnocConsEquivalence C y b w).functor =
      (iteratedStageTupleSnocConsEquivalence C x a z).functor ⋙
        (reindexStage (C := StageAtTuple C (stageTupleSnoc a z)) h.unop ⋙
          (reindexIteratedStage_isWaldhausenExact C (stageTupleSnocMap α f)).mapStage
            y.unop.len) := by
  have ht := tupleTransportReindex C (stageTupleSnoc_cons x a z)
    (stageTupleSnoc_cons y b w) (stageTupleSnocMap (stageTupleConsMap α h) f)
  rw [stageTupleSnocMap_cons_moving] at ht
  have hChart := congrArg (fun F => F ⋙
    (iteratedStageTupleConsEquivalence C y (stageTupleSnoc b w)).functor) ht
  rw [reindexCons] at hChart
  change _ = (iteratedStageTupleSnocConsEquivalence C x a z).functor ⋙ _ ⋙
    ((iteratedStageTupleConsEquivalence C y (stageTupleSnoc b w)).inverse ⋙
      (iteratedStageTupleConsEquivalence C y (stageTupleSnoc b w)).functor) at hChart
  rw [tupleConsChartInverseFunctor] at hChart
  exact hChart

set_option backward.isDefEq.respectTransparency false in
private theorem reindexSnocSuffixCons {r : ℕ} (a : StageSimplexTuple r)
    (x : SimplexCategoryᵒᵖ) {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w) :
    reindexIteratedStage C (stageTupleSnocMap (𝟙 (Fin.cons x a)) f) ⋙
        (iteratedStageTupleSnocConsEquivalence C x a w).functor =
      (iteratedStageTupleSnocConsEquivalence C x a z).functor ⋙
        (reindexIteratedStage_isWaldhausenExact C (stageTupleSnocMap (𝟙 a) f)).mapStage
          x.unop.len := by
  have h := reindexSnocConsMoving C (𝟙 a) (𝟙 x) f
  rw [consMapId, unop_id, reindexStage_id] at h
  simpa only [Functor.id_comp] using h

set_option backward.isDefEq.respectTransparency false in
private theorem mapTupleCons {A B : Type (max u v)}
    [Category.{v} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {F : A ⥤ B} (hF : F.IsWaldhausenExact) {r : ℕ}
    (x : SimplexCategoryᵒᵖ) (a : StageSimplexTuple r) :
    mapIteratedStage hF (stageTupleDegrees (Fin.cons x a)) ⋙
        (iteratedStageTupleConsEquivalence B x a).functor =
      (iteratedStageTupleConsEquivalence A x a).functor ⋙
        (mapIteratedStage_isWaldhausenExact hF (stageTupleDegrees a)).mapStage x.unop.len := by
  unfold iteratedStageTupleConsEquivalence
  change (mapIteratedStage hF (stageTupleDegrees (Fin.cons x a)) ⋙
      (iteratedStageListEquivalence B (stageTupleDegrees_cons x a)).functor) ⋙
      (iteratedStageConsEquivalence B x.unop.len (stageTupleDegrees a)).functor =
    (iteratedStageListEquivalence A (stageTupleDegrees_cons x a)).functor ⋙
      (iteratedStageConsEquivalence A x.unop.len (stageTupleDegrees a)).functor ⋙
      (mapIteratedStage_isWaldhausenExact hF (stageTupleDegrees a)).mapStage x.unop.len
  rw [mapIteratedStage_list_transport]
  change (iteratedStageListEquivalence A (stageTupleDegrees_cons x a)).functor ⋙
    (mapIteratedStage hF (x.unop.len :: stageTupleDegrees a) ⋙
      (iteratedStageConsEquivalence B x.unop.len (stageTupleDegrees a)).functor) = _
  rw [mapIteratedStage_cons_chart]

private theorem snocZeroCons (a : StageSimplexTuple 0) (z : SimplexCategoryᵒᵖ) :
    stageTupleSnoc a z = Fin.cons z a := by
  funext i
  cases i using Fin.cases with
  | zero =>
      simpa only [Fin.cons_zero, Fin.last_zero] using stageTupleSnoc_last a z
  | succ i => exact Fin.elim0 i

private theorem snocMapZeroCons (a : StageSimplexTuple 0)
    {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w) :
    eqToHom (snocZeroCons a z).symm ≫ stageTupleSnocMap (𝟙 a) f ≫
        eqToHom (snocZeroCons a w) = stageTupleConsMap (𝟙 a) f := by
  apply CategoryTheory.Pi.ext
  intro i
  simp only [CategoryTheory.Pi.comp_apply, tupleEqToHomApp]
  cases i using Fin.cases with
  | zero =>
      rw [consMapZero]
      change @Eq (z ⟶ w) _ f
      exact stageTupleSnocMap_last (𝟙 a) f
  | succ i => exact Fin.elim0 i

private theorem listChartTrans {ns ms ps : List ℕ} (h : ns = ms) (k : ms = ps) :
    (iteratedStageListEquivalence C h).functor ⋙
        (iteratedStageListEquivalence C k).functor =
      (iteratedStageListEquivalence C (h.trans k)).functor := by
  subst ms ps
  rfl

private theorem singletonSnocChart (a : StageSimplexTuple 0) (z : SimplexCategoryᵒᵖ) :
    (iteratedStageTupleEquivalence C (snocZeroCons a z)).functor ⋙
        (iteratedStageTupleConsEquivalence C z a).functor =
      (iteratedStageListEquivalence C (stageTupleDegrees_snoc a z)).functor ⋙
        (iteratedStageConsEquivalence C z.unop.len []).functor := by
  change ((iteratedStageListEquivalence C (congrArg stageTupleDegrees
      (snocZeroCons a z))).functor ⋙
      (iteratedStageListEquivalence C (stageTupleDegrees_cons z a)).functor) ⋙
      (iteratedStageConsEquivalence C z.unop.len []).functor = _
  rw [listChartTrans]
  rfl

private theorem listChartSymm {ns ms : List ℕ} (h : ns = ms) :
    (iteratedStageListEquivalence C h.symm).functor =
      (iteratedStageListEquivalence C h).inverse := by
  subst ms
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem singleReindexTupleZero (a : StageSimplexTuple 0)
    {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w) :
    iteratedStageSingleReindex C f ⋙
        (iteratedStageListEquivalence C (stageTupleDegrees_snoc a w).symm).functor =
      (iteratedStageListEquivalence C (stageTupleDegrees_snoc a z).symm).functor ⋙
        reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f) := by
  have ht := tupleTransportReindex C (snocZeroCons a z) (snocZeroCons a w)
    (stageTupleSnocMap (𝟙 a) f)
  rw [snocMapZeroCons, reindexCons] at ht
  have hm := stageMapEq (reindexIteratedStage_isWaldhausenExact C (𝟙 a))
    (Functor.IsWaldhausenExact.id (C := StageAtTuple C a))
    (reindexIteratedStage_id C 0 a) w.unop.len
  rw [hm, Functor.IsWaldhausenExact.mapStage_id, Functor.comp_id] at ht
  have h := congrArg (fun F => F ⋙ (iteratedStageTupleConsEquivalence C w a).functor) ht
  change reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f) ⋙
      ((iteratedStageTupleEquivalence C (snocZeroCons a w)).functor ⋙
        (iteratedStageTupleConsEquivalence C w a).functor) =
    ((iteratedStageTupleEquivalence C (snocZeroCons a z)).functor ⋙
      (iteratedStageTupleConsEquivalence C z a).functor) ⋙
      reindexStage (C := StageAtTuple C a) f.unop ⋙
      ((iteratedStageTupleConsEquivalence C w a).inverse ⋙
        (iteratedStageTupleConsEquivalence C w a).functor) at h
  rw [tupleConsChartInverseFunctor, singletonSnocChart, singletonSnocChart] at h
  have h₁ := congrArg (fun F => F ⋙ (iteratedStageConsEquivalence C w.unop.len []).inverse) h
  change reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f) ⋙
      (iteratedStageListEquivalence C (stageTupleDegrees_snoc a w)).functor ⋙
      ((iteratedStageConsEquivalence C w.unop.len []).functor ⋙
        (iteratedStageConsEquivalence C w.unop.len []).inverse) =
    (iteratedStageListEquivalence C (stageTupleDegrees_snoc a z)).functor ⋙
      iteratedStageSingleReindex C f at h₁
  rw [iteratedStageConsEquivalence_functor_inverse] at h₁
  let ez : StageAtTuple C (stageTupleSnoc a z) ≌ IteratedStage C [z.unop.len] :=
    iteratedStageListEquivalence C (stageTupleDegrees_snoc a z)
  let ew : StageAtTuple C (stageTupleSnoc a w) ≌ IteratedStage C [w.unop.len] :=
    iteratedStageListEquivalence C (stageTupleDegrees_snoc a w)
  let R : StageAtTuple C (stageTupleSnoc a z) ⥤ StageAtTuple C (stageTupleSnoc a w) :=
    reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f)
  change R ⋙ (ew.functor ⋙ 𝟭 (IteratedStage C [w.unop.len])) =
    ez.functor ⋙ iteratedStageSingleReindex C f at h₁
  have hDrop := congrArg (fun F => R ⋙ F) (Functor.comp_id ew.functor)
  have hOne : R ⋙ ew.functor = ez.functor ⋙ iteratedStageSingleReindex C f :=
    hDrop.symm.trans h₁
  have h₂ := congrArg (fun F => ez.inverse ⋙ F ⋙ ew.inverse) hOne
  change ez.inverse ⋙ R ⋙ (ew.functor ⋙ ew.inverse) =
    (ez.inverse ⋙ ez.functor) ⋙ iteratedStageSingleReindex C f ⋙ ew.inverse at h₂
  have hW : ew.functor ⋙ ew.inverse = 𝟭 (StageAtTuple C (stageTupleSnoc a w)) :=
    iteratedStageListEquivalence_functor_inverse C (stageTupleDegrees_snoc a w)
  have hZ : ez.inverse ⋙ ez.functor = 𝟭 (IteratedStage C [z.unop.len]) :=
    iteratedStageListEquivalence_inverse_functor C (stageTupleDegrees_snoc a z)
  rw [hW, hZ] at h₂
  have hTwo : ez.inverse ⋙ R = iteratedStageSingleReindex C f ⋙ ew.inverse := by
    simpa only [Functor.id_comp, Functor.comp_id] using h₂
  have hz : (iteratedStageListEquivalence C (stageTupleDegrees_snoc a z).symm).functor =
      ez.inverse := listChartSymm C (stageTupleDegrees_snoc a z)
  have hw : (iteratedStageListEquivalence C (stageTupleDegrees_snoc a w).symm).functor =
      ew.inverse := listChartSymm C (stageTupleDegrees_snoc a w)
  exact ((congrArg (fun F => iteratedStageSingleReindex C f ⋙ F) hw).trans hTwo.symm).trans
    (congrArg (fun F => F ⋙ R) hz).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original onefold suffix operator, iterated through every original
prefix stage, is the same appended tuple operator after flattening. -/
theorem iteratedStageTupleSnocFlattenEquivalence_suffix (r : ℕ) (a : StageSimplexTuple r)
    {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w) :
    mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f)
        (stageTupleDegrees a) ⋙
        (iteratedStageTupleSnocFlattenEquivalence C a w).functor =
      (iteratedStageTupleSnocFlattenEquivalence C a z).functor ⋙
        reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f) := by
  induction r with
  | zero =>
      change mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f) [] ⋙
          ((iteratedStageFlattenEquivalence C [] [w.unop.len]).functor ⋙
            (iteratedStageListEquivalence C (stageTupleDegrees_snoc a w).symm).functor) =
        (iteratedStageFlattenEquivalence C [] [z.unop.len]).functor ⋙
          (iteratedStageListEquivalence C (stageTupleDegrees_snoc a z).symm).functor ⋙
            reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f)
      rw [iteratedStageFlattenEquivalence_nil, iteratedStageFlattenEquivalence_nil]
      change (mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f) [] ⋙
          (iteratedStageNilEquivalence (IteratedStage C [w.unop.len])).functor) ⋙
          (iteratedStageListEquivalence C (stageTupleDegrees_snoc a w).symm).functor =
        (iteratedStageNilEquivalence (IteratedStage C [z.unop.len])).functor ⋙
          ((iteratedStageListEquivalence C (stageTupleDegrees_snoc a z).symm).functor ⋙
            reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f))
      rw [mapIteratedStage_nil_chart]
      exact congrArg (fun F =>
        (iteratedStageNilEquivalence (IteratedStage C [z.unop.len])).functor ⋙ F)
        (singleReindexTupleZero C a f)
  | succ r ih =>
      cases a using Fin.consCases with
      | cons x a =>
          let hM := mapIteratedStage_isWaldhausenExact
            (iteratedStageSingleReindex_isWaldhausenExact C f) (stageTupleDegrees a)
          let hA := (iteratedStageTupleSnocFlattenEquivalence_exact C a z).1
          let hB := (iteratedStageTupleSnocFlattenEquivalence_exact C a w).1
          let hS := reindexIteratedStage_isWaldhausenExact C (stageTupleSnocMap (𝟙 a) f)
          let EA := iteratedStageTupleConsEquivalence (IteratedStage C [z.unop.len]) x a
          let MA := iteratedStageTupleSnocConsEquivalence C x a z
          let MB := iteratedStageTupleSnocConsEquivalence C x a w
          have hTail := ih a
          have hLift : hM.mapStage x.unop.len ⋙ hB.mapStage x.unop.len =
              hA.mapStage x.unop.len ⋙ hS.mapStage x.unop.len :=
            (Functor.IsWaldhausenExact.mapStage_comp hM hB x.unop.len).symm.trans
              ((stageMapEq (hM.comp hB) (hA.comp hS) hTail x.unop.len).trans
                (Functor.IsWaldhausenExact.mapStage_comp hA hS x.unop.len))
          have hLeft :
              (mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f)
                (stageTupleDegrees (Fin.cons x a)) ⋙
                (iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) w).functor) ⋙
                  MB.functor =
                EA.functor ⋙ hM.mapStage x.unop.len ⋙ hB.mapStage x.unop.len := by
            change mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f)
              (stageTupleDegrees (Fin.cons x a)) ⋙
              ((iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) w).functor ⋙
                MB.functor) = _
            rw [iteratedStageTupleSnocFlattenEquivalence_cons]
            change (mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f)
              (stageTupleDegrees (Fin.cons x a)) ⋙
                (iteratedStageTupleConsEquivalence (IteratedStage C [w.unop.len]) x a).functor) ⋙
                  hB.mapStage x.unop.len = _
            rw [mapTupleCons]
            rfl
          have hRight :
              ((iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) z).functor ⋙
                reindexIteratedStage C (stageTupleSnocMap (𝟙 (Fin.cons x a)) f)) ⋙
                  MB.functor =
                EA.functor ⋙ hA.mapStage x.unop.len ⋙ hS.mapStage x.unop.len := by
            change (iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) z).functor ⋙
              (reindexIteratedStage C (stageTupleSnocMap (𝟙 (Fin.cons x a)) f) ⋙
                MB.functor) = _
            rw [reindexSnocSuffixCons]
            change ((iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) z).functor ⋙
              MA.functor) ⋙ hS.mapStage x.unop.len = _
            rw [iteratedStageTupleSnocFlattenEquivalence_cons]
            rfl
          have hMiddle := congrArg (fun F => EA.functor ⋙ F) hLift
          have h := congrArg (fun F => F ⋙ MB.inverse)
            (hLeft.trans (hMiddle.trans hRight.symm))
          change (mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f)
              (stageTupleDegrees (Fin.cons x a)) ⋙
              (iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) w).functor) ⋙
              (MB.functor ⋙ MB.inverse) =
            ((iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) z).functor ⋙
              reindexIteratedStage C (stageTupleSnocMap (𝟙 (Fin.cons x a)) f)) ⋙
              (MB.functor ⋙ MB.inverse) at h
          rw [snocConsChartFunctorInverse] at h
          simpa only [Functor.comp_id] using h

/-- The suffix square retains every original object, with its actual flattening chart. -/
theorem iteratedStageTupleSnocFlattenEquivalence_suffix_obj (r : ℕ)
    (a : StageSimplexTuple r) {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w)
    (X : StageAtTuple (IteratedStage C [z.unop.len]) a) :
    (iteratedStageTupleSnocFlattenEquivalence C a w).functor.obj
        ((mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f)
          (stageTupleDegrees a)).obj X) =
      (reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f)).obj
        ((iteratedStageTupleSnocFlattenEquivalence C a z).functor.obj X) :=
  Functor.congr_obj (iteratedStageTupleSnocFlattenEquivalence_suffix C r a f) X

/-- Every original morphism follows the same suffix and flattening square,
with the equality transports on its original endpoints. -/
theorem iteratedStageTupleSnocFlattenEquivalence_suffix_map (r : ℕ)
    (a : StageSimplexTuple r) {z w : SimplexCategoryᵒᵖ} (f : z ⟶ w)
    {X Y : StageAtTuple (IteratedStage C [z.unop.len]) a} (h : X ⟶ Y) :
    HEq ((iteratedStageTupleSnocFlattenEquivalence C a w).functor.map
        ((mapIteratedStage (iteratedStageSingleReindex_isWaldhausenExact C f)
          (stageTupleDegrees a)).map h))
      ((reindexIteratedStage C (stageTupleSnocMap (𝟙 a) f)).map
        ((iteratedStageTupleSnocFlattenEquivalence C a z).functor.map h)) :=
  Functor.hcongr_hom (iteratedStageTupleSnocFlattenEquivalence_suffix C r a f) h

end CategoryTheory.Waldhausen.SConstruction

end
