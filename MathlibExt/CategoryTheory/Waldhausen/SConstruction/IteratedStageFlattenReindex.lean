/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageTupleAppend
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageInnermostInsertion

/-!
# Reindexing the original prefix before and after flattening

The appended simplex remains the original innermost direction. The
original tuple reindexing on the prefix commutes with the actual degree-list
flattening chart and the original appended tuple map. All carrier charts
come from the existing list equalities and original Cons equivalences.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.Waldhausen.SConstruction

/-- The original head map and tail maps form their actual pointwise tuple morphism. -/
def stageTupleConsMap {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) :
    (Fin.cons x a : StageSimplexTuple (r + 1)) ⟶
      (Fin.cons y b : StageSimplexTuple (r + 1)) :=
  Fin.cases (motive := fun i => (Fin.cons x a : StageSimplexTuple (r + 1)) i ⟶
    (Fin.cons y b : StageSimplexTuple (r + 1)) i) f (fun i => α i)

private theorem consMap_zero {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) : stageTupleConsMap α f 0 = f := by
  unfold stageTupleConsMap
  exact Fin.cases_zero

private theorem consMap_succ {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) (i : Fin r) :
    stageTupleConsMap α f i.succ = α i := by
  unfold stageTupleConsMap
  exact Fin.cases_succ i

/-- A literal head and tail give the same original degree-list Cons. -/
theorem stageTupleDegrees_cons {r : ℕ} (x : SimplexCategoryᵒᵖ) (a : StageSimplexTuple r) :
    stageTupleDegrees (Fin.cons x a) = x.unop.len :: stageTupleDegrees a := by
  simp only [stageTupleDegrees, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

/-- The original appended direction commutes with literal head/tail splitting. -/
theorem stageTupleSnoc_cons {r : ℕ} (x : SimplexCategoryᵒᵖ) (a : StageSimplexTuple r)
    (z : SimplexCategoryᵒᵖ) :
    stageTupleSnoc (Fin.cons x a) z = Fin.cons x (stageTupleSnoc a z) :=
  (Fin.cons_snoc_eq_snoc_cons x a z).symm

/-- The appended operator of two tuple identities is the same original identity. -/
theorem stageTupleSnocMap_id {r : ℕ} (a : StageSimplexTuple r) (z : SimplexCategoryᵒᵖ) :
    stageTupleSnocMap (𝟙 a) (𝟙 z) = 𝟙 (stageTupleSnoc a z) := by
  funext i
  cases i using Fin.lastCases <;> simp [stageTupleSnocMap]

private theorem tupleEqToHom_app {r : ℕ} {a b : StageSimplexTuple r} (h : a = b)
    (i : Fin r) : (eqToHom h : a ⟶ b) i = eqToHom (congrArg (fun t => t i) h) := by
  subst b
  rfl

private theorem transport_comp {D : Type} [Category D]
    {A B A' B' A'' B'' : D} (ha : A = A') (hb : B = B')
    (hc : A' = A'') (hd : B' = B'') (f : A ⟶ B) :
    eqToHom hc.symm ≫ (eqToHom ha.symm ≫ f ≫ eqToHom hb) ≫ eqToHom hd =
      eqToHom (ha.trans hc).symm ≫ f ≫ eqToHom (hb.trans hd) := by
  subst A' B' A'' B''
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The original appended operator retains its head and appended tail
under the actual tuple chart. -/
theorem stageTupleSnocMap_cons {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) (z : SimplexCategoryᵒᵖ) :
    eqToHom (stageTupleSnoc_cons x a z).symm ≫
        stageTupleSnocMap (stageTupleConsMap α f) (𝟙 z) ≫
          eqToHom (stageTupleSnoc_cons y b z) =
      stageTupleConsMap (stageTupleSnocMap α (𝟙 z)) f := by
  apply CategoryTheory.Pi.ext
  intro i
  simp only [CategoryTheory.Pi.comp_apply, tupleEqToHom_app]
  cases i using Fin.cases with
  | zero =>
      change @Eq (x ⟶ y) _ f
      exact (stageTupleSnocMap_castSucc (stageTupleConsMap α f) (𝟙 z)
        (0 : Fin (r + 1))).trans (consMap_zero α f)
  | succ i =>
      cases i using Fin.lastCases with
      | last =>
          let k : Fin (r + 2) := (Fin.last r).succ
          have ha : (Fin.cons x (stageTupleSnoc a z) : StageSimplexTuple (r + 2)) k = z := by
            dsimp only [k]
            change stageTupleSnoc a z (Fin.last r) = z
            exact stageTupleSnoc_last a z
          have hb : (Fin.cons y (stageTupleSnoc b z) : StageSimplexTuple (r + 2)) k = z := by
            dsimp only [k]
            change stageTupleSnoc b z (Fin.last r) = z
            exact stageTupleSnoc_last b z
          apply (cancel_epi (eqToHom ha.symm)).mp
          apply (cancel_mono (eqToHom hb)).mp
          have hLeft := (transport_comp
            (congrArg (fun q => q k) (stageTupleSnoc_cons x a z))
            (congrArg (fun q => q k) (stageTupleSnoc_cons y b z)) ha hb
            (stageTupleSnocMap (stageTupleConsMap α f) (𝟙 z) k)).trans
              (stageTupleSnocMap_last (stageTupleConsMap α f) (𝟙 z))
          have hRight := (congrArg (fun m => eqToHom ha.symm ≫ m ≫ eqToHom hb)
            (consMap_succ (stageTupleSnocMap α (𝟙 z)) f (Fin.last r))).trans
              (stageTupleSnocMap_last α (𝟙 z))
          simpa only [Category.assoc] using hLeft.trans hRight.symm
      | cast i =>
          let k : Fin (r + 2) := i.castSucc.succ
          have ha : (Fin.cons x (stageTupleSnoc a z) : StageSimplexTuple (r + 2)) k = a i := by
            dsimp only [k]
            change stageTupleSnoc a z i.castSucc = a i
            exact stageTupleSnoc_castSucc a z i
          have hb : (Fin.cons y (stageTupleSnoc b z) : StageSimplexTuple (r + 2)) k = b i := by
            dsimp only [k]
            change stageTupleSnoc b z i.castSucc = b i
            exact stageTupleSnoc_castSucc b z i
          apply (cancel_epi (eqToHom ha.symm)).mp
          apply (cancel_mono (eqToHom hb)).mp
          have hLeft := (transport_comp
            (congrArg (fun q => q k) (stageTupleSnoc_cons x a z))
            (congrArg (fun q => q k) (stageTupleSnoc_cons y b z)) ha hb
            (stageTupleSnocMap (stageTupleConsMap α f) (𝟙 z) k)).trans
              ((stageTupleSnocMap_castSucc (stageTupleConsMap α f) (𝟙 z) i.succ).trans
                (consMap_succ α f i))
          have hRight := (congrArg (fun m => eqToHom ha.symm ≫ m ≫ eqToHom hb)
            (consMap_succ (stageTupleSnocMap α (𝟙 z)) f i.castSucc)).trans
              (stageTupleSnocMap_castSucc α (𝟙 z) i)
          simpa only [Category.assoc] using hLeft.trans hRight.symm

private theorem stageMapEq {A : Type (max u v)} {B : Type (max u v)}
    [Category.{v} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {F G : A ⥤ B} (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (h : F = G) (n : ℕ) : hF.mapStage n = hG.mapStage n := by
  subst G
  rfl

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Tuple equality uses the original equal-list carrier transport. -/
def iteratedStageTupleEquivalence {r : ℕ} {a b : StageSimplexTuple r} (h : a = b) :
    StageAtTuple C a ≌ StageAtTuple C b :=
  iteratedStageListEquivalence C (congrArg stageTupleDegrees h)

private theorem tupleTransport_reindex {r : ℕ}
    {a b a' b' : StageSimplexTuple r} (ha : a = a') (hb : b = b') (α : a ⟶ b) :
    reindexIteratedStage C α ⋙ (iteratedStageTupleEquivalence C hb).functor =
      (iteratedStageTupleEquivalence C ha).functor ⋙
        reindexIteratedStage C (eqToHom ha.symm ≫ α ≫ eqToHom hb) := by
  subst a' b'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    iteratedStageTupleEquivalence, iteratedStageListEquivalence, Equivalence.refl,
    Functor.id_comp, Functor.comp_id]

private theorem listTransport_trans {ns ms ps : List ℕ} (h : ns = ms) (k : ms = ps) :
    (iteratedStageListEquivalence C h).functor ⋙ (iteratedStageListEquivalence C k).functor =
      (iteratedStageListEquivalence C (h.trans k)).functor := by
  subst ms ps
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem flattenTransport_cons (n : ℕ) (ns bs ss ts : List ℕ)
    (hns : ns = n :: bs) (ht : bs ++ ss = ts) (hwhole : ns ++ ss = n :: ts) :
    (iteratedStageFlattenEquivalence C ns ss).functor ⋙
        (iteratedStageListEquivalence C hwhole).functor ⋙
          (iteratedStageConsEquivalence C n ts).functor =
      (iteratedStageListEquivalence (IteratedStage C ss) hns).functor ⋙
        (iteratedStageConsEquivalence (IteratedStage C ss) n bs).functor ⋙
          ((iteratedStageFlattenEquivalence_exact C bs ss).1.comp
            (iteratedStageListEquivalence_exact C ht).1).mapStage n := by
  subst ns ts
  let _ : HasZeroObject (Stage (IteratedStage (IteratedStage C ss) bs) n) :=
    generalStageHasZeroObject (IteratedStage (IteratedStage C ss) bs) n
  let _ : WaldhausenCategoryWithoutGluing (Stage (IteratedStage (IteratedStage C ss) bs) n) :=
    generalStageWaldhausenCategory (IteratedStage (IteratedStage C ss) bs) n
  let _ : HasZeroObject (Stage (IteratedStage C (bs ++ ss)) n) :=
    generalStageHasZeroObject (IteratedStage C (bs ++ ss)) n
  let _ : WaldhausenCategoryWithoutGluing (Stage (IteratedStage C (bs ++ ss)) n) :=
    generalStageWaldhausenCategory (IteratedStage C (bs ++ ss)) n
  have hMap := stageMapEq
    ((iteratedStageFlattenEquivalence_exact C bs ss).1.comp
      (iteratedStageListEquivalence_exact C (rfl : bs ++ ss = bs ++ ss)).1)
    (iteratedStageFlattenEquivalence_exact C bs ss).1
    (Functor.comp_id (iteratedStageFlattenEquivalence C bs ss).functor) n
  simp only [iteratedStageListEquivalence, Equivalence.refl,
    Functor.comp_id, Functor.id_comp]
  rw [iteratedStageFlattenEquivalence_cons]
  change (iteratedStageConsEquivalence (IteratedStage C ss) n bs).functor ⋙
      (iteratedStageFlattenEquivalence_exact C bs ss).1.mapStage n ⋙
        ((iteratedStageConsEquivalence C n (bs ++ ss)).inverse ⋙
          (iteratedStageConsEquivalence C n (bs ++ ss)).functor) = _
  rw [iteratedStageConsEquivalence_inverse_functor]
  exact congrArg (fun F =>
    (iteratedStageConsEquivalence (IteratedStage C ss) n bs).functor ⋙ F) hMap.symm

/-- The original empty and successor list transports are retained in a tuple Cons chart. -/
def iteratedStageTupleConsEquivalence {r : ℕ} (x : SimplexCategoryᵒᵖ)
    (a : StageSimplexTuple r) :
    StageAtTuple C (Fin.cons x a) ≌ Stage (StageAtTuple C a) x.unop.len :=
  (iteratedStageListEquivalence C (stageTupleDegrees_cons x a)).trans
    (iteratedStageConsEquivalence C x.unop.len (stageTupleDegrees a))

set_option backward.isDefEq.respectTransparency false in
private theorem tupleConsChart_eq {r : ℕ} (x : SimplexCategoryᵒᵖ) (a : StageSimplexTuple r) :
    iteratedStageTupleConsEquivalence C x a =
      iteratedStageOfFnSuccEquivalence C (fun i : Fin (r + 1) =>
        ((Fin.cons x a : StageSimplexTuple (r + 1)) i).unop.len) := by
  unfold iteratedStageTupleConsEquivalence iteratedStageOfFnSuccEquivalence
  rfl

private theorem tupleConsChart_functor_inverse {r : ℕ} (x : SimplexCategoryᵒᵖ)
    (a : StageSimplexTuple r) :
    (iteratedStageTupleConsEquivalence C x a).functor ⋙
        (iteratedStageTupleConsEquivalence C x a).inverse =
      𝟭 (StageAtTuple C (Fin.cons x a)) := by
  rw [tupleConsChart_eq]
  exact iteratedStageOfFnSuccEquivalence_functor_inverse C
    (fun i : Fin (r + 1) => ((Fin.cons x a : StageSimplexTuple (r + 1)) i).unop.len)

private theorem tupleConsChart_inverse_functor {r : ℕ} (x : SimplexCategoryᵒᵖ)
    (a : StageSimplexTuple r) :
    (iteratedStageTupleConsEquivalence C x a).inverse ⋙
        (iteratedStageTupleConsEquivalence C x a).functor =
      𝟭 (Stage (StageAtTuple C a) x.unop.len) := by
  rw [tupleConsChart_eq]
  exact iteratedStageOfFnSuccEquivalence_inverse_functor C
    (fun i : Fin (r + 1) => ((Fin.cons x a : StageSimplexTuple (r + 1)) i).unop.len)

set_option backward.isDefEq.respectTransparency false in
private theorem reindex_cons {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) :
    reindexIteratedStage C (stageTupleConsMap α f) =
      (iteratedStageTupleConsEquivalence C x a).functor ⋙
        (reindexStage (C := StageAtTuple C a) f.unop ⋙
          (reindexIteratedStage_isWaldhausenExact C α).mapStage y.unop.len) ⋙
        (iteratedStageTupleConsEquivalence C y b).inverse := by
  simpa +unfoldPartialApp only [stageTupleConsMap, Fin.cons,
    Fin.cases_zero, Fin.cases_succ, tupleConsChart_eq] using
    (reindexIteratedStage_succ C (stageTupleConsMap α f))

/-- The normalized original Cons chart of an appended tuple. -/
def iteratedStageTupleSnocConsEquivalence {r : ℕ} (x : SimplexCategoryᵒᵖ)
    (a : StageSimplexTuple r) (z : SimplexCategoryᵒᵖ) :
    StageAtTuple C (stageTupleSnoc (Fin.cons x a) z) ≌
      Stage (StageAtTuple C (stageTupleSnoc a z)) x.unop.len :=
  (iteratedStageTupleEquivalence C (stageTupleSnoc_cons x a z)).trans
    (iteratedStageTupleConsEquivalence C x (stageTupleSnoc a z))

private theorem snocConsChart_functor_inverse {r : ℕ} (x : SimplexCategoryᵒᵖ)
    (a : StageSimplexTuple r) (z : SimplexCategoryᵒᵖ) :
    (iteratedStageTupleSnocConsEquivalence C x a z).functor ⋙
        (iteratedStageTupleSnocConsEquivalence C x a z).inverse =
      𝟭 (StageAtTuple C (stageTupleSnoc (Fin.cons x a) z)) := by
  change (iteratedStageTupleEquivalence C (stageTupleSnoc_cons x a z)).functor ⋙
      ((iteratedStageTupleConsEquivalence C x (stageTupleSnoc a z)).functor ⋙
        (iteratedStageTupleConsEquivalence C x (stageTupleSnoc a z)).inverse) ⋙
      (iteratedStageTupleEquivalence C (stageTupleSnoc_cons x a z)).inverse = _
  rw [tupleConsChart_functor_inverse]
  exact iteratedStageListEquivalence_functor_inverse C
    (congrArg stageTupleDegrees (stageTupleSnoc_cons x a z))

set_option backward.isDefEq.respectTransparency false in
private theorem reindex_snoc_cons {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b)
    {x y : SimplexCategoryᵒᵖ} (f : x ⟶ y) (z : SimplexCategoryᵒᵖ) :
    reindexIteratedStage C (stageTupleSnocMap (stageTupleConsMap α f) (𝟙 z)) ⋙
        (iteratedStageTupleSnocConsEquivalence C y b z).functor =
      (iteratedStageTupleSnocConsEquivalence C x a z).functor ⋙
        (reindexStage (C := StageAtTuple C (stageTupleSnoc a z)) f.unop ⋙
          (reindexIteratedStage_isWaldhausenExact C (stageTupleSnocMap α (𝟙 z))).mapStage
            y.unop.len) := by
  have ht := tupleTransport_reindex C (stageTupleSnoc_cons x a z)
    (stageTupleSnoc_cons y b z) (stageTupleSnocMap (stageTupleConsMap α f) (𝟙 z))
  rw [stageTupleSnocMap_cons] at ht
  have h := congrArg (fun F => F ⋙
    (iteratedStageTupleConsEquivalence C y (stageTupleSnoc b z)).functor) ht
  rw [reindex_cons] at h
  change _ = (iteratedStageTupleSnocConsEquivalence C x a z).functor ⋙ _ ⋙
    ((iteratedStageTupleConsEquivalence C y (stageTupleSnoc b z)).inverse ⋙
      (iteratedStageTupleConsEquivalence C y (stageTupleSnoc b z)).functor) at h
  rw [tupleConsChart_inverse_functor] at h
  exact h

/-- The canonical flattening and actual appended degree equality
give the original tuple chart. -/
def iteratedStageTupleSnocFlattenEquivalence {r : ℕ} (a : StageSimplexTuple r)
    (z : SimplexCategoryᵒᵖ) :
    StageAtTuple (IteratedStage C [z.unop.len]) a ≌ StageAtTuple C (stageTupleSnoc a z) :=
  (iteratedStageFlattenEquivalence C (stageTupleDegrees a) [z.unop.len]).trans
    (iteratedStageListEquivalence C (stageTupleDegrees_snoc a z).symm)

/-- Both directions of the appended tuple chart preserve
the original Waldhausen structures. -/
theorem iteratedStageTupleSnocFlattenEquivalence_exact {r : ℕ} (a : StageSimplexTuple r)
    (z : SimplexCategoryᵒᵖ) :
    (iteratedStageTupleSnocFlattenEquivalence C a z).functor.IsWaldhausenExact ∧
      (iteratedStageTupleSnocFlattenEquivalence C a z).inverse.IsWaldhausenExact := by
  exact ⟨(iteratedStageFlattenEquivalence_exact C (stageTupleDegrees a) [z.unop.len]).1.comp
      (iteratedStageListEquivalence_exact C (stageTupleDegrees_snoc a z).symm).1,
    (iteratedStageListEquivalence_exact C (stageTupleDegrees_snoc a z).symm).2.comp
      (iteratedStageFlattenEquivalence_exact C (stageTupleDegrees a) [z.unop.len]).2⟩

set_option backward.isDefEq.respectTransparency false in
/-- Flattening in the actual head/tail chart is
the original Stage map of tail flattening. -/
theorem iteratedStageTupleSnocFlattenEquivalence_cons {r : ℕ} (x : SimplexCategoryᵒᵖ)
    (a : StageSimplexTuple r) (z : SimplexCategoryᵒᵖ) :
    (iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) z).functor ⋙
        (iteratedStageTupleSnocConsEquivalence C x a z).functor =
      (iteratedStageTupleConsEquivalence (IteratedStage C [z.unop.len]) x a).functor ⋙
        (iteratedStageTupleSnocFlattenEquivalence_exact C a z).1.mapStage x.unop.len := by
  let h₁ := (stageTupleDegrees_snoc (Fin.cons x a) z).symm
  let h₂ := congrArg stageTupleDegrees (stageTupleSnoc_cons x a z)
  let h₃ := stageTupleDegrees_cons x (stageTupleSnoc a z)
  have hTrans :
      (iteratedStageListEquivalence C h₁).functor ⋙
          (iteratedStageListEquivalence C h₂).functor ⋙
            (iteratedStageListEquivalence C h₃).functor =
        (iteratedStageListEquivalence C ((h₁.trans h₂).trans h₃)).functor :=
    (congrArg (fun F => F ⋙ (iteratedStageListEquivalence C h₃).functor)
      (listTransport_trans C h₁ h₂)).trans (listTransport_trans C (h₁.trans h₂) h₃)
  change (iteratedStageFlattenEquivalence C (stageTupleDegrees (Fin.cons x a))
      [z.unop.len]).functor ⋙
      ((iteratedStageListEquivalence C h₁).functor ⋙
        (iteratedStageListEquivalence C h₂).functor ⋙
          (iteratedStageListEquivalence C h₃).functor) ⋙
      (iteratedStageConsEquivalence C x.unop.len
        (stageTupleDegrees (stageTupleSnoc a z))).functor = _
  rw [hTrans]
  exact flattenTransport_cons C x.unop.len (stageTupleDegrees (Fin.cons x a))
    (stageTupleDegrees a) [z.unop.len] (stageTupleDegrees (stageTupleSnoc a z))
    (stageTupleDegrees_cons x a) (stageTupleDegrees_snoc a z).symm ((h₁.trans h₂).trans h₃)

set_option backward.isDefEq.respectTransparency false in
/-- Every original prefix operator commutes with the actual flattening chart
and identity suffix operator. -/
theorem iteratedStageTupleSnocFlattenEquivalence_reindex (r : ℕ)
    {a b : StageSimplexTuple r} (α : a ⟶ b) (z : SimplexCategoryᵒᵖ) :
    reindexIteratedStage (IteratedStage C [z.unop.len]) α ⋙
        (iteratedStageTupleSnocFlattenEquivalence C b z).functor =
      (iteratedStageTupleSnocFlattenEquivalence C a z).functor ⋙
        reindexIteratedStage C (stageTupleSnocMap α (𝟙 z)) := by
  induction r with
  | zero =>
      have hab : a = b := Subsingleton.elim _ _
      subst b
      have hα : α = 𝟙 a := by
        apply CategoryTheory.Pi.ext
        intro i
        exact Fin.elim0 i
      rw [hα, stageTupleSnocMap_id, reindexIteratedStage_id, reindexIteratedStage_id]
      rfl
  | succ r ih =>
      cases a using Fin.consCases with
      | cons x a =>
        cases b using Fin.consCases with
        | cons y b =>
          cases α using Fin.consCases with
          | cons f α =>
            change x ⟶ y at f
            change a ⟶ b at α
            let U := IteratedStage C [z.unop.len]
            let hR := reindexIteratedStage_isWaldhausenExact U α
            let hS := reindexIteratedStage_isWaldhausenExact C (stageTupleSnocMap α (𝟙 z))
            let hA := (iteratedStageTupleSnocFlattenEquivalence_exact C a z).1
            let hB := (iteratedStageTupleSnocFlattenEquivalence_exact C b z).1
            let EA := iteratedStageTupleConsEquivalence U x a
            let EB := iteratedStageTupleConsEquivalence U y b
            let MB := iteratedStageTupleSnocConsEquivalence C y b z
            have hTail := ih α
            have hLift : hR.mapStage y.unop.len ⋙ hB.mapStage y.unop.len =
                hA.mapStage y.unop.len ⋙ hS.mapStage y.unop.len :=
              (Functor.IsWaldhausenExact.mapStage_comp hR hB y.unop.len).symm.trans
                ((stageMapEq (hR.comp hB) (hA.comp hS) hTail y.unop.len).trans
                  (Functor.IsWaldhausenExact.mapStage_comp hA hS y.unop.len))
            have hLeft :
                (reindexIteratedStage U (stageTupleConsMap α f) ⋙
                  (iteratedStageTupleSnocFlattenEquivalence C (Fin.cons y b) z).functor) ⋙
                    MB.functor =
                  EA.functor ⋙ reindexStage (C := StageAtTuple U a) f.unop ⋙
                    hR.mapStage y.unop.len ⋙ hB.mapStage y.unop.len := by
              change reindexIteratedStage U (stageTupleConsMap α f) ⋙
                ((iteratedStageTupleSnocFlattenEquivalence C (Fin.cons y b) z).functor ⋙
                  MB.functor) = _
              rw [iteratedStageTupleSnocFlattenEquivalence_cons, reindex_cons]
              change EA.functor ⋙ reindexStage (C := StageAtTuple U a) f.unop ⋙
                hR.mapStage y.unop.len ⋙ (EB.inverse ⋙ EB.functor) ⋙
                  hB.mapStage y.unop.len = _
              rw [tupleConsChart_inverse_functor]
              rfl
            have hRight :
                ((iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) z).functor ⋙
                  reindexIteratedStage C (stageTupleSnocMap (stageTupleConsMap α f) (𝟙 z))) ⋙
                    MB.functor =
                  EA.functor ⋙ hA.mapStage x.unop.len ⋙
                    reindexStage (C := StageAtTuple C (stageTupleSnoc a z)) f.unop ⋙
                      hS.mapStage y.unop.len := by
              let H := reindexStage (C := StageAtTuple C (stageTupleSnoc a z)) f.unop ⋙
                hS.mapStage y.unop.len
              have hSnoc := congrArg (fun F =>
                (iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) z).functor ⋙ F)
                (reindex_snoc_cons C α f z)
              have hAssoc := (Functor.assoc
                (iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) z).functor
                (iteratedStageTupleSnocConsEquivalence C x a z).functor H).symm.trans
                  ((congrArg (fun F => F ⋙ H)
                    (iteratedStageTupleSnocFlattenEquivalence_cons C x a z)).trans
                      (Functor.assoc EA.functor (hA.mapStage x.unop.len) H))
              exact hSnoc.trans hAssoc
            have hMiddle :=
              (congrArg (fun F => EA.functor ⋙
                reindexStage (C := StageAtTuple U a) f.unop ⋙ F) hLift).trans
                  (congrArg (fun F => EA.functor ⋙ F ⋙ hS.mapStage y.unop.len)
                    (hA.mapStage_reindex f.unop))
            have h := congrArg (fun F => F ⋙ MB.inverse)
              (hLeft.trans (hMiddle.trans hRight.symm))
            change (reindexIteratedStage U (stageTupleConsMap α f) ⋙
                (iteratedStageTupleSnocFlattenEquivalence C (Fin.cons y b) z).functor) ⋙
                (MB.functor ⋙ MB.inverse) =
              ((iteratedStageTupleSnocFlattenEquivalence C (Fin.cons x a) z).functor ⋙
                reindexIteratedStage C (stageTupleSnocMap (stageTupleConsMap α f) (𝟙 z))) ⋙
                (MB.functor ⋙ MB.inverse) at h
            rw [snocConsChart_functor_inverse] at h
            exact h

/-- Every original object follows the same full prefix reindexing square. -/
theorem iteratedStageTupleSnocFlattenEquivalence_reindex_obj (r : ℕ)
    {a b : StageSimplexTuple r} (α : a ⟶ b) (z : SimplexCategoryᵒᵖ)
    (X : StageAtTuple (IteratedStage C [z.unop.len]) a) :
    (iteratedStageTupleSnocFlattenEquivalence C b z).functor.obj
        ((reindexIteratedStage (IteratedStage C [z.unop.len]) α).obj X) =
      (reindexIteratedStage C (stageTupleSnocMap α (𝟙 z))).obj
        ((iteratedStageTupleSnocFlattenEquivalence C a z).functor.obj X) :=
  Functor.congr_obj (iteratedStageTupleSnocFlattenEquivalence_reindex C r α z) X

/-- The same square retains the entire original morphism maps
with their actual endpoint transport. -/
theorem iteratedStageTupleSnocFlattenEquivalence_reindex_map (r : ℕ)
    {a b : StageSimplexTuple r} (α : a ⟶ b) (z : SimplexCategoryᵒᵖ)
    {X Y : StageAtTuple (IteratedStage C [z.unop.len]) a} (f : X ⟶ Y) :
    HEq ((iteratedStageTupleSnocFlattenEquivalence C b z).functor.map
        ((reindexIteratedStage (IteratedStage C [z.unop.len]) α).map f))
      ((reindexIteratedStage C (stageTupleSnocMap α (𝟙 z))).map
        ((iteratedStageTupleSnocFlattenEquivalence C a z).functor.map f)) :=
  Functor.hcongr_hom (iteratedStageTupleSnocFlattenEquivalence_reindex C r α z) f

open scoped Simplicial

/-- The original innermost interval insertion is viewed in the same actual appended tuple. -/
def iteratedStageTupleInnermostIntervalInsertion {r : ℕ} (a : StageSimplexTuple r)
    {z : SimplexCategoryᵒᵖ} (t : (Δ[1] : SSet.{max u v}).obj z) :
    StageAtTuple C a ⥤ StageAtTuple C (stageTupleSnoc a z) :=
  iteratedStageInnermostIntervalInsertion C (stageTupleDegrees a) t ⋙
    (iteratedStageListEquivalence C (stageTupleDegrees_snoc a z).symm).functor

/-- Exactness follows from the original insertion and original equal-list chart. -/
theorem iteratedStageTupleInnermostIntervalInsertion_isWaldhausenExact {r : ℕ}
    (a : StageSimplexTuple r) {z : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj z) :
    (iteratedStageTupleInnermostIntervalInsertion C a t).IsWaldhausenExact :=
  (iteratedStageInnermostIntervalInsertion_isWaldhausenExact C (stageTupleDegrees a) t).comp
    (iteratedStageListEquivalence_exact C (stageTupleDegrees_snoc a z).symm).1

/-- Every original prior tuple direction commutes with the complete original innermost insertion. -/
theorem iteratedStageTupleInnermostIntervalInsertion_reindex (r : ℕ)
    {a b : StageSimplexTuple r} (α : a ⟶ b) {z : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj z) :
    reindexIteratedStage C α ⋙ iteratedStageTupleInnermostIntervalInsertion C b t =
      iteratedStageTupleInnermostIntervalInsertion C a t ⋙
        reindexIteratedStage C (stageTupleSnocMap α (𝟙 z)) :=
  (congrArg (fun F => F ⋙ (iteratedStageTupleSnocFlattenEquivalence C b z).functor)
    (unflattenedInnermostIntervalInsertion_reindex C α t)).trans
      (congrArg (fun F => unflattenedInnermostIntervalInsertion C (stageTupleDegrees a) t ⋙ F)
        (iteratedStageTupleSnocFlattenEquivalence_reindex C r α z))

end CategoryTheory.Waldhausen.SConstruction

end
