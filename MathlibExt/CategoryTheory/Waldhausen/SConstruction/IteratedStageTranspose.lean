/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStageReindex
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.DoubleStageTransposeCoherence
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenNatIso

/-!
# The original arbitrary-list Stage transpose

An added coefficient stage moves through every original iterated stage by
the original double-stage axis swap. The original Nil and Cons charts and
the original exact stage maps retain both functor programs and all local
general-stage zero and Waldhausen values.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory Limits
open scoped Simplicial ZeroObject

universe u v

namespace CategoryTheory.Waldhausen.SConstruction

private structure ExactStageEquivalenceData
    (A B : Type (max u v)) [Category.{v} A] [HasZeroObject A] [WaldhausenCategory A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategory B] where
  equivalence : A ≌ B
  functorExact : equivalence.functor.IsWaldhausenExact
  inverseExact : equivalence.inverse.IsWaldhausenExact

private def ExactStageEquivalenceData.trans
    {A B D : Type (max u v)} [Category.{v} A] [HasZeroObject A] [WaldhausenCategory A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategory B]
    [Category.{v} D] [HasZeroObject D] [WaldhausenCategory D]
    (e : ExactStageEquivalenceData A B) (f : ExactStageEquivalenceData B D) :
    ExactStageEquivalenceData A D :=
  ⟨e.equivalence.trans f.equivalence, e.functorExact.comp f.functorExact,
    f.inverseExact.comp e.inverseExact⟩

private def exactStageEquivalence
    {A B : Type (max u v)} [Category.{v} A] [HasZeroObject A] [WaldhausenCategory A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategory B]
    (e : A ≌ B) (hF : e.functor.IsWaldhausenExact) (hG : e.inverse.IsWaldhausenExact)
    (n : ℕ) :
    letI := generalStageHasZeroObject A n;
    letI := generalStageWaldhausenCategory A n;
    letI := generalStageHasZeroObject B n;
    letI := generalStageWaldhausenCategory B n;
    ExactStageEquivalenceData (Stage A n) (Stage B n) := by
  letI := generalStageHasZeroObject A n
  letI := generalStageWaldhausenCategory A n
  letI := generalStageHasZeroObject B n
  letI := generalStageWaldhausenCategory B n
  let η : 𝟭 (Stage A n) ≅ hF.mapStage n ⋙ hG.mapStage n :=
    (eqToIso (Functor.IsWaldhausenExact.mapStage_id A n)).symm ≪≫
      (Functor.IsWaldhausenExact.id (C := A)).mapStageNatIso (hF.comp hG) e.unitIso n ≪≫
      eqToIso (Functor.IsWaldhausenExact.mapStage_comp hF hG n)
  let ε : hG.mapStage n ⋙ hF.mapStage n ≅ 𝟭 (Stage B n) :=
    (eqToIso (Functor.IsWaldhausenExact.mapStage_comp hG hF n)).symm ≪≫
      (hG.comp hF).mapStageNatIso (Functor.IsWaldhausenExact.id (C := B)) e.counitIso n ≪≫
      eqToIso (Functor.IsWaldhausenExact.mapStage_id B n)
  exact ⟨Equivalence.mk (hF.mapStage n) (hG.mapStage n) η ε,
    hF.mapStage_isWaldhausenExact n, hG.mapStage_isWaldhausenExact n⟩

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

private def iteratedStageTransposeData : (ns : List ℕ) → (n : ℕ) →
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject (IteratedStage C ns) n;
    letI := generalStageWaldhausenCategory (IteratedStage C ns) n;
    ExactStageEquivalenceData (IteratedStage (Stage C n) ns) (Stage (IteratedStage C ns) n)
  | [], n => by
      letI := generalStageHasZeroObject C n
      letI := generalStageWaldhausenCategory C n
      letI := generalStageHasZeroObject (IteratedStage C []) n
      letI := generalStageWaldhausenCategory (IteratedStage C []) n
      let e : ExactStageEquivalenceData (IteratedStage (Stage C n) []) (Stage C n) :=
        ⟨iteratedStageNilEquivalence (Stage C n),
          (iteratedStageNilEquivalence_exact (Stage C n)).1,
          (iteratedStageNilEquivalence_exact (Stage C n)).2⟩
      exact e.trans (exactStageEquivalence (iteratedStageNilEquivalence C).symm
        (iteratedStageNilEquivalence_exact C).2 (iteratedStageNilEquivalence_exact C).1 n)
  | m :: ns, n => by
      letI := generalStageHasZeroObject C n
      letI := generalStageWaldhausenCategory C n
      letI := generalStageHasZeroObject (IteratedStage C ns) n
      letI := generalStageWaldhausenCategory (IteratedStage C ns) n
      letI := generalStageHasZeroObject (IteratedStage C ns) m
      letI := generalStageWaldhausenCategory (IteratedStage C ns) m
      letI := generalStageHasZeroObject (IteratedStage (Stage C n) ns) m
      letI := generalStageWaldhausenCategory (IteratedStage (Stage C n) ns) m
      letI := generalStageHasZeroObject (Stage (IteratedStage C ns) n) m
      letI := generalStageWaldhausenCategory (Stage (IteratedStage C ns) n) m
      letI := generalStageHasZeroObject (Stage (IteratedStage C ns) m) n
      letI := generalStageWaldhausenCategory (Stage (IteratedStage C ns) m) n
      letI := generalStageHasZeroObject (IteratedStage C (m :: ns)) n
      letI := generalStageWaldhausenCategory (IteratedStage C (m :: ns)) n
      let M := iteratedStageTransposeData ns n
      let e : ExactStageEquivalenceData
          (IteratedStage (Stage C n) (m :: ns)) (Stage (IteratedStage (Stage C n) ns) m) :=
        ⟨iteratedStageConsEquivalence (Stage C n) m ns,
          (iteratedStageConsEquivalence_exact (Stage C n) m ns).1,
          (iteratedStageConsEquivalence_exact (Stage C n) m ns).2⟩
      let t : ExactStageEquivalenceData
          (Stage (Stage (IteratedStage C ns) n) m) (Stage (Stage (IteratedStage C ns) m) n) :=
        ⟨doubleStageTransposeEquivalence (IteratedStage C ns) m n,
          doubleStageTransposeFunctor_isWaldhausenExact (IteratedStage C ns) m n,
          doubleStageTransposeEquivalence_inverse_isWaldhausenExact (IteratedStage C ns) m n⟩
      exact ((e.trans (exactStageEquivalence M.equivalence M.functorExact M.inverseExact m)).trans t).trans
        (exactStageEquivalence (iteratedStageConsEquivalence C m ns).symm
          (iteratedStageConsEquivalence_exact C m ns).2
          (iteratedStageConsEquivalence_exact C m ns).1 n)

/-- Move the actual added coefficient stage through every original prior Stage in the list. -/
def iteratedStageTransposeEquivalence (ns : List ℕ) (n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    IteratedStage (Stage C n) ns ≌ Stage (IteratedStage C ns) n := by
  letI := generalStageHasZeroObject C n
  letI := generalStageWaldhausenCategory C n
  letI := generalStageHasZeroObject (IteratedStage C ns) n
  letI := generalStageWaldhausenCategory (IteratedStage C ns) n
  exact (iteratedStageTransposeData C ns n).equivalence

/-- Both original direction programs are exact for the original local Stage structures. -/
theorem iteratedStageTransposeEquivalence_exact (ns : List ℕ) (n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject (IteratedStage C ns) n;
    letI := generalStageWaldhausenCategory (IteratedStage C ns) n;
    (iteratedStageTransposeEquivalence C ns n).functor.IsWaldhausenExact ∧
      (iteratedStageTransposeEquivalence C ns n).inverse.IsWaldhausenExact := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject (IteratedStage C ns) n
  let := generalStageWaldhausenCategory (IteratedStage C ns) n
  exact ⟨(iteratedStageTransposeData C ns n).functorExact,
    (iteratedStageTransposeData C ns n).inverseExact⟩

/-- With no prior directions, the transpose is the original Nil chart followed
by the original lifted inverse Nil chart. -/
theorem iteratedStageTransposeEquivalence_nil_functor (n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    (iteratedStageTransposeEquivalence C [] n).functor =
      (iteratedStageNilEquivalence (Stage C n)).functor ⋙
        (iteratedStageNilEquivalence_exact C).2.mapStage n := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  rfl

/-- The actual successor transpose uses the original Cons chart, prior transpose,
literal double swap and original lifted inverse Cons chart. -/
theorem iteratedStageTransposeEquivalence_cons_functor (m : ℕ) (ns : List ℕ) (n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject (IteratedStage C ns) n;
    letI := generalStageWaldhausenCategory (IteratedStage C ns) n;
    letI := generalStageHasZeroObject (IteratedStage C ns) m;
    letI := generalStageWaldhausenCategory (IteratedStage C ns) m;
    (iteratedStageTransposeEquivalence C (m :: ns) n).functor =
      (iteratedStageConsEquivalence (Stage C n) m ns).functor ⋙
        (iteratedStageTransposeEquivalence_exact C ns n).1.mapStage m ⋙
        doubleStageTransposeFunctor (IteratedStage C ns) m n ⋙
        (iteratedStageConsEquivalence_exact C m ns).2.mapStage n := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject (IteratedStage C ns) n
  let := generalStageWaldhausenCategory (IteratedStage C ns) n
  let := generalStageHasZeroObject (IteratedStage C ns) m
  let := generalStageWaldhausenCategory (IteratedStage C ns) m
  rfl

private theorem stageMap_eq_of_eq
    {A B : Type (max u v)} [Category.{v} A] [HasZeroObject A] [WaldhausenCategory A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategory B]
    {F G : A ⥤ B} (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact)
    (h : F = G) (n : ℕ) : hF.mapStage n = hG.mapStage n := by
  subst G
  rfl

private theorem stageMap_eval
    {A B : Type (max u v)} [Category.{v} A] [HasZeroObject A] [WaldhausenCategory A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategory B]
    {F : A ⥤ B} (hF : F.IsWaldhausenExact) (n : ℕ) (x : Ar n) :
    hF.mapStage n ⋙ eval B n x = eval A n x ⋙ F := by
  rfl

private theorem mapIteratedStage_nil_functor
    {A B : Type (max u v)} [Category.{v} A] [HasZeroObject A] [WaldhausenCategory A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategory B]
    {F : A ⥤ B} (hF : F.IsWaldhausenExact) :
    mapIteratedStage hF [] =
      (iteratedStageNilEquivalence A).functor ⋙ F ⋙ (iteratedStageNilEquivalence B).inverse := by
  have h := congrArg (fun K : IteratedStage A [] ⥤ B =>
    K ⋙ (iteratedStageNilEquivalence B).inverse) (mapIteratedStage_nil_chart hF)
  simpa only [Functor.assoc, iteratedStageNilEquivalence_functor_inverse,
    Functor.comp_id] using h

private theorem mapIteratedStage_cons_functor
    {A B : Type (max u v)} [Category.{v} A] [HasZeroObject A] [WaldhausenCategory A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategory B]
    {F : A ⥤ B} (hF : F.IsWaldhausenExact) (m : ℕ) (ns : List ℕ) :
    letI := generalStageHasZeroObject (IteratedStage A ns) m;
    letI := generalStageWaldhausenCategory (IteratedStage A ns) m;
    letI := generalStageHasZeroObject (IteratedStage B ns) m;
    letI := generalStageWaldhausenCategory (IteratedStage B ns) m;
    mapIteratedStage hF (m :: ns) =
      (iteratedStageConsEquivalence A m ns).functor ⋙
        (mapIteratedStage_isWaldhausenExact hF ns).mapStage m ⋙
        (iteratedStageConsEquivalence B m ns).inverse := by
  let := generalStageHasZeroObject (IteratedStage A ns) m
  let := generalStageWaldhausenCategory (IteratedStage A ns) m
  let := generalStageHasZeroObject (IteratedStage B ns) m
  let := generalStageWaldhausenCategory (IteratedStage B ns) m
  have h := congrArg (fun K : IteratedStage A (m :: ns) ⥤ Stage (IteratedStage B ns) m =>
    K ⋙ (iteratedStageConsEquivalence B m ns).inverse) (mapIteratedStage_cons_chart hF m ns)
  simpa only [Functor.assoc, iteratedStageConsEquivalence_functor_inverse,
    Functor.comp_id] using h

/-- Every original interval evaluation after transpose is the actual iterated
map of that same exact interval evaluation. -/
theorem iteratedStageTransposeEquivalence_eval (ns : List ℕ) (n : ℕ) (x : Ar n) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    (iteratedStageTransposeEquivalence C ns n).functor ⋙ eval (IteratedStage C ns) n x =
      mapIteratedStage (evalIsGeneralStageWaldhausenExact C n x) ns := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  induction ns with
  | nil =>
      rw [iteratedStageTransposeEquivalence_nil_functor]
      rw [Functor.assoc, stageMap_eval]
      exact (mapIteratedStage_nil_functor (evalIsGeneralStageWaldhausenExact C n x)).symm
  | cons m ns ih =>
      let := generalStageHasZeroObject (IteratedStage C ns) n
      let := generalStageWaldhausenCategory (IteratedStage C ns) n
      let := generalStageHasZeroObject (IteratedStage C ns) m
      let := generalStageWaldhausenCategory (IteratedStage C ns) m
      let hT := (iteratedStageTransposeEquivalence_exact C ns n).1
      let hE := evalIsGeneralStageWaldhausenExact (IteratedStage C ns) n x
      let hM := mapIteratedStage_isWaldhausenExact (evalIsGeneralStageWaldhausenExact C n x) ns
      have hMap : hT.mapStage m ⋙ hE.mapStage m = hM.mapStage m := by
        rw [← Functor.IsWaldhausenExact.mapStage_comp]
        exact stageMap_eq_of_eq (hT.comp hE) hM ih m
      rw [iteratedStageTransposeEquivalence_cons_functor, Functor.assoc, Functor.assoc,
        Functor.assoc, stageMap_eval]
      rw [← Functor.assoc (doubleStageTransposeFunctor (IteratedStage C ns) m n)]
      rw [doubleStageTransposeFunctor_eval]
      rw [← Functor.assoc (hT.mapStage m) (hE.mapStage m), hMap]
      exact (mapIteratedStage_cons_functor (evalIsGeneralStageWaldhausenExact C n x) m ns).symm

/-- The original added simplex direction becomes the original outer reindexing,
as an equality of whole original functors. -/
theorem iteratedStageTransposeEquivalence_reindex
    {a b : SimplexCategory} (α : a ⟶ b) (ns : List ℕ) :
    letI := generalStageHasZeroObject C a.len;
    letI := generalStageWaldhausenCategory C a.len;
    letI := generalStageHasZeroObject C b.len;
    letI := generalStageWaldhausenCategory C b.len;
    mapIteratedStage (reindexStage_general_isWaldhausenExact C α) ns ⋙
        (iteratedStageTransposeEquivalence C ns a.len).functor =
      (iteratedStageTransposeEquivalence C ns b.len).functor ⋙
        reindexStage (C := IteratedStage C ns) α := by
  let := generalStageHasZeroObject C a.len
  let := generalStageWaldhausenCategory C a.len
  let := generalStageHasZeroObject C b.len
  let := generalStageWaldhausenCategory C b.len
  let hR := reindexStage_general_isWaldhausenExact C α
  induction ns with
  | nil =>
      let hN := (iteratedStageNilEquivalence_exact C).2
      rw [iteratedStageTransposeEquivalence_nil_functor,
        iteratedStageTransposeEquivalence_nil_functor]
      rw [← Functor.assoc (mapIteratedStage hR [])
        (iteratedStageNilEquivalence (Stage C a.len)).functor]
      rw [mapIteratedStage_nil_chart, Functor.assoc, hN.mapStage_reindex α]
      rfl
  | cons m ns ih =>
      let := generalStageHasZeroObject (IteratedStage C ns) a.len
      let := generalStageWaldhausenCategory (IteratedStage C ns) a.len
      let := generalStageHasZeroObject (IteratedStage C ns) b.len
      let := generalStageWaldhausenCategory (IteratedStage C ns) b.len
      let := generalStageHasZeroObject (IteratedStage C ns) m
      let := generalStageWaldhausenCategory (IteratedStage C ns) m
      let hM := mapIteratedStage_isWaldhausenExact hR ns
      let hA := (iteratedStageTransposeEquivalence_exact C ns a.len).1
      let hB := (iteratedStageTransposeEquivalence_exact C ns b.len).1
      let hX := reindexStage_general_isWaldhausenExact (IteratedStage C ns) α
      let hI := (iteratedStageConsEquivalence_exact C m ns).2
      have hMap : hM.mapStage m ⋙ hA.mapStage m = hB.mapStage m ⋙ hX.mapStage m := by
        rw [← Functor.IsWaldhausenExact.mapStage_comp,
          ← Functor.IsWaldhausenExact.mapStage_comp]
        exact stageMap_eq_of_eq (hM.comp hA) (hB.comp hX) ih m
      have hSwap : hX.mapStage m ⋙
          doubleStageTransposeFunctor (IteratedStage C ns) m a.len =
        doubleStageTransposeFunctor (IteratedStage C ns) m b.len ⋙
          reindexStage (C := Stage (IteratedStage C ns) m) α :=
        doubleStageTransposeFunctor_reindexInner (IteratedStage C ns) α m
      rw [iteratedStageTransposeEquivalence_cons_functor,
        iteratedStageTransposeEquivalence_cons_functor]
      rw [← Functor.assoc (mapIteratedStage hR (m :: ns))
        (iteratedStageConsEquivalence (Stage C a.len) m ns).functor]
      rw [mapIteratedStage_cons_chart]
      change (iteratedStageConsEquivalence (Stage C b.len) m ns).functor ⋙
          (hM.mapStage m ⋙ hA.mapStage m) ⋙
          doubleStageTransposeFunctor (IteratedStage C ns) m a.len ⋙ hI.mapStage a.len =
        (iteratedStageConsEquivalence (Stage C b.len) m ns).functor ⋙ hB.mapStage m ⋙
          doubleStageTransposeFunctor (IteratedStage C ns) m b.len ⋙ hI.mapStage b.len ⋙
          reindexStage (C := IteratedStage C (m :: ns)) α
      rw [hMap]
      change (iteratedStageConsEquivalence (Stage C b.len) m ns).functor ⋙ hB.mapStage m ⋙
          (hX.mapStage m ⋙ doubleStageTransposeFunctor (IteratedStage C ns) m a.len) ⋙
          hI.mapStage a.len = _
      rw [hSwap]
      change (iteratedStageConsEquivalence (Stage C b.len) m ns).functor ⋙ hB.mapStage m ⋙
          doubleStageTransposeFunctor (IteratedStage C ns) m b.len ⋙
          (reindexStage (C := Stage (IteratedStage C ns) m) α ⋙ hI.mapStage a.len) = _
      rw [hI.mapStage_reindex α]

/-- The original zeroth-face quotient is carried to the same quotient in the added
Stage direction. This is the whole original functor equation, including degree zero. -/
theorem iteratedStageTransposeEquivalence_quotient (ns : List ℕ) (n : ℕ) :
    letI := generalStageHasZeroObject C (n + 1);
    letI := generalStageWaldhausenCategory C (n + 1);
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    (iteratedStageTransposeEquivalence C ns (n + 1)).functor ⋙
        StageFirstQuotient.quotient (IteratedStage C ns) n =
      mapIteratedStage (StageFirstQuotient.quotient_isWaldhausenExact C n) ns ⋙
        (iteratedStageTransposeEquivalence C ns n).functor := by
  let := generalStageHasZeroObject C (n + 1)
  let := generalStageWaldhausenCategory C (n + 1)
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  exact (iteratedStageTransposeEquivalence_reindex C
    (SimplexCategory.δ (0 : Fin (n + 2))) ns).symm

private theorem transpose_list_chart {ns ms : List ℕ} (h : ns = ms) (n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    (iteratedStageTransposeEquivalence C ns n).functor =
      (iteratedStageListEquivalence (Stage C n) h).functor ⋙
        (iteratedStageTransposeEquivalence C ms n).functor ⋙
        (iteratedStageListEquivalence_exact C h).2.mapStage n := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  subst ms
  change (iteratedStageTransposeEquivalence C ns n).functor =
    𝟭 _ ⋙ (iteratedStageTransposeEquivalence C ns n).functor ⋙
      (Functor.IsWaldhausenExact.id (C := IteratedStage C ns)).mapStage n
  rw [Functor.IsWaldhausenExact.mapStage_id, Functor.id_comp, Functor.comp_id]

private theorem transpose_tuple_successor {r : ℕ} (a : StageSimplexTuple (r + 1)) (n : ℕ) :
    let ns := stageTupleDegrees (fun i => a i.succ)
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject (IteratedStage C ns) n;
    letI := generalStageWaldhausenCategory (IteratedStage C ns) n;
    letI := generalStageHasZeroObject (IteratedStage C ns) (a 0).unop.len;
    letI := generalStageWaldhausenCategory (IteratedStage C ns) (a 0).unop.len;
    letI := generalStageHasZeroObject
      (IteratedStage C (List.ofFn (fun i => (a i.succ).unop.len))) (a 0).unop.len;
    letI := generalStageWaldhausenCategory
      (IteratedStage C (List.ofFn (fun i => (a i.succ).unop.len))) (a 0).unop.len;
    (iteratedStageTransposeEquivalence C (stageTupleDegrees a) n).functor =
      (iteratedStageOfFnSuccEquivalence (Stage C n) (fun i => (a i).unop.len)).functor ⋙
        (iteratedStageTransposeEquivalence_exact C ns n).1.mapStage (a 0).unop.len ⋙
        doubleStageTransposeFunctor (IteratedStage C ns) (a 0).unop.len n ⋙
        (iteratedStageOfFnSuccEquivalence_exact C (fun i => (a i).unop.len)).2.mapStage n := by
  dsimp only
  let ns := stageTupleDegrees (fun i => a i.succ)
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject (IteratedStage C ns) n
  let := generalStageWaldhausenCategory (IteratedStage C ns) n
  let := generalStageHasZeroObject (IteratedStage C ns) (a 0).unop.len
  let := generalStageWaldhausenCategory (IteratedStage C ns) (a 0).unop.len
  let := generalStageHasZeroObject
    (IteratedStage C (List.ofFn (fun i => (a i.succ).unop.len))) (a 0).unop.len
  let := generalStageWaldhausenCategory
    (IteratedStage C (List.ofFn (fun i => (a i.succ).unop.len))) (a 0).unop.len
  rw [transpose_list_chart C (stageTupleDegrees_succ a) n]
  rw [iteratedStageTransposeEquivalence_cons_functor]
  change (iteratedStageListEquivalence (Stage C n) (stageTupleDegrees_succ a)).functor ⋙
      (iteratedStageConsEquivalence (Stage C n) (a 0).unop.len ns).functor ⋙
      (iteratedStageTransposeEquivalence_exact C ns n).1.mapStage (a 0).unop.len ⋙
      doubleStageTransposeFunctor (IteratedStage C ns) (a 0).unop.len n ⋙
      ((iteratedStageConsEquivalence_exact C (a 0).unop.len ns).2.mapStage n ⋙
        (iteratedStageListEquivalence_exact C (stageTupleDegrees_succ a)).2.mapStage n) = _
  rw [← Functor.IsWaldhausenExact.mapStage_comp]
  rfl

private theorem stageMap_inverse_functor
    {A B : Type (max u v)} [Category.{v} A] [HasZeroObject A] [WaldhausenCategory A]
    [Category.{v} B] [HasZeroObject B] [WaldhausenCategory B]
    (e : A ≌ B) (hF : e.functor.IsWaldhausenExact) (hG : e.inverse.IsWaldhausenExact)
    (h : e.inverse ⋙ e.functor = 𝟭 B) (n : ℕ) :
    hG.mapStage n ⋙ hF.mapStage n = 𝟭 (Stage B n) := by
  rw [← Functor.IsWaldhausenExact.mapStage_comp]
  exact (stageMap_eq_of_eq (hG.comp hF) (Functor.IsWaldhausenExact.id (C := B)) h n).trans
    (Functor.IsWaldhausenExact.mapStage_id B n)

/-- Every original prior simplex-tuple operator moves across the actual transpose
to the same original prior operator under the outer Stage map. -/
theorem iteratedStageTransposeEquivalence_reindexTuple {r : ℕ}
    {a b : StageSimplexTuple r} (α : a ⟶ b) (n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    reindexIteratedStage (Stage C n) α ⋙
        (iteratedStageTransposeEquivalence C (stageTupleDegrees b) n).functor =
      (iteratedStageTransposeEquivalence C (stageTupleDegrees a) n).functor ⋙
        (reindexIteratedStage_isWaldhausenExact C α).mapStage n := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  induction r with
  | zero =>
      have hab : a = b := Subsingleton.elim _ _
      subst b
      rw [reindexIteratedStage_zero]
      have hR := stageMap_eq_of_eq (reindexIteratedStage_isWaldhausenExact C α)
        (Functor.IsWaldhausenExact.id (C := StageAtTuple C a))
        (reindexIteratedStage_zero C a α) n
      rw [hR, Functor.IsWaldhausenExact.mapStage_id, Functor.id_comp, Functor.comp_id]
  | succ r ih =>
      let tailA : StageSimplexTuple r := fun i => a i.succ
      let tailB : StageSimplexTuple r := fun i => b i.succ
      let αt : tailA ⟶ tailB := fun i => α i.succ
      let Da := IteratedStage C (List.ofFn (fun i => (a i.succ).unop.len))
      let Db := IteratedStage C (List.ofFn (fun i => (b i.succ).unop.len))
      let Sa := IteratedStage (Stage C n) (List.ofFn (fun i => (a i.succ).unop.len))
      let Sb := IteratedStage (Stage C n) (List.ofFn (fun i => (b i.succ).unop.len))
      let ma := (a 0).unop.len
      let mb := (b 0).unop.len
      let f := (α 0).unop
      let := generalStageHasZeroObject Da n
      let := generalStageWaldhausenCategory Da n
      let := generalStageHasZeroObject Db n
      let := generalStageWaldhausenCategory Db n
      let := generalStageHasZeroObject Da ma
      let := generalStageWaldhausenCategory Da ma
      let := generalStageHasZeroObject Da mb
      let := generalStageWaldhausenCategory Da mb
      let := generalStageHasZeroObject Db mb
      let := generalStageWaldhausenCategory Db mb
      let := generalStageHasZeroObject Sa ma
      let := generalStageWaldhausenCategory Sa ma
      let := generalStageHasZeroObject Sa mb
      let := generalStageWaldhausenCategory Sa mb
      let := generalStageHasZeroObject Sb mb
      let := generalStageWaldhausenCategory Sb mb
      let := generalStageHasZeroObject (StageAtTuple C tailA) n
      let := generalStageWaldhausenCategory (StageAtTuple C tailA) n
      let := generalStageHasZeroObject (StageAtTuple C tailB) n
      let := generalStageWaldhausenCategory (StageAtTuple C tailB) n
      let := generalStageHasZeroObject (StageAtTuple C tailA) mb
      let := generalStageWaldhausenCategory (StageAtTuple C tailA) mb
      let := generalStageHasZeroObject (StageAtTuple C tailB) mb
      let := generalStageWaldhausenCategory (StageAtTuple C tailB) mb
      let := generalStageHasZeroObject (IteratedStage C (stageTupleDegrees tailA)) n
      let := generalStageWaldhausenCategory (IteratedStage C (stageTupleDegrees tailA)) n
      let := generalStageHasZeroObject (IteratedStage C (stageTupleDegrees tailB)) n
      let := generalStageWaldhausenCategory (IteratedStage C (stageTupleDegrees tailB)) n
      let hRS := reindexIteratedStage_isWaldhausenExact (Stage C n) αt
      let hR := reindexIteratedStage_isWaldhausenExact C αt
      let hTa := (iteratedStageTransposeEquivalence_exact C (stageTupleDegrees tailA) n).1
      let hTb := (iteratedStageTransposeEquivalence_exact C (stageTupleDegrees tailB) n).1
      have hTail : hRS.mapStage mb ⋙ hTb.mapStage mb =
          hTa.mapStage mb ⋙ (hR.mapStage_isWaldhausenExact n).mapStage mb := by
        rw [← Functor.IsWaldhausenExact.mapStage_comp,
          ← Functor.IsWaldhausenExact.mapStage_comp]
        exact stageMap_eq_of_eq (hRS.comp hTb) (hTa.comp (hR.mapStage_isWaldhausenExact n))
          (ih αt) mb
      have hDouble : (hR.mapStage_isWaldhausenExact n).mapStage mb ⋙
          doubleStageTransposeFunctor Db mb n =
        doubleStageTransposeFunctor Da mb n ⋙ (hR.mapStage_isWaldhausenExact mb).mapStage n :=
        (doubleStageTransposeFunctor_mapDoubleStage hR mb n).symm
      have hHead : reindexStage (C := Stage Da n) f ⋙
          doubleStageTransposeFunctor Da mb n =
        doubleStageTransposeFunctor Da ma n ⋙ (reindexStage_general_isWaldhausenExact Da f).mapStage n :=
        doubleStageTransposeFunctor_reindexOuter Da f n
      let ea := iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len)
      let eb := iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len)
      let eas := iteratedStageOfFnSuccEquivalence (Stage C n) (fun i => (a i).unop.len)
      let ebs := iteratedStageOfFnSuccEquivalence (Stage C n) (fun i => (b i).unop.len)
      let hEa := (iteratedStageOfFnSuccEquivalence_exact C (fun i => (a i).unop.len)).1
      let hEaI := (iteratedStageOfFnSuccEquivalence_exact C (fun i => (a i).unop.len)).2
      let hEbI := (iteratedStageOfFnSuccEquivalence_exact C (fun i => (b i).unop.len)).2
      let hH := reindexStage_general_isWaldhausenExact Da f
      have hMapped : (reindexIteratedStage_isWaldhausenExact C α).mapStage n =
          hEa.mapStage n ⋙ hH.mapStage n ⋙ (hR.mapStage_isWaldhausenExact mb).mapStage n ⋙
            hEbI.mapStage n := by
        have he := reindexIteratedStage_succ C α
        have hExact := (hEa.comp (hH.comp (hR.mapStage_isWaldhausenExact mb))).comp hEbI
        have hs := stageMap_eq_of_eq (reindexIteratedStage_isWaldhausenExact C α) hExact he n
        calc
          _ = ((hEa.comp (hH.comp (hR.mapStage_isWaldhausenExact mb))).comp hEbI).mapStage n := hs
          _ = _ := by
            erw [Functor.IsWaldhausenExact.mapStage_comp
                (hEa.comp (hH.comp (hR.mapStage_isWaldhausenExact mb))) hEbI n,
              Functor.IsWaldhausenExact.mapStage_comp hEa
                (hH.comp (hR.mapStage_isWaldhausenExact mb)) n,
              Functor.IsWaldhausenExact.mapStage_comp hH (hR.mapStage_isWaldhausenExact mb) n,
              Functor.assoc]
      have hCancel : hEaI.mapStage n ⋙ hEa.mapStage n = 𝟭 (Stage (Stage Da ma) n) :=
        stageMap_inverse_functor ea hEa hEaI
          (iteratedStageOfFnSuccEquivalence_inverse_functor C (fun i => (a i).unop.len)) n
      have hCancelS : ebs.inverse ⋙ ebs.functor = 𝟭 (Stage Sb mb) :=
        iteratedStageOfFnSuccEquivalence_inverse_functor (Stage C n) (fun i => (b i).unop.len)
      rw [reindexIteratedStage_succ, transpose_tuple_successor C b n,
        transpose_tuple_successor C a n, hMapped]
      change (eas.functor ⋙ (reindexStage (C := Sa) f ⋙ hRS.mapStage mb) ⋙ ebs.inverse) ⋙
          (ebs.functor ⋙ hTb.mapStage mb ⋙ doubleStageTransposeFunctor Db mb n ⋙ hEbI.mapStage n) =
        (eas.functor ⋙ hTa.mapStage ma ⋙ doubleStageTransposeFunctor Da ma n ⋙ hEaI.mapStage n) ⋙
          (hEa.mapStage n ⋙ hH.mapStage n ⋙ (hR.mapStage_isWaldhausenExact mb).mapStage n ⋙
            hEbI.mapStage n)
      change eas.functor ⋙ reindexStage (C := Sa) f ⋙ hRS.mapStage mb ⋙
          (ebs.inverse ⋙ ebs.functor) ⋙ hTb.mapStage mb ⋙
          doubleStageTransposeFunctor Db mb n ⋙ hEbI.mapStage n =
        eas.functor ⋙ hTa.mapStage ma ⋙ doubleStageTransposeFunctor Da ma n ⋙
          (hEaI.mapStage n ⋙ hEa.mapStage n) ⋙ hH.mapStage n ⋙
          (hR.mapStage_isWaldhausenExact mb).mapStage n ⋙ hEbI.mapStage n
      erw [hCancelS, hCancel,
        Functor.id_comp, Functor.id_comp]
      change eas.functor ⋙ reindexStage (C := Sa) f ⋙
          (hRS.mapStage mb ⋙ hTb.mapStage mb) ⋙ doubleStageTransposeFunctor Db mb n ⋙
          hEbI.mapStage n = _
      erw [hTail]
      change eas.functor ⋙ (reindexStage (C := Sa) f ⋙ hTa.mapStage mb) ⋙
          (hR.mapStage_isWaldhausenExact n).mapStage mb ⋙
          doubleStageTransposeFunctor Db mb n ⋙ hEbI.mapStage n = _
      erw [hTa.mapStage_reindex f]
      change eas.functor ⋙ hTa.mapStage ma ⋙ reindexStage (C := Stage Da n) f ⋙
          ((hR.mapStage_isWaldhausenExact n).mapStage mb ⋙ doubleStageTransposeFunctor Db mb n) ⋙
          hEbI.mapStage n = _
      erw [hDouble]
      change eas.functor ⋙ hTa.mapStage ma ⋙
          (reindexStage (C := Stage Da n) f ⋙ doubleStageTransposeFunctor Da mb n) ⋙
          (hR.mapStage_isWaldhausenExact mb).mapStage n ⋙ hEbI.mapStage n = _
      erw [hHead, Functor.assoc]

end CategoryTheory.Waldhausen.SConstruction
