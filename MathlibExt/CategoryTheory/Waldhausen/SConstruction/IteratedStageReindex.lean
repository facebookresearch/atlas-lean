/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.IteratedStage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageReindexWaldhausenExact

/-!
# Every original simplex direction of the iterated S-construction

A finite simplex tuple gives the original degree list. Reindexing a tuple
recursively uses exact reindexing in its head direction and the original
stage functor of the earned exact tail map. The canonical successor
carrier equivalences retain the same original stage structures.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Waldhausen.SConstruction

/-- A finite tuple of actual simplex degrees. -/
abbrev StageSimplexTuple (r : ℕ) := Fin r → SimplexCategoryᵒᵖ

/-- The original S-stage degree list associated to a finite simplex tuple. -/
def stageTupleDegrees {r : ℕ} (a : StageSimplexTuple r) : List ℕ :=
  List.ofFn (fun i => (a i).unop.len)

/-- A successor simplex tuple retains the original head and tail degrees. -/
theorem stageTupleDegrees_succ {r : ℕ} (a : StageSimplexTuple (r + 1)) :
    stageTupleDegrees a = (a 0).unop.len :: stageTupleDegrees (fun i => a i.succ) := by
  simp only [stageTupleDegrees, List.ofFn_succ]

variable (C : Type (max u v)) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Original iterated stages at their actual finite simplex tuple. -/
abbrev StageAtTuple {r : ℕ} (a : StageSimplexTuple r) :=
  IteratedStage C (stageTupleDegrees a)

private structure TupleReindexData {r : ℕ} (a b : StageSimplexTuple r) where
  functor : StageAtTuple C a ⥤ StageAtTuple C b
  exact : functor.IsWaldhausenExact

private def tupleReindexData : (r : ℕ) → (a b : StageSimplexTuple r) →
    (a ⟶ b) → TupleReindexData C a b
  | 0, a, b, α => by
      have ha : a = b := Subsingleton.elim _ _
      subst b
      exact ⟨𝟭 _, Functor.IsWaldhausenExact.id⟩
  | r + 1, a, b, α => by
      let tailA : StageSimplexTuple r := fun i => a i.succ
      let tailB : StageSimplexTuple r := fun i => b i.succ
      let αt : tailA ⟶ tailB := fun i => α i.succ
      let M := tupleReindexData r tailA tailB αt
      let D := StageAtTuple C tailA
      let E := StageAtTuple C tailB
      letI : HasZeroObject (Stage D (a 0).unop.len) :=
        generalStageHasZeroObject D (a 0).unop.len
      letI : WaldhausenCategoryWithoutGluing (Stage D (a 0).unop.len) :=
        generalStageWaldhausenCategory D (a 0).unop.len
      letI : HasZeroObject (Stage D (b 0).unop.len) :=
        generalStageHasZeroObject D (b 0).unop.len
      letI : WaldhausenCategoryWithoutGluing (Stage D (b 0).unop.len) :=
        generalStageWaldhausenCategory D (b 0).unop.len
      letI : HasZeroObject (Stage E (b 0).unop.len) :=
        generalStageHasZeroObject E (b 0).unop.len
      letI : WaldhausenCategoryWithoutGluing (Stage E (b 0).unop.len) :=
        generalStageWaldhausenCategory E (b 0).unop.len
      let head : Stage D (a 0).unop.len ⥤ Stage E (b 0).unop.len :=
        reindexStage (C := D) (α 0).unop ⋙ M.exact.mapStage (b 0).unop.len
      have hhead : head.IsWaldhausenExact :=
        (reindexStage_general_isWaldhausenExact D (α 0).unop).comp
          (M.exact.mapStage_isWaldhausenExact (b 0).unop.len)
      let ea := iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len)
      let eb := iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len)
      letI : HasZeroObject
          (Stage (IteratedStage C (List.ofFn (fun i => (a i.succ).unop.len))) (a 0).unop.len) :=
        generalStageHasZeroObject _ _
      letI : WaldhausenCategoryWithoutGluing
          (Stage (IteratedStage C (List.ofFn (fun i => (a i.succ).unop.len))) (a 0).unop.len) :=
        generalStageWaldhausenCategory _ _
      letI : HasZeroObject
          (Stage (IteratedStage C (List.ofFn (fun i => (b i.succ).unop.len))) (b 0).unop.len) :=
        generalStageHasZeroObject _ _
      letI : WaldhausenCategoryWithoutGluing
          (Stage (IteratedStage C (List.ofFn (fun i => (b i.succ).unop.len))) (b 0).unop.len) :=
        generalStageWaldhausenCategory _ _
      exact ⟨ea.functor ⋙ head ⋙ eb.inverse,
        ((iteratedStageOfFnSuccEquivalence_exact C (fun i => (a i).unop.len)).1.comp hhead).comp
          (iteratedStageOfFnSuccEquivalence_exact C (fun i => (b i).unop.len)).2⟩

/-- The actual original reindex functor for every finite tuple of simplex maps. -/
@[no_expose]
def reindexIteratedStage {r : ℕ} {a b : StageSimplexTuple r} (α : a ⟶ b) :
    StageAtTuple C a ⥤ StageAtTuple C b := (tupleReindexData C r a b α).functor

/-- Every actual tuple reindexing earns Waldhausen exactness internally. -/
theorem reindexIteratedStage_isWaldhausenExact {r : ℕ} {a b : StageSimplexTuple r}
    (α : a ⟶ b) : (reindexIteratedStage C α).IsWaldhausenExact := by
  unfold reindexIteratedStage
  exact (tupleReindexData C r a b α).exact


universe uE vE

private theorem stageMap_eq_of_eq {D : Type (max u v)} {E : Type (max uE vE)} [Category.{v} D]
    [HasZeroObject D] [WaldhausenCategoryWithoutGluing D] [Category.{vE} E]
    [HasZeroObject E] [WaldhausenCategoryWithoutGluing E] {F G : D ⥤ E}
    (hF : F.IsWaldhausenExact) (hG : G.IsWaldhausenExact) (h : F = G) (n : ℕ) :
    hF.mapStage n = hG.mapStage n := by
  subst G
  rfl


/-- With no simplex directions, the actual original reindexing is the identity. -/
theorem reindexIteratedStage_zero (a : StageSimplexTuple 0) (α : a ⟶ a) :
    reindexIteratedStage C α = 𝟭 (StageAtTuple C a) := by
  unfold reindexIteratedStage tupleReindexData
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual successor recursion is head reindexing followed by the exact tail stage map,
transported through the original degree-list successor equivalences. -/
theorem reindexIteratedStage_succ {r : ℕ} {a b : StageSimplexTuple (r + 1)} (α : a ⟶ b) :
    let D := StageAtTuple C (fun i => a i.succ)
    let E := StageAtTuple C (fun i => b i.succ)
    letI : HasZeroObject (Stage D (a 0).unop.len) := generalStageHasZeroObject D _
    letI : WaldhausenCategoryWithoutGluing (Stage D (a 0).unop.len) :=
      generalStageWaldhausenCategory D _
    letI : HasZeroObject (Stage D (b 0).unop.len) := generalStageHasZeroObject D _
    letI : WaldhausenCategoryWithoutGluing (Stage D (b 0).unop.len) :=
      generalStageWaldhausenCategory D _
    letI : HasZeroObject (Stage E (b 0).unop.len) := generalStageHasZeroObject E _
    letI : WaldhausenCategoryWithoutGluing (Stage E (b 0).unop.len) :=
      generalStageWaldhausenCategory E _
    reindexIteratedStage C α =
      (iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len)).functor ⋙
        (reindexStage (C := D) (α 0).unop ⋙
          (reindexIteratedStage_isWaldhausenExact C (fun i => α i.succ)).mapStage (b 0).unop.len) ⋙
        (iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len)).inverse := by
  dsimp only
  unfold reindexIteratedStage tupleReindexData
  dsimp only
  apply congrArg (fun H =>
    (iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len)).functor ⋙
      (reindexStage (C := StageAtTuple C (fun i => a i.succ)) (α 0).unop ⋙ H) ⋙
      (iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len)).inverse)
  apply stageMap_eq_of_eq
  cases r <;> rfl

/-- The original successor carrier's object calculation retains the head and tail maps. -/
theorem reindexIteratedStage_succ_obj {r : ℕ} {a b : StageSimplexTuple (r + 1)}
    (α : a ⟶ b) (X : StageAtTuple C a) :
    (reindexIteratedStage C α).obj X =
      (iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len)).inverse.obj
        (((reindexIteratedStage_isWaldhausenExact C (fun i => α i.succ)).mapStage
          (b 0).unop.len).obj
          ((reindexStage (C := StageAtTuple C (fun i => a i.succ)) (α 0).unop).obj
            ((iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len)).functor.obj X))) :=
  Functor.congr_obj (reindexIteratedStage_succ C α) X

/-- Every actual successor morphism is the same original head reindexing and mapped tail morphism.
-/
theorem reindexIteratedStage_succ_map {r : ℕ} {a b : StageSimplexTuple (r + 1)}
    (α : a ⟶ b) {X Y : StageAtTuple C a} (f : X ⟶ Y) :
    HEq ((reindexIteratedStage C α).map f)
      ((iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len)).inverse.map
        (((reindexIteratedStage_isWaldhausenExact C (fun i => α i.succ)).mapStage
          (b 0).unop.len).map
          ((reindexStage (C := StageAtTuple C (fun i => a i.succ)) (α 0).unop).map
            ((iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len)).functor.map f)))) := by
  have h := reindexIteratedStage_succ C α
  cases h
  rfl

private theorem transported_comp {A A' B B' D D' : Type (max u v)}
    [Category.{v} A] [Category.{v} A'] [Category.{v} B] [Category.{v} B']
    [Category.{v} D] [Category.{v} D']
    (ea : A ≌ A') (eb : B ≌ B') (ed : D ≌ D')
    (F : A' ⥤ B') (G : B' ⥤ D') (h : eb.inverse ⋙ eb.functor = 𝟭 B') :
    (ea.functor ⋙ F ⋙ eb.inverse) ⋙ (eb.functor ⋙ G ⋙ ed.inverse) =
      ea.functor ⋙ (F ⋙ G) ⋙ ed.inverse := by
  change ea.functor ⋙ F ⋙ (eb.inverse ⋙ eb.functor) ⋙ G ⋙ ed.inverse = _
  rw [h]
  rfl

universe uD vD

private theorem transported_naturality {A A' B B' : Type (max u v)}
    [Category.{v} A] [Category.{v} A'] [Category.{v} B] [Category.{v} B']
    {D D' E E' : Type (max uD vD)}
    [Category.{vD} D] [Category.{vD} D'] [Category.{vD} E] [Category.{vD} E']
    (ea : A ≌ A') (eb : B ≌ B') (ed : D ≌ D') (ee : E ≌ E')
    (R : A' ⥤ B') (S : D' ⥤ E') (F : A ⥤ D) (G : B ⥤ E)
    (F' : A' ⥤ D') (G' : B' ⥤ E')
    (ha : F ⋙ ed.functor = ea.functor ⋙ F')
    (hb : G ⋙ ee.functor = eb.functor ⋙ G')
    (hs : R ⋙ G' = F' ⋙ S)
    (hb₁ : eb.inverse ⋙ eb.functor = 𝟭 B')
    (he₁ : ee.functor ⋙ ee.inverse = 𝟭 E) :
    (ea.functor ⋙ R ⋙ eb.inverse) ⋙ G = F ⋙ (ed.functor ⋙ S ⋙ ee.inverse) := by
  have hb' : eb.inverse ⋙ G = G' ⋙ ee.inverse := by
    have h := congrArg (fun K : B ⥤ E' => eb.inverse ⋙ K ⋙ ee.inverse) hb
    have hleft : eb.inverse ⋙ (G ⋙ ee.functor) ⋙ ee.inverse = eb.inverse ⋙ G := by
      change eb.inverse ⋙ G ⋙ (ee.functor ⋙ ee.inverse) = _
      rw [he₁]
      rfl
    have hright : eb.inverse ⋙ (eb.functor ⋙ G') ⋙ ee.inverse = G' ⋙ ee.inverse := by
      change (eb.inverse ⋙ eb.functor) ⋙ G' ⋙ ee.inverse = _
      rw [hb₁]
      rfl
    exact hleft.symm.trans (h.trans hright)
  have h₁ := congrArg (fun K : B' ⥤ E => ea.functor ⋙ R ⋙ K) hb'
  have h₂ := congrArg (fun K : A' ⥤ E' => ea.functor ⋙ K ⋙ ee.inverse) hs
  have h₃ := congrArg (fun K : A ⥤ D' => K ⋙ S ⋙ ee.inverse) ha
  exact h₁.trans (h₂.trans h₃.symm)

/-- Every original finite tuple sends its identity operators to the actual identity. -/
theorem reindexIteratedStage_id (r : ℕ) (a : StageSimplexTuple r) :
    reindexIteratedStage C (𝟙 a) = 𝟭 (StageAtTuple C a) := by
  induction r with
  | zero =>
      unfold reindexIteratedStage tupleReindexData
      rfl
  | succ r ih =>
      let tailA : StageSimplexTuple r := fun i => a i.succ
      have ht := ih tailA
      unfold reindexIteratedStage tupleReindexData
      dsimp only
      have htail : (tupleReindexData C r tailA tailA (𝟙 tailA)).functor = 𝟭 _ := ht
      have hm := stageMap_eq_of_eq (tupleReindexData C r tailA tailA (𝟙 tailA)).exact
        (Functor.IsWaldhausenExact.id (C := StageAtTuple C tailA)) htail (a 0).unop.len
      simp only [Functor.IsWaldhausenExact.mapStage_id,
        ] at hm ⊢
      rw [hm]
      exact iteratedStageOfFnSuccEquivalence_functor_inverse C (fun i => (a i).unop.len)

/-- Original componentwise simplex composition gives the same source-first
composition on every actual iterated stage. -/
theorem reindexIteratedStage_comp (r : ℕ) {a b c : StageSimplexTuple r}
    (α : a ⟶ b) (β : b ⟶ c) :
    reindexIteratedStage C (α ≫ β) =
      reindexIteratedStage C α ⋙ reindexIteratedStage C β := by
  induction r with
  | zero =>
      have hab : a = b := Subsingleton.elim _ _
      have hac : a = c := Subsingleton.elim _ _
      subst b
      subst c
      unfold reindexIteratedStage tupleReindexData
      rfl
  | succ r ih =>
      let tailA : StageSimplexTuple r := fun i => a i.succ
      let tailB : StageSimplexTuple r := fun i => b i.succ
      let tailC : StageSimplexTuple r := fun i => c i.succ
      let αt : tailA ⟶ tailB := fun i => α i.succ
      let βt : tailB ⟶ tailC := fun i => β i.succ
      have ht := ih αt βt
      let MA := tupleReindexData C r tailA tailB αt
      let MB := tupleReindexData C r tailB tailC βt
      let MC := tupleReindexData C r tailA tailC (αt ≫ βt)
      have hm := stageMap_eq_of_eq MC.exact (MA.exact.comp MB.exact) ht (c 0).unop.len
      have hinner :
          reindexStage (C := StageAtTuple C tailA) ((α 0).unop) ⋙
              MA.exact.mapStage (b 0).unop.len ⋙
                reindexStage (C := StageAtTuple C tailB) ((β 0).unop) ⋙
                  MB.exact.mapStage (c 0).unop.len =
          reindexStage (C := StageAtTuple C tailA) (((α ≫ β) 0).unop) ⋙
            MC.exact.mapStage (c 0).unop.len := by
        rw [hm, Functor.IsWaldhausenExact.mapStage_comp]
        change reindexStage (C := StageAtTuple C tailA) (α 0).unop ⋙
            MA.exact.mapStage (b 0).unop.len ⋙
              reindexStage (C := StageAtTuple C tailB) (β 0).unop ⋙
                MB.exact.mapStage (c 0).unop.len =
          (reindexStage (C := StageAtTuple C tailA) (α 0).unop ⋙
              reindexStage (C := StageAtTuple C tailA) (β 0).unop) ⋙
            (MA.exact.mapStage (c 0).unop.len ⋙ MB.exact.mapStage (c 0).unop.len)
        exact congrArg
          (fun K => reindexStage (C := StageAtTuple C tailA) (α 0).unop ⋙ K ⋙
            MB.exact.mapStage (c 0).unop.len)
          (MA.exact.mapStage_reindex (β 0).unop).symm
      unfold reindexIteratedStage tupleReindexData
      dsimp only
      have hc := transported_comp
        (iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len))
        (iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len))
        (iteratedStageOfFnSuccEquivalence C (fun i => (c i).unop.len))
        (reindexStage (C := StageAtTuple C tailA) (α 0).unop ⋙
          MA.exact.mapStage (b 0).unop.len)
        (reindexStage (C := StageAtTuple C tailB) (β 0).unop ⋙
          MB.exact.mapStage (c 0).unop.len)
        (iteratedStageOfFnSuccEquivalence_inverse_functor C (fun i => (b i).unop.len))
      exact (congrArg
        (fun K => (iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len)).functor ⋙ K ⋙
          (iteratedStageOfFnSuccEquivalence C (fun i =>
              (c i).unop.len)).inverse) hinner.symm).trans hc.symm

variable {C}
variable {D : Type (max uD vD)} [Category.{vD} D] [HasZeroObject D]
    [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- The original exact base functor commutes with every original finite
tuple of simplex operators. -/
theorem mapIteratedStage_reindex (r : ℕ) {a b : StageSimplexTuple r} (α : a ⟶ b) :
    reindexIteratedStage C α ⋙ mapIteratedStage hF (stageTupleDegrees b) =
      mapIteratedStage hF (stageTupleDegrees a) ⋙ reindexIteratedStage D α := by
  induction r with
  | zero =>
      have hab : a = b := Subsingleton.elim _ _
      subst b
      unfold reindexIteratedStage tupleReindexData
      rfl
  | succ r ih =>
      let tailA : StageSimplexTuple r := fun i => a i.succ
      let tailB : StageSimplexTuple r := fun i => b i.succ
      let αt : tailA ⟶ tailB := fun i => α i.succ
      have ht := ih αt
      let MC := tupleReindexData C r tailA tailB αt
      let MD := tupleReindexData D r tailA tailB αt
      let hA := mapIteratedStage_isWaldhausenExact hF (stageTupleDegrees tailA)
      let hB := mapIteratedStage_isWaldhausenExact hF (stageTupleDegrees tailB)
      have hEq := stageMap_eq_of_eq (MC.exact.comp hB) (hA.comp MD.exact) ht (b 0).unop.len
      have hs :
          (reindexStage (C := StageAtTuple C tailA) (α 0).unop ⋙
              MC.exact.mapStage (b 0).unop.len) ⋙ hB.mapStage (b 0).unop.len =
          hA.mapStage (a 0).unop.len ⋙
            (reindexStage (C := StageAtTuple D tailA) (α 0).unop ⋙
              MD.exact.mapStage (b 0).unop.len) := by
        rw [Functor.assoc]
        rw [← Functor.IsWaldhausenExact.mapStage_comp MC.exact hB, hEq,
          Functor.IsWaldhausenExact.mapStage_comp hA MD.exact]
        exact congrArg (fun K => K ⋙ MD.exact.mapStage (b 0).unop.len)
          (hA.mapStage_reindex (α 0).unop)
      unfold reindexIteratedStage tupleReindexData
      dsimp only
      exact transported_naturality
        (iteratedStageOfFnSuccEquivalence C (fun i => (a i).unop.len))
        (iteratedStageOfFnSuccEquivalence C (fun i => (b i).unop.len))
        (iteratedStageOfFnSuccEquivalence D (fun i => (a i).unop.len))
        (iteratedStageOfFnSuccEquivalence D (fun i => (b i).unop.len))
        (reindexStage (C := StageAtTuple C tailA) (α 0).unop ⋙
          MC.exact.mapStage (b 0).unop.len)
        (reindexStage (C := StageAtTuple D tailA) (α 0).unop ⋙
          MD.exact.mapStage (b 0).unop.len)
        (mapIteratedStage hF (stageTupleDegrees a))
        (mapIteratedStage hF (stageTupleDegrees b))
        (hA.mapStage (a 0).unop.len) (hB.mapStage (b 0).unop.len)
        (mapIteratedStage_tuple_successor hF (fun i => (a i).unop.len))
        (mapIteratedStage_tuple_successor hF (fun i => (b i).unop.len)) hs
        (iteratedStageOfFnSuccEquivalence_inverse_functor C (fun i => (b i).unop.len))
        (iteratedStageOfFnSuccEquivalence_functor_inverse D (fun i => (b i).unop.len))

end CategoryTheory.Waldhausen.SConstruction
