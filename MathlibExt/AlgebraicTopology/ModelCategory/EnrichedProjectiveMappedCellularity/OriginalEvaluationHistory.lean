/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import MathlibExt.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizationSmallness
import MathlibExt.CategoryTheory.SmallObject.FullyFaithful
import MathlibExt.CategoryTheory.SmallObject.IsoEligibility
import MathlibExt.CategoryTheory.MorphismProperty.Retract
import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.TransfiniteAbsorption
import Mathlib.CategoryTheory.Limits.Connected
import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.OriginalShapes
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.CellTrace

/-!
# Actual tagged histories for original evaluated cell complexes

The original coefficient generation at κ constructs a tagged relative I-cell
history for every supplied P-cell presentation whose actual evaluated
generators are cofibrations. The input cofans, pushouts, outer ordinal,
source object, endpoint cocone and all actual individual generator projections
are retained through the coherent original-stage splitting.

Every normalized cell is traced by the canonical normalization equality and
the exact completed-shape transport to its original outer occurrence and
original individual I-factor cell. Empty maximal joins have no cells.
The history, its complete endpoint retract, tags and cell-image maps are outputs.
No target cellularity or compactness record is supplied.
-/

set_option autoImplicit false

noncomputable section OriginalHistoryPart1

universe w u v t o

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.CellularEvaluationHistory

variable {C : Type u} [Category.{v} C]
  {α : Type t} {A B : α → C} {g : ∀ i, A i ⟶ B i}
  {X Y : C} {f : X ⟶ Y}

/-- Push the original attachment through an actual pushout, retaining all labels and cofans. -/
def pushAttachment (c : AttachCells.{w} g f) {X' Y' : C}
    (a : X ⟶ X') {q : X' ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a f q b) :
    AttachCells.{w} g q where
  ι := c.ι
  π := c.π
  cofan₁ := c.cofan₁
  cofan₂ := c.cofan₂
  isColimit₁ := c.isColimit₁
  isColimit₂ := c.isColimit₂
  m := c.m
  hm := c.hm
  g₁ := c.g₁ ≫ a
  g₂ := c.g₂ ≫ b
  isPushout := c.isPushout.paste_horiz sq

theorem pushAttachment_labels (c : AttachCells.{w} g f) {X' Y' : C}
    (a : X ⟶ X') {q : X' ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a f q b) :
    (pushAttachment c a sq).ι = c.ι := rfl

theorem pushAttachment_label (c : AttachCells.{w} g f) {X' Y' : C}
    (a : X ⟶ X') {q : X' ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a f q b)
    (k : c.ι) : (pushAttachment c a sq).π k = c.π k := rfl

theorem pushAttachment_sourceCofan (c : AttachCells.{w} g f) {X' Y' : C}
    (a : X ⟶ X') {q : X' ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a f q b) :
    (pushAttachment c a sq).cofan₁ = c.cofan₁ := rfl

theorem pushAttachment_targetCofan (c : AttachCells.{w} g f) {X' Y' : C}
    (a : X ⟶ X') {q : X' ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a f q b) :
    (pushAttachment c a sq).cofan₂ = c.cofan₂ := rfl

theorem pushAttachment_cell (c : AttachCells.{w} g f) {X' Y' : C}
    (a : X ⟶ X') {q : X' ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a f q b)
    (k : c.ι) : (pushAttachment c a sq).cell k = c.cell k ≫ b := by
  change c.cofan₂.inj k ≫ (c.g₂ ≫ b) = (c.cofan₂.inj k ≫ c.g₂) ≫ b
  exact (Category.assoc _ _ _).symm

section Complex

variable {O : Type o} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {αO : O → Type t} {AO BO : ∀ j, αO j → C}
  {gO : ∀ j i, AO j i ⟶ BO j i}
  (c : RelativeCellComplex.{w} gO f) {X' Y' : C}
  (a : X ⟶ X') [HasPushoutsAlong a]
  {q : X' ⟶ Y'} {b : Y ⟶ Y'} (sq : IsPushout a f q b)

/-- The unchanged original-order pushout presentation supplied by the canonical constructor. -/
def pushedPresentation : CategoryTheory.TransfiniteCompositionOfShape O q := by
  let d : (⊤ : MorphismProperty C).TransfiniteCompositionOfShape O f :=
    { toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape
      map_mem _ _ := trivial }
  exact (d.cobaseChange a sq).toTransfiniteCompositionOfShape

/-- Every old stage maps into its corresponding original-order pushed stage. -/
def pushedStage (j : O) : c.F.obj j ⟶ (pushedPresentation c a sq).F.obj j := by
  change c.F.obj j ⟶ pushout (c.isoBot.inv ≫ c.F.map (homOfLE bot_le : ⊥ ⟶ j)) a
  exact pushout.inl _ _

/-- Every original successor rectangle is a genuine pushout. -/
theorem pushedRectangle {j j' : O} (s : j ⟶ j') :
    IsPushout (pushedStage c a sq j) (c.F.map s)
      ((pushedPresentation c a sq).F.map s) (pushedStage c a sq j') := by
  let u (k : O) : X ⟶ c.F.obj k := c.isoBot.inv ≫ c.F.map (homOfLE bot_le : ⊥ ⟶ k)
  have hu : u j ≫ c.F.map s = u j' := by
    dsimp only [u]
    rw [Category.assoc, ← c.F.map_comp]
    rfl
  let d : pushout (u j) a ⟶ pushout (u j') a :=
    (pushedPresentation c a sq).F.map s
  have hd₀ : pushout.inl (u j) a ≫ d = c.F.map s ≫ pushout.inl (u j') a := by
    change pushout.inl (u j) a ≫
      pushout.desc (c.F.map s ≫ pushout.inl (u j') a) (pushout.inr (u j') a) _ = _
    exact pushout.inl_desc _ _ _
  have hd₁ : pushout.inr (u j) a ≫ d = pushout.inr (u j') a := by
    change pushout.inr (u j) a ≫
      pushout.desc (c.F.map s ≫ pushout.inl (u j') a) (pushout.inr (u j') a) _ = _
    exact pushout.inr_desc _ _ _
  have whole : IsPushout (u j ≫ c.F.map s) a (pushout.inl (u j') a)
      (pushout.inr (u j) a ≫ d) := by
    rw [hu, hd₁]
    exact IsPushout.of_hasPushout (u j') a
  exact (whole.of_left hd₀.symm (IsPushout.of_hasPushout (u j) a)).flip

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The old endpoint inclusion is retained through the same original endpoint pushout map. -/
theorem pushedStage_endpoint (j : O) :
    pushedStage c a sq j ≫ (pushedPresentation c a sq).incl.app j = c.incl.app j ≫ b := by
  change pushout.inl (c.isoBot.inv ≫ c.F.map (homOfLE bot_le : ⊥ ⟶ j)) a ≫
    ((pushout.desc (c.incl.app j ≫ pushout.inl f a) (pushout.inr f a) _ ≫ 𝟙 _) ≫
      sq.flip.isoPushout.inv) = c.incl.app j ≫ b
  rw [Category.comp_id, ← Category.assoc, pushout.inl_desc, Category.assoc,
    sq.flip.inl_isoPushout_inv]

/-- Push the full original presented complex without selecting replacement labels. -/
def pushedComplex : RelativeCellComplex.{w} gO q where
  toTransfiniteCompositionOfShape := pushedPresentation c a sq
  attachCells j hj :=
    pushAttachment (c.attachCells j hj) (pushedStage c a sq j)
      (pushedRectangle c a sq (homOfLE (Order.le_succ j)))

/-- Each actual original attachment's cell-label carrier is unchanged. -/
theorem pushedComplex_labels (j : O) (hj : ¬ IsMax j) :
    ((pushedComplex c a sq).attachCells j hj).ι = (c.attachCells j hj).ι := rfl

/-- The original complete cell occurrence, including its original stage, is retained. -/
def pushedCell (e : c.Cells) : (pushedComplex c a sq).Cells where
  j := e.j
  hj := e.hj
  k := e.k

/-- The original generating arrow label remains the same. -/
theorem pushedCell_label (e : c.Cells) : (pushedCell c a sq e).i = e.i := rfl

/-- Every typed cell endpoint retains the actual original endpoint pushout map. -/
theorem pushedCell_endpoint (e : c.Cells) :
    (pushedCell c a sq e).ι = e.ι ≫ b := by
  change (pushAttachment (c.attachCells e.j e.hj) (pushedStage c a sq e.j)
    (pushedRectangle c a sq (homOfLE (Order.le_succ e.j)))).cell e.k ≫
      (pushedPresentation c a sq).incl.app (Order.succ e.j) =
    ((c.attachCells e.j e.hj).cell e.k ≫ c.incl.app (Order.succ e.j)) ≫ b
  have hcell := pushAttachment_cell (c.attachCells e.j e.hj)
    (pushedStage c a sq e.j) (pushedRectangle c a sq (homOfLE (Order.le_succ e.j))) e.k
  have hstage := pushedStage_endpoint c a sq (Order.succ e.j)
  exact (congrArg (fun z => z ≫ (pushedPresentation c a sq).incl.app (Order.succ e.j))
    hcell).trans ((Category.assoc _ _ _).trans
      ((congrArg (fun z => (c.attachCells e.j e.hj).cell e.k ≫ z) hstage).trans
        (Category.assoc _ _ _).symm))

end Complex

end HomotopicalAlgebra.CellularEvaluationHistory

end OriginalHistoryPart1

noncomputable section OriginalHistoryPart2

universe w u v t o

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.CellularEvaluationHistory

variable {C : Type u} [Category.{v} C]
  {I : Type w} [HasColimitsOfShape (Discrete I) C]
  {O : Type o} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {α : Type t} {A B : α → C} {g : ∀ i, A i ⟶ B i}
  {X Y : I → C} {f : ∀ i, X i ⟶ Y i}
  (c : ∀ i, RelativeCellComplex.{w} (fun _ : O => g) (f i))

/-- The original family of presented stage diagrams, before taking any coproduct. -/
def familyObjects : O ⥤ Discrete I ⥤ C where
  obj j := Discrete.functor (fun i : I => (c i).F.obj j)
  map s := Discrete.natTrans (fun i : Discrete I => (c i.as).F.map s)
  map_id j := by
    ext i
    exact (c i.as).F.map_id j
  map_comp s t := by
    ext i
    exact (c i.as).F.map_comp s t

/-- The pointwise coproduct retains the same supplied original ordinal. -/
def familyDiagram : O ⥤ C := familyObjects c ⋙ colim

/-- The original component endpoint cocones form the original family endpoint cocone. -/
def familyEndpoint : Cocone (familyObjects c) where
  pt := Discrete.functor Y
  ι :=
    { app j := Discrete.natTrans (fun i : Discrete I => (c i.as).incl.app j)
      naturality j j' s := by
        ext i
        change (c i.as).F.map s ≫ (c i.as).incl.app j' = (c i.as).incl.app j ≫ 𝟙 _
        exact (c i.as).incl.naturality s }

/-- The actual family endpoint is colimiting because each original component endpoint is. -/
def familyEndpointIsColimit : IsColimit (familyEndpoint c) := by
  apply evaluationJointlyReflectsColimits
  intro i
  change IsColimit (Cocone.mk (Y i.as) (c i.as).incl)
  exact (c i.as).isColimit

omit [HasColimitsOfShape (Discrete I) C] in
/-- Every original limit stage of the whole component family retains its original colimit. -/
theorem familyObjects_continuous : (familyObjects c).IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨by
    apply evaluationJointlyReflectsColimits
    intro i
    change IsColimit ((Set.principalSegIio j).cocone (c i.as).F)
    let _ : (c i.as).F.IsWellOrderContinuous := (c i.as).isWellOrderContinuous
    exact (c i.as).F.isColimitOfIsWellOrderContinuous j hj⟩

/-- The entire pointwise coproduct presentation is on the unchanged original ordinal. -/
def familyPresentation : CategoryTheory.TransfiniteCompositionOfShape O (Limits.Sigma.map f) where
  F := familyDiagram c
  isoBot := (colim : (Discrete I ⥤ C) ⥤ C).mapIso
    (Discrete.natIso (fun i : Discrete I => (c i.as).isoBot))
  isWellOrderContinuous := by
    let _ : (familyObjects c).IsWellOrderContinuous := familyObjects_continuous c
    let _ : PreservesWellOrderContinuousOfShape O
        (colim : (Discrete I ⥤ C) ⥤ C) :=
      { preservesColimitsOfShape := fun _ _ => inferInstance }
    change (familyObjects c ⋙ colim).IsWellOrderContinuous
    infer_instance
  incl :=
    { app j := Limits.Sigma.map
        (fun i => (show (c i).F.obj j ⟶ Y i from (c i).incl.app j))
      naturality j j' s := by
        apply Sigma.hom_ext
        intro i
        change Sigma.ι (fun i => (c i).F.obj j) i ≫
          (Limits.Sigma.map (fun i => (c i).F.map s) ≫
            Limits.Sigma.map (fun i => (show (c i).F.obj j' ⟶ Y i from (c i).incl.app j'))) =
          Sigma.ι (fun i => (c i).F.obj j) i ≫
            (Limits.Sigma.map (fun i => (show (c i).F.obj j ⟶ Y i from (c i).incl.app j)) ≫ 𝟙 _)
        rw [Sigma.ι_map_assoc, Sigma.ι_map, Category.comp_id, Sigma.ι_map]
        have hi : (c i).F.map s ≫ (c i).incl.app j' = (c i).incl.app j :=
          ((c i).incl.naturality s).trans (Category.comp_id _)
        exact (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ Sigma.ι Y i) hi) }
  isColimit := by
    have h := isColimitOfPreserves (colim : (Discrete I ⥤ C) ⥤ C)
      (familyEndpointIsColimit c)
    exact h.ofIsoColimit (Cocone.ext (Iso.refl _) (by
      intro j
      change colim.map (Discrete.natTrans
        (fun i : Discrete I => (show (c i.as).F.obj j ⟶ Y i.as from (c i.as).incl.app j))) ≫
        𝟙 _ = Limits.Sigma.map (fun i => (show (c i).F.obj j ⟶ Y i from (c i).incl.app j))
      rw [Category.comp_id]
      rfl))
  fac := by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι X i ≫
      (Limits.Sigma.map (fun i => (show X i ⟶ (c i).F.obj ⊥ from (c i).isoBot.inv)) ≫
        Limits.Sigma.map (fun i => (show (c i).F.obj ⊥ ⟶ Y i from (c i).incl.app ⊥))) =
      Sigma.ι X i ≫ Limits.Sigma.map f
    rw [Sigma.ι_map_assoc, Sigma.ι_map, Sigma.ι_map, ← Category.assoc, (c i).fac]

section Attachments

variable (j : O) (hj : ¬ IsMax j)

/-- Every new coproduct cell is tagged by its original component and original occurrence. -/
abbrev familyIndices := Σ i : I, ((c i).attachCells j hj).ι

/-- The original coproduct source cofan, indexed by component and original attaching occurrence. -/
def familySourceCofan : Cofan (fun k : familyIndices c j hj => A
    (((c k.1).attachCells j hj).π k.2)) :=
  Cofan.mk (∐ fun i : I => ((c i).attachCells j hj).cofan₁.pt)
    (fun k => ((c k.1).attachCells j hj).cofan₁.inj k.2 ≫
      Sigma.ι (fun i : I => ((c i).attachCells j hj).cofan₁.pt) k.1)

/-- The original coproduct target cofan, indexed by component and original attaching occurrence. -/
def familyTargetCofan : Cofan (fun k : familyIndices c j hj => B
    (((c k.1).attachCells j hj).π k.2)) :=
  Cofan.mk (∐ fun i : I => ((c i).attachCells j hj).cofan₂.pt)
    (fun k => ((c k.1).attachCells j hj).cofan₂.inj k.2 ≫
      Sigma.ι (fun i : I => ((c i).attachCells j hj).cofan₂.pt) k.1)

/-- Flattening the original component source cofans preserves the actual original injections. -/
def familySourceIsColimit : IsColimit (familySourceCofan c j hj) :=
  Cofan.isColimitTrans _ (coproductIsCoproduct _)
    (fun i => ((c i).attachCells j hj).cofan₁.inj)
    (fun i => ((c i).attachCells j hj).isColimit₁)

/-- Flattening the original component target cofans preserves the actual original injections. -/
def familyTargetIsColimit : IsColimit (familyTargetCofan c j hj) :=
  Cofan.isColimitTrans _ (coproductIsCoproduct _)
    (fun i => ((c i).attachCells j hj).cofan₂.inj)
    (fun i => ((c i).attachCells j hj).isColimit₂)

/-- The pointwise coproduct successor is the original coproduct of the supplied pushout squares. -/
theorem familySuccessorIsPushout :
    IsPushout (Limits.Sigma.map (fun i => ((c i).attachCells j hj).g₁))
      (Limits.Sigma.map (fun i => ((c i).attachCells j hj).m))
      ((familyDiagram c).map (homOfLE (Order.le_succ j)))
      (Limits.Sigma.map (fun i => ((c i).attachCells j hj).g₂)) := by
  let g₁ : Discrete.functor (fun i : I => ((c i).attachCells j hj).cofan₁.pt) ⟶
      Discrete.functor (fun i : I => (c i).F.obj j) :=
    Discrete.natTrans (fun i : Discrete I => ((c i.as).attachCells j hj).g₁)
  let m : Discrete.functor (fun i : I => ((c i).attachCells j hj).cofan₁.pt) ⟶
      Discrete.functor (fun i : I => ((c i).attachCells j hj).cofan₂.pt) :=
    Discrete.natTrans (fun i : Discrete I => ((c i.as).attachCells j hj).m)
  let g₂ : Discrete.functor (fun i : I => ((c i).attachCells j hj).cofan₂.pt) ⟶
      Discrete.functor (fun i : I => (c i).F.obj (Order.succ j)) :=
    Discrete.natTrans (fun i : Discrete I => ((c i.as).attachCells j hj).g₂)
  let fs := (familyObjects c).map (homOfLE (Order.le_succ j))
  have h : IsPushout g₁ m fs g₂ := IsPushout.of_forall_isPushout_app
    (fun i => ((c i.as).attachCells j hj).isPushout)
  exact h.map (colim : (Discrete I ⥤ C) ⥤ C)

/-- Each pointwise coproduct attachment retains the original base generator of its tagged cell. -/
def familyAttachment : AttachCells.{w} g ((familyDiagram c).map (homOfLE (Order.le_succ j))) where
  ι := familyIndices c j hj
  π k := ((c k.1).attachCells j hj).π k.2
  cofan₁ := familySourceCofan c j hj
  cofan₂ := familyTargetCofan c j hj
  isColimit₁ := familySourceIsColimit c j hj
  isColimit₂ := familyTargetIsColimit c j hj
  m := Limits.Sigma.map (fun i => ((c i).attachCells j hj).m)
  hm := by
    rintro ⟨i, k⟩
    change (((c i).attachCells j hj).cofan₁.inj k ≫
      Sigma.ι (fun i => ((c i).attachCells j hj).cofan₁.pt) i) ≫
      Limits.Sigma.map (fun i => ((c i).attachCells j hj).m) =
      g (((c i).attachCells j hj).π k) ≫
        (((c i).attachCells j hj).cofan₂.inj k ≫
          Sigma.ι (fun i => ((c i).attachCells j hj).cofan₂.pt) i)
    rw [Category.assoc, Sigma.ι_map, ← Category.assoc, ((c i).attachCells j hj).hm]
    exact Category.assoc _ _ _
  g₁ := Limits.Sigma.map (fun i => ((c i).attachCells j hj).g₁)
  g₂ := Limits.Sigma.map (fun i => ((c i).attachCells j hj).g₂)
  isPushout := familySuccessorIsPushout c j hj

end Attachments

/-- A pointwise coproduct of original relative complexes is an actual same-ordinal complex. -/
def familyComplex : RelativeCellComplex.{w} (fun _ : O => g) (Limits.Sigma.map f) where
  toTransfiniteCompositionOfShape := familyPresentation c
  attachCells j hj := familyAttachment c j hj

/-- An original cell occurrence gives exactly its original component tag and original ordinal. -/
def familyCell (i : I) (e : (c i).Cells) : (familyComplex c).Cells where
  j := e.j
  hj := e.hj
  k := ⟨i, e.k⟩

theorem familyCell_label (i : I) (e : (c i).Cells) :
    (familyCell c i e).i = e.i := rfl

/-- Every tagged cell endpoint factors through the original component endpoint injection. -/
theorem familyCell_endpoint (i : I) (e : (c i).Cells) :
    (familyCell c i e).ι = e.ι ≫ Sigma.ι Y i := by
  change (((((c i).attachCells e.j e.hj).cofan₂.inj e.k ≫
    Sigma.ι (fun i => ((c i).attachCells e.j e.hj).cofan₂.pt) i) ≫
      Limits.Sigma.map (fun i => ((c i).attachCells e.j e.hj).g₂)) ≫
        Limits.Sigma.map (fun i =>
          (show (c i).F.obj (Order.succ e.j) ⟶ Y i from (c i).incl.app (Order.succ e.j)))) =
    ((((c i).attachCells e.j e.hj).cofan₂.inj e.k ≫
      ((c i).attachCells e.j e.hj).g₂) ≫ (c i).incl.app (Order.succ e.j)) ≫ Sigma.ι Y i
  simp only [Category.assoc, Sigma.ι_map]

end HomotopicalAlgebra.CellularEvaluationHistory

end OriginalHistoryPart2

noncomputable section OriginalHistoryPart3

universe w u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.CellularEvaluationHistory

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

local instance originalEligibility : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject

/-- The original chosen-cardinal I factor of one actual evaluated generating arrow. -/
def generatorRepresentative {X Y : C} (f : X ⟶ Y) : X ⟶ SmallObject.obj d.I κ f :=
  SmallObject.ιObj d.I κ f

/-- The complete original I-cell history of the same individual arrow's factor. -/
def generatorHistory {X Y : C} (f : X ⟶ Y) :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => d.I.homFamily)
      (generatorRepresentative d f) :=
  SmallObject.relativeCellComplexιObj d.I κ f

/-- The literal original factor projection lands in the same individual generating codomain. -/
def generatorProjection {X Y : C} (f : X ⟶ Y) : SmallObject.obj d.I κ f ⟶ Y :=
  SmallObject.πObj d.I κ f

/-- Every original cofibration splits its actual individual I factor at the same κ. -/
def generatorRetraction {X Y : C} (f : X ⟶ Y) (hf : cofibrations C f) :
    RetractArrow f (generatorRepresentative d f) :=
  CellularCofibrationTransport.originalFactoryRetract d f hf

theorem generatorRetraction_inclusion_source {X Y : C} (f : X ⟶ Y)
    (hf : cofibrations C f) : (generatorRetraction d f hf).i.left = 𝟙 X := rfl

theorem generatorRetraction_retraction_source {X Y : C} (f : X ⟶ Y)
    (hf : cofibrations C f) : (generatorRetraction d f hf).r.left = 𝟙 X := rfl

theorem generatorRetraction_projection {X Y : C} (f : X ⟶ Y)
    (hf : cofibrations C f) :
    (generatorRetraction d f hf).r.right = generatorProjection d f := rfl

section Family

variable [HasColimitsOfSize.{w, w} C]
  {I : Type w} {X Y : I → C} (f : ∀ i, X i ⟶ Y i)
  (hf : ∀ i, cofibrations C (f i))

/-- Each original coordinate has the codomain of its own original I factory. -/
abbrev generatorTargets (i : I) : C := SmallObject.obj d.I κ (f i)

/-- A coproduct representative factors each actual generating occurrence individually first. -/
def generatorFamilyRepresentative : (∐ X) ⟶ (∐ generatorTargets d f) :=
  Limits.Sigma.map (fun i => generatorRepresentative d (f i))

/-- The actual family I-cell history retains κ and all individual occurrence tags. -/
def generatorFamilyHistory :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => d.I.homFamily)
      (generatorFamilyRepresentative d f) :=
  familyComplex (fun i => generatorHistory d (f i))

/-- The original family projection is the coproduct of the individual original projections. -/
def generatorFamilyProjection : (∐ generatorTargets d f) ⟶ (∐ Y) :=
  Limits.Sigma.map (fun i =>
          (show generatorTargets d f i ⟶ Y i from generatorProjection d (f i)))

/-- The whole original family arrow is a source-fixed retract of this tagged I-cell representative. -/
def generatorFamilyRetraction :
    RetractArrow (Limits.Sigma.map f) (generatorFamilyRepresentative d f) where
  i := Arrow.homMk (𝟙 (∐ X))
    (Limits.Sigma.map (fun i => (show Y i ⟶ generatorTargets d f i from
      (generatorRetraction d (f i) (hf i)).i.right))) (by
      change 𝟙 (∐ X) ≫ Limits.Sigma.map (fun i => generatorRepresentative d (f i)) =
        Limits.Sigma.map f ≫ Limits.Sigma.map (fun i => (show Y i ⟶ generatorTargets d f i from
          (generatorRetraction d (f i) (hf i)).i.right))
      rw [Category.id_comp, Sigma.map_comp_map]
      apply congrArg (fun z => Limits.Sigma.map z)
      funext i
      have h : 𝟙 (X i) ≫ generatorRepresentative d (f i) =
          f i ≫ (generatorRetraction d (f i) (hf i)).i.right :=
        (generatorRetraction d (f i) (hf i)).i_w
      exact (Category.id_comp _).symm.trans h)
  r := Arrow.homMk (𝟙 (∐ X)) (generatorFamilyProjection d f) (by
      change 𝟙 (∐ X) ≫ Limits.Sigma.map f =
        Limits.Sigma.map (fun i => generatorRepresentative d (f i)) ≫
          Limits.Sigma.map (fun i =>
          (show generatorTargets d f i ⟶ Y i from generatorProjection d (f i)))
      rw [Category.id_comp, Sigma.map_comp_map]
      apply congrArg (fun z => Limits.Sigma.map z)
      funext i
      exact (SmallObject.ιObj_πObj d.I κ (f i)).symm)
  retract := by
    ext
    · exact Category.id_comp _
    · change Limits.Sigma.map (fun i => (generatorRetraction d (f i) (hf i)).i.right) ≫
        Limits.Sigma.map (fun i =>
          (show generatorTargets d f i ⟶ Y i from generatorProjection d (f i))) = 𝟙 (∐ Y)
      rw [Sigma.map_comp_map]
      have h : (fun i => (generatorRetraction d (f i) (hf i)).i.right ≫
          generatorProjection d (f i)) = (fun i => 𝟙 (Y i)) := by
        funext i
        exact (generatorRetraction d (f i) (hf i)).retract_right
      rw [h, Sigma.map_id]

theorem generatorFamilyRetraction_inclusion_source :
    (generatorFamilyRetraction d f hf).i.left = 𝟙 (∐ X) := rfl

theorem generatorFamilyRetraction_retraction_source :
    (generatorFamilyRetraction d f hf).r.left = 𝟙 (∐ X) := rfl

theorem generatorFamilyRetraction_projection :
    (generatorFamilyRetraction d f hf).r.right = generatorFamilyProjection d f := rfl

/-- Each original base-cell occurrence retains the coordinate of its original generating arrow. -/
def generatorFamilyCellIndex (e : (generatorFamilyHistory d f).Cells) : I := e.k.1

/-- The corresponding original individual factory cell remains on the same κ ordinal. -/
def generatorFamilyCellOriginal (e : (generatorFamilyHistory d f).Cells) :
    (generatorHistory d (f (generatorFamilyCellIndex d f e))).Cells where
  j := e.j
  hj := e.hj
  k := e.k.2

theorem generatorFamilyCell_label (e : (generatorFamilyHistory d f).Cells) :
    (generatorFamilyCellOriginal d f e).i = e.i := rfl

/-- Every actual family base-cell inclusion factors through its individual original factory endpoint. -/
theorem generatorFamilyCell_endpoint (e : (generatorFamilyHistory d f).Cells) :
    e.ι = (generatorFamilyCellOriginal d f e).ι ≫
      Sigma.ι (generatorTargets d f) (generatorFamilyCellIndex d f e) := by
  rcases e with ⟨j, hj, i, k⟩
  exact familyCell_endpoint (fun i => generatorHistory d (f i)) i ⟨j, hj, k⟩

/-- The projection of each actual base cell lands through the codomain of its original
individual generating occurrence, rather than only through the whole successor endpoint. -/
theorem generatorFamilyCell_image (e : (generatorFamilyHistory d f).Cells) :
    e.ι ≫ generatorFamilyProjection d f =
      ((generatorFamilyCellOriginal d f e).ι ≫
        generatorProjection d (f (generatorFamilyCellIndex d f e))) ≫
          Sigma.ι Y (generatorFamilyCellIndex d f e) := by
  have he := generatorFamilyCell_endpoint d f e
  have hm : Sigma.ι (generatorTargets d f) (generatorFamilyCellIndex d f e) ≫
      generatorFamilyProjection d f =
      generatorProjection d (f (generatorFamilyCellIndex d f e)) ≫
        Sigma.ι Y (generatorFamilyCellIndex d f e) := by
    exact Sigma.ι_map (fun i =>
      (show generatorTargets d f i ⟶ Y i from generatorProjection d (f i))) _
  exact (congrArg (fun z => z ≫ generatorFamilyProjection d f) he).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => (generatorFamilyCellOriginal d f e).ι ≫ z) hm).trans
        (Category.assoc _ _ _).symm))

end Family

end HomotopicalAlgebra.CellularEvaluationHistory

end OriginalHistoryPart3

noncomputable section OriginalHistoryPart4

universe w uC vC uD vD t o

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.CellularEvaluationHistory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

section MappedAttachment

variable {α : Type t} {A B : α → C} {g : ∀ i, A i ⟶ B i}
  {X Y : C} {f : X ⟶ Y} (c : AttachCells.{w} g f) (F : C ⥤ D)
  [PreservesColimitsOfSize.{w, w} F]

/-- The existing mapped attachment retains its actual original occurrence carrier. -/
theorem mappedAttachment_labels : (c.map F).ι = c.ι := rfl

/-- Each mapped original cell map is the functor's image of the same original cell map. -/
theorem mappedAttachment_cell (k : c.ι) : (c.map F).cell k = F.map (c.cell k) := by
  change F.map (c.cofan₂.inj k) ≫ F.map c.g₂ = F.map (c.cofan₂.inj k ≫ c.g₂)
  exact (F.map_comp _ _).symm

end MappedAttachment

section MappedComplex

variable {O : Type o} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {α : O → Type t} {A B : ∀ j, α j → C} {g : ∀ j i, A j i ⟶ B j i}
  {X Y : C} {f : X ⟶ Y} (c : RelativeCellComplex.{w} g f) (F : C ⥤ D)
  [PreservesColimitsOfSize.{w, w} F] [PreservesColimitsOfShape O F]
  [PreservesWellOrderContinuousOfShape O F]

/-- A mapped complex keeps the original ordinal and the same cell occurrence in each cofan. -/
def mappedComplexCell (e : c.Cells) : (c.map F).Cells where
  j := e.j
  hj := e.hj
  k := e.k

theorem mappedComplexCell_label (e : c.Cells) : (mappedComplexCell c F e).i = e.i := rfl

/-- The actual original cell endpoint inclusion is mapped by the same functor. -/
theorem mappedComplexCell_endpoint (e : c.Cells) :
    (mappedComplexCell c F e).ι = F.map e.ι := by
  change (F.map ((c.attachCells e.j e.hj).cofan₂.inj e.k) ≫
    F.map (c.attachCells e.j e.hj).g₂) ≫
      (F.map (c.incl.app (Order.succ e.j)) ≫ 𝟙 _) =
    F.map (((c.attachCells e.j e.hj).cofan₂.inj e.k ≫
      (c.attachCells e.j e.hj).g₂) ≫ c.incl.app (Order.succ e.j))
  rw [Category.comp_id, F.map_comp, F.map_comp]

end MappedComplex

section ReindexedComplex

variable (P Q : MorphismProperty C) (q : P.toSet → Q.toSet)
  (e : ∀ p : P.toSet, Arrow.mk p.1.hom ≅ Arrow.mk (q p).1.hom)
  {O : Type o} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)

/-- The existing Arrow-isomorphism reindexing keeps the same original cell occurrence. -/
def reindexedComplexCell (a : c.Cells) : (c.reindexByArrowIso P Q q e).Cells where
  j := a.j
  hj := a.hj
  k := a.k

/-- Reindexing changes only the chosen actual generator label. -/
theorem reindexedComplexCell_label (a : c.Cells) :
    (reindexedComplexCell P Q q e c a).i = q a.i := rfl

/-- The exact right component of the original Arrow isomorphism is the sole cell comparison. -/
theorem reindexedComplexCell_endpoint (a : c.Cells) :
    (reindexedComplexCell P Q q e c a).ι =
      (e a.i).inv.right ≫ a.ι := by
  change ((((e a.i).inv.right ≫ (c.attachCells a.j a.hj).cofan₂.inj a.k) ≫
      (c.attachCells a.j a.hj).g₂) ≫ c.incl.app (Order.succ a.j)) =
    (e a.i).inv.right ≫
      (((c.attachCells a.j a.hj).cofan₂.inj a.k ≫
        (c.attachCells a.j a.hj).g₂) ≫ c.incl.app (Order.succ a.j))
  exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans
    (congrArg (fun z => (e a.i).inv.right ≫ z) (Category.assoc _ _ _).symm)

end ReindexedComplex

end HomotopicalAlgebra.CellularEvaluationHistory

end OriginalHistoryPart4

noncomputable section OriginalHistoryPart5

universe w uV vV uD vD t

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.CellularEvaluationHistory

variable {V : Type uV} [Category.{vV} V] [ModelCategory V]
  [HasColimitsOfSize.{w, w} V]
  {D : Type uD} [Category.{vD} D]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData V κ)
  {α : Type t} {A B : α → D} {g : ∀ i, A i ⟶ B i}
  {X Y : D} {f : X ⟶ Y} (c : AttachCells.{w} g f)
  (R : D ⥤ V) [PreservesColimitsOfSize.{w, w} R]

/-- The evaluated source of each original attaching occurrence. -/
abbrev evaluatedSources (i : c.ι) : V := R.obj (A (c.π i))
/-- The evaluated target of each original attaching occurrence. -/
abbrev evaluatedTargets (i : c.ι) : V := R.obj (B (c.π i))
/-- The original attaching generator after applying the given evaluation functor. -/
abbrev evaluatedGenerators (i : c.ι) : evaluatedSources c R i ⟶ evaluatedTargets c R i :=
  R.map (g (c.π i))

/-- The original evaluated source cofan compared with its actual categorical coproduct. -/
def evaluatedSourceIso : (∐ evaluatedSources c R) ≅ R.obj c.cofan₁.pt :=
  IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct _) (c.map R).isColimit₁

/-- The original evaluated target cofan compared with its actual categorical coproduct. -/
def evaluatedTargetIso : (∐ evaluatedTargets c R) ≅ R.obj c.cofan₂.pt :=
  IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct _) (c.map R).isColimit₂

omit [ModelCategory V] in
theorem evaluatedSourceIso_inj (i : c.ι) :
    Sigma.ι (evaluatedSources c R) i ≫ (evaluatedSourceIso c R).hom =
      R.map (c.cofan₁.inj i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _) (c.map R).isColimit₁ ⟨i⟩

omit [ModelCategory V] in
theorem evaluatedTargetIso_inj (i : c.ι) :
    Sigma.ι (evaluatedTargets c R) i ≫ (evaluatedTargetIso c R).hom =
      R.map (c.cofan₂.inj i) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _) (c.map R).isColimit₂ ⟨i⟩

/-- The evaluated original boundary, composed with the actual source-cofan comparison. -/
def evaluatedBoundary : (∐ evaluatedSources c R) ⟶ R.obj X :=
  (evaluatedSourceIso c R).hom ≫ R.map c.g₁

/-- The evaluated original cell map, composed with the actual target-cofan comparison. -/
def evaluatedCellMap : (∐ evaluatedTargets c R) ⟶ R.obj Y :=
  (evaluatedTargetIso c R).hom ≫ R.map c.g₂

omit [ModelCategory V] in
theorem evaluatedGenerators_coproduct :
    (evaluatedSourceIso c R).hom ≫ R.map c.m =
      Limits.Sigma.map (evaluatedGenerators c R) ≫ (evaluatedTargetIso c R).hom := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, evaluatedSourceIso_inj, Sigma.ι_map_assoc, evaluatedTargetIso_inj]
  exact (R.map_comp _ _).symm.trans
    ((congrArg R.map (c.hm i)).trans (R.map_comp _ _))

omit [ModelCategory V] in
/-- The exact original evaluated pushout uses the original coordinate generators and cofan maps. -/
theorem evaluatedStagePushout :
    IsPushout (evaluatedBoundary c R) (Limits.Sigma.map (evaluatedGenerators c R))
      (R.map f) (evaluatedCellMap c R) := by
  let _ : PreservesColimitsOfSize.{0, 0} R := preservesSmallestColimits_of_preservesColimits R
  apply (c.isPushout.map R).of_iso' (evaluatedSourceIso c R)
    (Iso.refl _) (evaluatedTargetIso c R) (Iso.refl _)
  · exact (Category.comp_id _).symm
  · exact evaluatedGenerators_coproduct c R
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · exact (Category.comp_id _).symm

variable (hg : ∀ i : c.ι, cofibrations V (evaluatedGenerators c R i))

/-- The source-fixed retract of the original evaluated generator coproduct onto its I-cell factory. -/
abbrev evaluatedFamilyRetraction :=
  generatorFamilyRetraction d (evaluatedGenerators c R) hg

/-- The original evaluated boundary transported through the factory's source retraction. -/
def evaluatedRepresentativeBoundary : (∐ evaluatedSources c R) ⟶ R.obj X :=
  (evaluatedFamilyRetraction d c R hg).r.left ≫ evaluatedBoundary c R

/-- The original evaluated successor represented by the pushout of its I-cell factory. -/
def evaluatedStageRepresentative : R.obj X ⟶
    pushout (generatorFamilyRepresentative d (evaluatedGenerators c R))
      (evaluatedRepresentativeBoundary d c R hg) :=
  pushout.inr _ _

/-- The original-κ I-cell history is pushed through the original evaluated cofan boundary. -/
def evaluatedStageHistory :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => d.I.homFamily)
      (evaluatedStageRepresentative d c R hg) :=
  pushedComplex (generatorFamilyHistory d (evaluatedGenerators c R))
    (evaluatedRepresentativeBoundary d c R hg)
    (IsPushout.of_hasPushout
      (generatorFamilyRepresentative d (evaluatedGenerators c R))
      (evaluatedRepresentativeBoundary d c R hg)).flip

/-- The exact original evaluated endpoint is the original cofan pushout endpoint. -/
def evaluatedStageArrowIso : Arrow.mk (R.map f) ≅
    Arrow.mk (pushout.inr (Limits.Sigma.map (evaluatedGenerators c R))
      (evaluatedBoundary c R)) :=
  Arrow.isoMk (Iso.refl _) (evaluatedStagePushout c R).flip.isoPushout
    (by
      rw [Iso.refl_hom, Category.id_comp]
      exact (evaluatedStagePushout c R).flip.inr_isoPushout_hom.symm)

/-- Both actual original cofan pushouts construct the source-fixed stage retract. -/
def evaluatedStageRetraction :
    RetractArrow (R.map f) (evaluatedStageRepresentative d c R hg) :=
  (Retract.ofIso (evaluatedStageArrowIso c R)).trans
    (MorphismProperty.pushoutRetract (evaluatedFamilyRetraction d c R hg)
      (evaluatedBoundary c R))

theorem evaluatedStageRetraction_inclusion_source :
    (evaluatedStageRetraction d c R hg).i.left = 𝟙 (R.obj X) := by
  exact Category.id_comp _

theorem evaluatedStageRetraction_retraction_source :
    (evaluatedStageRetraction d c R hg).r.left = 𝟙 (R.obj X) := by
  exact Category.id_comp _

/-- The same original factory cell before pushing its history through the evaluated boundary. -/
def evaluatedStageOriginalCell (e : (evaluatedStageHistory d c R hg).Cells) :
    (generatorFamilyHistory d (evaluatedGenerators c R)).Cells where
  j := e.j
  hj := e.hj
  k := e.k

/-- The original target attaching occurrence selected by this evaluated factory cell. -/
def evaluatedStageCellIndex (e : (evaluatedStageHistory d c R hg).Cells) : c.ι :=
  generatorFamilyCellIndex d (evaluatedGenerators c R) (evaluatedStageOriginalCell d c R hg e)

/-- The original base-cell target map into the evaluated target of its selected occurrence. -/
def evaluatedStageCellFactor (e : (evaluatedStageHistory d c R hg).Cells) :
    e.i.1.right ⟶ R.obj (B (c.π (evaluatedStageCellIndex d c R hg e))) :=
  (generatorFamilyCellOriginal d (evaluatedGenerators c R)
    (evaluatedStageOriginalCell d c R hg e)).ι ≫
      generatorProjection d (evaluatedGenerators c R (evaluatedStageCellIndex d c R hg e))

omit [ModelCategory V] in
theorem evaluatedCellMap_inj (i : c.ι) :
    Sigma.ι (evaluatedTargets c R) i ≫ evaluatedCellMap c R = R.map (c.cell i) := by
  rw [evaluatedCellMap, ← Category.assoc, evaluatedTargetIso_inj]
  exact (R.map_comp _ _).symm

end HomotopicalAlgebra.CellularEvaluationHistory

end OriginalHistoryPart5

noncomputable section OriginalHistoryPart6

universe w uV vV uD vD t

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.CellularEvaluationHistory

section PushoutProjection

variable {C : Type uV} [Category.{vV} C] [HasPushouts C]

/-- The original representative's codomain map is retained by the actual pushout retract. -/
theorem pushoutRetraction_inl_projection {A B U V X : C} {f : A ⟶ B} {g : U ⟶ V}
    (h : RetractArrow f g) (a : A ⟶ X) :
    pushout.inl g (h.r.left ≫ a) ≫ (MorphismProperty.pushoutRetract h a).r.right =
      h.r.right ≫ pushout.inl f a := by
  change pushout.inl g (h.r.left ≫ a) ≫
    pushout.desc (h.r.right ≫ pushout.inl f a) (pushout.inr f a) _ = _
  exact pushout.inl_desc _ _ _

end PushoutProjection

variable {V : Type uV} [Category.{vV} V] [ModelCategory V]
  [HasColimitsOfSize.{w, w} V]
  {D : Type uD} [Category.{vD} D]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData V κ)
  {α : Type t} {A B : α → D} {g : ∀ i, A i ⟶ B i}
  {X Y : D} {f : X ⟶ Y} (c : AttachCells.{w} g f)
  (R : D ⥤ V) [PreservesColimitsOfSize.{w, w} R]
  (hg : ∀ i : c.ι, cofibrations V (evaluatedGenerators c R i))

/-- The two original pushout projections are composed with the actual original endpoint comparison. -/
theorem evaluatedStageRetraction_projection :
    (evaluatedStageRetraction d c R hg).r.right =
      (MorphismProperty.pushoutRetract (evaluatedFamilyRetraction d c R hg)
        (evaluatedBoundary c R)).r.right ≫
          (evaluatedStagePushout c R).flip.isoPushout.inv := rfl

/-- Every pushed base cell retains its original individual-family occurrence and endpoint map. -/
theorem evaluatedStageOriginalCell_endpoint (e : (evaluatedStageHistory d c R hg).Cells) :
    e.ι = (evaluatedStageOriginalCell d c R hg e).ι ≫
      pushout.inl (generatorFamilyRepresentative d (evaluatedGenerators c R))
        (evaluatedRepresentativeBoundary d c R hg) :=
  pushedCell_endpoint (generatorFamilyHistory d (evaluatedGenerators c R))
    (evaluatedRepresentativeBoundary d c R hg)
    (IsPushout.of_hasPushout
      (generatorFamilyRepresentative d (evaluatedGenerators c R))
      (evaluatedRepresentativeBoundary d c R hg)).flip
    (evaluatedStageOriginalCell d c R hg e)

/-- The original tagged family projection is retained through the original evaluated cell cofan. -/
theorem evaluatedStage_inl_projection :
    pushout.inl (generatorFamilyRepresentative d (evaluatedGenerators c R))
      (evaluatedRepresentativeBoundary d c R hg) ≫
      (evaluatedStageRetraction d c R hg).r.right =
      generatorFamilyProjection d (evaluatedGenerators c R) ≫ evaluatedCellMap c R := by
  have hp := pushoutRetraction_inl_projection (evaluatedFamilyRetraction d c R hg)
    (evaluatedBoundary c R)
  have hp' : pushout.inl (generatorFamilyRepresentative d (evaluatedGenerators c R))
      (evaluatedRepresentativeBoundary d c R hg) ≫
      (MorphismProperty.pushoutRetract (evaluatedFamilyRetraction d c R hg)
        (evaluatedBoundary c R)).r.right =
      generatorFamilyProjection d (evaluatedGenerators c R) ≫
        pushout.inl (Limits.Sigma.map (evaluatedGenerators c R)) (evaluatedBoundary c R) :=
    hp.trans (congrArg (fun z => z ≫
      pushout.inl (Limits.Sigma.map (evaluatedGenerators c R)) (evaluatedBoundary c R))
      (generatorFamilyRetraction_projection d (evaluatedGenerators c R) hg))
  have hs := (evaluatedStagePushout c R).flip.inl_isoPushout_inv
  exact (congrArg (fun z => pushout.inl
    (generatorFamilyRepresentative d (evaluatedGenerators c R))
      (evaluatedRepresentativeBoundary d c R hg) ≫ z)
      (evaluatedStageRetraction_projection d c R hg)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (evaluatedStagePushout c R).flip.isoPushout.inv) hp').trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun z => generatorFamilyProjection d (evaluatedGenerators c R) ≫ z) hs))))

/-- Every actual base-cell image factors through the original evaluated codomain of the same
original attaching-cell occurrence. No sparse-support or target-cellularity data is supplied. -/
theorem evaluatedStageCell_image (e : (evaluatedStageHistory d c R hg).Cells) :
    e.ι ≫ (evaluatedStageRetraction d c R hg).r.right =
      evaluatedStageCellFactor d c R hg e ≫ R.map (c.cell (evaluatedStageCellIndex d c R hg e)) := by
  have hi := evaluatedStageOriginalCell_endpoint d c R hg e
  have hr := evaluatedStage_inl_projection d c R hg
  have he : (evaluatedStageOriginalCell d c R hg e).ι ≫
      generatorFamilyProjection d (evaluatedGenerators c R) =
      evaluatedStageCellFactor d c R hg e ≫
        Sigma.ι (evaluatedTargets c R) (evaluatedStageCellIndex d c R hg e) :=
    generatorFamilyCell_image d (evaluatedGenerators c R)
      (evaluatedStageOriginalCell d c R hg e)
  have hb := evaluatedCellMap_inj c R (evaluatedStageCellIndex d c R hg e)
  exact (congrArg (fun z => z ≫ (evaluatedStageRetraction d c R hg).r.right) hi).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => (evaluatedStageOriginalCell d c R hg e).ι ≫ z) hr).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ evaluatedCellMap c R) he).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun z => evaluatedStageCellFactor d c R hg e ≫ z) hb))))))

end HomotopicalAlgebra.CellularEvaluationHistory

end OriginalHistoryPart6

noncomputable section OriginalHistoryPart7

universe w uV vV uD vD t

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.CellularEvaluationHistory

section Shift

variable {C : Type uV} [Category.{vV} C]
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {α : O → Type t} {A B : ∀ j, α j → C} {g : ∀ j i, A j i ⟶ B j i}
  {X Y : C} {f : X ⟶ Y} (c : RelativeCellComplex.{w} g f)
  {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f')

/-- Move only the endpoint arrow through its supplied actual Arrow isomorphism. -/
def shiftedComplex : RelativeCellComplex.{w} g f' where
  toTransfiniteCompositionOfShape := c.toTransfiniteCompositionOfShape.ofArrowIso e
  attachCells := c.attachCells

/-- The same original cell after transporting the complex through the original arrow isomorphism. -/
def shiftedCell (a : c.Cells) : (shiftedComplex c e).Cells where
  j := a.j
  hj := a.hj
  k := a.k

theorem shiftedCell_endpoint (a : c.Cells) :
    (shiftedCell c e a).ι = a.ι ≫ e.hom.right := by
  change (c.attachCells a.j a.hj).cell a.k ≫
    (c.incl.app (Order.succ a.j) ≫ e.hom.right) =
      ((c.attachCells a.j a.hj).cell a.k ≫ c.incl.app (Order.succ a.j)) ≫ e.hom.right
  exact (Category.assoc _ _ _).symm

end Shift

section SplitEquality

variable {C : Type uV} [Category.{vV} C]
  {S T : SmallObject.CoherentRetracts.SplitObject C}

theorem splitObject_eq_retraction (h : S = T) :
    (eqToHom (congrArg SmallObject.CoherentRetracts.SplitObject.target h.symm) ≫
      S.retraction) ≫ eqToHom (congrArg SmallObject.CoherentRetracts.SplitObject.source h) =
        T.retraction := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end SplitEquality

namespace OriginalStages

variable {V : Type uV} [Category.{vV} V] [ModelCategory V]
  [HasColimitsOfSize.{w, w} V]
  {D : Type uD} [Category.{vD} D]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData V κ)
  {P : MorphismProperty D}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : D} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)
  (R : D ⥤ V) [PreservesColimitsOfSize.{w, w} R]
  (hP : ∀ p : P.toSet, cofibrations V (R.map p.1.hom))

local instance originalContinuityPreserved : PreservesWellOrderContinuousOfShape O R :=
  { preservesColimitsOfShape := fun _ _ => inferInstance }

/-- The given original ordinal presentation after applying the evaluation functor. -/
def sourcePresentation : CategoryTheory.TransfiniteCompositionOfShape O (R.map f) :=
  c.toTransfiniteCompositionOfShape.map R

include hP

omit [HasColimitsOfSize.{w, w} V] [PreservesColimitsOfSize.{w, w} R] in
theorem stepCofibrations (i : {j : O // ¬ IsMax j})
    (k : (c.attachCells i.1 i.2).ι) :
    cofibrations V (evaluatedGenerators (c.attachCells i.1 i.2) R k) :=
  hP ((c.attachCells i.1 i.2).π k)

/-- The actual I-cell representative of an original evaluated successor. -/
def stepArrow (i : {j : O // ¬ IsMax j}) :=
  evaluatedStageRepresentative d (c.attachCells i.1 i.2) R (stepCofibrations c R hP i)

/-- The original source-fixed successor retract onto its actual I-cell representative. -/
def stepRetraction (i : {j : O // ¬ IsMax j}) :
    RetractArrow ((sourcePresentation c R).F.map (homOfLE (Order.le_succ i.1)))
      (stepArrow d c R hP i) :=
  evaluatedStageRetraction d (c.attachCells i.1 i.2) R (stepCofibrations c R hP i)

/-- The actual original-cardinal I-cell history of the represented successor. -/
def stepHistory (i : {j : O // ¬ IsMax j}) :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => d.I.homFamily)
      (stepArrow d c R hP i) :=
  evaluatedStageHistory d (c.attachCells i.1 i.2) R (stepCofibrations c R hP i)

theorem stepMembership (i : {j : O // ¬ IsMax j}) :
    SmallObject.relativeCellMaps.{w} d.I (stepArrow d c R hP i) :=
  SmallObject.relativeCellComplex_mem_relativeCellMaps d.I (stepHistory d c R hP i)

/-- The coherent original prefix splittings obtained from the actual successor representatives. -/
def sourceSection :
    (SmallObject.CoherentRetracts.prefixSplitFunctor (SmallObject.relativeCellMaps.{w} d.I)
      (sourcePresentation c R).F).sections :=
  SmallObject.CoherentRetracts.ChosenStages.chosenSection
    (SmallObject.relativeCellMaps.{w} d.I) (sourcePresentation c R).F
    (stepArrow d c R hP) (stepRetraction d c R hP) (stepMembership d c R hP)

/-- The coherent I-cell diagram constructed on the original outer ordinal. -/
def targetDiagram : O ⥤ V :=
  SmallObject.CoherentRetracts.ChosenStages.targetDiagram
    (SmallObject.relativeCellMaps.{w} d.I) (sourcePresentation c R).F
    (stepArrow d c R hP) (stepRetraction d c R hP) (stepMembership d c R hP)

/-- The complete endpoint data produced from the original coherent prefix section. -/
def originalEndpoint :
    SmallObject.CoherentRetracts.EndpointOfSectionData (SmallObject.relativeCellMaps.{w} d.I)
      (sourcePresentation c R) (sourceSection d c R hP) :=
  SmallObject.CoherentRetracts.endpointOfSection _ (sourcePresentation c R)
    (sourceSection d c R hP)

/-- The actual natural retraction from the constructed diagram to the evaluated original diagram. -/
def originalRetraction : (targetDiagram d c R hP) ⟶ (sourcePresentation c R).F :=
  SmallObject.CoherentRetracts.retractionOfSection _ (sourcePresentation c R)
    (sourceSection d c R hP)

/-- The actual natural inclusion of the evaluated original diagram into the constructed diagram. -/
def originalInclusion : (sourcePresentation c R).F ⟶ targetDiagram d c R hP :=
  SmallObject.CoherentRetracts.inclusionOfSection _ (sourcePresentation c R)
    (sourceSection d c R hP)

theorem originalSplitting : originalInclusion d c R hP ≫ originalRetraction d c R hP =
    𝟙 (sourcePresentation c R).F :=
  SmallObject.CoherentRetracts.section_natural_splitting _ (sourcePresentation c R)
    (sourceSection d c R hP)

/-- The original coherent prefix splitting at the given outer stage. -/
def currentState (j : O) : SmallObject.CoherentRetracts.PrefixSplit
    (SmallObject.relativeCellMaps.{w} d.I) (sourcePresentation c R).F j :=
  (sourceSection d c R hP).val (op j)

/-- The original split object at the endpoint of the given closed prefix. -/
def currentObject (j : O) : SmallObject.CoherentRetracts.SplitObject V :=
  (currentState d c R hP j).D.obj ⟨j, le_rfl⟩

theorem currentSource_eq (j : O) :
    (currentObject d c R hP j).source = (sourcePresentation c R).F.obj j :=
  Functor.congr_obj (currentState d c R hP j).source_eq ⟨j, le_rfl⟩

/-- The actual successor retract transported to the source of the original coherent prefix. -/
def transportedStepRetraction (i : {j : O // ¬ IsMax j}) :=
  SmallObject.CoherentRetracts.PrefixSplitSuccessor.transportOriginalRetract
    (SmallObject.relativeCellMaps.{w} d.I) (sourcePresentation c R).F i.1
    (currentState d c R hP i.1) (stepArrow d c R hP i) (stepRetraction d c R hP i)

/-- The original successor split object, constructed by its actual source-fixed pushout. -/
def nextObject (i : {j : O // ¬ IsMax j}) : SmallObject.CoherentRetracts.SplitObject V :=
  SmallObject.CoherentRetracts.SplitObject.successorObject (currentObject d c R hP i.1)
    (SmallObject.CoherentRetracts.PrefixSplitSuccessor.sourceMap
      (SmallObject.relativeCellMaps.{w} d.I) (sourcePresentation c R).F i.1
      (currentState d c R hP i.1))
    (SmallObject.ArrowRetractRootNormalization.root (transportedStepRetraction d c R hP i))
    (SmallObject.ArrowRetractRootNormalization.arrowRetract
      (transportedStepRetraction d c R hP i)) (by rfl)

theorem currentObject_succ (i : {j : O // ¬ IsMax j}) :
    currentObject d c R hP (Order.succ i.1) = nextObject d c R hP i := by
  have hs : currentState d c R hP (Order.succ i.1) =
      SmallObject.CoherentRetracts.PrefixSplitSuccessor.originalSuccessorState
        (SmallObject.relativeCellMaps.{w} d.I) (sourcePresentation c R).F i.1
        (currentState d c R hP i.1) i.2 (stepArrow d c R hP i)
        (stepRetraction d c R hP i) (stepMembership d c R hP i) :=
    SmallObject.CoherentRetracts.ChosenStages.section_succ
      (SmallObject.relativeCellMaps.{w} d.I) (sourcePresentation c R).F
      (stepArrow d c R hP) (stepRetraction d c R hP) (stepMembership d c R hP) i.1 i.2
  exact (congrArg (fun S : SmallObject.CoherentRetracts.PrefixSplit
    (SmallObject.relativeCellMaps.{w} d.I) (sourcePresentation c R).F (Order.succ i.1) =>
      S.D.obj ⟨Order.succ i.1, le_rfl⟩) hs).trans
      (SmallObject.SuccStruct.extendToSucc_obj_succ_eq i.2 _ _)

theorem originalRetraction_app (j : O) :
    (originalRetraction d c R hP).app j =
      (currentObject d c R hP j).retraction ≫ eqToHom (currentSource_eq d c R hP j) := by
  change (currentObject d c R hP j).retraction ≫
    (eqToHom (SmallObject.CoherentRetracts.PrefixSplitGlue.wholeDiagram_source
      (SmallObject.relativeCellMaps.{w} d.I) (sourcePresentation c R).F
      (sourceSection d c R hP))).app j = _
  rw [eqToHom_app]
  rfl

/-- The original chosen-cardinal history is pushed through the actual coherent successor square. -/
def pushedInnerHistory (i : {j : O // ¬ IsMax j}) :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => d.I.homFamily)
      ((targetDiagram d c R hP).map (homOfLE (Order.le_succ i.1))) := by
  let Q := SmallObject.relativeCellMaps.{w} d.I
  let S := (sourceSection d c R hP).val (op i.1)
  let h := SmallObject.CoherentRetracts.PrefixSplitSuccessor.transportOriginalRetract Q
    (sourcePresentation c R).F i.1 S (stepArrow d c R hP i) (stepRetraction d c R hP i)
  let a := h.r.left ≫ (S.D.obj ⟨i.1, le_rfl⟩).inclusion
  let sq := SmallObject.CoherentRetracts.SplitObject.originalSuccessorPushout
    (S.D.obj ⟨i.1, le_rfl⟩)
    (SmallObject.CoherentRetracts.PrefixSplitSuccessor.sourceMap Q
      (sourcePresentation c R).F i.1 S) (stepArrow d c R hP i) h
  let pushed := pushedComplex (stepHistory d c R hP i) a sq
  have ha := SmallObject.CoherentRetracts.ChosenStages.targetDiagram_arrowSucc Q
    (sourcePresentation c R).F (stepArrow d c R hP) (stepRetraction d c R hP)
    (stepMembership d c R hP) i.1 i.2
  exact shiftedComplex pushed (eqToIso ha.symm)

/-- The same original successor-factory cell before the coherent prefix pushout. -/
def innerOriginalCell (i : {j : O // ¬ IsMax j})
    (a : (pushedInnerHistory d c R hP i).Cells) : (stepHistory d c R hP i).Cells where
  j := a.j
  hj := a.hj
  k := a.k

/-- The original attaching occurrence selected by a genuine inner factory cell. -/
def innerOriginalIndex (i : {j : O // ¬ IsMax j})
    (a : (pushedInnerHistory d c R hP i).Cells) : (c.attachCells i.1 i.2).ι :=
  evaluatedStageCellIndex d (c.attachCells i.1 i.2) R (stepCofibrations c R hP i)
    (innerOriginalCell d c R hP i a)

/-- The full base-cell target map into the evaluation of its original attaching occurrence. -/
def innerFactor (i : {j : O // ¬ IsMax j})
    (a : (pushedInnerHistory d c R hP i).Cells) :
    a.i.1.right ⟶ R.obj (((c.attachCells i.1 i.2).π
      (innerOriginalIndex d c R hP i a)).1.right) :=
  evaluatedStageCellFactor d (c.attachCells i.1 i.2) R (stepCofibrations c R hP i)
    (innerOriginalCell d c R hP i a)

/-- The original factory endpoint map into the next coherent split object. -/
def nextCellMap (i : {j : O // ¬ IsMax j}) :
    (Arrow.mk (stepArrow d c R hP i)).right ⟶ (nextObject d c R hP i).target :=
  SmallObject.ArrowRetractRootNormalization.oldTargetMap (transportedStepRetraction d c R hP i) ≫
    pushout.inl (SmallObject.ArrowRetractRootNormalization.root
      (transportedStepRetraction d c R hP i)) (currentObject d c R hP i.1).inclusion

theorem transportedStepRetraction_right (i : {j : O // ¬ IsMax j}) :
    (transportedStepRetraction d c R hP i).r.right = (stepRetraction d c R hP i).r.right := by
  change (stepRetraction d c R hP i).r.right ≫ 𝟙 _ = _
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem nextCellMap_projection (i : {j : O // ¬ IsMax j}) :
    nextCellMap d c R hP i ≫ (nextObject d c R hP i).retraction =
      (stepRetraction d c R hP i).r.right := by
  change (SmallObject.ArrowRetractRootNormalization.oldTargetMap
    (transportedStepRetraction d c R hP i) ≫ pushout.inl _ _) ≫
      pushout.desc (SmallObject.ArrowRetractRootNormalization.projection
        (transportedStepRetraction d c R hP i)) _ _ = _
  rw [Category.assoc, pushout.inl_desc,
    SmallObject.ArrowRetractRootNormalization.oldTargetMap_projection,
    transportedStepRetraction_right]

theorem nextObject_retraction (i : {j : O // ¬ IsMax j}) :
    eqToHom (congrArg SmallObject.CoherentRetracts.SplitObject.target
      (currentObject_succ d c R hP i).symm) ≫
      (originalRetraction d c R hP).app (Order.succ i.1) =
        (nextObject d c R hP i).retraction := by
  rw [originalRetraction_app]
  exact (Category.assoc _ _ _).symm.trans
    (splitObject_eq_retraction (currentObject_succ d c R hP i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem innerCell_endpoint (i : {j : O // ¬ IsMax j})
    (a : (pushedInnerHistory d c R hP i).Cells) :
    a.ι = ((innerOriginalCell d c R hP i a).ι ≫ nextCellMap d c R hP i) ≫
      eqToHom (congrArg SmallObject.CoherentRetracts.SplitObject.target
        (currentObject_succ d c R hP i).symm) := by
  let Q := SmallObject.relativeCellMaps.{w} d.I
  let S := currentState d c R hP i.1
  let h := transportedStepRetraction d c R hP i
  let v := h.r.left ≫ (currentObject d c R hP i.1).inclusion
  let sq := SmallObject.CoherentRetracts.SplitObject.originalSuccessorPushout
    (currentObject d c R hP i.1)
    (SmallObject.CoherentRetracts.PrefixSplitSuccessor.sourceMap Q
      (sourcePresentation c R).F i.1 S) (stepArrow d c R hP i) h
  let e := eqToIso (SmallObject.CoherentRetracts.ChosenStages.targetDiagram_arrowSucc Q
    (sourcePresentation c R).F (stepArrow d c R hP) (stepRetraction d c R hP)
    (stepMembership d c R hP) i.1 i.2).symm
  let b := innerOriginalCell d c R hP i a
  have h₁ := pushedCell_endpoint (stepHistory d c R hP i) v sq b
  have h₂ := shiftedCell_endpoint (pushedComplex (stepHistory d c R hP i) v sq) e
    (pushedCell (stepHistory d c R hP i) v sq b)
  have he : e.hom.right = eqToHom (congrArg SmallObject.CoherentRetracts.SplitObject.target
      (currentObject_succ d c R hP i).symm) := by
    change Arrow.rightFunc.map e.hom = _
    simp only [e, eqToIso.hom, eqToHom_map]
  exact h₂.trans ((congrArg (fun z => z ≫ e.hom.right) h₁).trans
    (congrArg (fun z => ((innerOriginalCell d c R hP i a).ι ≫ nextCellMap d c R hP i) ≫ z) he))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem innerCell_image (i : {j : O // ¬ IsMax j})
    (a : (pushedInnerHistory d c R hP i).Cells) :
    a.ι ≫ (originalRetraction d c R hP).app (Order.succ i.1) =
      innerFactor d c R hP i a ≫
        R.map ((c.attachCells i.1 i.2).cell (innerOriginalIndex d c R hP i a)) := by
  have hi := innerCell_endpoint d c R hP i a
  have hr := nextObject_retraction d c R hP i
  have hp := nextCellMap_projection d c R hP i
  have hlast := evaluatedStageCell_image d (c.attachCells i.1 i.2) R
    (stepCofibrations c R hP i) (innerOriginalCell d c R hP i a)
  exact (congrArg (fun z => z ≫ (originalRetraction d c R hP).app (Order.succ i.1)) hi).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => ((innerOriginalCell d c R hP i a).ι ≫ nextCellMap d c R hP i) ≫ z)
          hr).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => (innerOriginalCell d c R hP i a).ι ≫ z) hp).trans hlast))))

end OriginalStages

end HomotopicalAlgebra.CellularEvaluationHistory

end OriginalHistoryPart7

noncomputable section OriginalHistoryPart8

universe w uV vV uD vD

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.CellularEvaluationHistory.OriginalStages

variable {V : Type uV} [Category.{vV} V] [ModelCategory V]
  [HasColimitsOfSize.{w, w} V]
  {D : Type uD} [Category.{vD} D]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData V κ)
  {P : MorphismProperty D}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : D} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)
  (R : D ⥤ V) [PreservesColimitsOfSize.{w, w} R]
  (hP : ∀ p : P.toSet, cofibrations V (R.map p.1.hom))

/-- The original actual endpoint inclusion and projection split the same original evaluated endpoint. -/
theorem originalEndpoint_splitting :
    (originalEndpoint d c R hP).retract.i.right ≫
      (originalEndpoint d c R hP).retract.r.right = 𝟙 (R.obj Y) :=
  (originalEndpoint d c R hP).retract.retract_right

/-- The original source-root arrow is recovered through the same actual endpoint projection. -/
theorem originalEndpoint_root :
    (originalEndpoint d c R hP).arrow ≫ (originalEndpoint d c R hP).retract.r.right =
      R.map f := by
  have h := (originalEndpoint d c R hP).retract.r_w
  rw [(originalEndpoint d c R hP).retraction_source] at h
  exact h.symm.trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every original outer endpoint cocone leg retains its actual component retraction. -/
theorem originalEndpoint_projection (j : O) :
    (originalEndpoint d c R hP).presentation.incl.app j ≫
      (originalEndpoint d c R hP).retract.r.right =
      (originalRetraction d c R hP).app j ≫ (sourcePresentation c R).incl.app j := by
  let Q := SmallObject.relativeCellMaps.{w} d.I
  let F := (sourcePresentation c R).F
  let x := sourceSection d c R hP
  let G := SmallObject.CoherentRetracts.PrefixSplitGlue.wholeDiagram Q F x
  let hs := SmallObject.CoherentRetracts.PrefixSplitGlue.wholeDiagram_source Q F x
  let cF : Cocone (G ⋙ SmallObject.CoherentRetracts.SplitObject.sourceFunctor) :=
    (Cocone.precompose (eqToHom hs)).obj (Cocone.mk (R.obj Y) (sourcePresentation c R).incl)
  let r := SmallObject.CoherentRetracts.SplitObject.retractionNatTrans G
  change colimit.ι (G ⋙ SmallObject.CoherentRetracts.SplitObject.targetFunctor) j ≫
    (colimit.isColimit _).map cF r = _
  have h := (colimit.isColimit (G ⋙ SmallObject.CoherentRetracts.SplitObject.targetFunctor)).ι_map
    cF r j
  exact h.trans (Category.assoc _ _ _).symm

end HomotopicalAlgebra.CellularEvaluationHistory.OriginalStages

end OriginalHistoryPart8

noncomputable section OriginalHistoryPart9

universe w u v t

open CategoryTheory Limits MorphismProperty
open CategoryTheory.SmallObject.CellularNormalization

namespace HomotopicalAlgebra.CellularEvaluationHistory

variable {C : Type u} [Category.{v} C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : Type t} {A B : α → C} (g : ∀ i, A i ⟶ B i)
  (F : J ⥤ C)
  (K : {j : J // ¬ IsMax j} → OriginalInnerShape.{w})
  (c : ∀ i : {j : J // ¬ IsMax j}, RelativeCellComplex.{w}
    (fun _ : (K i).carrier => g) (F.map (homOfLE (Order.le_succ i.1))))

/-- Complete the actual inner relative histories using only an empty singleton at a maximal stage. -/
def completeRelativeHistories (j : J) :
    RelativeCellComplex.{w} (fun _ : (completeOriginalShapes K j).carrier => g)
      (F.map (homOfLE (Order.le_succ j))) := by
  classical
  by_cases hj : IsMax j
  · let singleton : OriginalInnerShape.{w} :=
      { carrier := ULift.{w} (Fin 1)
        linearOrder := inferInstance
        orderBot := inferInstance
        succOrder := SuccOrder.ofLinearWellFoundedLT (ULift.{w} (Fin 1))
        wellFounded := inferInstance }
    letI : LinearOrder singleton.carrier := singleton.linearOrder
    letI : OrderBot singleton.carrier := singleton.orderBot
    letI : SuccOrder singleton.carrier := singleton.succOrder
    letI : WellFoundedLT singleton.carrier := singleton.wellFounded
    let E : singleton.carrier ≃o Fin 1 :=
      { toEquiv := Equiv.ulift
        map_rel_iff' := Iff.rfl }
    let base : RelativeCellComplex.{w} (fun _ : singleton.carrier => g)
        (F.map (homOfLE (Order.le_succ j))) :=
      { toTransfiniteCompositionOfShape := (maximalInner F j hj).ofOrderIso E
        attachCells := fun k hk => False.elim (hk (by
          intro l hl
          exact le_of_eq (Subsingleton.elim l k))) }
    have he : completeOriginalShapes K j = singleton := by
      simp only [completeOriginalShapes, dite_eq_left hj]
      rfl
    exact he.symm ▸ base
  · exact (completeOriginalShapes_nonmax K j hj).symm ▸ c ⟨j, hj⟩

theorem transportRelative_transfinite {S T : OriginalInnerShape.{w}} (h : S = T)
    {X Y : C} {f : X ⟶ Y}
    (a : RelativeCellComplex.{w} (fun _ : S.carrier => g) f) :
    (h ▸ a).toTransfiniteCompositionOfShape = h ▸ a.toTransfiniteCompositionOfShape := by
  cases h
  rfl

/-- Transport the same original cell through equality of its actual inner ordinal shape. -/
def transportRelativeCell {S T : OriginalInnerShape.{w}} (h : S = T)
    {X Y : C} {f : X ⟶ Y}
    (a : RelativeCellComplex.{w} (fun _ : S.carrier => g) f)
    (b : (h ▸ a).Cells) : a.Cells := by
  cases h
  exact b

theorem transportRelativeCell_label {S T : OriginalInnerShape.{w}} (h : S = T)
    {X Y : C} {f : X ⟶ Y}
    (a : RelativeCellComplex.{w} (fun _ : S.carrier => g) f)
    (b : (h ▸ a).Cells) : (transportRelativeCell g h a b).i = b.i := by
  cases h
  rfl

theorem transportRelativeCell_endpoint {S T : OriginalInnerShape.{w}} (h : S = T)
    {X Y : C} {f : X ⟶ Y}
    (a : RelativeCellComplex.{w} (fun _ : S.carrier => g) f)
    (b : (h ▸ a).Cells) :
    b.ι = eqToHom (congrArg B (transportRelativeCell_label g h a b)).symm ≫
      (transportRelativeCell g h a b).ι := by
  cases h
  exact (Category.id_comp _).symm

omit [OrderBot J] [WellFoundedLT J] in
/-- Completing relative histories retains the canonical whole original transfinite records. -/
theorem completeRelativeHistories_transfinite (j : J) :
    (completeRelativeHistories g F K c j).toTransfiniteCompositionOfShape =
      completeOriginalHistories F K (fun i => (c i).toTransfiniteCompositionOfShape) j := by
  classical
  by_cases hj : IsMax j
  · simp only [completeRelativeHistories, completeOriginalHistories, dite_eq_left hj]
    exact transportRelative_transfinite g _ _
  · simp only [completeRelativeHistories, completeOriginalHistories, dite_eq_right hj]
    exact transportRelative_transfinite g (completeOriginalShapes_nonmax K j hj).symm (c ⟨j, hj⟩)

/-- Transport the same original cell through equality of the actual fixed-shape complex. -/
def transportFixedComplexCell {S : OriginalInnerShape.{w}}
    {X Y : C} {f : X ⟶ Y}
    {a b : RelativeCellComplex.{w} (fun _ : S.carrier => g) f}
    (h : a = b) (z : a.Cells) : b.Cells := h ▸ z

theorem transportFixedComplexCell_label {S : OriginalInnerShape.{w}}
    {X Y : C} {f : X ⟶ Y}
    {a b : RelativeCellComplex.{w} (fun _ : S.carrier => g) f}
    (h : a = b) (z : a.Cells) : (transportFixedComplexCell g h z).i = z.i := by
  cases h
  rfl

theorem transportFixedComplexCell_endpoint {S : OriginalInnerShape.{w}}
    {X Y : C} {f : X ⟶ Y}
    {a b : RelativeCellComplex.{w} (fun _ : S.carrier => g) f}
    (h : a = b) (z : a.Cells) :
    z.ι = eqToHom (congrArg B (transportFixedComplexCell_label g h z)).symm ≫
      (transportFixedComplexCell g h z).ι := by
  cases h
  exact (Category.id_comp _).symm

omit [OrderBot J] [WellFoundedLT J] in
theorem completedCell_outer_notMax (j : J)
    (a : (completeRelativeHistories g F K c j).Cells) : ¬ IsMax j := by
  intro hj
  have hsub : Subsingleton (completeOriginalShapes K j).carrier := by
    simp only [completeOriginalShapes, dite_eq_left hj]
    infer_instance
  exact a.hj (fun l _ => le_of_eq (hsub.elim l a.j))

omit [OrderBot J] [WellFoundedLT J] in
theorem completedRelativeHistory_nonmax (j : J) (hj : ¬ IsMax j) :
    completeRelativeHistories g F K c j =
      (completeOriginalShapes_nonmax K j hj).symm ▸ c ⟨j, hj⟩ := by
  classical
  dsimp only [completeRelativeHistories]
  rw [dite_eq_right hj]

/-- Recover the literal original inner occurrence by the exact shape and
complex equalities, without choosing a new occurrence from its image. -/
def originalCompletedCell (j : J) (a : (completeRelativeHistories g F K c j).Cells) :
    Σ' hj : ¬ IsMax j, (c ⟨j, hj⟩).Cells :=
  let hj := completedCell_outer_notMax g F K c j a
  let h := (completeOriginalShapes_nonmax K j hj).symm
  let z := transportFixedComplexCell g (completedRelativeHistory_nonmax g F K c j hj) a
  ⟨hj, transportRelativeCell g h (c ⟨j, hj⟩) z⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
omit [OrderBot J] [WellFoundedLT J] in
theorem originalCompletedCell_label (j : J)
    (a : (completeRelativeHistories g F K c j).Cells) :
    (originalCompletedCell g F K c j a).2.i = a.i := by
  let hj := completedCell_outer_notMax g F K c j a
  let h := (completeOriginalShapes_nonmax K j hj).symm
  let z := transportFixedComplexCell g (completedRelativeHistory_nonmax g F K c j hj) a
  exact (transportRelativeCell_label g h (c ⟨j, hj⟩) z).trans
    (transportFixedComplexCell_label g (completedRelativeHistory_nonmax g F K c j hj) a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
omit [OrderBot J] [WellFoundedLT J] in
theorem originalCompletedCell_endpoint (j : J)
    (a : (completeRelativeHistories g F K c j).Cells) :
    a.ι = eqToHom (congrArg B (originalCompletedCell_label g F K c j a)).symm ≫
      (originalCompletedCell g F K c j a).2.ι := by
  let hj := completedCell_outer_notMax g F K c j a
  let h := (completeOriginalShapes_nonmax K j hj).symm
  let z := transportFixedComplexCell g (completedRelativeHistory_nonmax g F K c j hj) a
  have h₁ := transportFixedComplexCell_endpoint g (completedRelativeHistory_nonmax g F K c j hj) a
  have h₂ := transportRelativeCell_endpoint g h (c ⟨j, hj⟩) z
  rw [h₁, h₂]
  simp only [originalCompletedCell, ← Category.assoc, eqToHom_trans]
  rfl

omit [OrderBot J] [WellFoundedLT J] in
/-- Every completed real cell is an original nonmaximal inner occurrence; maximal dummy
histories have no cells. Only the typed transport of the unchanged label is used. -/
theorem completeRelativeHistories_original (j : J)
    (a : (completeRelativeHistories g F K c j).Cells) :
    ∃ hj : ¬ IsMax j, ∃ b : (c ⟨j, hj⟩).Cells, ∃ hi : b.i = a.i,
      a.ι = eqToHom (congrArg B hi).symm ≫ b.ι := by
  classical
  by_cases hj : IsMax j
  · have hsub : Subsingleton (completeOriginalShapes K j).carrier := by
      simp only [completeOriginalShapes, dite_eq_left hj]
      infer_instance
    exact (a.hj (fun l _ => le_of_eq (hsub.elim l a.j))).elim
  · have hc : completeRelativeHistories g F K c j =
        (completeOriginalShapes_nonmax K j hj).symm ▸ c ⟨j, hj⟩ := by
      dsimp only [completeRelativeHistories]
      rw [dite_eq_right hj]
    revert a
    rw [hc]
    intro a
    let h := (completeOriginalShapes_nonmax K j hj).symm
    refine ⟨hj, transportRelativeCell g h (c ⟨j, hj⟩) a,
      transportRelativeCell_label g h (c ⟨j, hj⟩) a, ?_⟩
    exact transportRelativeCell_endpoint g h (c ⟨j, hj⟩) a

end HomotopicalAlgebra.CellularEvaluationHistory

end OriginalHistoryPart9

noncomputable section OriginalHistoryPart10

universe w uV vV uD vD

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.CellularEvaluationHistory

variable {V : Type uV} [Category.{vV} V] [ModelCategory V]
  {D : Type uD} [Category.{vD} D]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {P : MorphismProperty D}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : D} {f : X ⟶ Y}

/-- Returned original evaluated-cell data. Every history, split map and original occurrence
is constructed from the original coefficient generation and supplied target cell complex. -/
structure OriginalEvaluationHistory (d : CofibrantGenerationData V κ)
    (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f) (R : D ⥤ V) where
  /-- The actual ordinal shape of the derived base I-cell history. -/
  shape : SmallObject.CellularNormalization.OriginalInnerShape.{w}
  /-- The endpoint of the derived base I-cell history. -/
  Z : V
  /-- The original evaluated source map into the derived history endpoint. -/
  u : R.obj X ⟶ Z
  /-- The actual base I-cell complex presenting the returned source map. -/
  b : RelativeCellComplex.{w} (fun _ : shape.carrier => d.I.homFamily) u
  /-- The derived retraction from the base-history endpoint to the original evaluated endpoint. -/
  r : Z ⟶ R.obj Y
  /-- The derived section of the original evaluated endpoint into the base-history endpoint. -/
  s : R.obj Y ⟶ Z
  hs : s ≫ r = 𝟙 (R.obj Y)
  hr : u ≫ r = R.map f
  /-- The original target-cell occurrence attached to every actual base-history cell. -/
  tag : b.Cells → c.Cells
  /-- The full base-cell target map into the evaluation of its tagged original target cell. -/
  image (e : b.Cells) : e.i.1.right ⟶ R.obj (tag e).i.1.right
  hImage (e : b.Cells) : e.ι ≫ r = image e ≫ R.map (tag e).ι

namespace OriginalEvaluationHistory

/-- The actual ordinal carrier of the returned original evaluated history. -/
abbrev K {d : CofibrantGenerationData V κ}
    {c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f} {R : D ⥤ V}
    (h : OriginalEvaluationHistory d c R) : Type w := h.shape.carrier

end OriginalEvaluationHistory

end HomotopicalAlgebra.CellularEvaluationHistory

end OriginalHistoryPart10

noncomputable section OriginalHistoryPart11

universe w uV vV uD vD

open CategoryTheory Limits MorphismProperty Opposite
open CategoryTheory.SmallObject.CellularNormalization

namespace HomotopicalAlgebra.CellularEvaluationHistory.OriginalStages

variable {V : Type uV} [Category.{vV} V] [ModelCategory V]
  [HasColimitsOfSize.{w, w} V]
  {D : Type uD} [Category.{vD} D]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData V κ)
  {P : MorphismProperty D}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : D} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)
  (R : D ⥤ V) [PreservesColimitsOfSize.{w, w} R]
  (hP : ∀ p : P.toSet, cofibrations V (R.map p.1.hom))

/-- The original regular-cardinal ordinal shape used by every genuine base I-cell factory. -/
def originalκShape : OriginalInnerShape.{w} where
  carrier := κ.ord.ToType
  linearOrder := inferInstance
  orderBot := inferInstance
  succOrder := inferInstance
  wellFounded := inferInstance

/-- The original inner histories with their endpoint completion and empty maximal branch. -/
def completedShapes (j : O) : OriginalInnerShape.{w} :=
  completeOriginalShapes (fun _ : {j : O // ¬ IsMax j} => originalκShape (κ := κ)) j

/-- The actual endpoint-completed inner history at each original outer stage. -/
def completedInner (j : O) :
    RelativeCellComplex.{w} (fun _ : (completedShapes (κ := κ) (O := O) j).carrier => d.I.homFamily)
      ((targetDiagram d c R hP).map (homOfLE (Order.le_succ j))) :=
  completeRelativeHistories d.I.homFamily (targetDiagram d c R hP)
    (fun _ : {j : O // ¬ IsMax j} => originalκShape (κ := κ))
    (pushedInnerHistory d c R hP) j

/-- The original linear order on the endpoint-completed inner history. -/
local instance completedLinear (j : O) : LinearOrder (completedShapes (κ := κ) (O := O) j).carrier :=
  (completedShapes (κ := κ) (O := O) j).linearOrder
/-- The original bottom of the endpoint-completed inner history. -/
local instance completedBottom (j : O) : OrderBot (completedShapes (κ := κ) (O := O) j).carrier :=
  (completedShapes (κ := κ) (O := O) j).orderBot
/-- The original successor order on the endpoint-completed inner history. -/
local instance completedSucc (j : O) : SuccOrder (completedShapes (κ := κ) (O := O) j).carrier :=
  (completedShapes (κ := κ) (O := O) j).succOrder
local instance completedWF (j : O) : WellFoundedLT (completedShapes (κ := κ) (O := O) j).carrier :=
  (completedShapes (κ := κ) (O := O) j).wellFounded

/-- The actual flattened ordinal carrier of the original completed inner histories. -/
abbrev normalizedShapeCarrier :=
  Index (fun j : O => (completedShapes (κ := κ) (O := O) j).carrier)

local instance normalizedWF : WellFoundedLT (normalizedShapeCarrier (κ := κ) (O := O)) :=
  lexWellFounded
/-- The canonical successor order on the actual flattened original history. -/
local instance normalizedSucc : SuccOrder (normalizedShapeCarrier (κ := κ) (O := O)) :=
  flatSuccOrder

/-- The complete ordinal shape of the actual normalized original I-cell history. -/
def normalizedShape : OriginalInnerShape.{w} where
  carrier := normalizedShapeCarrier (κ := κ) (O := O)
  linearOrder := inferInstance
  orderBot := inferInstance
  succOrder := inferInstance
  wellFounded := inferInstance

/-- The actual empty cofan used at maximal inner joins in the original normalization. -/
def originalEmptyCofan : Cofan (fun i : PEmpty.{w + 1} => (i.elim : V)) :=
  colimit.cocone (Discrete.functor (fun i : PEmpty.{w + 1} => (i.elim : V)))

/-- The original categorical colimit cocone for the empty attaching family. -/
def originalEmptyCofanIsColimit : IsColimit (originalEmptyCofan (V := V)) :=
  colimit.isColimit _

/-- The actual normalized base I-cell complex of the constructed coherent original endpoint. -/
def normalizedBaseComplex :
    RelativeCellComplex.{w} (fun _ : (normalizedShape (κ := κ) (O := O)).carrier => d.I.homFamily)
      (originalEndpoint d c R hP).arrow :=
  normalizeRelativeCells (fun _ : O => d.I.homFamily)
    (originalEndpoint d c R hP).presentation.toTransfiniteCompositionOfShape
    (completedInner d c R hP) (originalEmptyCofan (V := V)) (originalEmptyCofan (V := V))
    (originalEmptyCofanIsColimit (V := V)) (originalEmptyCofanIsColimit (V := V))

/-- The literal original inner occurrence of a normalized base cell. -/
def normalizedInnerCell (a : (normalizedBaseComplex d c R hP).Cells) :
    UsedCells (fun _ : O => d.I.homFamily) (targetDiagram d c R hP)
      (completedInner d c R hP) :=
  CellTrace.originalCell (fun _ : O => d.I.homFamily)
    (originalEndpoint d c R hP).presentation.toTransfiniteCompositionOfShape
    (completedInner d c R hP) (originalEmptyCofan (V := V)) (originalEmptyCofan (V := V))
    (originalEmptyCofanIsColimit (V := V)) (originalEmptyCofanIsColimit (V := V)) a

end HomotopicalAlgebra.CellularEvaluationHistory.OriginalStages

end OriginalHistoryPart11

noncomputable section OriginalHistoryPart12

universe w uV vV uD vD

open CategoryTheory Limits MorphismProperty Opposite
open CategoryTheory.SmallObject.CellularNormalization

namespace HomotopicalAlgebra.CellularEvaluationHistory.OriginalStages

variable {V : Type uV} [Category.{vV} V] [ModelCategory V]
  [HasColimitsOfSize.{w, w} V]
  {D : Type uD} [Category.{vD} D]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData V κ)
  {P : MorphismProperty D}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : D} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)
  (R : D ⥤ V) [PreservesColimitsOfSize.{w, w} R]
  (hP : ∀ p : P.toSet, cofibrations V (R.map p.1.hom))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem normalizedInnerCell_label (a : (normalizedBaseComplex d c R hP).Cells) :
    (normalizedInnerCell d c R hP a).2.i = a.i :=
  CellTrace.originalCell_label (fun _ : O => d.I.homFamily)
    (originalEndpoint d c R hP).presentation.toTransfiniteCompositionOfShape
    (completedInner d c R hP) (originalEmptyCofan (V := V)) (originalEmptyCofan (V := V))
    (originalEmptyCofanIsColimit (V := V)) (originalEmptyCofanIsColimit (V := V)) a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem normalizedInnerCell_endpoint (a : (normalizedBaseComplex d c R hP).Cells) :
    a.ι = eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
      (normalizedInnerCell_label d c R hP a)).symm ≫
      (normalizedInnerCell d c R hP a).2.ι ≫
        (originalEndpoint d c R hP).presentation.incl.app
          (Order.succ (normalizedInnerCell d c R hP a).1) :=
  CellTrace.originalCell_endpoint (fun _ : O => d.I.homFamily)
    (originalEndpoint d c R hP).presentation.toTransfiniteCompositionOfShape
    (completedInner d c R hP) (originalEmptyCofan (V := V)) (originalEmptyCofan (V := V))
    (originalEmptyCofanIsColimit (V := V)) (originalEmptyCofanIsColimit (V := V)) a

/-- The genuine original inner occurrence recovered through exact shape and complex equalities. -/
def normalizedRealCell (a : (normalizedBaseComplex d c R hP).Cells) :=
  let n := normalizedInnerCell d c R hP a
  originalCompletedCell d.I.homFamily (targetDiagram d c R hP)
    (fun _ : {j : O // ¬ IsMax j} => originalκShape (κ := κ))
    (pushedInnerHistory d c R hP) n.1 n.2

/-- The original target-cell occurrence selected by a normalized base cell. -/
def normalizedTag (a : (normalizedBaseComplex d c R hP).Cells) : c.Cells :=
  let n := normalizedInnerCell d c R hP a
  let r := normalizedRealCell d c R hP a
  ⟨n.1, r.1, innerOriginalIndex d c R hP ⟨n.1, r.1⟩ r.2⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The full map from a normalized base-cell target into the evaluation of its original target cell. -/
def normalizedImage (a : (normalizedBaseComplex d c R hP).Cells) :
    a.i.1.right ⟶ R.obj (normalizedTag d c R hP a).i.1.right :=
  let n := normalizedInnerCell d c R hP a
  let r := normalizedRealCell d c R hP a
  eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
      (normalizedInnerCell_label d c R hP a)).symm ≫
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
      (originalCompletedCell_label d.I.homFamily (targetDiagram d c R hP)
        (fun _ : {j : O // ¬ IsMax j} => originalκShape (κ := κ))
        (pushedInnerHistory d c R hP) n.1 n.2)).symm ≫
      innerFactor d c R hP ⟨n.1, r.1⟩ r.2

theorem normalizedTag_stage (a : (normalizedBaseComplex d c R hP).Cells) :
    (normalizedTag d c R hP a).j = (normalizedInnerCell d c R hP a).1 := rfl

theorem normalizedTag_occurrence (a : (normalizedBaseComplex d c R hP).Cells) :
    (normalizedTag d c R hP a).k = innerOriginalIndex d c R hP
      ⟨(normalizedInnerCell d c R hP a).1, (normalizedRealCell d c R hP a).1⟩
      (normalizedRealCell d c R hP a).2 := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem normalizedImage_spec (a : (normalizedBaseComplex d c R hP).Cells) :
    a.ι ≫ (originalEndpoint d c R hP).retract.r.right =
      normalizedImage d c R hP a ≫ R.map (normalizedTag d c R hP a).ι := by
  let n := normalizedInnerCell d c R hP a
  let r := normalizedRealCell d c R hP a
  let hj := r.1
  let b := r.2
  have hi : b.i = n.2.i := originalCompletedCell_label d.I.homFamily (targetDiagram d c R hP)
    (fun _ : {j : O // ¬ IsMax j} => originalκShape (κ := κ))
    (pushedInnerHistory d c R hP) n.1 n.2
  have hb : n.2.ι = eqToHom (congrArg (fun p : d.I.toSet => p.1.right) hi).symm ≫ b.ι :=
    originalCompletedCell_endpoint d.I.homFamily (targetDiagram d c R hP)
    (fun _ : {j : O // ¬ IsMax j} => originalκShape (κ := κ))
    (pushedInnerHistory d c R hP) n.1 n.2
  let i : {j : O // ¬ IsMax j} := ⟨n.1, hj⟩
  let e : c.Cells := ⟨n.1, hj, innerOriginalIndex d c R hP i b⟩
  let qa : a.i.1.right ⟶ n.2.i.1.right :=
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
      (normalizedInnerCell_label d c R hP a)).symm
  let qb : n.2.i.1.right ⟶ b.i.1.right :=
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) hi).symm
  let q : a.i.1.right ⟶ R.obj e.i.1.right := qa ≫ qb ≫ innerFactor d c R hP i b
  change a.ι ≫ (originalEndpoint d c R hP).retract.r.right = q ≫ R.map e.ι
  have ha : a.ι = qa ≫ n.2.ι ≫
      (originalEndpoint d c R hP).presentation.incl.app (Order.succ n.1) :=
    normalizedInnerCell_endpoint d c R hP a
  have hn : n.2.ι = qb ≫ b.ι := hb
  have hp := originalEndpoint_projection d c R hP (Order.succ n.1)
  have him := innerCell_image d c R hP i b
  calc
    a.ι ≫ (originalEndpoint d c R hP).retract.r.right =
        qa ≫ qb ≫ b.ι ≫ (originalRetraction d c R hP).app (Order.succ n.1) ≫
          (sourcePresentation c R).incl.app (Order.succ n.1) := by
            rw [ha, hn]
            simp only [Category.assoc]
            rw [hp]
    _ = qa ≫ qb ≫ innerFactor d c R hP i b ≫
        R.map ((c.attachCells n.1 hj).cell (innerOriginalIndex d c R hP i b)) ≫
          R.map (c.incl.app (Order.succ n.1)) := by
            rw [← Category.assoc b.ι, him]
            change qa ≫ qb ≫ (innerFactor d c R hP i b ≫
                R.map ((c.attachCells n.1 hj).cell (innerOriginalIndex d c R hP i b))) ≫
              (R.map (c.incl.app (Order.succ n.1)) ≫ 𝟙 _) = _
            simp only [Category.comp_id, Category.assoc]
    _ = q ≫ R.map e.ι := by
      change qa ≫ qb ≫ innerFactor d c R hP i b ≫ R.map _ ≫ R.map _ =
        q ≫ R.map ((c.attachCells n.1 hj).cell (innerOriginalIndex d c R hP i b) ≫
          c.incl.app (Order.succ n.1))
      rw [R.map_comp]
      simp only [q, Category.assoc]

theorem normalizedCell_image_exists (a : (normalizedBaseComplex d c R hP).Cells) :
    ∃ e : c.Cells, ∃ q : a.i.1.right ⟶ R.obj e.i.1.right,
      a.ι ≫ (originalEndpoint d c R hP).retract.r.right = q ≫ R.map e.ι :=
  ⟨normalizedTag d c R hP a, normalizedImage d c R hP a, normalizedImage_spec d c R hP a⟩

/-- The tagged base history is derived from the original generators, every supplied
original cofan and pushout, and the actual coherent endpoint retraction. -/
def originalEvaluationHistory : OriginalEvaluationHistory d c R := by
  exact
    { shape := normalizedShape (κ := κ) (O := O)
      Z := (originalEndpoint d c R hP).target
      u := (originalEndpoint d c R hP).arrow
      b := normalizedBaseComplex d c R hP
      r := (originalEndpoint d c R hP).retract.r.right
      s := (originalEndpoint d c R hP).retract.i.right
      hs := originalEndpoint_splitting d c R hP
      hr := originalEndpoint_root d c R hP
      tag := normalizedTag d c R hP
      image := normalizedImage d c R hP
      hImage := normalizedImage_spec d c R hP }

end HomotopicalAlgebra.CellularEvaluationHistory.OriginalStages

end OriginalHistoryPart12

noncomputable section OriginalHistoryConstructor

universe w uV vV uD vD

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.CellularEvaluationHistory

variable {V : Type uV} [Category.{vV} V] [ModelCategory V]
  [HasColimitsOfSize.{w, w} V]
  {D : Type uD} [Category.{vD} D]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData V κ)
  {P : MorphismProperty D}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : D} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)
  (R : D ⥤ V) [PreservesColimitsOfSize.{w, w} R]
  (hP : ∀ p : P.toSet, cofibrations V (R.map p.1.hom))

/-- Derive the complete original evaluated history from the actual coefficient
generation and every supplied original cell occurrence. -/
def ofOriginalGenerators : OriginalEvaluationHistory d c R :=
  OriginalStages.originalEvaluationHistory d c R hP

/-- The original coherent endpoint arrow remains the actual returned root arrow. -/
theorem ofOriginalGenerators_root : (ofOriginalGenerators d c R hP).u =
    (OriginalStages.originalEndpoint d c R hP).arrow := rfl

/-- The actual returned projection is the original whole endpoint retraction. -/
theorem ofOriginalGenerators_projection : (ofOriginalGenerators d c R hP).r =
    (OriginalStages.originalEndpoint d c R hP).retract.r.right := rfl

/-- The actual returned section is the original whole endpoint inclusion. -/
theorem ofOriginalGenerators_section : (ofOriginalGenerators d c R hP).s =
    (OriginalStages.originalEndpoint d c R hP).retract.i.right := rfl

/-- The actual history is the canonical normalization of all original κ-stage
individual-generator and cofan histories. -/
theorem ofOriginalGenerators_complex : (ofOriginalGenerators d c R hP).b =
    OriginalStages.normalizedBaseComplex d c R hP := rfl

/-- The original outer ordinal of every normalized occurrence is retained literally. -/
theorem ofOriginalGenerators_tag_stage (a : (ofOriginalGenerators d c R hP).b.Cells) :
    ((ofOriginalGenerators d c R hP).tag a).j =
      (OriginalStages.normalizedInnerCell d c R hP a).1 := rfl

/-- The target tag is the exact original cofan index of the same individual
factory cell, transported only through the original normalization and shape equalities. -/
theorem ofOriginalGenerators_tag_occurrence (a : (ofOriginalGenerators d c R hP).b.Cells) :
    ((ofOriginalGenerators d c R hP).tag a).k = OriginalStages.innerOriginalIndex d c R hP
      ⟨(OriginalStages.normalizedInnerCell d c R hP a).1,
        (OriginalStages.normalizedRealCell d c R hP a).1⟩
      (OriginalStages.normalizedRealCell d c R hP a).2 := rfl

end HomotopicalAlgebra.CellularEvaluationHistory

end OriginalHistoryConstructor
