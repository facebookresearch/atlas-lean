/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
public import MathlibExt.CategoryTheory.SmallObject.RelativeSourceSmallness
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Batteries.Tactic.Alias
public import Mathlib.SetTheory.Cardinal.Basic
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.Order.WellFounded
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
public import MathlibExt.CategoryTheory.Limits.TransfiniteCompletion
public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.Attachments

/-!
# Original cellular sources and presented subcomplexes

The compactness predicate is the relative-cell compactness of Hirschhorn,
Definitions 10.8.1 and 12.1.1. A subcomplex retains the original ordinal,
every chosen cell occurrence and its original generating arrow, the actual
stage comparisons, and the original endpoint cocones.

`CellularSource` records only cellularity of the original model and its
specified generating families. Relative compactness and smallness concern
those families; no localization class, factorization or local-object
criterion is a field.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

/-- A genuine subcomplex on the unchanged original ordinal presentation.
The cell embeddings select occurrences from each original attaching cofan. -/
structure CellularSubcomplex {P : MorphismProperty C}
    {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f) where
  /-- The endpoint of the subcomplex on the original ordinal presentation. -/
  endpoint : C
  /-- The composite from the original source to the subcomplex endpoint. -/
  hom : X ⟶ endpoint
  /-- The inclusion from the subcomplex endpoint into the original endpoint. -/
  inclusion : endpoint ⟶ Y
  /-- The relative cell complex presenting the subcomplex on the same ordinal and generating
  arrows. -/
  complex : RelativeCellComplex.{w} (fun _ : O => P.homFamily) hom
  /-- The natural comparison from the subcomplex diagram to the original cell diagram. -/
  comparison : complex.F ⟶ c.F
  comparison_bot : complex.isoBot.inv ≫ comparison.app ⊥ = c.isoBot.inv
  comparison_endpoint (j : O) :
    complex.incl.app j ≫ inclusion = comparison.app j ≫ c.incl.app j
  /-- The embedding selecting subcomplex cell occurrences from each original attaching cofan. -/
  cellIndex (j : O) (hj : ¬ IsMax j) :
    (complex.attachCells j hj).ι ↪ (c.attachCells j hj).ι
  label_eq (j : O) (hj : ¬ IsMax j) (k : (complex.attachCells j hj).ι) :
    (complex.attachCells j hj).π k = (c.attachCells j hj).π (cellIndex j hj k)
  cell_eq (j : O) (hj : ¬ IsMax j) (k : (complex.attachCells j hj).ι) :
    (complex.attachCells j hj).cell k ≫ comparison.app (Order.succ j) =
      eqToHom (congrArg (fun p : P.toSet => p.1.right) (label_eq j hj k)) ≫
        (c.attachCells j hj).cell (cellIndex j hj k)

namespace CellularSubcomplex

variable {P : MorphismProperty C}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  {c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f}

/-- The full original complex is its own subcomplex with all original maps. -/
def full (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f) :
    CellularSubcomplex c where
  endpoint := Y
  hom := f
  inclusion := 𝟙 Y
  complex := c
  comparison := 𝟙 c.F
  comparison_bot := by simp
  comparison_endpoint j := by simp
  cellIndex _ _ := Function.Embedding.refl _
  label_eq _ _ _ := rfl
  cell_eq j hj k := by
    change (c.attachCells j hj).cell k ≫ 𝟙 _ = 𝟙 _ ≫ (c.attachCells j hj).cell k
    simp

variable (t : CellularSubcomplex c)

/-- Both original root and endpoint maps recover the same supplied arrow. -/
@[reassoc]
theorem fac : t.hom ≫ t.inclusion = f := by
  rw [← t.complex.fac, Category.assoc, t.comparison_endpoint,
    ← Category.assoc, t.comparison_bot, c.fac]

/-- Every selected occurrence remains at its original ordinal stage. -/
def originalCell (a : t.complex.Cells) : c.Cells where
  j := a.j
  hj := a.hj
  k := t.cellIndex a.j a.hj a.k

/-- Selection preserves the actual original generator, rather than its class. -/
theorem originalCell_label (a : t.complex.Cells) :
    a.i = (t.originalCell a).i := t.label_eq a.j a.hj a.k

/-- Each original cell inclusion is recovered by the same endpoint comparison. -/
@[reassoc]
theorem originalCell_inclusion (a : t.complex.Cells) :
    a.ι ≫ t.inclusion =
      eqToHom (congrArg (fun p : P.toSet => p.1.right) (t.originalCell_label a)) ≫
        (t.originalCell a).ι := by
  dsimp only [RelativeCellComplex.Cells.ι, RelativeCellComplex.Cells.i, originalCell]
  rw [Category.assoc, t.comparison_endpoint, ← Category.assoc,
    t.cell_eq, Category.assoc]

/-- The genuine selected occurrences inject into all original occurrences. -/
def cellEmbedding : t.complex.Cells ↪ c.Cells := by
  let e₁ : t.complex.Cells ≃ Σ a : {j : O // ¬ IsMax j},
      (t.complex.attachCells a.1 a.2).ι :=
    { toFun a := ⟨⟨a.j, a.hj⟩, a.k⟩
      invFun a := ⟨a.1.1, a.1.2, a.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  let e₂ : c.Cells ≃ Σ a : {j : O // ¬ IsMax j},
      (c.attachCells a.1 a.2).ι :=
    { toFun a := ⟨⟨a.j, a.hj⟩, a.k⟩
      invFun a := ⟨a.1.1, a.1.2, a.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact e₁.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl _)
      (fun a => t.cellIndex a.1 a.2)).trans e₂.symm.toEmbedding)

/-- The same occurrence injection bounds the actual subcomplex size. -/
theorem cells_cardinal_le : Cardinal.mk t.complex.Cells ≤ Cardinal.mk c.Cells :=
  Cardinal.mk_le_of_injective t.cellEmbedding.injective

end CellularSubcomplex

/-- Relative compactness at one bound on every original presented cell chain. -/
def IsCellularCompactAt (P : MorphismProperty C) (A : C) (γ : Cardinal.{w}) : Prop :=
  ∀ (O : Type w) [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    (X Y : C) (f : X ⟶ Y)
    (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f) (g : A ⟶ Y),
    ∃ (t : CellularSubcomplex c),
      Cardinal.mk t.complex.Cells ≤ γ ∧ ∃ h : A ⟶ t.endpoint, h ≫ t.inclusion = g

/-- Compactness relative to the actual chosen generating family. -/
def IsCellularCompact (P : MorphismProperty C) (A : C) : Prop :=
  ∃ γ : Cardinal.{w}, IsCellularCompactAt P A γ

namespace IsCellularCompactAt

variable {P : MorphismProperty C} {A B : C} {γ δ : Cardinal.{w}}

/-- Enlarging a bound keeps the original cell presentation and comparison maps. -/
theorem mono (h : IsCellularCompactAt P A γ) (hγδ : γ ≤ δ) :
    IsCellularCompactAt P A δ := by
  intro O _ _ _ _ X Y f c g
  obtain ⟨t, ht, k, hk⟩ := h O X Y f c g
  exact ⟨t, ht.trans hγδ, k, hk⟩

/-- Retracts preserve the same bound and every original endpoint comparison. -/
theorem of_retract (h : IsCellularCompactAt P A γ)
    (i : B ⟶ A) (r : A ⟶ B) (hir : i ≫ r = 𝟙 B) :
    IsCellularCompactAt P B γ := by
  intro O _ _ _ _ X Y f c g
  obtain ⟨t, ht, k, hk⟩ := h O X Y f c (r ≫ g)
  refine ⟨t, ht, i ≫ k, ?_⟩
  rw [Category.assoc, hk, ← Category.assoc, hir, Category.id_comp]

end IsCellularCompactAt

/-- The original source Hom preserves every sufficiently long regular chain
of relative `P`-cell maps; neither the original ordinal nor the cocone changes. -/
def IsUniformlySmallRelativeTo (P : MorphismProperty C) (A : C) : Prop :=
  ∃ β : Cardinal.{w},
    ∀ (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType], β < κ →
      ∀ (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous],
        (∀ j : κ.ord.ToType, ¬ IsMax j →
          SmallObject.relativeCellMaps.{w} P
            (F.map (homOfLE (Order.le_succ j)))) →
        PreservesColimit F (coyoneda.obj (op A))

/-- Exact original cellularity of the specified actual model and generating families. -/
structure CellularSource [ModelCategory C]
    {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ) : Prop where
  I_domains_compact (i : d.I.toSet) : IsCellularCompact.{w} d.I i.1.left
  I_codomains_compact (i : d.I.toSet) : IsCellularCompact.{w} d.I i.1.right
  J_domains_small (j : d.J.toSet) : IsUniformlySmallRelativeTo.{w} d.I j.1.left
  effectiveCofibrations : cofibrations C ≤ MorphismProperty.regularMono C

namespace CellularSource

variable [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ} (h : CellularSource d)

/-- The actual regular-mono presentation of any original cofibration. -/
def effectivePresentation {A B : C} (f : A ⟶ B) (hf : cofibrations C f) : RegularMono f := by
  letI : IsRegularMono f := h.effectiveCofibrations f hf
  exact IsRegularMono.getStruct f

include h in
/-- Original cofibrations are actual monomorphisms at arbitrary endpoints. -/
theorem mono_of_cofibration {A B : C} (f : A ⟶ B) (hf : cofibrations C f) : Mono f := by
  let _ : IsRegularMono f := h.effectiveCofibrations f hf
  infer_instance

/-- Effective monomorphism retains the original two pushout inclusions. -/
def originalPushoutEqualizer {A B : C} (f : A ⟶ B) (hf : cofibrations C f) :
    IsLimit (Fork.ofι f (pushout.condition (f := f) (g := f))) := by
  letI : IsRegularMono f := h.effectiveCofibrations f hf
  let r : RegularMono f := IsRegularMono.getStruct f
  let k := pushout.desc r.left r.right r.w
  have hk₀ : pushout.inl f f ≫ k = r.left := pushout.inl_desc _ _ _
  have hk₁ : pushout.inr f f ≫ k = r.right := pushout.inr_desc _ _ _
  let g (s : Fork (pushout.inl f f) (pushout.inr f f)) : Fork r.left r.right :=
    Fork.ofι s.ι (by
      rw [← hk₀, ← hk₁, ← Category.assoc, ← Category.assoc]
      exact congrArg (fun a => a ≫ k) s.condition)
  refine Fork.IsLimit.mk _ (fun s => r.isLimit.lift (g s)) ?_ ?_
  · intro s
    exact Fork.IsLimit.lift_ι r.isLimit
  · intro s m hm
    apply Fork.IsLimit.hom_ext r.isLimit
    have hg : r.isLimit.lift (g s) ≫ f = s.ι :=
      Fork.IsLimit.lift_ι (t := g s) r.isLimit
    exact hm.trans hg.symm

end CellularSource

end HomotopicalAlgebra

universe w' t

namespace HomotopicalAlgebra.RelativeCellComplex

variable {C : Type u} [Category.{v} C]
  {O : Type w'} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {α : O → Type t} {A B : (j : O) → α j → C}
  {basicCell : (j : O) → (k : α j) → A j k ⟶ B j k}
  {X Y Z T : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} basicCell f) (q : Y ⟶ T) (p : Z ⟶ T) [Mono p]
  (r : X ⟶ Z) (hr : r ≫ p = f ≫ q)
  (b : (a : c.Cells) → B a.j a.i ⟶ Z)
  (hb : ∀ a : c.Cells, b a ≫ p = a.ι ≫ q)

include r hr b hb in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem stageLiftExists (j : O) :
    ∃ m : c.F.obj j ⟶ Z, m ≫ p = c.incl.app j ≫ q := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    refine ⟨c.isoBot.hom ≫ r, ?_⟩
    have hroot : c.isoBot.hom ≫ f = c.incl.app ⊥ := by
      calc
        c.isoBot.hom ≫ f = c.isoBot.hom ≫ (c.isoBot.inv ≫ c.incl.app ⊥) :=
          congrArg (fun z => c.isoBot.hom ≫ z) c.fac.symm
        _ = c.incl.app ⊥ := c.isoBot.hom_inv_id_assoc _
    rw [Category.assoc, hr, ← Category.assoc]
    exact congrArg (fun z => z ≫ q) hroot
  | succ j hj ih =>
    obtain ⟨m, hm⟩ := ih
    let a := c.attachCells j hj
    let s : Cofan (fun k : a.ι => B j (a.π k)) :=
      Cofan.mk Z (fun k => b ⟨j, hj, k⟩)
    let n : a.cofan₂.pt ⟶ Z := a.isColimit₂.desc s
    have hn (k : a.ι) : a.cofan₂.inj k ≫ n = b ⟨j, hj, k⟩ :=
      a.isColimit₂.fac s ⟨k⟩
    have hnp : n ≫ p = a.g₂ ≫ c.incl.app (Order.succ j) ≫ q := by
      apply Cofan.IsColimit.hom_ext a.isColimit₂
      intro k
      rw [← Category.assoc, hn]
      have hcell := hb ⟨j, hj, k⟩
      change b ⟨j, hj, k⟩ ≫ p =
        ((a.cofan₂.inj k ≫ a.g₂) ≫ c.incl.app (Order.succ j)) ≫ q at hcell
      simpa only [Cells.i, Category.assoc] using hcell
    have hmn : a.g₁ ≫ m = a.m ≫ n := by
      apply (cancel_mono p).1
      simp only [Category.assoc, hm, hnp]
      rw [← (Cocone.mk Y c.incl).w (homOfLE (Order.le_succ j))]
      simp only [← Category.assoc]
      rw [a.isPushout.w]
    refine ⟨a.isPushout.desc m n hmn, ?_⟩
    apply a.isPushout.hom_ext
    · rw [← Category.assoc, a.isPushout.inl_desc]
      rw [← Category.assoc, (Cocone.mk Y c.incl).w]
      exact hm
    · rw [← Category.assoc, a.isPushout.inr_desc]
      exact hnp
  | isSuccLimit j hj ih =>
    let m (k : Set.Iio j) : c.F.obj k.1 ⟶ Z := (ih k.1 k.2).choose
    have hm (k : Set.Iio j) : m k ≫ p = c.incl.app k.1 ≫ q :=
      (ih k.1 k.2).choose_spec
    let s : Cocone ((Set.principalSegIio j).monotone.functor ⋙ c.F) :=
      { pt := Z
        ι :=
          { app := m
            naturality := fun k l g => by
              change (c.F.map ((Set.principalSegIio j).monotone.functor.map g)) ≫ m l =
                m k ≫ 𝟙 Z
              rw [Category.comp_id]
              apply (cancel_mono p).1
              simp only [Category.assoc, hm]
              change c.F.map (homOfLE (leOfHom g) : k.1 ⟶ l.1) ≫
                c.incl.app l.1 ≫ q = c.incl.app k.1 ≫ q
              simpa only [Category.assoc] using congrArg (fun z => z ≫ q)
                ((Cocone.mk Y c.incl).w
                  (homOfLE (leOfHom g) : k.1 ⟶ l.1)) } }
    let hc := c.F.isColimitOfIsWellOrderContinuous j hj
    refine ⟨hc.desc s, ?_⟩
    apply hc.hom_ext
    intro k
    rw [← Category.assoc, hc.fac]
    exact (hm k).trans (by
      change c.incl.app k.1 ≫ q =
        c.F.map (homOfLE k.2.le) ≫ c.incl.app j ≫ q
      rw [← Category.assoc, (Cocone.mk Y c.incl).w])

include c r hr b hb in
/-- A map through a monomorphism is constructed from its actual root and all
original cell maps, using the original successor pushouts and limit cocones. -/
theorem exists_lift_through_mono : ∃ m : Y ⟶ Z, m ≫ p = q := by
  let m (j : O) : c.F.obj j ⟶ Z := (stageLiftExists c q p r hr b hb j).choose
  have hm (j : O) : m j ≫ p = c.incl.app j ≫ q :=
    (stageLiftExists c q p r hr b hb j).choose_spec
  let s : Cocone c.F :=
    { pt := Z
      ι :=
        { app := m
          naturality := fun j k g => by
            change c.F.map g ≫ m k = m j ≫ 𝟙 Z
            rw [Category.comp_id]
            apply (cancel_mono p).1
            simp only [Category.assoc, hm]
            simpa only [Category.assoc] using
              congrArg (fun z => z ≫ q) ((Cocone.mk Y c.incl).w g) } }
  refine ⟨c.isColimit.desc s, ?_⟩
  apply c.isColimit.hom_ext
  intro j
  rw [← Category.assoc, c.isColimit.fac]
  exact hm j

end HomotopicalAlgebra.RelativeCellComplex

namespace HomotopicalAlgebra.CellularSubcomplex

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  {c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f}
  (t : CellularSubcomplex c)

/-- The literal original occurrences selected by the supplied subcomplex. -/
def support : Set c.Cells := Set.range t.originalCell

/-- No two selected cells become the same original occurrence. -/
theorem originalCell_injective : Function.Injective t.originalCell := by
  intro a b hab
  apply t.cellEmbedding.injective
  exact hab

/-- Membership retains the actual selected occurrence and its original label. -/
theorem mem_support (a : c.Cells) :
    a ∈ t.support ↔ ∃ b : t.complex.Cells, t.originalCell b = a := Iff.rfl

/-- The support cardinal is exactly the cardinal of the genuine selected cells. -/
theorem support_cardinal : Cardinal.mk t.support = Cardinal.mk t.complex.Cells :=
  Cardinal.mk_range_eq t.originalCell t.originalCell_injective

/-- Every actual occurrence belongs to the full original complex. -/
theorem full_support : (full c).support = Set.univ := by
  ext a
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨a, rfl⟩

end HomotopicalAlgebra.CellularSubcomplex

namespace HomotopicalAlgebra.RelativeCellComplex

variable {C : Type u} [Category.{v} C]
  {O : Type w'} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {α : O → Type t} {A B : (j : O) → α j → C}
  {basicCell : (j : O) → (k : α j) → A j k ⟶ B j k}
  {X Y : C} {f : X ⟶ Y} (c : RelativeCellComplex.{w} basicCell f)

/-- The original root map into an unchanged original stage. -/
def rootAtStage (j : O) : X ⟶ c.F.obj j :=
  c.isoBot.inv ≫ c.F.map (homOfLE bot_le)

/-- Original root maps are compatible with all original stage transitions. -/
@[reassoc]
theorem rootAtStage_map {j k : O} (g : j ⟶ k) :
    c.rootAtStage j ≫ c.F.map g = c.rootAtStage k := by
  dsimp only [rootAtStage]
  rw [Category.assoc, ← c.F.map_comp]
  rfl

/-- The original endpoint leg recovers the supplied original root arrow. -/
@[reassoc]
theorem rootAtStage_incl (j : O) : c.rootAtStage j ≫ c.incl.app j = f := by
  dsimp only [rootAtStage]
  rw [Category.assoc, (Cocone.mk Y c.incl).w]
  exact c.fac

variable {c}

/-- An actual original cell inclusion into any later original stage. -/
def Cells.toStage (a : c.Cells) (j : O) (ha : a.j < j) : B a.j a.i ⟶ c.F.obj j :=
  (c.attachCells a.j a.hj).cell a.k ≫ c.F.map (homOfLE (Order.succ_le_of_lt ha))

/-- Original cell stage maps retain every actual later transition. -/
@[reassoc]
theorem Cells.toStage_map (a : c.Cells) {j k : O} (ha : a.j < j) (g : j ⟶ k) :
    a.toStage j ha ≫ c.F.map g = a.toStage k (ha.trans_le (leOfHom g)) := by
  dsimp only [toStage, i]
  rw [Category.assoc, ← c.F.map_comp]
  rfl

/-- The original cell's endpoint inclusion is its actual later stage map. -/
@[reassoc]
theorem Cells.toStage_incl (a : c.Cells) (j : O) (ha : a.j < j) :
    a.toStage j ha ≫ c.incl.app j = a.ι := by
  dsimp only [toStage, ι, i]
  rw [Category.assoc, (Cocone.mk Y c.incl).w]

end HomotopicalAlgebra.RelativeCellComplex

namespace HomotopicalAlgebra.CellularSubcomplex

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  {c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f}
  (t : CellularSubcomplex c)

/-- A selected cell keeps the original generator codomain at the actual
subcomplex endpoint. -/
def originalCellTarget (a : t.complex.Cells) : (t.originalCell a).i.1.right ⟶ t.endpoint :=
  eqToHom (congrArg (fun z : P.toSet => z.1.right) (t.originalCell_label a).symm) ≫ a.ι

/-- Its original codomain inclusion recovers the same ambient endpoint map. -/
@[reassoc]
theorem originalCellTarget_inclusion (a : t.complex.Cells) :
    t.originalCellTarget a ≫ t.inclusion = (t.originalCell a).ι := by
  dsimp only [originalCellTarget]
  rw [Category.assoc, t.originalCell_inclusion]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- A selected cell's original generator codomain maps to every later
unchanged stage of the supplied subcomplex. -/
def originalCellAtStage (a : t.complex.Cells) (j : O) (ha : a.j < j) :
    (t.originalCell a).i.1.right ⟶ t.complex.F.obj j :=
  eqToHom (congrArg (fun z : P.toSet => z.1.right) (t.originalCell_label a).symm) ≫
    a.toStage j ha

/-- These actual original-generator stage maps retain all later transitions. -/
@[reassoc]
theorem originalCellAtStage_map (a : t.complex.Cells) {j k : O}
    (ha : a.j < j) (g : j ⟶ k) :
    t.originalCellAtStage a j ha ≫ t.complex.F.map g =
      t.originalCellAtStage a k (ha.trans_le (leOfHom g)) := by
  dsimp only [originalCellAtStage]
  rw [Category.assoc, a.toStage_map]

/-- Every selected stage retains the same original-generator endpoint map. -/
@[reassoc]
theorem originalCellAtStage_incl (a : t.complex.Cells) (j : O) (ha : a.j < j) :
    t.originalCellAtStage a j ha ≫ t.complex.incl.app j = t.originalCellTarget a := by
  dsimp only [originalCellAtStage, originalCellTarget]
  rw [Category.assoc, a.toStage_incl]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A selected cell's actual later-stage comparison is the literal original
cell map into the same original ambient stage. -/
@[reassoc]
theorem originalCellAtStage_comparison (a : t.complex.Cells) (j : O) (ha : a.j < j) :
    t.originalCellAtStage a j ha ≫ t.comparison.app j =
      (t.originalCell a).toStage j ha := by
  dsimp only [originalCellAtStage, RelativeCellComplex.Cells.toStage,
    RelativeCellComplex.Cells.i, originalCell]
  simp only [Category.assoc]
  rw [t.comparison.naturality]
  rw [← Category.assoc ((t.complex.attachCells a.j a.hj).cell a.k), t.cell_eq]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

end HomotopicalAlgebra.CellularSubcomplex

namespace HomotopicalAlgebra.CellularSubcomplex

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  {c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f}
  (t : CellularSubcomplex c)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original roots retain the complete original stage comparison. -/
@[reassoc]
theorem rootAtStage_comparison (j : O) :
    t.complex.rootAtStage j ≫ t.comparison.app j = c.rootAtStage j := by
  dsimp only [RelativeCellComplex.rootAtStage]
  rw [Category.assoc, t.comparison.naturality, ← Category.assoc, t.comparison_bot]

end HomotopicalAlgebra.CellularSubcomplex

section EffectiveCellularFamilyResearchPromotion

open CategoryTheory Limits MorphismProperty Opposite
open CategoryTheory.SmallObject

namespace HomotopicalAlgebra

/-- The original model's effective-cofibration condition alone. -/
def EffectiveCofibrations (C : Type u) [Category.{v} C] [CategoryWithCofibrations C] : Prop :=
  cofibrations C ≤ MorphismProperty.regularMono C

namespace EffectiveCofibrations

variable {C : Type u} [Category.{v} C] [ModelCategory C] (h : EffectiveCofibrations C)

/-- The regular-monomorphism presentation of a cofibration supplied by effectiveness. -/
def effectivePresentation {A B : C} (f : A ⟶ B) (hf : cofibrations C f) : RegularMono f := by
  letI : IsRegularMono f := h f hf
  exact IsRegularMono.getStruct f

include h in
/-- Original cofibrations are actual monomorphisms at arbitrary endpoints. -/
theorem mono_of_cofibration {A B : C} (f : A ⟶ B) (hf : cofibrations C f) : Mono f := by
  let _ : IsRegularMono f := h f hf
  infer_instance

/-- Effective monomorphism retains the original two pushout inclusions. -/
def originalPushoutEqualizer {A B : C} (f : A ⟶ B) (hf : cofibrations C f) :
    IsLimit (Fork.ofι f (pushout.condition (f := f) (g := f))) := by
  letI : IsRegularMono f := h f hf
  let r : RegularMono f := IsRegularMono.getStruct f
  let k := pushout.desc r.left r.right r.w
  have hk₀ : pushout.inl f f ≫ k = r.left := pushout.inl_desc _ _ _
  have hk₁ : pushout.inr f f ≫ k = r.right := pushout.inr_desc _ _ _
  let g (s : Fork (pushout.inl f f) (pushout.inr f f)) : Fork r.left r.right :=
    Fork.ofι s.ι (by
      rw [← hk₀, ← hk₁, ← Category.assoc, ← Category.assoc]
      exact congrArg (fun a => a ≫ k) s.condition)
  refine Fork.IsLimit.mk _ (fun s => r.isLimit.lift (g s)) ?_ ?_
  · intro s
    exact Fork.IsLimit.lift_ι r.isLimit
  · intro s m hm
    apply Fork.IsLimit.hom_ext r.isLimit
    have hg : r.isLimit.lift (g s) ≫ f = s.ι :=
      Fork.IsLimit.lift_ι (t := g s) r.isLimit
    exact hm.trans hg.symm


end EffectiveCofibrations
end HomotopicalAlgebra

namespace HomotopicalAlgebra.EffectiveCellularSubcomplexExtension

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)

/-- The exact attaching-domain map of the original occurrence. -/
def boundary (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι) :
    ((c.attachCells j hj).π k).1.left ⟶ c.F.obj j :=
  (c.attachCells j hj).cofan₁.inj k ≫ (c.attachCells j hj).g₁

/-- The actual original attaching square on each cell occurrence. -/
theorem boundary_cell (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι) :
    boundary d c j hj k ≫ c.F.map (homOfLE (Order.le_succ j)) =
      d.I.homFamily ((c.attachCells j hj).π k) ≫ (c.attachCells j hj).cell k := by
  dsimp only [boundary, AttachCells.cell]
  rw [Category.assoc, (c.attachCells j hj).isPushout.w,
    ← Category.assoc, (c.attachCells j hj).hm]
  exact Category.assoc _ _ _

/-- Every original successor is an actual original cofibration. -/
theorem originalSuccessorCofibration (j : O) (hj : ¬ IsMax j) :
    cofibrations C (c.F.map (homOfLE (Order.le_succ j))) := by
  rw [← trivialFibrations_llp, ← d.I_rlp]
  exact d.I.transfiniteCompositions_pushouts_coproducts_le_llp_rlp _
    (SmallObject.attachCells_mem_relativeCellMaps d.I (c.attachCells j hj))

variable (h : EffectiveCofibrations C)

include h in
/-- Original cellularity proves monicity of the actual original successor. -/
theorem originalSuccessorMono (j : O) (hj : ¬ IsMax j) :
    Mono (c.F.map (homOfLE (Order.le_succ j))) :=
  h.mono_of_cofibration _ (originalSuccessorCofibration d c j hj)

/-- Equality of original generator labels retains the whole original arrow. -/
theorem generatorTransport (p q : d.I.toSet) (e : p = q) :
    d.I.homFamily p ≫ eqToHom (congrArg (fun a : d.I.toSet => a.1.right) e) =
      eqToHom (congrArg (fun a : d.I.toSet => a.1.left) e) ≫ d.I.homFamily q := by
  cases e
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
/-- The original domain comparison is derived from its selected codomain square. -/
theorem subcomplexBoundary (t : CellularSubcomplex c) (j : O) (hj : ¬ IsMax j)
    (a : (t.complex.attachCells j hj).ι) :
    boundary d t.complex j hj a ≫ t.comparison.app j =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (t.label_eq j hj a)) ≫
        boundary d c j hj (t.cellIndex j hj a) := by
  let _ : Mono (c.F.map (homOfLE (Order.le_succ j))) := originalSuccessorMono d c h j hj
  apply (cancel_mono (c.F.map (homOfLE (Order.le_succ j)))).1
  calc
    (boundary d t.complex j hj a ≫ t.comparison.app j) ≫
        c.F.map (homOfLE (Order.le_succ j)) =
      boundary d t.complex j hj a ≫
        (t.complex.F.map (homOfLE (Order.le_succ j)) ≫ t.comparison.app (Order.succ j)) := by
          rw [Category.assoc, ← t.comparison.naturality]
    _ = (d.I.homFamily ((t.complex.attachCells j hj).π a) ≫
        (t.complex.attachCells j hj).cell a) ≫ t.comparison.app (Order.succ j) := by
          rw [← Category.assoc, boundary_cell]
    _ = d.I.homFamily ((t.complex.attachCells j hj).π a) ≫
        (eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (t.label_eq j hj a)) ≫
          (c.attachCells j hj).cell (t.cellIndex j hj a)) := by
          rw [Category.assoc, t.cell_eq]
    _ = (eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (t.label_eq j hj a)) ≫
        d.I.homFamily ((c.attachCells j hj).π (t.cellIndex j hj a))) ≫
          (c.attachCells j hj).cell (t.cellIndex j hj a) := by
          rw [← Category.assoc, generatorTransport d _ _ (t.label_eq j hj a)]
    _ = (eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (t.label_eq j hj a)) ≫
        boundary d c j hj (t.cellIndex j hj a)) ≫
          c.F.map (homOfLE (Order.le_succ j)) := by
          rw [Category.assoc, ← boundary_cell d c j hj (t.cellIndex j hj a), ← Category.assoc]

section OriginalFamily

variable {T : Type w} (t : T → CellularSubcomplex c) {E B : C}
  (α : ∀ i : T, (t i).endpoint ⟶ E)

/-- A family's prescribed cell map is transported to its same original generating codomain. -/
def familyCellImage (j : O) (hj : ¬ IsMax j) (i : T)
    (a : ((t i).complex.attachCells j hj).ι) :
    ((c.attachCells j hj).π ((t i).cellIndex j hj a)).1.right ⟶ E :=
  eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a).symm) ≫
    ((t i).complex.attachCells j hj).cell a ≫ (t i).complex.incl.app (Order.succ j) ≫ α i

/-- Shared original occurrences receive the same actual prescribed map. -/
def FamilyCellCompatible : Prop :=
  ∀ (j : O) (hj : ¬ IsMax j) (i i' : T)
    (a : ((t i).complex.attachCells j hj).ι) (b : ((t i').complex.attachCells j hj).ι)
    (e : (t i).cellIndex j hj a = (t i').cellIndex j hj b),
    familyCellImage d c t α j hj i a =
      eqToHom (congrArg (fun k => ((c.attachCells j hj).π k).1.right) e) ≫
        familyCellImage d c t α j hj i' b

/-- Selection means an actual occurrence belongs to at least one original subcomplex. -/
def Selected (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι) : Prop :=
  ∃ (i : T) (a : ((t i).complex.attachCells j hj).ι), (t i).cellIndex j hj a = k

/-- An actual selected occurrence keeps its original codomain and a prescribed family map. -/
def selectedCellImage (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι)
    (hk : Selected d c t j hj k) : ((c.attachCells j hj).π k).1.right ⟶ E :=
  eqToHom (congrArg (fun a => ((c.attachCells j hj).π a).1.right)
    hk.choose_spec.choose_spec.symm) ≫
      familyCellImage d c t α j hj hk.choose hk.choose_spec.choose

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility makes the chosen map agree with every selected original witness. -/
theorem selectedCellImage_eq (hcells : FamilyCellCompatible d c t α)
    (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι)
    (hk : Selected d c t j hj k) (i : T) (a : ((t i).complex.attachCells j hj).ι)
    (e : (t i).cellIndex j hj a = k) :
    eqToHom (congrArg (fun a => ((c.attachCells j hj).π a).1.right) e) ≫
      selectedCellImage d c t α j hj k hk = familyCellImage d c t α j hj i a := by
  dsimp only [selectedCellImage]
  rw [← Category.assoc, eqToHom_trans]
  exact (hcells j hj i hk.choose a hk.choose_spec.choose
    (e.trans hk.choose_spec.choose_spec.symm)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
/-- The prescribed selected map has the correct original attaching boundary at an extended stage. -/
theorem familyCellImage_boundary (j : O) (hj : ¬ IsMax j) (m : c.F.obj j ⟶ E)
    (hext : ∀ i : T, (t i).comparison.app j ≫ m = (t i).complex.incl.app j ≫ α i)
    (i : T) (a : ((t i).complex.attachCells j hj).ι) :
    d.I.homFamily ((c.attachCells j hj).π ((t i).cellIndex j hj a)) ≫
      familyCellImage d c t α j hj i a =
        boundary d c j hj ((t i).cellIndex j hj a) ≫ m := by
  let e := (t i).label_eq j hj a
  let L := eqToHom (congrArg (fun p : d.I.toSet => p.1.left) e)
  let Li := eqToHom (congrArg (fun p : d.I.toSet => p.1.left) e.symm)
  let Ri := eqToHom (congrArg (fun p : d.I.toSet => p.1.right) e.symm)
  change d.I.homFamily ((c.attachCells j hj).π ((t i).cellIndex j hj a)) ≫
    (Ri ≫ ((t i).complex.attachCells j hj).cell a ≫
      (t i).complex.incl.app (Order.succ j) ≫ α i) = _
  calc
    _ = (Li ≫ d.I.homFamily (((t i).complex.attachCells j hj).π a)) ≫
        (((t i).complex.attachCells j hj).cell a ≫
          (t i).complex.incl.app (Order.succ j) ≫ α i) := by
            rw [← Category.assoc, generatorTransport d _ _ e.symm]
    _ = Li ≫ ((d.I.homFamily (((t i).complex.attachCells j hj).π a) ≫
        ((t i).complex.attachCells j hj).cell a) ≫
          (t i).complex.incl.app (Order.succ j) ≫ α i) := by simp only [Category.assoc]
    _ = Li ≫ ((boundary d (t i).complex j hj a ≫
        (t i).complex.F.map (homOfLE (Order.le_succ j))) ≫
          (t i).complex.incl.app (Order.succ j) ≫ α i) := by
            rw [← boundary_cell d (t i).complex j hj a]
    _ = Li ≫ (boundary d (t i).complex j hj a ≫ (t i).complex.incl.app j ≫ α i) := by
      simp only [Category.assoc]
      rw [← Category.assoc ((t i).complex.F.map (homOfLE (Order.le_succ j)))
        ((t i).complex.incl.app (Order.succ j)) (α i),
        (Cocone.mk (t i).endpoint (t i).complex.incl).w]
    _ = Li ≫ ((boundary d (t i).complex j hj a ≫ (t i).comparison.app j) ≫ m) := by
      rw [Category.assoc, hext i]
    _ = Li ≫ ((L ≫ boundary d c j hj ((t i).cellIndex j hj a)) ≫ m) := by
      rw [subcomplexBoundary d c h (t i) j hj a]
    _ = boundary d c j hj ((t i).cellIndex j hj a) ≫ m := by
      dsimp only [Li, L]
      rw [← Category.assoc, ← Category.assoc, eqToHom_trans]
      simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every prescribed original cell map retains its actual square against the given right map. -/
theorem familyCellImage_right (q : E ⟶ B) (β : Y ⟶ B)
    (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (j : O) (hj : ¬ IsMax j) (i : T) (a : ((t i).complex.attachCells j hj).ι) :
    familyCellImage d c t α j hj i a ≫ q =
      (c.attachCells j hj).cell ((t i).cellIndex j hj a) ≫ c.incl.app (Order.succ j) ≫ β := by
  dsimp only [familyCellImage]
  simp only [Category.assoc]
  rw [hα i, ← Category.assoc ((t i).complex.incl.app (Order.succ j)),
    (t i).comparison_endpoint]
  simp only [Category.assoc]
  rw [← Category.assoc (((t i).complex.attachCells j hj).cell a)
    ((t i).comparison.app (Order.succ j)) (c.incl.app (Order.succ j) ≫ β), (t i).cell_eq]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
/-- The chosen selected-cell map satisfies the exact current stage boundary. -/
theorem selectedCellImage_boundary (hcells : FamilyCellCompatible d c t α)
    (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι) (hk : Selected d c t j hj k)
    (m : c.F.obj j ⟶ E)
    (hext : ∀ i : T, (t i).comparison.app j ≫ m = (t i).complex.incl.app j ≫ α i) :
    d.I.homFamily ((c.attachCells j hj).π k) ≫ selectedCellImage d c t α j hj k hk =
      boundary d c j hj k ≫ m := by
  have hw := hk
  obtain ⟨i, a, e⟩ := hw
  subst k
  have hm := selectedCellImage_eq d c t α hcells j hj _ hk i a rfl
  simp only [eqToHom_refl, Category.id_comp] at hm
  rw [hm]
  exact familyCellImage_boundary d c h t α j hj m hext i a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The chosen selected-cell map keeps its exact original square against the right map. -/
theorem selectedCellImage_right (hcells : FamilyCellCompatible d c t α)
    (q : E ⟶ B) (β : Y ⟶ B) (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι) (hk : Selected d c t j hj k) :
    selectedCellImage d c t α j hj k hk ≫ q =
      (c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j) ≫ β := by
  have hw := hk
  obtain ⟨i, a, e⟩ := hw
  subst k
  have hm := selectedCellImage_eq d c t α hcells j hj _ hk i a rfl
  simp only [eqToHom_refl, Category.id_comp] at hm
  rw [hm]
  exact familyCellImage_right d c t α q β hα j hj i a

variable (q : E ⟶ B) (r : X ⟶ E) (β : Y ⟶ B)

/-- A stage lift retains every prescribed original subcomplex-stage map. -/
@[ext]
structure StageState (j : O) extends
    HasLiftingProperty.transfiniteComposition.SqStruct (Cocone.mk Y c.incl) q
      (c.isoBot.hom ≫ r) β j where
  subcomplex (i : T) : (t i).comparison.app j ≫ f' = (t i).complex.incl.app j ≫ α i

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restriction preserves every actual smaller original subcomplex equation. -/
def stageMap {j j' : O} (s : StageState d c t α q r β j) (u : j' ⟶ j) :
    StageState d c t α q r β j' where
  __ := s.toSqStruct.map u
  subcomplex i := by
    dsimp
    rw [← Category.assoc, ← (t i).comparison.naturality, Category.assoc,
      s.subcomplex i, ← Category.assoc, (Cocone.mk (t i).endpoint (t i).complex.incl).w]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original constrained lift states form an actual inverse system on the unchanged order. -/
def stageFunctor : Oᵒᵖ ⥤ Type _ where
  obj j := StageState d c t α q r β j.unop
  map u := ↾fun s => stageMap d c t α q r β s u.unop
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro s
    ext
    change c.F.map (𝟙 j.unop) ≫ s.f' = s.f'
    rw [c.F.map_id, Category.id_comp]
  map_comp u v := by
    apply ConcreteCategory.hom_ext
    intro s
    ext
    change c.F.map (v.unop ≫ u.unop) ≫ s.f' =
      c.F.map v.unop ≫ (c.F.map u.unop ≫ s.f')
    rw [c.F.map_comp, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An unprescribed original cell has its actual square against the given right map. -/
theorem missingCellSquare (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j)
    (k : (c.attachCells j hj).ι) :
    CommSq (boundary d c j hj k ≫ s.f') (d.I.homFamily ((c.attachCells j hj).π k)) q
      ((c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j) ≫ β) where
  w := by
    rw [Category.assoc, s.w₂]
    change boundary d c j hj k ≫ (c.incl.app j ≫ β) =
      d.I.homFamily ((c.attachCells j hj).π k) ≫
        ((c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j) ≫ β)
    calc
      _ = boundary d c j hj k ≫
          (c.F.map (homOfLE (Order.le_succ j)) ≫ c.incl.app (Order.succ j)) ≫ β := by
            rw [(Cocone.mk Y c.incl).w]
      _ = d.I.homFamily ((c.attachCells j hj).π k) ≫
          ((c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j) ≫ β) := by
            simpa only [Category.assoc] using congrArg
              (fun z => z ≫ c.incl.app (Order.succ j) ≫ β) (boundary_cell d c j hj k)

/-- Selected original cells use their prescribed map; every missing I cell uses its original
lift. -/
def completionCellImage (hq : d.I.rlp q) (j : O) (hj : ¬ IsMax j)
    (s : StageState d c t α q r β j) (k : (c.attachCells j hj).ι) :
    ((c.attachCells j hj).π k).1.right ⟶ E := by
  classical
  exact if hk : Selected d c t j hj k then selectedCellImage d c t α j hj k hk else
    let _ : HasLiftingProperty (d.I.homFamily ((c.attachCells j hj).π k)) q :=
      hq _ ((c.attachCells j hj).π k).2
    (missingCellSquare d c t α q r β j hj s k).lift

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
/-- The completed occurrence map has the actual original attaching boundary. -/
theorem completionCellImage_boundary (hq : d.I.rlp q)
    (hcells : FamilyCellCompatible d c t α) (j : O) (hj : ¬ IsMax j)
    (s : StageState d c t α q r β j) (k : (c.attachCells j hj).ι) :
    d.I.homFamily ((c.attachCells j hj).π k) ≫ completionCellImage d c t α q r β hq j hj s k =
      boundary d c j hj k ≫ s.f' := by
  classical
  dsimp only [completionCellImage]
  split_ifs with hk
  · exact selectedCellImage_boundary d c h t α hcells j hj k hk s.f' s.subcomplex
  · let _ : HasLiftingProperty (d.I.homFamily ((c.attachCells j hj).π k)) q :=
      hq _ ((c.attachCells j hj).π k).2
    exact (missingCellSquare d c t α q r β j hj s k).fac_left

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every completed cell retains its actual original square against the right map. -/
theorem completionCellImage_right (hq : d.I.rlp q)
    (hcells : FamilyCellCompatible d c t α) (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j)
    (k : (c.attachCells j hj).ι) :
    completionCellImage d c t α q r β hq j hj s k ≫ q =
      (c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j) ≫ β := by
  classical
  dsimp only [completionCellImage]
  split_ifs with hk
  · exact selectedCellImage_right d c t α hcells q β hα j hj k hk
  · let _ : HasLiftingProperty (d.I.homFamily ((c.attachCells j hj).π k)) q :=
      hq _ ((c.attachCells j hj).π k).2
    exact (missingCellSquare d c t α q r β j hj s k).fac_right

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every prescribed family cell remains its exact selected map after completion. -/
theorem completionCellImage_family (hq : d.I.rlp q)
    (hcells : FamilyCellCompatible d c t α) (j : O) (hj : ¬ IsMax j)
    (s : StageState d c t α q r β j) (i : T) (a : ((t i).complex.attachCells j hj).ι) :
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a)) ≫
      completionCellImage d c t α q r β hq j hj s ((t i).cellIndex j hj a) =
        ((t i).complex.attachCells j hj).cell a ≫ (t i).complex.incl.app (Order.succ j) ≫ α i := by
  classical
  have hk : Selected d c t j hj ((t i).cellIndex j hj a) := ⟨i, a, rfl⟩
  have hm := selectedCellImage_eq d c t α hcells j hj _ hk i a rfl
  simp only [eqToHom_refl, Category.id_comp] at hm
  dsimp only [completionCellImage]
  rw [dite_eq_left hk, hm]
  dsimp only [familyCellImage]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- The original target cofan combines all actual completed occurrence maps. -/
def completionCofanMap (hq : d.I.rlp q) (j : O) (hj : ¬ IsMax j)
    (s : StageState d c t α q r β j) : (c.attachCells j hj).cofan₂.pt ⟶ E :=
  (c.attachCells j hj).isColimit₂.desc
    (Cofan.mk E (fun k => completionCellImage d c t α q r β hq j hj s k))

/-- Each original cofan injection retains its own actual completed occurrence map. -/
theorem completionCofanMap_inj (hq : d.I.rlp q) (j : O) (hj : ¬ IsMax j)
    (s : StageState d c t α q r β j) (k : (c.attachCells j hj).ι) :
    (c.attachCells j hj).cofan₂.inj k ≫ completionCofanMap d c t α q r β hq j hj s =
      completionCellImage d c t α q r β hq j hj s k :=
  (c.attachCells j hj).isColimit₂.fac _ ⟨k⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
/-- The actual original pushout extends the current stage using exactly these completed cells. -/
def successorLift (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) : c.F.obj (Order.succ j) ⟶ E := by
  refine (c.attachCells j hj).isPushout.desc s.f'
    (completionCofanMap d c t α q r β hq j hj s) ?_
  apply (c.attachCells j hj).isColimit₁.hom_ext
  intro k
  change (c.attachCells j hj).cofan₁.inj k.as ≫ ((c.attachCells j hj).g₁ ≫ s.f') =
    (c.attachCells j hj).cofan₁.inj k.as ≫
      ((c.attachCells j hj).m ≫ completionCofanMap d c t α q r β hq j hj s)
  rw [← Category.assoc, ← Category.assoc, (c.attachCells j hj).hm]
  simp only [Category.assoc]
  rw [completionCofanMap_inj]
  simpa only [boundary, Category.assoc] using
    (completionCellImage_boundary d c h t α q r β hq hcells j hj s k.as).symm

/-- The original successor map recovers the same current stage lift. -/
theorem successorLift_stage (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) :
    c.F.map (homOfLE (Order.le_succ j)) ≫ successorLift d c h t α q r β hq hcells j hj s =
      s.f' := by
  simp only [successorLift, IsPushout.inl_desc]

/-- Every original cell injection recovers its same completed occurrence map. -/
theorem successorLift_cell (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) (k : (c.attachCells j hj).ι) :
    (c.attachCells j hj).cell k ≫ successorLift d c h t α q r β hq hcells j hj s =
      completionCellImage d c t α q r β hq j hj s k := by
  rw [AttachCells.cell, Category.assoc]
  simp only [successorLift, IsPushout.inr_desc]
  exact completionCofanMap_inj d c t α q r β hq j hj s k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original common root gives the actual initial constrained state. -/
def bottomState (hrq : r ≫ q = f ≫ β) (hroot : ∀ i : T, (t i).hom ≫ α i = r) :
    StageState d c t α q r β ⊥ where
  f' := c.isoBot.hom ≫ r
  w₁ := by
    change c.F.map (𝟙 (⊥ : O)) ≫ (c.isoBot.hom ≫ r) = c.isoBot.hom ≫ r
    rw [c.F.map_id, Category.id_comp]
  w₂ := by
    change (c.isoBot.hom ≫ r) ≫ q = c.incl.app ⊥ ≫ β
    have hfac : c.isoBot.hom ≫ f = c.incl.app ⊥ := by
      symm
      simpa only [c.isoBot.hom_inv_id_assoc] using
        congrArg (fun z => c.isoBot.hom ≫ z) c.fac
    rw [Category.assoc, hrq, ← Category.assoc, hfac]
  subcomplex i := by
    apply (cancel_epi (t i).complex.isoBot.inv).1
    change (t i).complex.isoBot.inv ≫
      ((t i).comparison.app ⊥ ≫ (c.isoBot.hom ≫ r)) =
        (t i).complex.isoBot.inv ≫ ((t i).complex.incl.app ⊥ ≫ α i)
    rw [← Category.assoc, (t i).comparison_bot, ← Category.assoc,
      c.isoBot.inv_hom_id, Category.id_comp, ← Category.assoc, (t i).complex.fac]
    exact (hroot i).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original successor extends all prescribed subcomplex maps at that same successor. -/
def successorState (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) :
    StageState d c t α q r β (Order.succ j) where
  f' := successorLift d c h t α q r β hq hcells j hj s
  w₁ := by
    rw [← homOfLE_comp bot_le (Order.le_succ j), c.F.map_comp, Category.assoc,
      successorLift_stage, s.w₁]
  w₂ := by
    apply (c.attachCells j hj).hom_ext
    · rw [← Category.assoc, successorLift_stage]
      change s.f' ≫ q = c.F.map (homOfLE (Order.le_succ j)) ≫ c.incl.app (Order.succ j) ≫ β
      rw [← Category.assoc, (Cocone.mk Y c.incl).w]
      exact s.w₂
    · intro k
      rw [← Category.assoc, successorLift_cell,
        completionCellImage_right d c t α q r β hq hcells hα]
  subcomplex i := by
    apply ((t i).complex.attachCells j hj).hom_ext
    · calc
        _ = ((t i).complex.F.map (homOfLE (Order.le_succ j)) ≫
            (t i).comparison.app (Order.succ j)) ≫
              successorLift d c h t α q r β hq hcells j hj s := (Category.assoc _ _ _).symm
        _ = ((t i).comparison.app j ≫ c.F.map (homOfLE (Order.le_succ j))) ≫
              successorLift d c h t α q r β hq hcells j hj s :=
                congrArg (fun z => z ≫ successorLift d c h t α q r β hq hcells j hj s)
                  ((t i).comparison.naturality (homOfLE (Order.le_succ j)))
        _ = (t i).comparison.app j ≫ s.f' := by rw [Category.assoc, successorLift_stage]
        _ = (t i).complex.incl.app j ≫ α i := s.subcomplex i
        _ = _ := by rw [← Category.assoc, (Cocone.mk (t i).endpoint (t i).complex.incl).w]
    · intro a
      calc
        _ = (((t i).complex.attachCells j hj).cell a ≫
            (t i).comparison.app (Order.succ j)) ≫
              successorLift d c h t α q r β hq hcells j hj s := (Category.assoc _ _ _).symm
        _ = (eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a)) ≫
            (c.attachCells j hj).cell ((t i).cellIndex j hj a)) ≫
              successorLift d c h t α q r β hq hcells j hj s :=
                congrArg (fun z => z ≫ successorLift d c h t α q r β hq hcells j hj s)
                  ((t i).cell_eq j hj a)
        _ = eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a)) ≫
            completionCellImage d c t α q r β hq j hj s ((t i).cellIndex j hj a) := by
              rw [Category.assoc, successorLift_cell]
        _ = _ := completionCellImage_family d c t α q r β hq hcells j hj s i a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each actual successor state restricts to the same original preceding state. -/
theorem successorState_restrict (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) :
    (stageFunctor d c t α q r β).map (homOfLE (Order.le_succ j)).op
      (successorState d c h t α q r β hq hcells hα j hj s) = s := by
  change stageMap d c t α q r β
    (successorState d c h t α q r β hq hcells hα j hj s)
      (homOfLE (Order.le_succ j)) = s
  ext
  exact successorLift_stage d c h t α q r β hq hcells j hj s

section OriginalLimit

variable {j : O} (hj : Order.IsSuccLimit j)
  (s : ((Set.principalSegIio j).monotone.functor.op ⋙ stageFunctor d c t α q r β).sections)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The same actual constrained family gives the original ordinary square family. -/
def ordinaryLimitFamily :
    ((Set.principalSegIio j).monotone.functor.op ⋙
      HasLiftingProperty.transfiniteComposition.sqFunctor (Cocone.mk Y c.incl) q
        (c.isoBot.hom ≫ r) β).sections where
  val a := (s.val a).toSqStruct
  property u := by
    exact congrArg StageState.toSqStruct (s.property u)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Both original continuous chains retain every subcomplex equation at an original limit. -/
def limitState : StageState d c t α q r β j where
  __ := HasLiftingProperty.transfiniteComposition.wellOrderInductionData.lift hj
    (ordinaryLimitFamily d c t α q r β s)
  subcomplex i := by
    apply ((t i).complex.F.isColimitOfIsWellOrderContinuous j hj).hom_ext
    intro a
    dsimp
    calc
      _ = ((t i).complex.F.map (homOfLE a.2.le) ≫ (t i).comparison.app j) ≫
          HasLiftingProperty.transfiniteComposition.wellOrderInductionData.liftHom hj
            (ordinaryLimitFamily d c t α q r β s) := (Category.assoc _ _ _).symm
      _ = ((t i).comparison.app a.1 ≫ c.F.map (homOfLE a.2.le)) ≫
          HasLiftingProperty.transfiniteComposition.wellOrderInductionData.liftHom hj
            (ordinaryLimitFamily d c t α q r β s) :=
              congrArg (fun z => z ≫
                HasLiftingProperty.transfiniteComposition.wellOrderInductionData.liftHom hj
                  (ordinaryLimitFamily d c t α q r β s))
                    ((t i).comparison.naturality (homOfLE a.2.le))
      _ = (t i).comparison.app a.1 ≫ (s.val (op a)).f' := by
        rw [Category.assoc,
          HasLiftingProperty.transfiniteComposition.wellOrderInductionData.liftHom_fac]
        rfl
      _ = (t i).complex.incl.app a.1 ≫ α i := (s.val (op a)).subcomplex i
      _ = _ := by rw [← Category.assoc, (Cocone.mk (t i).endpoint (t i).complex.incl).w]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual limit state restricts to every original supplied preceding state. -/
theorem limitState_restrict (a : O) (ha : a < j) :
    (stageFunctor d c t α q r β).map (homOfLE ha.le).op
      (limitState d c t α q r β hj s) = s.val (op ⟨a, ha⟩) := by
  change stageMap d c t α q r β (limitState d c t α q r β hj s)
    (homOfLE ha.le) = s.val (op ⟨a, ha⟩)
  ext
  exact HasLiftingProperty.transfiniteComposition.wellOrderInductionData.liftHom_fac hj
    (ordinaryLimitFamily d c t α q r β s) a ha

end OriginalLimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The full inverse-system induction data is constructed from the original cell lifts and
limits. -/
def familyInductionData (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β) :
    (stageFunctor d c t α q r β).WellOrderInductionData :=
  Functor.WellOrderInductionData.ofExists
    (fun j hj s => ⟨successorState d c h t α q r β hq hcells hα j hj s,
      successorState_restrict d c h t α q r β hq hcells hα j hj s⟩)
    (fun _j hj s => ⟨limitState d c t α q r β hj s,
      fun a ha => limitState_restrict d c t α q r β hj s a ha⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
/-- Actual original cell lifts produce one whole lift extending the compatible subcomplex family. -/
theorem existsFamilyLift (hq : d.I.rlp q) (hrq : r ≫ q = f ≫ β)
    (hroot : ∀ i : T, (t i).hom ≫ α i = r)
    (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (hcells : FamilyCellCompatible d c t α) :
    ∃ ℓ : Y ⟶ E, f ≫ ℓ = r ∧ ℓ ≫ q = β ∧ ∀ i : T, (t i).inclusion ≫ ℓ = α i := by
  let s := (familyInductionData d c h t α q r β hq hcells hα).sectionsMk
    (bottomState d c t α q r β hrq hroot)
  let z : Cocone c.F := Cocone.mk E
    { app j := (s.val (op j)).f'
      naturality j j' u := by
        have hu := congrArg (fun z : StageState d c t α q r β j => z.f') (s.property u.op)
        change c.F.map u ≫ (s.val (op j')).f' = (s.val (op j)).f' at hu
        simpa using hu }
  let ℓ := c.isColimit.desc z
  have hℓ (j : O) : c.incl.app j ≫ ℓ = (s.val (op j)).f' := c.isColimit.fac z j
  refine ⟨ℓ, ?_, ?_, ?_⟩
  · have hs := congrArg (fun z : StageState d c t α q r β ⊥ => z.f')
      ((familyInductionData d c h t α q r β hq hcells hα).sectionsMk_val_op_bot
        (bottomState d c t α q r β hrq hroot))
    change (s.val (op ⊥)).f' = c.isoBot.hom ≫ r at hs
    calc
      f ≫ ℓ = (c.isoBot.inv ≫ c.incl.app ⊥) ≫ ℓ := congrArg (fun z => z ≫ ℓ) c.fac.symm
      _ = c.isoBot.inv ≫ (c.incl.app ⊥ ≫ ℓ) := Category.assoc _ _ _
      _ = c.isoBot.inv ≫ (s.val (op ⊥)).f' := congrArg (fun z => c.isoBot.inv ≫ z) (hℓ ⊥)
      _ = c.isoBot.inv ≫ (c.isoBot.hom ≫ r) := congrArg (fun z => c.isoBot.inv ≫ z) hs
      _ = r := c.isoBot.inv_hom_id_assoc r
  · apply c.isColimit.hom_ext
    intro j
    rw [← Category.assoc, hℓ]
    exact (s.val (op j)).w₂
  · intro i
    apply (t i).complex.isColimit.hom_ext
    intro j
    rw [← Category.assoc, (t i).comparison_endpoint, Category.assoc, hℓ]
    exact (s.val (op j)).subcomplex i

end OriginalFamily

section OriginalInclusion

variable (t : CellularSubcomplex c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
/-- Every original subcomplex inclusion is a cofibration, derived by filling its missing
original I cells. -/
theorem inclusionCofibration : cofibrations C t.inclusion := by
  rw [← trivialFibrations_llp, ← d.I_rlp]
  intro E B q hq
  refine ⟨fun {α} {β} sq => ?_⟩
  let tf : PUnit.{w + 1} → CellularSubcomplex c := fun _ => t
  let af : ∀ i : PUnit.{w + 1}, (tf i).endpoint ⟶ E := fun _ => α
  have hrq : (t.hom ≫ α) ≫ q = f ≫ β := by
    rw [Category.assoc, sq.w, ← Category.assoc, t.fac]
  have hroot : ∀ i : PUnit.{w + 1}, (tf i).hom ≫ af i = t.hom ≫ α := fun _ => rfl
  have hα : ∀ i : PUnit.{w + 1}, af i ≫ q = (tf i).inclusion ≫ β := fun _ => sq.w
  have hcells : FamilyCellCompatible d c tf af := by
    intro j hj i i' a b e
    change t.cellIndex j hj a = t.cellIndex j hj b at e
    have hab : a = b := (t.cellIndex j hj).injective e
    subst b
    change familyCellImage d c tf af j hj i a =
      𝟙 _ ≫ familyCellImage d c tf af j hj i' a
    rw [Category.id_comp]
  obtain ⟨ℓ, _hℓroot, hℓq, hℓ⟩ :=
    existsFamilyLift d c h tf af q (t.hom ≫ α) β hq hrq hroot hα hcells
  exact CommSq.HasLift.mk' { l := ℓ, fac_left := hℓ PUnit.unit, fac_right := hℓq }

include h in
/-- Monicity of an original subcomplex inclusion follows from its proved cofibration. -/
theorem inclusionMono : Mono t.inclusion :=
  h.mono_of_cofibration t.inclusion (inclusionCofibration d c h t)

/-- The original subcomplex inclusion has its actual regular-mono presentation. -/
def inclusionRegularMono : RegularMono t.inclusion :=
  h.effectivePresentation t.inclusion (inclusionCofibration d c h t)

/-- The original inclusion equalizes its two actual original pushout legs. -/
def inclusionPushoutEqualizer :
    IsLimit (Fork.ofι t.inclusion (pushout.condition (f := t.inclusion) (g := t.inclusion))) :=
  h.originalPushoutEqualizer t.inclusion (inclusionCofibration d c h t)

end OriginalInclusion

end HomotopicalAlgebra.EffectiveCellularSubcomplexExtension

end EffectiveCellularFamilyResearchPromotion


section EffectiveCellularPrefixContainmentResearchPromotion

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra.EffectiveCellularSubcomplexExtension

namespace HomotopicalAlgebra.EffectiveCellularSubcomplexExtension

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)

omit [OrderBot O] [SuccOrder O] [WellFoundedLT O] in
/-- A nonmaximal prefix stage is an actual nonmaximal original stage. -/
theorem prefixNotMax {j : O} (a : Set.Iic j) (ha : ¬ IsMax a) : ¬ IsMax a.1 := by
  rw [not_isMax_iff] at ha ⊢
  obtain ⟨b, hab⟩ := ha
  exact ⟨b.1, hab⟩

omit [OrderBot O] [SuccOrder O] [WellFoundedLT O] in
/-- A genuine prefix cell occurs strictly before its original endpoint stage. -/
theorem prefixStage_lt_endpoint {j : O} (a : Set.Iic j) (ha : ¬ IsMax a) : a.1 < j := by
  rw [not_isMax_iff] at ha
  obtain ⟨b, hab⟩ := ha
  exact lt_of_lt_of_le hab b.2

omit [OrderBot O] [WellFoundedLT O] in
/-- The exact original successor equality supplies the sole attachment target transport. -/
theorem prefixSuccessorEq {j : O} (a : Set.Iic j) (ha : ¬ IsMax a) :
    (Order.succ a).1 = Order.succ a.1 := Set.Iic.coe_succ_of_not_isMax ha

/-- The original closed-prefix composition retains its original root X and actual endpoint. -/
def prefixShape (j : O) :
    TransfiniteCompositionOfShape (Set.Iic j)
      (c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) where
  F := (Set.initialSegIic j).monotone.functor ⋙ c.F
  isoBot := c.isoBot
  isWellOrderContinuous := (c.toTransfiniteCompositionOfShape.iic j).isWellOrderContinuous
  incl := (c.toTransfiniteCompositionOfShape.iic j).incl
  isColimit := (c.toTransfiniteCompositionOfShape.iic j).isColimit
  fac := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Only the exact Iic successor target equality transports the actual original attaching arrow. -/
def prefixStepIso (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    Arrow.mk (c.F.map (homOfLE (Order.le_succ a.1))) ≅
      Arrow.mk ((prefixShape d c j).F.map (homOfLE (Order.le_succ a))) :=
  Arrow.isoMk (Iso.refl _)
    (c.F.mapIso (eqToIso (prefixSuccessorEq a ha).symm)) (by
      change 𝟙 _ ≫ c.F.map
        ((Set.initialSegIic j).monotone.functor.map (homOfLE (Order.le_succ a))) =
          c.F.map (homOfLE (Order.le_succ a.1)) ≫
            c.F.map (eqToHom (prefixSuccessorEq a ha).symm)
      rw [Category.id_comp, ← c.F.map_comp]
      congr 1)

/-- The actual original relative I complex restricts to its closed prefix with unchanged root. -/
def prefixComplex (j : O) :
    RelativeCellComplex.{w} (fun _ : Set.Iic j => d.I.homFamily)
      (c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) where
  __ := prefixShape d c j
  attachCells a ha := (c.attachCells a.1 (prefixNotMax a ha)).ofArrowIso (prefixStepIso d c j a ha)

/-- The prefix retains the exact original stage restriction. -/
theorem prefixComplex_functor (j : O) :
    (prefixComplex d c j).F = (Set.initialSegIic j).monotone.functor ⋙ c.F := rfl

/-- The original bottom isomorphism is retained literally. -/
theorem prefixComplex_isoBot (j : O) : (prefixComplex d c j).isoBot = c.isoBot := rfl

/-- Each actual prefix endpoint leg is the original original-stage map. -/
theorem prefixComplex_incl (j : O) (a : Set.Iic j) :
    (prefixComplex d c j).incl.app a = c.F.map (homOfLE a.2) := rfl

/-- Every original attaching source cofan is retained literally. -/
theorem prefixComplex_sourceCofan (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).cofan₁ =
      (c.attachCells a.1 (prefixNotMax a ha)).cofan₁ := rfl

/-- Every original attaching target cofan is retained literally. -/
theorem prefixComplex_targetCofan (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).cofan₂ =
      (c.attachCells a.1 (prefixNotMax a ha)).cofan₂ := rfl

/-- Each original generator label is retained literally at its same original stage. -/
theorem prefixComplex_label (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex d c j).attachCells a ha).π k =
      (c.attachCells a.1 (prefixNotMax a ha)).π k := rfl

/-- The original coproduct of generating arrows is retained literally. -/
theorem prefixComplex_attachingMap (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).m = (c.attachCells a.1 (prefixNotMax a ha)).m := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original attaching-domain map is retained at its exact original prefix stage. -/
theorem prefixComplex_boundary (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    boundary d (prefixComplex d c j) a ha k = boundary d c a.1 (prefixNotMax a ha) k := by
  change (c.attachCells a.1 (prefixNotMax a ha)).cofan₁.inj k ≫
    ((c.attachCells a.1 (prefixNotMax a ha)).g₁ ≫ 𝟙 _) =
      (c.attachCells a.1 (prefixNotMax a ha)).cofan₁.inj k ≫
        (c.attachCells a.1 (prefixNotMax a ha)).g₁
  rw [Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each actual prefix cell keeps the original cell map and exact successor target transport. -/
theorem prefixComplex_cell (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex d c j).attachCells a ha).cell k =
      (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫
        c.F.map (eqToHom (prefixSuccessorEq a ha).symm) := by
  change (c.attachCells a.1 (prefixNotMax a ha)).cofan₂.inj k ≫
    ((c.attachCells a.1 (prefixNotMax a ha)).g₂ ≫
      c.F.map (eqToHom (prefixSuccessorEq a ha).symm)) = _
  exact (Category.assoc _ _ _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A prefix occurrence includes by the exact original cell map to the actual original stage j. -/
theorem prefixComplex_cell_inclusion (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    (({ j := a, hj := ha, k := k } : (prefixComplex d c j).Cells)).ι =
      (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫
        c.F.map (homOfLE (Order.succ_le_of_lt (prefixStage_lt_endpoint a ha))) := by
  dsimp only [RelativeCellComplex.Cells.ι]
  rw [prefixComplex_cell, prefixComplex_incl, Category.assoc, ← c.F.map_comp]
  congr 1

variable (t : CellularSubcomplex c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original subcomplex restricts to a genuine subcomplex of the same original closed prefix. -/
def prefixSubcomplex (j : O) : CellularSubcomplex (prefixComplex d c j) where
  endpoint := t.complex.F.obj j
  hom := t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))
  inclusion := t.comparison.app j
  complex := prefixComplex d t.complex j
  comparison := Functor.whiskerLeft (Set.initialSegIic j).monotone.functor t.comparison
  comparison_bot := t.comparison_bot
  comparison_endpoint a := t.comparison.naturality (homOfLE a.2)
  cellIndex a ha := t.cellIndex a.1 (prefixNotMax a ha)
  label_eq a ha k := t.label_eq a.1 (prefixNotMax a ha) k
  cell_eq a ha k := by
    rw [prefixComplex_cell, prefixComplex_cell]
    change ((t.complex.attachCells a.1 (prefixNotMax a ha)).cell k ≫
        t.complex.F.map (eqToHom (prefixSuccessorEq a ha).symm)) ≫
          t.comparison.app (Order.succ a).1 =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (t.label_eq a.1 (prefixNotMax a ha) k)) ≫
        ((c.attachCells a.1 (prefixNotMax a ha)).cell (t.cellIndex a.1 (prefixNotMax a ha) k) ≫
          c.F.map (eqToHom (prefixSuccessorEq a ha).symm))
    rw [Category.assoc, t.comparison.naturality,
      ← Category.assoc, t.cell_eq, Category.assoc]

/-- The prefix subcomplex endpoint is exactly its original stage endpoint. -/
theorem prefixSubcomplex_endpoint (j : O) :
    (prefixSubcomplex d c t j).endpoint = t.complex.F.obj j := rfl

/-- The prefix inclusion is exactly the original natural comparison at that stage. -/
theorem prefixSubcomplex_inclusion (j : O) :
    (prefixSubcomplex d c t j).inclusion = t.comparison.app j := rfl

/-- The original occurrence embedding is retained literally in every prefix attachment. -/
theorem prefixSubcomplex_cellIndex (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    (prefixSubcomplex d c t j).cellIndex a ha = t.cellIndex a.1 (prefixNotMax a ha) := rfl

end HomotopicalAlgebra.EffectiveCellularSubcomplexExtension

namespace HomotopicalAlgebra.EffectiveCellularSubcomplexContainment

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (t u : CellularSubcomplex c)

/-- Containment is inclusion of the actual selected original occurrence supports. -/
def SupportLE : Prop := Set.range t.originalCell ⊆ Set.range u.originalCell

/-- Every original subcomplex contains its own exact original occurrences. -/
theorem supportRefl : SupportLE d c t t := Set.Subset.refl _

/-- Actual original occurrence support inclusion composes. -/
theorem supportTrans (v : CellularSubcomplex c) (H : SupportLE d c t u) (K : SupportLE d c u v) :
    SupportLE d c t v := fun _ ha => K (H ha)

/-- Original occurrence selection is injective, as retained by the original cell embeddings. -/
theorem originalCell_injective : Function.Injective t.originalCell := t.cellEmbedding.injective

/-- An actual support inclusion selects a cell occurrence from the original larger subcomplex. -/
def supportCell (H : SupportLE d c t u) (a : t.complex.Cells) : u.complex.Cells :=
  (H ⟨a, rfl⟩).choose

/-- Selection retains the exact original ambient occurrence. -/
theorem supportCell_original (H : SupportLE d c t u) (a : t.complex.Cells) :
    u.originalCell (supportCell d c t u H a) = t.originalCell a := (H ⟨a, rfl⟩).choose_spec

/-- Selection retains the actual original ordinal of the cell occurrence. -/
theorem supportCell_stage (H : SupportLE d c t u) (a : t.complex.Cells) :
    (supportCell d c t u H a).j = a.j :=
  congrArg (fun b : c.Cells => b.j) (supportCell_original d c t u H a)

/-- The support containment gives an actual injection of original selected occurrences. -/
def supportCellEmbedding (H : SupportLE d c t u) : t.complex.Cells ↪ u.complex.Cells where
  toFun := supportCell d c t u H
  inj' := by
    intro a b hab
    apply originalCell_injective d c t
    exact (supportCell_original d c t u H a).symm.trans
      ((congrArg u.originalCell hab).trans (supportCell_original d c t u H b))

/-- Matching original occurrences retain their original generating label. -/
theorem cellLabelEq (a : t.complex.Cells) (b : u.complex.Cells)
    (hab : u.originalCell b = t.originalCell a) : a.i = b.i :=
  (t.originalCell_label a).trans
    ((congrArg (fun z : c.Cells => z.i) hab).symm.trans (u.originalCell_label b).symm)

/-- Exact equality of original occurrences transports their actual ambient cell map. -/
theorem ambientCell_transport (a b : c.Cells) (e : a = b) :
    eqToHom (congrArg (fun z : c.Cells => z.i.1.right) e) ≫ b.ι = a.ι := by
  cases e
  simp

/-- The original matching cell map has its actual target in the larger original subcomplex. -/
def cellMapInto (a : t.complex.Cells) (b : u.complex.Cells)
    (hab : u.originalCell b = t.originalCell a) : a.i.1.right ⟶ u.endpoint :=
  eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (cellLabelEq d c t u a b hab)) ≫ b.ι

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original cell target map recovers the exact original ambient inclusion. -/
theorem cellMapInto_ambient (a : t.complex.Cells) (b : u.complex.Cells)
    (hab : u.originalCell b = t.originalCell a) :
    cellMapInto d c t u a b hab ≫ u.inclusion = a.ι ≫ t.inclusion := by
  dsimp only [cellMapInto]
  calc
    _ = eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (cellLabelEq d c t u a b hab)) ≫
        (b.ι ≫ u.inclusion) := Category.assoc _ _ _
    _ = eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (cellLabelEq d c t u a b hab)) ≫
        (eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (u.originalCell_label b)) ≫
          (u.originalCell b).ι) :=
            congrArg (fun z => eqToHom
              (congrArg (fun p : d.I.toSet => p.1.right) (cellLabelEq d c t u a b hab)) ≫ z)
                (u.originalCell_inclusion b)
    _ = eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (t.originalCell_label a)) ≫
        (eqToHom (congrArg (fun z : c.Cells => z.i.1.right) hab.symm) ≫
          (u.originalCell b).ι) := by simp only [← Category.assoc, eqToHom_trans]
    _ = eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (t.originalCell_label a)) ≫
        (t.originalCell a).ι := congrArg
          (fun z => eqToHom
            (congrArg (fun p : d.I.toSet => p.1.right) (t.originalCell_label a)) ≫ z)
            (ambientCell_transport d c (t.originalCell a) (u.originalCell b) hab.symm)
    _ = a.ι ≫ t.inclusion := (t.originalCell_inclusion a).symm

/-- Original attaching occurrences inject into the actual original full cell family. -/
def occurrenceEmbedding (j : O) (hj : ¬ IsMax j) : (c.attachCells j hj).ι ↪ c.Cells where
  toFun k := { j := j, hj := hj, k := k }
  inj' := by
    intro a b hab
    cases hab
    rfl

/-- Support containment supplies an original occurrence at the same original stage. -/
theorem existsStageCell (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) :
    ∃ a : (u.complex.attachCells j hj).ι, u.cellIndex j hj a = t.cellIndex j hj k := by
  let a : t.complex.Cells := { j := j, hj := hj, k := k }
  obtain ⟨b, hb⟩ := H ⟨a, rfl⟩
  rcases b with ⟨j', hj', k'⟩
  have hj'j : j' = j := congrArg (fun z : c.Cells => z.j) hb
  subst j'
  refine ⟨k', ?_⟩
  apply (occurrenceEmbedding d c j hj).injective
  exact hb

/-- The selected larger occurrence remains in its actual original attaching family. -/
def stageCell (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) : (u.complex.attachCells j hj).ι :=
  (existsStageCell d c t u H j hj k).choose

/-- The two original stage occurrences select precisely the same ambient cell. -/
theorem stageCell_original (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) :
    u.cellIndex j hj (stageCell d c t u H j hj k) = t.cellIndex j hj k :=
  (existsStageCell d c t u H j hj k).choose_spec

/-- Each original attaching-family map is an actual occurrence embedding. -/
def stageCellEmbedding (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j) :
    (t.complex.attachCells j hj).ι ↪ (u.complex.attachCells j hj).ι where
  toFun := stageCell d c t u H j hj
  inj' := by
    intro a b hab
    apply (t.cellIndex j hj).injective
    exact (stageCell_original d c t u H j hj a).symm.trans
      ((congrArg (u.cellIndex j hj) hab).trans (stageCell_original d c t u H j hj b))

/-- The stage occurrence embedding retains the actual original generator label. -/
theorem stageCell_label (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).π k =
      (u.complex.attachCells j hj).π (stageCell d c t u H j hj k) :=
  (t.label_eq j hj k).trans
    ((congrArg (c.attachCells j hj).π (stageCell_original d c t u H j hj k)).symm.trans
      (u.label_eq j hj (stageCell d c t u H j hj k)).symm)

/-- Support containment restricts to the genuine original closed-prefix subcomplexes. -/
theorem prefixSupportLE (H : SupportLE d c t u) (j : O) :
    SupportLE d (prefixComplex d c j) (prefixSubcomplex d c t j) (prefixSubcomplex d c u j) := by
  intro z hz
  obtain ⟨a, rfl⟩ := hz
  let k := stageCell d c t u H a.j.1 (prefixNotMax a.j a.hj) a.k
  let b : (prefixSubcomplex d c u j).complex.Cells := { j := a.j, hj := a.hj, k := k }
  refine ⟨b, ?_⟩
  exact congrArg
    (fun k : (c.attachCells a.j.1 (prefixNotMax a.j a.hj)).ι =>
      ({ j := a.j, hj := a.hj, k := k } : (prefixComplex d c j).Cells))
        (stageCell_original d c t u H a.j.1 (prefixNotMax a.j a.hj) a.k)

/-- Exact equality of stage occurrences transports their actual original target-stage map. -/
theorem ambientStageCell_transport (j : O) (hj : ¬ IsMax j)
    (a b : (c.attachCells j hj).ι) (e : a = b) :
    eqToHom (congrArg (fun k => ((c.attachCells j hj).π k).1.right) e) ≫
      (c.attachCells j hj).cell b = (c.attachCells j hj).cell a := by
  cases e
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The two matched original cell maps have precisely the same original target-stage comparison. -/
theorem stageCellMap_ambient (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).cell k ≫ t.comparison.app (Order.succ j) =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (stageCell_label d c t u H j hj k)) ≫
        ((u.complex.attachCells j hj).cell (stageCell d c t u H j hj k) ≫
          u.comparison.app (Order.succ j)) := by
  calc
    _ = eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (t.label_eq j hj k)) ≫
        (c.attachCells j hj).cell (t.cellIndex j hj k) := t.cell_eq j hj k
    _ = eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (t.label_eq j hj k)) ≫
        (eqToHom (congrArg (fun a => ((c.attachCells j hj).π a).1.right)
          (stageCell_original d c t u H j hj k).symm) ≫
            (c.attachCells j hj).cell (u.cellIndex j hj (stageCell d c t u H j hj k))) :=
              congrArg (fun z =>
                eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (t.label_eq j hj k)) ≫ z)
                (ambientStageCell_transport d c j hj _ _
                  (stageCell_original d c t u H j hj k).symm).symm
    _ = eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (stageCell_label d c t u H j hj k)) ≫
        (eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
          (u.label_eq j hj (stageCell d c t u H j hj k))) ≫
            (c.attachCells j hj).cell (u.cellIndex j hj (stageCell d c t u H j hj k))) := by
              simp only [← Category.assoc, eqToHom_trans]
    _ = _ := congrArg
      (fun z => eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
        (stageCell_label d c t u H j hj k)) ≫ z)
        (u.cell_eq j hj (stageCell d c t u H j hj k)).symm

variable (h : EffectiveCofibrations C)

include h in
/-- Actual support containment constructs an endpoint map from the original root and cells. -/
theorem existsContainmentMap (H : SupportLE d c t u) :
    ∃ m : t.endpoint ⟶ u.endpoint, m ≫ u.inclusion = t.inclusion := by
  let _ : Mono u.inclusion := inclusionMono d c h u
  exact t.complex.exists_lift_through_mono t.inclusion u.inclusion u.hom
    (u.fac.trans t.fac.symm)
    (fun a => cellMapInto d c t u a (supportCell d c t u H a) (supportCell_original d c t u H a))
    (fun a => cellMapInto_ambient d c t u a (supportCell d c t u H a)
      (supportCell_original d c t u H a))

/-- The actual map into the larger original subcomplex is chosen from the proved construction. -/
def containmentMap (H : SupportLE d c t u) : t.endpoint ⟶ u.endpoint :=
  (existsContainmentMap d c t u h H).choose

/-- The actual endpoint map retains its original ambient endpoint comparison. -/
theorem containmentMap_ambient (H : SupportLE d c t u) :
    containmentMap d c t u h H ≫ u.inclusion = t.inclusion :=
  (existsContainmentMap d c t u h H).choose_spec

/-- The map preserves the exact original root X. -/
theorem containmentMap_root (H : SupportLE d c t u) :
    t.hom ≫ containmentMap d c t u h H = u.hom := by
  let _ : Mono u.inclusion := inclusionMono d c h u
  apply (cancel_mono u.inclusion).1
  rw [Category.assoc, containmentMap_ambient, t.fac, u.fac]

/-- Monicity determines every original endpoint comparison uniquely. -/
theorem containmentMap_unique (H : SupportLE d c t u) (m : t.endpoint ⟶ u.endpoint)
    (hm : m ≫ u.inclusion = t.inclusion) : m = containmentMap d c t u h H := by
  let _ : Mono u.inclusion := inclusionMono d c h u
  exact (cancel_mono u.inclusion).1 (hm.trans (containmentMap_ambient d c t u h H).symm)

/-- Every matching original cell map is preserved by the actual endpoint comparison. -/
theorem containmentMap_cell (H : SupportLE d c t u) (a : t.complex.Cells) (b : u.complex.Cells)
    (hab : u.originalCell b = t.originalCell a) :
    a.ι ≫ containmentMap d c t u h H = cellMapInto d c t u a b hab := by
  let _ : Mono u.inclusion := inclusionMono d c h u
  apply (cancel_mono u.inclusion).1
  rw [Category.assoc, containmentMap_ambient]
  exact (cellMapInto_ambient d c t u a b hab).symm

include h in
/-- The proved prefix inclusion gives monicity of every original stage comparison. -/
theorem stageComparisonMono (v : CellularSubcomplex c) (j : O) : Mono (v.comparison.app j) := by
  simpa only [prefixSubcomplex_endpoint, prefixSubcomplex_inclusion] using
    inclusionMono d (prefixComplex d c j) h (prefixSubcomplex d c v j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual endpoint containment of exact prefixes supplies every original stage map. -/
def stageMap (H : SupportLE d c t u) (j : O) : t.complex.F.obj j ⟶ u.complex.F.obj j :=
  containmentMap d (prefixComplex d c j) (prefixSubcomplex d c t j) (prefixSubcomplex d c u j) h
    (prefixSupportLE d c t u H j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original stage map retains its original ambient natural comparison. -/
theorem stageMap_ambient (H : SupportLE d c t u) (j : O) :
    stageMap d c t u h H j ≫ u.comparison.app j = t.comparison.app j :=
  containmentMap_ambient d (prefixComplex d c j)
    (prefixSubcomplex d c t j) (prefixSubcomplex d c u j) h (prefixSupportLE d c t u H j)

/-- Every original stage comparison is determined uniquely by its ambient comparison. -/
theorem stageMap_unique (H : SupportLE d c t u) (j : O) (m : t.complex.F.obj j ⟶ u.complex.F.obj j)
    (hm : m ≫ u.comparison.app j = t.comparison.app j) : m = stageMap d c t u h H j := by
  let _ : Mono (u.comparison.app j) := stageComparisonMono d c h u j
  exact (cancel_mono (u.comparison.app j)).1 (hm.trans (stageMap_ambient d c t u h H j).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original selected cell keeps its exact original same-stage label and target map. -/
theorem stageMap_cell (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).cell k ≫ stageMap d c t u h H (Order.succ j) =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (stageCell_label d c t u H j hj k)) ≫
        (u.complex.attachCells j hj).cell (stageCell d c t u H j hj k) := by
  let _ : Mono (u.comparison.app (Order.succ j)) := stageComparisonMono d c h u (Order.succ j)
  apply (cancel_mono (u.comparison.app (Order.succ j))).1
  rw [Category.assoc, stageMap_ambient]
  simpa only [Category.assoc] using stageCellMap_ambient d c t u H j hj k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original stage maps commute with every original order morphism. -/
theorem stageMap_naturality (H : SupportLE d c t u) {j k : O} (a : j ⟶ k) :
    t.complex.F.map a ≫ stageMap d c t u h H k =
      stageMap d c t u h H j ≫ u.complex.F.map a := by
  let _ : Mono (u.comparison.app k) := stageComparisonMono d c h u k
  apply (cancel_mono (u.comparison.app k)).1
  rw [Category.assoc, stageMap_ambient, Category.assoc, u.comparison.naturality,
    ← Category.assoc, stageMap_ambient]
  exact t.comparison.naturality a

/-- The actual whole natural transformation is assembled on the unchanged original ordinal. -/
def comparison (H : SupportLE d c t u) : t.complex.F ⟶ u.complex.F where
  app j := stageMap d c t u h H j
  naturality _ _ a := stageMap_naturality d c t u h H a

/-- The whole comparison recovers the original ambient natural transformation. -/
theorem comparison_ambient (H : SupportLE d c t u) :
    comparison d c t u h H ≫ u.comparison = t.comparison := by
  ext j
  exact stageMap_ambient d c t u h H j

/-- All actual original source stages retain the original endpoint cocone maps. -/
theorem comparison_endpoint (H : SupportLE d c t u) (j : O) :
    t.complex.incl.app j ≫ containmentMap d c t u h H =
      (comparison d c t u h H).app j ≫ u.complex.incl.app j := by
  change t.complex.incl.app j ≫ containmentMap d c t u h H =
    stageMap d c t u h H j ≫ u.complex.incl.app j
  let _ : Mono u.inclusion := inclusionMono d c h u
  apply (cancel_mono u.inclusion).1
  rw [Category.assoc, containmentMap_ambient, t.comparison_endpoint,
    Category.assoc, u.comparison_endpoint, ← Category.assoc, stageMap_ambient]

/-- The actual bottom comparison preserves the original root isomorphisms. -/
theorem comparison_bot (H : SupportLE d c t u) :
    t.complex.isoBot.inv ≫ (comparison d c t u h H).app ⊥ = u.complex.isoBot.inv := by
  change t.complex.isoBot.inv ≫ stageMap d c t u h H ⊥ = u.complex.isoBot.inv
  let _ : Mono (u.comparison.app ⊥) := stageComparisonMono d c h u ⊥
  apply (cancel_mono (u.comparison.app ⊥)).1
  rw [Category.assoc, stageMap_ambient, t.comparison_bot, u.comparison_bot]

/-- Every actual full stage comparison is determined uniquely by its original ambient map. -/
theorem comparison_unique (H : SupportLE d c t u) (a : t.complex.F ⟶ u.complex.F)
    (ha : a ≫ u.comparison = t.comparison) : a = comparison d c t u h H := by
  ext j
  exact stageMap_unique d c t u h H j (a.app j) (NatTrans.congr_app ha j)

/-- Containment presents the original t as a genuine original subcomplex of the original u. -/
def asSubcomplex (H : SupportLE d c t u) : CellularSubcomplex u.complex where
  endpoint := t.endpoint
  hom := t.hom
  inclusion := containmentMap d c t u h H
  complex := t.complex
  comparison := comparison d c t u h H
  comparison_bot := comparison_bot d c t u h H
  comparison_endpoint j := comparison_endpoint d c t u h H j
  cellIndex j hj := stageCellEmbedding d c t u H j hj
  label_eq j hj k := stageCell_label d c t u H j hj k
  cell_eq j hj k := stageMap_cell d c t u h H j hj k

/-- The containment presentation retains the exact original smaller complex. -/
theorem asSubcomplex_complex (H : SupportLE d c t u) :
    (asSubcomplex d c t u h H).complex = t.complex := rfl

/-- Its original inclusion is exactly the actual constructed containment map. -/
theorem asSubcomplex_inclusion (H : SupportLE d c t u) :
    (asSubcomplex d c t u h H).inclusion = containmentMap d c t u h H := rfl

/-- Its original stage comparison is exactly the constructed whole natural transformation. -/
theorem asSubcomplex_comparison (H : SupportLE d c t u) :
    (asSubcomplex d c t u h H).comparison = comparison d c t u h H := rfl

/-- The actual relative inclusion is a cofibration because this is a genuine original subcomplex. -/
theorem containmentMap_cofibration (H : SupportLE d c t u) :
    cofibrations C (containmentMap d c t u h H) :=
  inclusionCofibration d u.complex h (asSubcomplex d c t u h H)

/-- The proved original containment cofibration is an actual monomorphism. -/
theorem containmentMap_mono (H : SupportLE d c t u) : Mono (containmentMap d c t u h H) :=
  h.mono_of_cofibration _ (containmentMap_cofibration d c t u h H)

/-- The proved original containment cofibration retains its regular-mono presentation. -/
def containmentMapRegularMono (H : SupportLE d c t u) : RegularMono (containmentMap d c t u h H) :=
  h.effectivePresentation _ (containmentMap_cofibration d c t u h H)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original stage containment is a cofibration of genuine original prefix subcomplexes. -/
theorem stageMap_cofibration (H : SupportLE d c t u) (j : O) :
    cofibrations C (stageMap d c t u h H j) :=
  containmentMap_cofibration d (prefixComplex d c j)
    (prefixSubcomplex d c t j) (prefixSubcomplex d c u j) h (prefixSupportLE d c t u H j)

/-- The original stage containment is an actual monomorphism. -/
theorem stageMap_mono (H : SupportLE d c t u) (j : O) : Mono (stageMap d c t u h H j) :=
  h.mono_of_cofibration _ (stageMap_cofibration d c t u h H j)

/-- The original stage containment retains its actual regular-mono presentation. -/
def stageMapRegularMono (H : SupportLE d c t u) (j : O) : RegularMono (stageMap d c t u h H j) :=
  h.effectivePresentation _ (stageMap_cofibration d c t u h H j)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every exact prefix containment retains the original root map to that original stage. -/
theorem stageMap_root (H : SupportLE d c t u) (j : O) :
    (t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫
      stageMap d c t u h H j =
        u.complex.isoBot.inv ≫ u.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j)) :=
  containmentMap_root d (prefixComplex d c j)
    (prefixSubcomplex d c t j) (prefixSubcomplex d c u j) h (prefixSupportLE d c t u H j)

/-- An original support self-inclusion gives precisely the original identity map. -/
theorem containmentMap_refl (H : SupportLE d c t t) : containmentMap d c t t h H = 𝟙 t.endpoint :=
  (containmentMap_unique d c t t h H (𝟙 t.endpoint) (Category.id_comp _)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Original endpoint containment comparisons compose along original support inclusion. -/
theorem containmentMap_comp (v : CellularSubcomplex c) (H : SupportLE d c t u)
    (K : SupportLE d c u v) :
    containmentMap d c t u h H ≫ containmentMap d c u v h K =
      containmentMap d c t v h (supportTrans d c t u v H K) := by
  apply containmentMap_unique d c t v h (supportTrans d c t u v H K)
  rw [Category.assoc, containmentMap_ambient, containmentMap_ambient]

/-- Original stage self-containment is precisely the original stage identity. -/
theorem stageMap_refl (H : SupportLE d c t t) (j : O) :
    stageMap d c t t h H j = 𝟙 (t.complex.F.obj j) :=
  (stageMap_unique d c t t h H j (𝟙 _) (Category.id_comp _)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Containment comparisons compose at every original stage. -/
theorem stageMap_comp (v : CellularSubcomplex c) (H : SupportLE d c t u) (K : SupportLE d c u v)
    (j : O) :
    stageMap d c t u h H j ≫ stageMap d c u v h K j =
      stageMap d c t v h (supportTrans d c t u v H K) j := by
  apply stageMap_unique d c t v h (supportTrans d c t u v H K) j
  rw [Category.assoc, stageMap_ambient, stageMap_ambient]

/-- The whole comparison of an original support with itself is its exact natural identity. -/
theorem comparison_refl (H : SupportLE d c t t) : comparison d c t t h H = 𝟙 t.complex.F := by
  ext j
  exact stageMap_refl d c t h H j

/-- The whole original natural comparisons compose on the unchanged original ordinal. -/
theorem comparison_comp (v : CellularSubcomplex c) (H : SupportLE d c t u) (K : SupportLE d c u v) :
    comparison d c t u h H ≫ comparison d c u v h K =
      comparison d c t v h (supportTrans d c t u v H K) := by
  ext j
  exact stageMap_comp d c t u h v H K j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Equal original supports give inverse actual endpoint comparisons. -/
def endpointIso (e : Set.range t.originalCell = Set.range u.originalCell) :
    t.endpoint ≅ u.endpoint where
  hom := containmentMap d c t u h e.le
  inv := containmentMap d c u t h e.ge
  hom_inv_id := by
    let _ : Mono t.inclusion := inclusionMono d c h t
    apply (cancel_mono t.inclusion).1
    rw [Category.assoc, containmentMap_ambient, containmentMap_ambient, Category.id_comp]
  inv_hom_id := by
    let _ : Mono u.inclusion := inclusionMono d c h u
    apply (cancel_mono u.inclusion).1
    rw [Category.assoc, containmentMap_ambient, containmentMap_ambient, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Equal original supports give inverse actual comparisons at every original stage. -/
def stageIso (e : Set.range t.originalCell = Set.range u.originalCell) (j : O) :
    t.complex.F.obj j ≅ u.complex.F.obj j where
  hom := stageMap d c t u h e.le j
  inv := stageMap d c u t h e.ge j
  hom_inv_id := by
    let _ : Mono (t.comparison.app j) := stageComparisonMono d c h t j
    apply (cancel_mono (t.comparison.app j)).1
    rw [Category.assoc, stageMap_ambient, stageMap_ambient, Category.id_comp]
  inv_hom_id := by
    let _ : Mono (u.comparison.app j) := stageComparisonMono d c h u j
    apply (cancel_mono (u.comparison.app j)).1
    rw [Category.assoc, stageMap_ambient, stageMap_ambient, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Equal original supports retain the actual whole original stage comparison isomorphism. -/
def comparisonIso (e : Set.range t.originalCell = Set.range u.originalCell) :
    t.complex.F ≅ u.complex.F :=
  NatIso.ofComponents (fun j => stageIso d c t u h e j)
    (fun a => stageMap_naturality d c t u h e.le a)

/-- The endpoint isomorphism preserves the exact original root. -/
theorem endpointIso_root (e : Set.range t.originalCell = Set.range u.originalCell) :
    t.hom ≫ (endpointIso d c t u h e).hom = u.hom :=
  containmentMap_root d c t u h e.le

/-- The endpoint isomorphism preserves the exact original ambient endpoint inclusion. -/
theorem endpointIso_ambient (e : Set.range t.originalCell = Set.range u.originalCell) :
    (endpointIso d c t u h e).hom ≫ u.inclusion = t.inclusion :=
  containmentMap_ambient d c t u h e.le

/-- The stage isomorphisms preserve every original ambient stage comparison. -/
theorem stageIso_ambient (e : Set.range t.originalCell = Set.range u.originalCell) (j : O) :
    (stageIso d c t u h e j).hom ≫ u.comparison.app j = t.comparison.app j :=
  stageMap_ambient d c t u h e.le j

/-- The whole original comparison isomorphism preserves the actual ambient natural map. -/
theorem comparisonIso_ambient (e : Set.range t.originalCell = Set.range u.originalCell) :
    (comparisonIso d c t u h e).hom ≫ u.comparison = t.comparison :=
  comparison_ambient d c t u h e.le

/-- The actual endpoint and stage isomorphisms commute with every original endpoint cocone leg. -/
theorem isomorphism_endpoint (e : Set.range t.originalCell = Set.range u.originalCell) (j : O) :
    t.complex.incl.app j ≫ (endpointIso d c t u h e).hom =
      (stageIso d c t u h e j).hom ≫ u.complex.incl.app j :=
  comparison_endpoint d c t u h e.le j

/-- The endpoint isomorphism retains each actual matched original generator codomain map. -/
theorem endpointIso_cell (e : Set.range t.originalCell = Set.range u.originalCell)
    (a : t.complex.Cells) (b : u.complex.Cells) (hab : u.originalCell b = t.originalCell a) :
    a.ι ≫ (endpointIso d c t u h e).hom = cellMapInto d c t u a b hab :=
  containmentMap_cell d c t u h e.le a b hab

/-- The stage isomorphism retains the exact original stage root. -/
theorem stageIso_root (e : Set.range t.originalCell = Set.range u.originalCell) (j : O) :
    (t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫
      (stageIso d c t u h e j).hom =
        u.complex.isoBot.inv ≫ u.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j)) :=
  stageMap_root d c t u h e.le j

/-- The stage isomorphism retains the actual original selected cell and its original generator. -/
theorem stageIso_cell (e : Set.range t.originalCell = Set.range u.originalCell)
    (j : O) (hj : ¬ IsMax j) (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).cell k ≫ (stageIso d c t u h e (Order.succ j)).hom =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (stageCell_label d c t u e.le j hj k)) ≫
        (u.complex.attachCells j hj).cell (stageCell d c t u e.le j hj k) :=
  stageMap_cell d c t u h e.le j hj k

end HomotopicalAlgebra.EffectiveCellularSubcomplexContainment

end EffectiveCellularPrefixContainmentResearchPromotion


section EffectiveCellularUnionResearchPromotion

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.EffectiveCellularUnion

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  {c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f}
  {I : Type w} (t : I → CellularSubcomplex c)

/-- A cut is an original stage, or the original endpoint. -/
def before (cut : Option O) (a : c.Cells) : Prop :=
  match cut with
  | none => True
  | some j => a.j < j

/-- The object at an unchanged original stage or original endpoint. -/
abbrev ambient (cut : Option O) : C :=
  match cut with
  | none => Y
  | some j => c.F.obj j

/-- The same original root arrow at every cut. -/
def ambientRoot (cut : Option O) : X ⟶ ambient (c := c) cut :=
  match cut with
  | none => f
  | some j => c.rootAtStage j

/-- The original cell's actual map at its chosen later cut. -/
def ambientCell (a : c.Cells) (cut : Option O) (ha : before cut a) :
    a.i.1.right ⟶ ambient (c := c) cut :=
  match cut with
  | none => a.ι
  | some j => a.toStage j ha

private theorem ambientCell_congr (a b : c.Cells) (e : a = b)
    (cut : Option O) (ha : before cut a) (hb : before cut b) :
    ambientCell a cut ha =
      eqToHom (congrArg (fun z : c.Cells => z.i.1.right) e) ≫ ambientCell b cut hb := by
  cases e
  rw [eqToHom_refl, Category.id_comp]

/-- Every supplied subcomplex keeps its actual endpoint or stage object. -/
abbrev piece (i : I) (cut : Option O) : C :=
  match cut with
  | none => (t i).endpoint
  | some j => (t i).complex.F.obj j

/-- The original root into the supplied actual subcomplex piece. -/
def pieceRoot (i : I) (cut : Option O) : X ⟶ piece t i cut :=
  match cut with
  | none => (t i).hom
  | some j => (t i).complex.rootAtStage j

/-- The supplied actual whole comparison at each cut. -/
abbrev pieceComparison (i : I) (cut : Option O) :
    piece t i cut ⟶ ambient (c := c) cut :=
  match cut with
  | none => (t i).inclusion
  | some j => (t i).comparison.app j

/-- The cell map is transported only to the same original generator codomain. -/
def pieceCell (i : I) (a : (t i).complex.Cells) (cut : Option O)
    (ha : before cut ((t i).originalCell a)) :
    ((t i).originalCell a).i.1.right ⟶ piece t i cut :=
  match cut with
  | none => (t i).originalCellTarget a
  | some j => (t i).originalCellAtStage a j ha

@[reassoc]
theorem pieceRoot_comparison (i : I) (cut : Option O) :
    pieceRoot t i cut ≫ pieceComparison t i cut = ambientRoot (c := c) cut := by
  cases cut with
  | none => exact (t i).fac
  | some j => exact (t i).rootAtStage_comparison j

@[reassoc]
theorem pieceCell_comparison (i : I) (a : (t i).complex.Cells) (cut : Option O)
    (ha : before cut ((t i).originalCell a)) :
    pieceCell t i a cut ha ≫ pieceComparison t i cut =
      ambientCell ((t i).originalCell a) cut ha := by
  cases cut with
  | none => exact (t i).originalCellTarget_inclusion a
  | some j => exact (t i).originalCellAtStage_comparison a j ha

/-- Original stages lie below later original stages and the original endpoint. -/
abbrev CutLE (a b : Option O) : Prop :=
  match a, b with
  | none, none => True
  | none, some _ => False
  | some _, none => True
  | some j, some k => j ≤ k

theorem before_mono {a b : Option O} (hab : CutLE a b) {z : c.Cells}
    (hz : before a z) : before b z := by
  cases a with
  | none =>
    cases b with
    | none => trivial
    | some k => exact False.elim hab
  | some j =>
    cases b with
    | none => trivial
    | some k => exact hz.trans_le hab

/-- The same original piece transition, including its actual endpoint cocone. -/
abbrev pieceMap (i : I) (a b : Option O) (hab : CutLE a b) :
    piece t i a ⟶ piece t i b :=
  match a, b with
  | none, none => 𝟙 (t i).endpoint
  | none, some _ => False.elim hab
  | some j, none => (t i).complex.incl.app j
  | some _j, some _k => (t i).complex.F.map (homOfLE hab)

/-- The literal original ambient transition or original endpoint leg. -/
def ambientMap (a b : Option O) (hab : CutLE a b) :
    ambient (c := c) a ⟶ ambient (c := c) b :=
  match a, b with
  | none, none => 𝟙 Y
  | none, some _ => False.elim hab
  | some j, none => c.incl.app j
  | some _j, some _k => c.F.map (homOfLE hab)

@[reassoc]
theorem pieceRoot_map (i : I) (a b : Option O) (hab : CutLE a b) :
    pieceRoot t i a ≫ pieceMap t i a b hab = pieceRoot t i b := by
  cases a with
  | none =>
    cases b with
    | none =>
      change (t i).hom ≫ 𝟙 (t i).endpoint = (t i).hom
      exact Category.comp_id _
    | some k => exact False.elim hab
  | some j =>
    cases b with
    | none => exact (t i).complex.rootAtStage_incl j
    | some k => exact (t i).complex.rootAtStage_map (homOfLE hab)

@[reassoc]
theorem pieceCell_map (i : I) (z : (t i).complex.Cells) (a b : Option O)
    (hab : CutLE a b) (hz : before a ((t i).originalCell z)) :
    pieceCell t i z a hz ≫ pieceMap t i a b hab =
      pieceCell t i z b (before_mono hab hz) := by
  cases a with
  | none =>
    cases b with
    | none =>
      change (t i).originalCellTarget z ≫ 𝟙 (t i).endpoint = (t i).originalCellTarget z
      exact Category.comp_id _
    | some k => exact False.elim hab
  | some j =>
    cases b with
    | none => exact (t i).originalCellAtStage_incl z j hz
    | some k => exact (t i).originalCellAtStage_map z hz (homOfLE hab)

@[reassoc]
theorem pieceMap_comparison (i : I) (a b : Option O) (hab : CutLE a b) :
    pieceMap t i a b hab ≫ pieceComparison t i b =
      pieceComparison t i a ≫ ambientMap (c := c) a b hab := by
  cases a with
  | none =>
    cases b with
    | none =>
      change 𝟙 (t i).endpoint ≫ (t i).inclusion = (t i).inclusion ≫ 𝟙 Y
      rw [Category.id_comp, Category.comp_id]
    | some k => exact False.elim hab
  | some j =>
    cases b with
    | none => exact (t i).comparison_endpoint j
    | some k => exact (t i).comparison.naturality (homOfLE hab)

@[reassoc]
theorem ambientRoot_map (a b : Option O) (hab : CutLE a b) :
    ambientRoot (c := c) a ≫ ambientMap (c := c) a b hab = ambientRoot (c := c) b := by
  cases a with
  | none =>
    cases b with
    | none =>
      change f ≫ 𝟙 Y = f
      exact Category.comp_id _
    | some k => exact False.elim hab
  | some j =>
    cases b with
    | none => exact c.rootAtStage_incl j
    | some k => exact c.rootAtStage_map (homOfLE hab)

/-- A relation identifies two actual selected occurrences of the same
original cell. It does not identify different original cells. -/
structure SharedCell (cut : Option O) where
  /-- The index of the first effective subcomplex containing this shared original cell. -/
  left : I
  /-- The index of the second effective subcomplex containing this shared original cell. -/
  right : I
  /-- The selected cell occurrence in the first effective subcomplex. -/
  leftCell : (t left).complex.Cells
  /-- The selected cell occurrence in the second effective subcomplex. -/
  rightCell : (t right).complex.Cells
  same : (t left).originalCell leftCell = (t right).originalCell rightCell
  leftBefore : before cut ((t left).originalCell leftCell)
  rightBefore : before cut ((t right).originalCell rightCell)

/-- Only the same root and the same selected original cells are glued. -/
def shape (cut : Option O) : MultispanShape.{w, w} where
  L := I ⊕ SharedCell t cut
  R := Option I
  fst a := match a with
    | Sum.inl _ => none
    | Sum.inr a => some a.left
  snd a := match a with
    | Sum.inl i => some i
    | Sum.inr a => some a.right

/-- The literal original root and cell maps form the actual gluing diagram. -/
def index (cut : Option O) : MultispanIndex (shape t cut) C where
  left a := match a with
    | Sum.inl _ => X
    | Sum.inr a => ((t a.left).originalCell a.leftCell).i.1.right
  right i := match i with
    | none => X
    | some i => piece t i cut
  fst a := match a with
    | Sum.inl _ => 𝟙 X
    | Sum.inr a => pieceCell t a.left a.leftCell cut a.leftBefore
  snd a := match a with
    | Sum.inl i => pieceRoot t i cut
    | Sum.inr a =>
      eqToHom (congrArg (fun z : c.Cells => z.i.1.right) a.same) ≫
        pieceCell t a.right a.rightCell cut a.rightBefore

variable [HasColimitsOfSize.{w, w} C]

/-- This actual colimit exists from the original I coproduct dictionary and
the original finite coequalizers, including an empty family of subcomplexes. -/
def obj (cut : Option O) : C := multicoequalizer (index t cut)

/-- The unchanged root enters the actual union piece. -/
def root (cut : Option O) : X ⟶ obj t cut := Multicoequalizer.π (index t cut) none

/-- Each supplied piece has its actual original union colimit map. -/
def inclusion (i : I) (cut : Option O) : piece t i cut ⟶ obj t cut :=
  Multicoequalizer.π (index t cut) (some i)

@[reassoc]
theorem pieceRoot_inclusion (i : I) (cut : Option O) :
    pieceRoot t i cut ≫ inclusion t i cut = root t cut := by
  exact (Category.id_comp _).symm.trans
    (Multicoequalizer.condition (index t cut) (Sum.inl i)) |>.symm

/-- Every original shared-cell relation holds at the actual union object. -/
@[reassoc]
theorem sharedCell_inclusion (cut : Option O) (a : SharedCell t cut) :
    pieceCell t a.left a.leftCell cut a.leftBefore ≫ inclusion t a.left cut =
      eqToHom (congrArg (fun z : c.Cells => z.i.1.right) a.same) ≫
        pieceCell t a.right a.rightCell cut a.rightBefore ≫ inclusion t a.right cut := by
  simpa only [Category.assoc] using
    (show pieceCell t a.left a.leftCell cut a.leftBefore ≫ inclusion t a.left cut =
      (eqToHom (congrArg (fun z : c.Cells => z.i.1.right) a.same) ≫
        pieceCell t a.right a.rightCell cut a.rightBefore) ≫ inclusion t a.right cut from
      Multicoequalizer.condition (index t cut) (Sum.inr a))

/-- The original root and piece comparisons give the actual ambient cocone. -/
def ambientCoconeMap (cut : Option O) (i : Option I) :
    (index t cut).right i ⟶ ambient (c := c) cut :=
  match i with
  | none => ambientRoot cut
  | some i => pieceComparison t i cut

omit [HasColimitsOfSize.{w, w} C] in
/-- The ambient cocone satisfies the original root and shared-cell equations. -/
theorem ambientCoconeCondition (cut : Option O) (a : (shape t cut).L) :
    (index t cut).fst a ≫ ambientCoconeMap t cut ((shape t cut).fst a) =
      (index t cut).snd a ≫ ambientCoconeMap t cut ((shape t cut).snd a) := by
  cases a with
  | inl i =>
    exact (Category.id_comp _).trans (pieceRoot_comparison t i cut).symm
  | inr a =>
    change pieceCell t a.left a.leftCell cut a.leftBefore ≫ pieceComparison t a.left cut =
      (eqToHom (congrArg (fun z : c.Cells => z.i.1.right) a.same) ≫
        pieceCell t a.right a.rightCell cut a.rightBefore) ≫ pieceComparison t a.right cut
    rw [pieceCell_comparison, Category.assoc, pieceCell_comparison]
    exact ambientCell_congr _ _ a.same cut a.leftBefore a.rightBefore

/-- The union comparison is the descender of the actual original cocone. -/
def comparison (cut : Option O) : obj t cut ⟶ ambient (c := c) cut :=
  Multicoequalizer.desc (index t cut) _ (ambientCoconeMap t cut)
    (ambientCoconeCondition t cut)

@[reassoc]
theorem root_comparison (cut : Option O) :
    root t cut ≫ comparison t cut = ambientRoot (c := c) cut :=
  Multicoequalizer.π_desc (index t cut) _ _ _ none

@[reassoc]
theorem inclusion_comparison (i : I) (cut : Option O) :
    inclusion t i cut ≫ comparison t cut = pieceComparison t i cut :=
  Multicoequalizer.π_desc (index t cut) _ _ _ (some i)

include t in
/-- Actual maps from a union are determined by the same root and all
unchanged original subcomplex pieces. -/
theorem hom_ext (cut : Option O) {Z : C} {f g : obj t cut ⟶ Z}
    (hr : root t cut ≫ f = root t cut ≫ g)
    (ht : ∀ i : I, inclusion t i cut ≫ f = inclusion t i cut ≫ g) : f = g := by
  apply Multicoequalizer.hom_ext (index t cut)
  intro i
  cases i with
  | none => exact hr
  | some i => exact ht i

/-- All target maps use the original transitions and original union inclusions. -/
def mapCoconeMap (a b : Option O) (hab : CutLE a b) (i : Option I) :
    (index t a).right i ⟶ obj t b :=
  match i with
  | none => root t b
  | some i => pieceMap t i a b hab ≫ inclusion t i b

/-- The unchanged original transitions preserve each actual shared-cell relation. -/
theorem mapCoconeCondition (a b : Option O) (hab : CutLE a b) (z : (shape t a).L) :
    (index t a).fst z ≫ mapCoconeMap t a b hab ((shape t a).fst z) =
      (index t a).snd z ≫ mapCoconeMap t a b hab ((shape t a).snd z) := by
  cases z with
  | inl i =>
    change 𝟙 X ≫ root t b = pieceRoot t i a ≫ (pieceMap t i a b hab ≫ inclusion t i b)
    rw [Category.id_comp, ← Category.assoc, pieceRoot_map, pieceRoot_inclusion]
  | inr z =>
    change pieceCell t z.left z.leftCell a z.leftBefore ≫
      (pieceMap t z.left a b hab ≫ inclusion t z.left b) =
      (eqToHom (congrArg (fun k : c.Cells => k.i.1.right) z.same) ≫
        pieceCell t z.right z.rightCell a z.rightBefore) ≫
          (pieceMap t z.right a b hab ≫ inclusion t z.right b)
    rw [← Category.assoc, pieceCell_map]
    simp only [Category.assoc]
    rw [← Category.assoc (pieceCell t z.right z.rightCell a z.rightBefore), pieceCell_map]
    exact sharedCell_inclusion t b
      { left := z.left
        right := z.right
        leftCell := z.leftCell
        rightCell := z.rightCell
        same := z.same
        leftBefore := before_mono hab z.leftBefore
        rightBefore := before_mono hab z.rightBefore }

/-- The actual union transition is the descender of these same original maps. -/
def map (a b : Option O) (hab : CutLE a b) : obj t a ⟶ obj t b :=
  Multicoequalizer.desc (index t a) _ (mapCoconeMap t a b hab)
    (mapCoconeCondition t a b hab)

@[reassoc]
theorem root_map (a b : Option O) (hab : CutLE a b) : root t a ≫ map t a b hab = root t b :=
  Multicoequalizer.π_desc (index t a) _ _ _ none

@[reassoc]
theorem inclusion_map (i : I) (a b : Option O) (hab : CutLE a b) :
    inclusion t i a ≫ map t a b hab = pieceMap t i a b hab ≫ inclusion t i b :=
  Multicoequalizer.π_desc (index t a) _ _ _ (some i)

@[reassoc]
theorem map_comparison (a b : Option O) (hab : CutLE a b) :
    map t a b hab ≫ comparison t b = comparison t a ≫ ambientMap (c := c) a b hab := by
  apply hom_ext t a
  · rw [← Category.assoc, root_map, root_comparison,
      ← Category.assoc, root_comparison, ambientRoot_map]
  · intro i
    rw [← Category.assoc, inclusion_map, Category.assoc, inclusion_comparison,
      ← Category.assoc, inclusion_comparison]
    exact pieceMap_comparison t i a b hab

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The union retains the actual whole original stage order. -/
abbrev F : O ⥤ C where
  obj j := obj t (some j)
  map g := map t (some _) (some _) (leOfHom g)
  map_id j := by
    apply hom_ext t (some j)
    · rw [root_map, Category.comp_id]
    · intro i
      rw [inclusion_map, Category.comp_id]
      change (t i).complex.F.map (𝟙 j) ≫ inclusion t i (some j) = inclusion t i (some j)
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
  map_comp g h := by
    apply hom_ext t (some _)
    · rw [root_map, ← Category.assoc, root_map, root_map]
    · intro i
      rw [inclusion_map, ← Category.assoc, inclusion_map, Category.assoc, inclusion_map]
      change (t i).complex.F.map (g ≫ h) ≫ inclusion t i (some _) =
        (t i).complex.F.map g ≫ ((t i).complex.F.map h ≫ inclusion t i (some _))
      rw [CategoryTheory.Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The union's endpoint cocone keeps every actual original endpoint map. -/
abbrev endpointCocone : Cocone (F t) where
  pt := obj t none
  ι :=
    { app j := map t (some j) none trivial
      naturality j k g := by
        change map t (some j) (some k) (leOfHom g) ≫ map t (some k) none trivial =
          map t (some j) none trivial ≫ 𝟙 (obj t none)
        rw [Category.comp_id]
        apply hom_ext t (some j)
        · rw [← Category.assoc, root_map, root_map, root_map]
        · intro i
          rw [← Category.assoc, inclusion_map, Category.assoc, inclusion_map, inclusion_map]
          change (t i).complex.F.map g ≫ ((t i).complex.incl.app k ≫ inclusion t i none) =
            (t i).complex.incl.app j ≫ inclusion t i none
          rw [← Category.assoc, (Cocone.mk (t i).endpoint (t i).complex.incl).w] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An actual union cocone restricts along the original maps of each whole
input complex. -/
def pieceCocone (s : Cocone (F t)) (i : I) : Cocone (t i).complex.F where
  pt := s.pt
  ι :=
    { app j := inclusion t i (some j) ≫ s.ι.app j
      naturality j k g := by
        change (t i).complex.F.map g ≫ (inclusion t i (some k) ≫ s.ι.app k) =
          (inclusion t i (some j) ≫ s.ι.app j) ≫ 𝟙 s.pt
        calc
          _ = (inclusion t i (some j) ≫ map t (some j) (some k) (leOfHom g)) ≫ s.ι.app k := by
            rw [inclusion_map, Category.assoc]
            rfl
          _ = inclusion t i (some j) ≫ s.ι.app j := by
            rw [Category.assoc]
            exact congrArg (fun z => inclusion t i (some j) ≫ z) (s.w g)
          _ = (inclusion t i (some j) ≫ s.ι.app j) ≫ 𝟙 s.pt :=
            (Category.comp_id _).symm }

/-- Every piece uses its actual original endpoint colimit descender. -/
def pieceDesc (s : Cocone (F t)) (i : I) : (t i).endpoint ⟶ s.pt :=
  (t i).complex.isColimit.desc (pieceCocone t s i)

@[reassoc]
theorem pieceDesc_fac (s : Cocone (F t)) (i : I) (j : O) :
    (t i).complex.incl.app j ≫ pieceDesc t s i = inclusion t i (some j) ≫ s.ι.app j :=
  (t i).complex.isColimit.fac (pieceCocone t s i) j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Each selected original cell retains its actual stage in the piece descender. -/
@[reassoc]
theorem pieceCell_desc (s : Cocone (F t)) (i : I) (z : (t i).complex.Cells)
    (j : O) (hz : before (some j) ((t i).originalCell z)) :
    pieceCell t i z none trivial ≫ pieceDesc t s i =
      pieceCell t i z (some j) hz ≫ inclusion t i (some j) ≫ s.ι.app j := by
  change (t i).originalCellTarget z ≫ pieceDesc t s i =
    (t i).originalCellAtStage z j hz ≫ inclusion t i (some j) ≫ s.ι.app j
  rw [← (t i).originalCellAtStage_incl z j hz, Category.assoc, pieceDesc_fac]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every actual original stage gives the same union root cocone map. -/
@[reassoc]
theorem root_cocone (s : Cocone (F t)) (j : O) :
    root t (some j) ≫ s.ι.app j = root t (some ⊥) ≫ s.ι.app ⊥ := by
  calc
    _ = (root t (some ⊥) ≫ map t (some ⊥) (some j) bot_le) ≫ s.ι.app j :=
      congrArg (fun z => z ≫ s.ι.app j) (root_map t _ _ bot_le).symm
    _ = root t (some ⊥) ≫ s.ι.app ⊥ := by
      rw [Category.assoc]
      exact congrArg (fun z => root t (some ⊥) ≫ z) (s.w (homOfLE bot_le))

/-- The original piece endpoint maps and the original root form the final
actual colimit cocone. -/
def wholeCoconeMap (s : Cocone (F t)) (i : Option I) : (index t none).right i ⟶ s.pt :=
  match i with
  | none => root t (some ⊥) ≫ s.ι.app ⊥
  | some i => pieceDesc t s i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The whole original cocone respects the same root and original cell occurrences. -/
theorem wholeCoconeCondition (s : Cocone (F t)) (a : (shape t none).L) :
    (index t none).fst a ≫ wholeCoconeMap t s ((shape t none).fst a) =
      (index t none).snd a ≫ wholeCoconeMap t s ((shape t none).snd a) := by
  cases a with
  | inl i =>
    change 𝟙 X ≫ (root t (some ⊥) ≫ s.ι.app ⊥) = (t i).hom ≫ pieceDesc t s i
    rw [Category.id_comp]
    have hi : (t i).complex.isoBot.inv ≫ inclusion t i (some ⊥) = root t (some ⊥) := by
      simpa only [pieceRoot, RelativeCellComplex.rootAtStage, homOfLE_refl,
        CategoryTheory.Functor.map_id, Category.comp_id] using pieceRoot_inclusion t i (some ⊥)
    symm
    calc
      (t i).hom ≫ pieceDesc t s i =
          ((t i).complex.isoBot.inv ≫ (t i).complex.incl.app ⊥) ≫ pieceDesc t s i :=
        congrArg (fun z => z ≫ pieceDesc t s i) (t i).complex.fac.symm
      _ = (t i).complex.isoBot.inv ≫ (inclusion t i (some ⊥) ≫ s.ι.app ⊥) := by
        rw [Category.assoc, pieceDesc_fac]
      _ = root t (some ⊥) ≫ s.ι.app ⊥ := by rw [← Category.assoc, hi]
  | inr a =>
    let j := Order.succ a.leftCell.j
    have ha : before (some j) ((t a.left).originalCell a.leftCell) :=
      Order.lt_succ_of_not_isMax a.leftCell.hj
    have hb : before (some j) ((t a.right).originalCell a.rightCell) := by
      change ((t a.right).originalCell a.rightCell).j < j
      rw [← congrArg (fun z : c.Cells => z.j) a.same]
      exact ha
    let z : SharedCell t (some j) :=
      { left := a.left
        right := a.right
        leftCell := a.leftCell
        rightCell := a.rightCell
        same := a.same
        leftBefore := ha
        rightBefore := hb }
    change pieceCell t a.left a.leftCell none trivial ≫ pieceDesc t s a.left =
      (eqToHom (congrArg (fun k : c.Cells => k.i.1.right) a.same) ≫
        pieceCell t a.right a.rightCell none trivial) ≫ pieceDesc t s a.right
    rw [pieceCell_desc t s a.left a.leftCell j ha, Category.assoc,
      pieceCell_desc t s a.right a.rightCell j hb]
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ s.ι.app j) (sharedCell_inclusion t (some j) z)

/-- This final descender uses all actual input endpoint cocones and their
original cell and root maps. -/
def wholeDesc (s : Cocone (F t)) : (endpointCocone t).pt ⟶ s.pt :=
  Multicoequalizer.desc (index t none) _ (wholeCoconeMap t s) (wholeCoconeCondition t s)

@[reassoc]
theorem wholeDesc_root (s : Cocone (F t)) :
    root t none ≫ wholeDesc t s = root t (some ⊥) ≫ s.ι.app ⊥ :=
  Multicoequalizer.π_desc (index t none) _ _ _ none

@[reassoc]
theorem wholeDesc_piece (s : Cocone (F t)) (i : I) :
    inclusion t i none ≫ wholeDesc t s = pieceDesc t s i :=
  Multicoequalizer.π_desc (index t none) _ _ _ (some i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual union endpoint cocone is colimiting by the unchanged whole
input complex cocones and original shared-cell maps. -/
def endpointIsColimit : IsColimit (endpointCocone t) where
  desc s := wholeDesc t s
  fac s j := by
    apply hom_ext t (some j)
    · rw [← Category.assoc, root_map, wholeDesc_root]
      exact (root_cocone t s j).symm
    · intro i
      rw [← Category.assoc, inclusion_map, Category.assoc, wholeDesc_piece]
      exact pieceDesc_fac t s i j
  uniq s m hm := by
    apply hom_ext t none
    · rw [wholeDesc_root]
      calc
        root t none ≫ m =
            (root t (some ⊥) ≫ (endpointCocone t).ι.app ⊥) ≫ m :=
          congrArg (fun z => z ≫ m) (root_map t (some ⊥) none trivial).symm
        _ = root t (some ⊥) ≫ s.ι.app ⊥ := by rw [Category.assoc, hm]
    · intro i
      rw [wholeDesc_piece]
      apply (t i).complex.isColimit.hom_ext
      intro j
      calc
        _ = ((t i).complex.incl.app j ≫ inclusion t i none) ≫ m :=
          (Category.assoc _ _ _).symm
        _ = (inclusion t i (some j) ≫ (endpointCocone t).ι.app j) ≫ m :=
          congrArg (fun z => z ≫ m) (inclusion_map t i (some j) none trivial).symm
        _ = inclusion t i (some j) ≫ s.ι.app j := by rw [Category.assoc, hm]
        _ = (t i).complex.incl.app j ≫ pieceDesc t s i := (pieceDesc_fac t s i j).symm

open EffectiveCellularSubcomplexExtension

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual union endpoint relations give compatible prescribed maps
on exactly the same original cell occurrences. -/
theorem wholeFamilyCompatible {E : C} (α : obj t none ⟶ E) :
    FamilyCellCompatible d c t (fun i => inclusion t i none ≫ α) := by
  intro j hj i i' a b e
  let ca : (t i).complex.Cells := ⟨j, hj, a⟩
  let cb : (t i').complex.Cells := ⟨j, hj, b⟩
  have he : (t i).originalCell ca = (t i').originalCell cb :=
    congrArg (fun k => ({ j := j, hj := hj, k := k } : c.Cells)) e
  let z : SharedCell t none :=
    { left := i
      right := i'
      leftCell := ca
      rightCell := cb
      same := he
      leftBefore := trivial
      rightBefore := trivial }
  have hz := congrArg (fun q => q ≫ α) (sharedCell_inclusion t none z)
  simpa only [familyCellImage, pieceCell, CellularSubcomplex.originalCellTarget,
    RelativeCellComplex.Cells.ι, RelativeCellComplex.Cells.i, CellularSubcomplex.originalCell,
    ca, cb, z, Category.assoc] using hz

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual union endpoint comparison is a cofibration, proved by
filling missing original cells and preserving every original piece map. -/
theorem endpointComparisonCofibration (h : EffectiveCofibrations C) :
    cofibrations C (comparison t none) := by
  rw [← trivialFibrations_llp, ← d.I_rlp]
  intro E B q hq
  refine ⟨fun {α} {β} sq => ?_⟩
  let af (i : I) : (t i).endpoint ⟶ E := inclusion t i none ≫ α
  let r : X ⟶ E := root t none ≫ α
  have hrq : r ≫ q = f ≫ β := by
    dsimp only [r]
    rw [Category.assoc, sq.w, ← Category.assoc, root_comparison]
    rfl
  have hr (i : I) : (t i).hom ≫ af i = r := by
    change pieceRoot t i none ≫ (inclusion t i none ≫ α) = root t none ≫ α
    rw [← Category.assoc, pieceRoot_inclusion]
  have haf (i : I) : af i ≫ q = (t i).inclusion ≫ β := by
    dsimp only [af]
    rw [Category.assoc, sq.w, ← Category.assoc, inclusion_comparison]
  obtain ⟨ℓ, hℓr, hℓq, hℓ⟩ := existsFamilyLift d c h t af q r β hq hrq hr haf
    (wholeFamilyCompatible t α)
  have hcomp : comparison t none ≫ ℓ = α := by
    apply hom_ext t none
    · rw [← Category.assoc, root_comparison]
      exact hℓr
    · intro i
      rw [← Category.assoc, inclusion_comparison]
      exact hℓ i
  exact CommSq.HasLift.mk' { l := ℓ, fac_left := hcomp, fac_right := hℓq }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A prefix family's cell image is the exact original cell map to that
same original endpoint stage, followed by its actual union projection. -/
theorem prefixFamilyImage {E : C} (j : O) (α : obj t (some j) ⟶ E)
    (a : Set.Iic j) (ha : ¬ IsMax a) (i : I)
    (k : ((t i).complex.attachCells a.1 (prefixNotMax a ha)).ι) :
    familyCellImage d (prefixComplex d c j)
      (fun i => prefixSubcomplex d c (t i) j)
      (fun i => inclusion t i (some j) ≫ α) a ha i k =
    pieceCell t i ⟨a.1, prefixNotMax a ha, k⟩ (some j)
      (prefixStage_lt_endpoint a ha) ≫ inclusion t i (some j) ≫ α := by
  let e := eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
    ((t i).label_eq a.1 (prefixNotMax a ha) k).symm)
  let z : (prefixComplex d (t i).complex j).Cells := ⟨a, ha, k⟩
  have h₀ : familyCellImage d (prefixComplex d c j)
      (fun i => prefixSubcomplex d c (t i) j)
      (fun i => inclusion t i (some j) ≫ α) a ha i k =
        e ≫ z.ι ≫ (inclusion t i (some j) ≫ α) := by
    dsimp only [familyCellImage, prefixSubcomplex, e, z, RelativeCellComplex.Cells.ι]
    simp only [Category.assoc]
  calc
    _ = e ≫ z.ι ≫ (inclusion t i (some j) ≫ α) := h₀
    _ = e ≫ ((t i).complex.attachCells a.1 (prefixNotMax a ha)).cell k ≫
        (t i).complex.F.map (homOfLE (Order.succ_le_of_lt (prefixStage_lt_endpoint a ha))) ≫
          (inclusion t i (some j) ≫ α) := by
      rw [prefixComplex_cell_inclusion, Category.assoc]
    _ = _ := by
      dsimp only [e, pieceCell, CellularSubcomplex.originalCellAtStage,
        RelativeCellComplex.Cells.toStage, RelativeCellComplex.Cells.i,
        CellularSubcomplex.originalCell]
      simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The literal original-stage relations give compatible maps on the
actual closed original prefix, including all original occurrence labels. -/
theorem prefixFamilyCompatible {E : C} (j : O) (α : obj t (some j) ⟶ E) :
    FamilyCellCompatible d (prefixComplex d c j)
      (fun i => prefixSubcomplex d c (t i) j)
      (fun i => inclusion t i (some j) ≫ α) := by
  intro a ha i i' k k' e
  change (t i).cellIndex a.1 (prefixNotMax a ha) k =
    (t i').cellIndex a.1 (prefixNotMax a ha) k' at e
  let ca : (t i).complex.Cells := ⟨a.1, prefixNotMax a ha, k⟩
  let cb : (t i').complex.Cells := ⟨a.1, prefixNotMax a ha, k'⟩
  have he : (t i).originalCell ca = (t i').originalCell cb :=
    congrArg (fun k => ({ j := a.1, hj := prefixNotMax a ha, k := k } : c.Cells)) e
  let z : SharedCell t (some j) :=
    { left := i
      right := i'
      leftCell := ca
      rightCell := cb
      same := he
      leftBefore := prefixStage_lt_endpoint a ha
      rightBefore := prefixStage_lt_endpoint a ha }
  rw [prefixFamilyImage, prefixFamilyImage]
  simpa only [ca, cb, z, RelativeCellComplex.Cells.i, CellularSubcomplex.originalCell,
    Category.assoc] using
      congrArg (fun q => q ≫ α) (sharedCell_inclusion t (some j) z)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every actual union-stage comparison is a cofibration, from the
unchanged closed-prefix histories and the original I lifting property. -/
theorem stageComparisonCofibration (h : EffectiveCofibrations C) (j : O) :
    cofibrations C (comparison t (some j)) := by
  rw [← trivialFibrations_llp, ← d.I_rlp]
  intro E B q hq
  refine ⟨fun {α} {β} sq => ?_⟩
  let tf := fun i => prefixSubcomplex d c (t i) j
  let af (i : I) : (tf i).endpoint ⟶ E := inclusion t i (some j) ≫ α
  let r : X ⟶ E := root t (some j) ≫ α
  have hrq : r ≫ q =
      (c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫ β := by
    dsimp only [r]
    rw [Category.assoc, sq.w, ← Category.assoc, root_comparison]
    rfl
  have hr (i : I) : (tf i).hom ≫ af i = r := by
    change pieceRoot t i (some j) ≫ (inclusion t i (some j) ≫ α) = root t (some j) ≫ α
    rw [← Category.assoc, pieceRoot_inclusion]
  have haf (i : I) : af i ≫ q = (tf i).inclusion ≫ β := by
    dsimp only [af]
    rw [Category.assoc, sq.w, ← Category.assoc, inclusion_comparison]
    rfl
  obtain ⟨ℓ, hℓr, hℓq, hℓ⟩ := existsFamilyLift d (prefixComplex d c j) h tf af q r β
    hq hrq hr haf (prefixFamilyCompatible t j α)
  have hcomp : comparison t (some j) ≫ ℓ = α := by
    apply hom_ext t (some j)
    · rw [← Category.assoc, root_comparison]
      exact hℓr
    · intro i
      rw [← Category.assoc, inclusion_comparison]
      exact hℓ i
  exact CommSq.HasLift.mk' { l := ℓ, fac_left := hcomp, fac_right := hℓq }

section OriginalLimit

variable {j : O} (hj : Order.IsSuccLimit j)
  (s : Cocone ((Set.principalSegIio j).monotone.functor ⋙ F t))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An actual limit cocone restricts to each unchanged original input chain. -/
def limitPieceCocone (i : I) :
    Cocone ((Set.principalSegIio j).monotone.functor ⋙ (t i).complex.F) where
  pt := s.pt
  ι :=
    { app a := inclusion t i (some a.1) ≫ s.ι.app a
      naturality a b g := by
        change (t i).complex.F.map (homOfLE (leOfHom g)) ≫
          (inclusion t i (some b.1) ≫ s.ι.app b) =
            (inclusion t i (some a.1) ≫ s.ι.app a) ≫ 𝟙 s.pt
        calc
          _ = (inclusion t i (some a.1) ≫ map t (some a.1) (some b.1) (leOfHom g)) ≫
              s.ι.app b := by rw [inclusion_map, Category.assoc]
          _ = inclusion t i (some a.1) ≫ s.ι.app a := by
            rw [Category.assoc]
            exact congrArg (fun z => inclusion t i (some a.1) ≫ z) (s.w g)
          _ = _ := (Category.comp_id _).symm }

/-- The same original input limit universal property constructs its map. -/
def limitPieceDesc (i : I) : (t i).complex.F.obj j ⟶ s.pt :=
  ((t i).complex.F.isColimitOfIsWellOrderContinuous j hj).desc (limitPieceCocone t s i)

@[reassoc]
theorem limitPieceDesc_fac (i : I) (a : O) (ha : a < j) :
    (t i).complex.F.map (homOfLE ha.le) ≫ limitPieceDesc t hj s i =
      inclusion t i (some a) ≫ s.ι.app ⟨a, ha⟩ :=
  ((t i).complex.F.isColimitOfIsWellOrderContinuous j hj).fac (limitPieceCocone t s i) ⟨a, ha⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every smaller original stage recovers the same actual limit root map. -/
@[reassoc]
theorem root_limit_cocone (a : Set.Iio j) :
    root t (some a.1) ≫ s.ι.app a =
      root t (some ⊥) ≫ s.ι.app ⟨⊥, hj.bot_lt⟩ := by
  calc
    _ = (root t (some ⊥) ≫ map t (some ⊥) (some a.1) bot_le) ≫ s.ι.app a :=
      congrArg (fun z => z ≫ s.ι.app a) (root_map t _ _ bot_le).symm
    _ = root t (some ⊥) ≫ s.ι.app ⟨⊥, hj.bot_lt⟩ := by
      rw [Category.assoc]
      let a₀ : Set.Iio j := ⟨⊥, hj.bot_lt⟩
      have hle : a₀ ≤ a := show a₀.1 ≤ a.1 from bot_le
      have hw := s.w (homOfLE hle)
      change map t (some ⊥) (some a.1) bot_le ≫ s.ι.app a = s.ι.app a₀ at hw
      exact congrArg (fun z => root t (some ⊥) ≫ z) hw

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Original cell maps descend from their same actual smaller original stage. -/
@[reassoc]
theorem limitPieceCell_desc (i : I) (z : (t i).complex.Cells)
    (hz : before (some j) ((t i).originalCell z)) (a : O) (ha : a < j)
    (hza : before (some a) ((t i).originalCell z)) :
    pieceCell t i z (some j) hz ≫ limitPieceDesc t hj s i =
      pieceCell t i z (some a) hza ≫ inclusion t i (some a) ≫ s.ι.app ⟨a, ha⟩ := by
  change (t i).originalCellAtStage z j hz ≫ limitPieceDesc t hj s i =
    (t i).originalCellAtStage z a hza ≫ inclusion t i (some a) ≫ s.ι.app ⟨a, ha⟩
  rw [← (t i).originalCellAtStage_map z hza (homOfLE ha.le), Category.assoc,
    limitPieceDesc_fac]

/-- The actual original root and input limit maps form the union limit cocone. -/
def limitCoconeMap (i : Option I) : (index t (some j)).right i ⟶ s.pt :=
  match i with
  | none => root t (some ⊥) ≫ s.ι.app ⟨⊥, hj.bot_lt⟩
  | some i => limitPieceDesc t hj s i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Original continuity respects the same original root and shared-cell relations. -/
theorem limitCoconeCondition (a : (shape t (some j)).L) :
    (index t (some j)).fst a ≫ limitCoconeMap t hj s ((shape t (some j)).fst a) =
      (index t (some j)).snd a ≫ limitCoconeMap t hj s ((shape t (some j)).snd a) := by
  cases a with
  | inl i =>
    change 𝟙 X ≫ (root t (some ⊥) ≫ s.ι.app ⟨⊥, hj.bot_lt⟩) =
      (t i).complex.rootAtStage j ≫ limitPieceDesc t hj s i
    rw [Category.id_comp]
    have hi : (t i).complex.isoBot.inv ≫ inclusion t i (some ⊥) = root t (some ⊥) := by
      simpa only [pieceRoot, RelativeCellComplex.rootAtStage, homOfLE_refl,
        CategoryTheory.Functor.map_id, Category.comp_id] using pieceRoot_inclusion t i (some ⊥)
    dsimp only [RelativeCellComplex.rootAtStage]
    rw [Category.assoc, limitPieceDesc_fac t hj s i ⊥ hj.bot_lt, ← Category.assoc, hi]
  | inr a =>
    let k := Order.succ a.leftCell.j
    have hk : k < j := (Order.IsSuccLimit.succ_lt_iff hj).mpr a.leftBefore
    have ha : before (some k) ((t a.left).originalCell a.leftCell) :=
      Order.lt_succ_of_not_isMax a.leftCell.hj
    have hb : before (some k) ((t a.right).originalCell a.rightCell) := by
      change ((t a.right).originalCell a.rightCell).j < k
      rw [← congrArg (fun z : c.Cells => z.j) a.same]
      exact ha
    let z : SharedCell t (some k) :=
      { left := a.left
        right := a.right
        leftCell := a.leftCell
        rightCell := a.rightCell
        same := a.same
        leftBefore := ha
        rightBefore := hb }
    change pieceCell t a.left a.leftCell (some j) a.leftBefore ≫ limitPieceDesc t hj s a.left =
      (eqToHom (congrArg (fun z : c.Cells => z.i.1.right) a.same) ≫
        pieceCell t a.right a.rightCell (some j) a.rightBefore) ≫ limitPieceDesc t hj s a.right
    rw [limitPieceCell_desc t hj s a.left a.leftCell a.leftBefore k hk ha,
      Category.assoc, limitPieceCell_desc t hj s a.right a.rightCell a.rightBefore k hk hb]
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ s.ι.app ⟨k, hk⟩) (sharedCell_inclusion t (some k) z)

/-- The limit descender uses the actual original input limit cocones. -/
def limitDesc : obj t (some j) ⟶ s.pt :=
  Multicoequalizer.desc (index t (some j)) _ (limitCoconeMap t hj s)
    (limitCoconeCondition t hj s)

@[reassoc]
theorem limitDesc_root :
    root t (some j) ≫ limitDesc t hj s = root t (some ⊥) ≫ s.ι.app ⟨⊥, hj.bot_lt⟩ :=
  Multicoequalizer.π_desc (index t (some j)) _ _ _ none

@[reassoc]
theorem limitDesc_piece (i : I) :
    inclusion t i (some j) ≫ limitDesc t hj s = limitPieceDesc t hj s i :=
  Multicoequalizer.π_desc (index t (some j)) _ _ _ (some i)

end OriginalLimit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual union diagram is continuous on the unchanged original ordinal. -/
theorem wellOrderContinuous : (F t).IsWellOrderContinuous where
  nonempty_isColimit j hj := ⟨
    { desc s := limitDesc t hj s
      fac s a := by
        have ha : a.1 < j := a.2
        change map t (some a.1) (some j) ha.le ≫ limitDesc t hj s = s.ι.app a
        apply hom_ext t (some a.1)
        · rw [← Category.assoc, root_map, limitDesc_root]
          exact (root_limit_cocone t hj s a).symm
        · intro i
          rw [← Category.assoc, inclusion_map, Category.assoc, limitDesc_piece]
          exact limitPieceDesc_fac t hj s i a.1 a.2
      uniq s m hm := by
        change obj t (some j) ⟶ s.pt at m
        have hm' (a : Set.Iio j) :
            map t (some a.1) (some j) (show a.1 ≤ j from (show a.1 < j from a.2).le) ≫ m =
              s.ι.app a := by
          have hma := hm a
          change map t (some a.1) (some j) (show a.1 ≤ j from (show a.1 < j from a.2).le) ≫ m =
            s.ι.app a at hma
          exact hma
        apply hom_ext t (some j)
        · rw [limitDesc_root]
          calc
            root t (some j) ≫ m =
                (root t (some ⊥) ≫ (F t).map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫ m :=
              congrArg (fun z => z ≫ m) (root_map t (some ⊥) (some j) bot_le).symm
            _ = root t (some ⊥) ≫ s.ι.app ⟨⊥, hj.bot_lt⟩ := by
              let a₀ : Set.Iio j := ⟨⊥, by exact hj.bot_lt⟩
              exact (Category.assoc _ _ _).trans
                (congrArg (fun z => root t (some ⊥) ≫ z) (hm' a₀))
        · intro i
          rw [limitDesc_piece]
          apply ((t i).complex.F.isColimitOfIsWellOrderContinuous j hj).hom_ext
          intro a
          calc
            _ = ((t i).complex.F.map (homOfLE a.2.le) ≫ inclusion t i (some j)) ≫ m :=
              (Category.assoc _ _ _).symm
            _ = (inclusion t i (some a.1) ≫ (F t).map (homOfLE a.2.le)) ≫ m :=
              congrArg (fun z => z ≫ m) (inclusion_map t i (some a.1) (some j) a.2.le).symm
            _ = inclusion t i (some a.1) ≫ s.ι.app a := by rw [Category.assoc, hm']
            _ = (t i).complex.F.map (homOfLE a.2.le) ≫ limitPieceDesc t hj s i :=
              (limitPieceDesc_fac t hj s i a.1 a.2).symm }⟩

section OriginalAttachments

variable (j : O) (hj : ¬ IsMax j)

/-- The actual original occurrences selected by at least one original piece. -/
abbrev cells : Type w := {k : (c.attachCells j hj).ι // Selected d c t j hj k}

/-- The actual selected original occurrence retains one original piece witness. -/
def witnessPiece (k : cells t j hj) : I := k.2.choose

/-- Its witness is a literal original occurrence in that unchanged piece stage. -/
def witnessCell (k : cells t j hj) : ((t (witnessPiece t j hj k)).complex.attachCells j hj).ι :=
  k.2.choose_spec.choose

omit [HasColimitsOfSize.{w, w} C] in
/-- The witness selects exactly the same original occurrence. -/
theorem witnessCell_eq (k : cells t j hj) :
    (t (witnessPiece t j hj k)).cellIndex j hj (witnessCell t j hj k) = k.1 :=
  k.2.choose_spec.choose_spec

/-- The selected cell uses its unchanged original generating arrow label. -/
abbrev cellLabel (k : cells t j hj) : d.I.toSet := (c.attachCells j hj).π k.1

omit [HasColimitsOfSize.{w, w} C] in
/-- The chosen witness retains the exact original generator. -/
theorem witnessLabel_eq (k : cells t j hj) :
    ((t (witnessPiece t j hj k)).complex.attachCells j hj).π (witnessCell t j hj k) =
      cellLabel t j hj k :=
  ((t (witnessPiece t j hj k)).label_eq j hj (witnessCell t j hj k)).trans
    (congrArg (c.attachCells j hj).π (witnessCell_eq t j hj k))

/-- The actual original generator domain maps through the chosen original piece
at the unchanged stage. -/
def sourceCell (k : cells t j hj) : (cellLabel t j hj k).1.left ⟶ obj t (some j) :=
  eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (witnessLabel_eq t j hj k).symm) ≫
    boundary d (t (witnessPiece t j hj k)).complex j hj (witnessCell t j hj k) ≫
      inclusion t (witnessPiece t j hj k) (some j)

/-- The same selected original generating codomain enters the next original union stage. -/
def targetCell (k : cells t j hj) : (cellLabel t j hj k).1.right ⟶ obj t (some (Order.succ j)) :=
  eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (witnessLabel_eq t j hj k).symm) ≫
    ((t (witnessPiece t j hj k)).complex.attachCells j hj).cell (witnessCell t j hj k) ≫
      inclusion t (witnessPiece t j hj k) (some (Order.succ j))

omit [HasColimitsOfSize.{w, w} C] in
private theorem boundary_congr (k k' : (c.attachCells j hj).ι) (e : k = k') :
    boundary d c j hj k =
      eqToHom (congrArg (fun a => ((c.attachCells j hj).π a).1.left) e) ≫ boundary d c j hj k' := by
  cases e
  rw [eqToHom_refl, Category.id_comp]

omit [HasColimitsOfSize.{w, w} C] in
private theorem cell_congr (k k' : (c.attachCells j hj).ι) (e : k = k') :
    (c.attachCells j hj).cell k =
      eqToHom (congrArg (fun a => ((c.attachCells j hj).π a).1.right) e) ≫
        (c.attachCells j hj).cell k' := by
  cases e
  rw [eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The chosen domain map is the original attaching map under the actual stage comparison. -/
@[reassoc]
theorem sourceCell_comparison (h : EffectiveCofibrations C) (k : cells t j hj) :
    sourceCell t j hj k ≫ comparison t (some j) = boundary d c j hj k.1 := by
  dsimp only [sourceCell]
  rw [Category.assoc, Category.assoc, inclusion_comparison, subcomplexBoundary d c h]
  rw [← Category.assoc, eqToHom_trans]
  exact (boundary_congr j hj k.1 _ (witnessCell_eq t j hj k).symm).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The chosen target map is the original cell inclusion under the actual next-stage comparison. -/
@[reassoc]
theorem targetCell_comparison (k : cells t j hj) :
    targetCell t j hj k ≫ comparison t (some (Order.succ j)) = (c.attachCells j hj).cell k.1 := by
  dsimp only [targetCell]
  rw [Category.assoc, Category.assoc, inclusion_comparison, (t (witnessPiece t j hj k)).cell_eq]
  rw [← Category.assoc, eqToHom_trans]
  exact (cell_congr j hj k.1 _ (witnessCell_eq t j hj k).symm).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every selected cell retains its exact original attaching square in the actual union. -/
theorem cell_square (h : EffectiveCofibrations C) (k : cells t j hj) :
    sourceCell t j hj k ≫ (F t).map (homOfLE (Order.le_succ j)) =
      d.I.homFamily (cellLabel t j hj k) ≫ targetCell t j hj k := by
  let _ : Mono (comparison t (some (Order.succ j))) :=
    h.mono_of_cofibration _ (stageComparisonCofibration t h (Order.succ j))
  apply (cancel_mono (comparison t (some (Order.succ j)))).1
  rw [Category.assoc, map_comparison, ← Category.assoc, sourceCell_comparison t j hj h,
    Category.assoc, targetCell_comparison]
  exact boundary_cell d c j hj k.1

/-- The actual selected original domains use their working-size source cofan. -/
abbrev sourceCofan : Cofan (fun k : cells t j hj => (cellLabel t j hj k).1.left) :=
  colimit.cocone (Discrete.functor (fun k : cells t j hj => (cellLabel t j hj k).1.left))

/-- The actual selected original codomains use their working-size target cofan. -/
abbrev targetCofan : Cofan (fun k : cells t j hj => (cellLabel t j hj k).1.right) :=
  colimit.cocone (Discrete.functor (fun k : cells t j hj => (cellLabel t j hj k).1.right))

/-- The original selected I arrows give the literal coproduct attaching arrow. -/
def cellMap : (sourceCofan t j hj).pt ⟶ (targetCofan t j hj).pt :=
  (colimit.isColimit _).desc
    (Cofan.mk _ (fun k => d.I.homFamily (cellLabel t j hj k) ≫ (targetCofan t j hj).inj k))

@[reassoc]
theorem cellMap_inj (k : cells t j hj) :
    (sourceCofan t j hj).inj k ≫ cellMap t j hj =
      d.I.homFamily (cellLabel t j hj k) ≫ (targetCofan t j hj).inj k :=
  (colimit.isColimit (Discrete.functor
    (fun k : cells t j hj => (cellLabel t j hj k).1.left))).fac
      (Cofan.mk _ (fun k => d.I.homFamily (cellLabel t j hj k) ≫ (targetCofan t j hj).inj k)) ⟨k⟩

/-- The unchanged actual source maps combine through their original source cofan. -/
def sourceMap : (sourceCofan t j hj).pt ⟶ obj t (some j) :=
  (colimit.isColimit _).desc (Cofan.mk _ (sourceCell t j hj))

/-- The unchanged actual target cell maps combine through their original target cofan. -/
def targetMap : (targetCofan t j hj).pt ⟶ obj t (some (Order.succ j)) :=
  (colimit.isColimit _).desc (Cofan.mk _ (targetCell t j hj))

@[reassoc]
theorem sourceMap_inj (k : cells t j hj) :
    (sourceCofan t j hj).inj k ≫ sourceMap t j hj = sourceCell t j hj k :=
  (colimit.isColimit (Discrete.functor
    (fun k : cells t j hj => (cellLabel t j hj k).1.left))).fac
      (Cofan.mk _ (sourceCell t j hj)) ⟨k⟩

@[reassoc]
theorem targetMap_inj (k : cells t j hj) :
    (targetCofan t j hj).inj k ≫ targetMap t j hj = targetCell t j hj k :=
  (colimit.isColimit (Discrete.functor
    (fun k : cells t j hj => (cellLabel t j hj k).1.right))).fac
      (Cofan.mk _ (targetCell t j hj)) ⟨k⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The entire original selected-cell cofans satisfy the actual original union square. -/
theorem attaching_square (h : EffectiveCofibrations C) :
    sourceMap t j hj ≫ (F t).map (homOfLE (Order.le_succ j)) =
      cellMap t j hj ≫ targetMap t j hj := by
  apply (colimit.isColimit (Discrete.functor
    (fun k : cells t j hj => (cellLabel t j hj k).1.left))).hom_ext
  intro k
  change ((sourceCofan t j hj).inj k.as) ≫
    (sourceMap t j hj ≫ (F t).map (homOfLE (Order.le_succ j))) =
      (sourceCofan t j hj).inj k.as ≫ (cellMap t j hj ≫ targetMap t j hj)
  rw [← Category.assoc, sourceMap_inj t j hj k.as,
    ← Category.assoc, cellMap_inj t j hj k.as, Category.assoc, targetMap_inj t j hj k.as]
  exact cell_square t j hj h k.as

/-- Every supplied piece cell selects its literal original union occurrence. -/
abbrev familyOccurrence (i : I) (a : ((t i).complex.attachCells j hj).ι) : cells t j hj :=
  ⟨(t i).cellIndex j hj a, ⟨i, a, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every original witness gives the same union attaching-domain map. -/
theorem sourceCell_family (h : EffectiveCofibrations C) (i : I)
    (a : ((t i).complex.attachCells j hj).ι) :
    eqToHom (congrArg (fun p : d.I.toSet => p.1.left) ((t i).label_eq j hj a)) ≫
      sourceCell t j hj (familyOccurrence t j hj i a) =
        boundary d (t i).complex j hj a ≫ inclusion t i (some j) := by
  let _ : Mono (comparison t (some j)) := h.mono_of_cofibration _ (stageComparisonCofibration t h j)
  apply (cancel_mono (comparison t (some j))).1
  rw [Category.assoc, sourceCell_comparison t j hj h, Category.assoc, inclusion_comparison]
  exact (subcomplexBoundary d c h (t i) j hj a).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every original witness gives the same union target-cell map. -/
theorem targetCell_family (h : EffectiveCofibrations C) (i : I)
    (a : ((t i).complex.attachCells j hj).ι) :
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a)) ≫
      targetCell t j hj (familyOccurrence t j hj i a) =
        ((t i).complex.attachCells j hj).cell a ≫ inclusion t i (some (Order.succ j)) := by
  let _ : Mono (comparison t (some (Order.succ j))) :=
    h.mono_of_cofibration _ (stageComparisonCofibration t h (Order.succ j))
  apply (cancel_mono (comparison t (some (Order.succ j)))).1
  rw [Category.assoc, targetCell_comparison t j hj, Category.assoc, inclusion_comparison]
  exact ((t i).cell_eq j hj a).symm

variable (s : PushoutCocone (sourceMap t j hj) (cellMap t j hj))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An arbitrary pushout test cocone retains each original selected cell square. -/
theorem testCell_square (k : cells t j hj) :
    sourceCell t j hj k ≫ s.inl =
      d.I.homFamily (cellLabel t j hj k) ≫ (targetCofan t j hj).inj k ≫ s.inr := by
  have h := congrArg (fun q => (sourceCofan t j hj).inj k ≫ q) s.condition
  rw [← Category.assoc, sourceMap_inj t j hj k,
    ← Category.assoc, cellMap_inj t j hj k, Category.assoc] at h
  exact h

/-- Original piece cells map through their same original selected target summand. -/
def pieceStepCell (i : I) (a : ((t i).complex.attachCells j hj).ι) :
    (((t i).complex.attachCells j hj).π a).1.right ⟶ s.pt :=
  eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a)) ≫
    (targetCofan t j hj).inj (familyOccurrence t j hj i a) ≫ s.inr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original piece attaching boundary agrees in every test cocone. -/
theorem pieceStepCell_boundary (h : EffectiveCofibrations C) (i : I)
    (a : ((t i).complex.attachCells j hj).ι) :
    boundary d (t i).complex j hj a ≫ (inclusion t i (some j) ≫ s.inl) =
      d.I.homFamily (((t i).complex.attachCells j hj).π a) ≫ pieceStepCell t j hj s i a := by
  rw [← Category.assoc, ← sourceCell_family t j hj h i a, Category.assoc, testCell_square]
  dsimp only [pieceStepCell]
  rw [← Category.assoc, ← generatorTransport d _ _ ((t i).label_eq j hj a), Category.assoc]

/-- The actual original target cofan combines the test values of all piece cells. -/
def pieceStepCofanMap (i : I) : ((t i).complex.attachCells j hj).cofan₂.pt ⟶ s.pt :=
  ((t i).complex.attachCells j hj).isColimit₂.desc (Cofan.mk _ (pieceStepCell t j hj s i))

@[reassoc]
theorem pieceStepCofanMap_inj (i : I) (a : ((t i).complex.attachCells j hj).ι) :
    ((t i).complex.attachCells j hj).cofan₂.inj a ≫ pieceStepCofanMap t j hj s i =
      pieceStepCell t j hj s i a :=
  ((t i).complex.attachCells j hj).isColimit₂.fac (Cofan.mk _ (pieceStepCell t j hj s i)) ⟨a⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Each original piece pushout supplies its actual next-stage test map. -/
def pieceStepMap (h : EffectiveCofibrations C) (i : I) :
    (t i).complex.F.obj (Order.succ j) ⟶ s.pt := by
  refine ((t i).complex.attachCells j hj).isPushout.desc
    (inclusion t i (some j) ≫ s.inl) (pieceStepCofanMap t j hj s i) ?_
  apply ((t i).complex.attachCells j hj).isColimit₁.hom_ext
  intro a
  change ((t i).complex.attachCells j hj).cofan₁.inj a.as ≫
      (((t i).complex.attachCells j hj).g₁ ≫ (inclusion t i (some j) ≫ s.inl)) =
    ((t i).complex.attachCells j hj).cofan₁.inj a.as ≫
      (((t i).complex.attachCells j hj).m ≫ pieceStepCofanMap t j hj s i)
  calc
    _ = boundary d (t i).complex j hj a.as ≫ (inclusion t i (some j) ≫ s.inl) := by
      dsimp only [boundary]
      simp only [Category.assoc]
    _ = d.I.homFamily (((t i).complex.attachCells j hj).π a.as) ≫
        pieceStepCell t j hj s i a.as := pieceStepCell_boundary t j hj s h i a.as
    _ = (d.I.homFamily (((t i).complex.attachCells j hj).π a.as) ≫
        ((t i).complex.attachCells j hj).cofan₂.inj a.as) ≫ pieceStepCofanMap t j hj s i := by
      rw [Category.assoc, pieceStepCofanMap_inj]
    _ = (((t i).complex.attachCells j hj).cofan₁.inj a.as ≫
        ((t i).complex.attachCells j hj).m) ≫ pieceStepCofanMap t j hj s i :=
      congrArg (fun z => z ≫ pieceStepCofanMap t j hj s i)
        (((t i).complex.attachCells j hj).hm a.as).symm
    _ = _ := Category.assoc _ _ _

@[reassoc]
theorem pieceStepMap_stage (h : EffectiveCofibrations C) (i : I) :
    (t i).complex.F.map (homOfLE (Order.le_succ j)) ≫ pieceStepMap t j hj s h i =
      inclusion t i (some j) ≫ s.inl := by
  simp only [pieceStepMap, IsPushout.inl_desc]

@[reassoc]
theorem pieceStepMap_cell (h : EffectiveCofibrations C) (i : I)
    (a : ((t i).complex.attachCells j hj).ι) :
    ((t i).complex.attachCells j hj).cell a ≫ pieceStepMap t j hj s h i =
      pieceStepCell t j hj s i a := by
  rw [AttachCells.cell, Category.assoc]
  simp only [pieceStepMap, IsPushout.inr_desc]
  exact pieceStepCofanMap_inj t j hj s i a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every test piece map preserves the same original common root. -/
theorem pieceStepMap_root (h : EffectiveCofibrations C) (i : I) :
    pieceRoot t i (some (Order.succ j)) ≫ pieceStepMap t j hj s h i = root t (some j) ≫ s.inl := by
  change (t i).complex.rootAtStage (Order.succ j) ≫ pieceStepMap t j hj s h i = _
  rw [← (t i).complex.rootAtStage_map (homOfLE (Order.le_succ j)),
    Category.assoc, pieceStepMap_stage, ← Category.assoc]
  exact congrArg (fun z => z ≫ s.inl) (pieceRoot_inclusion t i (some j))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Earlier original cells retain their actual earlier-stage test maps. -/
theorem pieceStepMap_before_cell (h : EffectiveCofibrations C) (i : I) (z : (t i).complex.Cells)
    (hz : before (some (Order.succ j)) ((t i).originalCell z))
    (hzj : before (some j) ((t i).originalCell z)) :
    pieceCell t i z (some (Order.succ j)) hz ≫ pieceStepMap t j hj s h i =
      pieceCell t i z (some j) hzj ≫ inclusion t i (some j) ≫ s.inl := by
  change (t i).originalCellAtStage z (Order.succ j) hz ≫ pieceStepMap t j hj s h i =
    (t i).originalCellAtStage z j hzj ≫ inclusion t i (some j) ≫ s.inl
  rw [← (t i).originalCellAtStage_map z hzj (homOfLE (Order.le_succ j)),
    Category.assoc, pieceStepMap_stage]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A current original cell uses exactly its own original union target summand. -/
theorem pieceStepMap_current_cell (h : EffectiveCofibrations C) (i : I)
    (a : ((t i).complex.attachCells j hj).ι) :
    pieceCell t i ⟨j, hj, a⟩ (some (Order.succ j)) (Order.lt_succ_of_not_isMax hj) ≫
        pieceStepMap t j hj s h i =
      (targetCofan t j hj).inj (familyOccurrence t j hj i a) ≫ s.inr := by
  change (eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a).symm) ≫
    (((t i).complex.attachCells j hj).cell a ≫ (t i).complex.F.map (𝟙 (Order.succ j)))) ≫
      pieceStepMap t j hj s h i = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id,
    Category.assoc, pieceStepMap_cell]
  dsimp only [pieceStepCell]
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

private theorem targetCofan_inj_congr (k k' : cells t j hj) (e : k = k') :
    (targetCofan t j hj).inj k =
      eqToHom (congrArg (fun z : cells t j hj => (cellLabel t j hj z).1.right) e) ≫
        (targetCofan t j hj).inj k' := by
  cases e
  rw [eqToHom_refl, Category.id_comp]

/-- The actual next-stage piece maps and common root form the test gluing cocone. -/
def stepCoconeMap (h : EffectiveCofibrations C) (i : Option I) :
    (index t (some (Order.succ j))).right i ⟶ s.pt :=
  match i with
  | none => root t (some j) ≫ s.inl
  | some i => pieceStepMap t j hj s h i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual test maps respect both earlier and current shared original cells. -/
theorem stepCoconeCondition (h : EffectiveCofibrations C) (z : (shape t (some (Order.succ j))).L) :
    (index t (some (Order.succ j))).fst z ≫ stepCoconeMap t j hj s h
        ((shape t (some (Order.succ j))).fst z) =
      (index t (some (Order.succ j))).snd z ≫ stepCoconeMap t j hj s h
        ((shape t (some (Order.succ j))).snd z) := by
  cases z with
  | inl i =>
    change 𝟙 X ≫ (root t (some j) ≫ s.inl) =
      pieceRoot t i (some (Order.succ j)) ≫ pieceStepMap t j hj s h i
    rw [Category.id_comp]
    exact (pieceStepMap_root t j hj s h i).symm
  | inr z =>
    rcases z with ⟨i, i', ⟨a, ha, k⟩, ⟨b, hb, k'⟩, same, hba, hbb⟩
    have hstage : a = b := congrArg (fun z : c.Cells => z.j) same
    have hle : a ≤ j := (Order.lt_succ_iff_of_not_isMax hj).mp hba
    by_cases hlt : a < j
    · have hlt' : b < j := hstage ▸ hlt
      change pieceCell t i ⟨a, ha, k⟩ (some (Order.succ j)) hba ≫
          pieceStepMap t j hj s h i =
        (eqToHom (congrArg (fun z : c.Cells => z.i.1.right) same) ≫
          pieceCell t i' ⟨b, hb, k'⟩ (some (Order.succ j)) hbb) ≫ pieceStepMap t j hj s h i'
      rw [pieceStepMap_before_cell t j hj s h i ⟨a, ha, k⟩ hba hlt,
        Category.assoc, pieceStepMap_before_cell t j hj s h i' ⟨b, hb, k'⟩ hbb hlt']
      simpa only [Category.assoc] using congrArg (fun q => q ≫ s.inl)
        (sharedCell_inclusion t (some j)
          { left := i, right := i', leftCell := ⟨a, ha, k⟩, rightCell := ⟨b, hb, k'⟩,
            same := same, leftBefore := hlt, rightBefore := hlt' })
    · have haj : a = j := le_antisymm hle (le_of_not_gt hlt)
      subst a
      subst b
      have ek : (t i).cellIndex j hj k = (t i').cellIndex j hj k' := by
        change ({ j := j, hj := hj, k := (t i).cellIndex j hj k } : c.Cells) =
          ({ j := j, hj := hj, k := (t i').cellIndex j hj k' } : c.Cells) at same
        injection same
      change pieceCell t i ⟨j, hj, k⟩ (some (Order.succ j)) hba ≫ pieceStepMap t j hj s h i =
        (eqToHom (congrArg (fun z : c.Cells => z.i.1.right) same) ≫
          pieceCell t i' ⟨j, hj, k'⟩ (some (Order.succ j)) hbb) ≫ pieceStepMap t j hj s h i'
      rw [pieceStepMap_current_cell, Category.assoc, pieceStepMap_current_cell]
      have e : familyOccurrence t j hj i k = familyOccurrence t j hj i' k' := Subtype.ext ek
      have hi : (targetCofan t j hj).inj (familyOccurrence t j hj i k) =
          eqToHom (congrArg (fun z : cells t j hj => (cellLabel t j hj z).1.right) e) ≫
            (targetCofan t j hj).inj (familyOccurrence t j hj i' k') := by
        exact targetCofan_inj_congr t j hj _ _ e
      simpa only [Category.assoc] using congrArg (fun q => q ≫ s.inr) hi

/-- Every test pushout cocone descends through the actual original next-stage union. -/
def stepDesc (h : EffectiveCofibrations C) : obj t (some (Order.succ j)) ⟶ s.pt :=
  Multicoequalizer.desc (index t (some (Order.succ j))) _
    (stepCoconeMap t j hj s h) (stepCoconeCondition t j hj s h)

@[reassoc]
theorem stepDesc_root (h : EffectiveCofibrations C) :
    root t (some (Order.succ j)) ≫ stepDesc t j hj s h = root t (some j) ≫ s.inl :=
  Multicoequalizer.π_desc (index t (some (Order.succ j))) _ _ _ none

@[reassoc]
theorem stepDesc_piece (h : EffectiveCofibrations C) (i : I) :
    inclusion t i (some (Order.succ j)) ≫ stepDesc t j hj s h = pieceStepMap t j hj s h i :=
  Multicoequalizer.π_desc (index t (some (Order.succ j))) _ _ _ (some i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual next-stage descender keeps the supplied source-stage map. -/
@[reassoc]
theorem stepDesc_stage (h : EffectiveCofibrations C) :
    (F t).map (homOfLE (Order.le_succ j)) ≫ stepDesc t j hj s h = s.inl := by
  apply hom_ext t (some j)
  · rw [← Category.assoc, root_map, stepDesc_root]
  · intro i
    rw [← Category.assoc, inclusion_map, Category.assoc, stepDesc_piece]
    exact pieceStepMap_stage t j hj s h i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Every original selected target summand retains the test cocone value. -/
@[reassoc]
theorem stepDesc_cell (h : EffectiveCofibrations C) (k : cells t j hj) :
    targetCell t j hj k ≫ stepDesc t j hj s h = (targetCofan t j hj).inj k ≫ s.inr := by
  obtain ⟨i, a, ek⟩ := k.2
  have e : familyOccurrence t j hj i a = k := Subtype.ext ek
  subst k
  apply (cancel_epi (eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
    ((t i).label_eq j hj a)))).1
  rw [← Category.assoc, targetCell_family t j hj h i a,
    Category.assoc, stepDesc_piece, pieceStepMap_cell]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The complete actual original target cofan retains the test target map. -/
@[reassoc]
theorem stepDesc_target (h : EffectiveCofibrations C) :
    targetMap t j hj ≫ stepDesc t j hj s h = s.inr := by
  apply (colimit.isColimit (Discrete.functor
    (fun k : cells t j hj => (cellLabel t j hj k).1.right))).hom_ext
  intro k
  change (targetCofan t j hj).inj k.as ≫ (targetMap t j hj ≫ stepDesc t j hj s h) =
    (targetCofan t j hj).inj k.as ≫ s.inr
  rw [← Category.assoc, targetMap_inj t j hj k.as, stepDesc_cell]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The source stage and every original selected target cell determine the
actual next-stage descender uniquely. -/
theorem stepDesc_unique (h : EffectiveCofibrations C) (m : obj t (some (Order.succ j)) ⟶ s.pt)
    (hm₀ : (F t).map (homOfLE (Order.le_succ j)) ≫ m = s.inl)
    (hm₁ : targetMap t j hj ≫ m = s.inr) : m = stepDesc t j hj s h := by
  have hmCell (k : cells t j hj) : targetCell t j hj k ≫ m =
    (targetCofan t j hj).inj k ≫ s.inr := by
    rw [← targetMap_inj t j hj k, Category.assoc, hm₁]
  apply hom_ext t (some (Order.succ j))
  · rw [stepDesc_root]
    calc
      root t (some (Order.succ j)) ≫ m =
          (root t (some j) ≫ (F t).map (homOfLE (Order.le_succ j))) ≫ m :=
        congrArg (fun z => z ≫ m) (root_map t (some j) (some (Order.succ j)) (Order.le_succ j)).symm
      _ = root t (some j) ≫ s.inl := by rw [Category.assoc, hm₀]
  · intro i
    rw [stepDesc_piece]
    apply ((t i).complex.attachCells j hj).hom_ext
    · rw [← Category.assoc, ← inclusion_map t i (some j) (some (Order.succ j)) (Order.le_succ j),
        Category.assoc, hm₀, pieceStepMap_stage]
    · intro a
      rw [← Category.assoc, ← targetCell_family t j hj h i a,
        Category.assoc, hmCell, pieceStepMap_cell]
      rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual union successor is the pushout of the selected original I cells. -/
theorem attachingIsPushout (h : EffectiveCofibrations C) :
    IsPushout (sourceMap t j hj) (cellMap t j hj)
      ((F t).map (homOfLE (Order.le_succ j))) (targetMap t j hj) :=
  IsPushout.of_isColimit (PushoutCocone.IsColimit.mk (attaching_square t j hj h)
    (fun s => stepDesc t j hj s h) (fun s => stepDesc_stage t j hj s h)
    (fun s => stepDesc_target t j hj s h)
    (fun s m hm₀ hm₁ => stepDesc_unique t j hj s h m hm₀ hm₁))

/-- All chosen original cells, their unchanged generating labels, and their
actual original maps form the union attaching data. -/
abbrev attachCells (h : EffectiveCofibrations C) :
    AttachCells.{w} d.I.homFamily ((F t).map (homOfLE (Order.le_succ j))) where
  ι := cells t j hj
  π := cellLabel t j hj
  cofan₁ := sourceCofan t j hj
  cofan₂ := targetCofan t j hj
  isColimit₁ := colimit.isColimit _
  isColimit₂ := colimit.isColimit _
  m := cellMap t j hj
  hm := cellMap_inj t j hj
  g₁ := sourceMap t j hj
  g₂ := targetMap t j hj
  isPushout := attachingIsPushout t j hj h

end OriginalAttachments

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The union bottom keeps the original root as its actual inverse map. -/
abbrev botIso (h : EffectiveCofibrations C) : (F t).obj ⊥ ≅ X := by
  let b : obj t (some ⊥) ⟶ X := comparison t (some ⊥) ≫ c.isoBot.hom
  letI : Mono (comparison t (some ⊥)) :=
    h.mono_of_cofibration _ (stageComparisonCofibration t h ⊥)
  letI : Mono b := inferInstance
  have hb : root t (some ⊥) ≫ b = 𝟙 X := by
    dsimp only [b]
    rw [← Category.assoc, root_comparison]
    change (c.isoBot.inv ≫ c.F.map (𝟙 (⊥ : O))) ≫ c.isoBot.hom = 𝟙 X
    rw [c.F.map_id, Category.comp_id, c.isoBot.inv_hom_id]
  refine ⟨b, root t (some ⊥), ?_, hb⟩
  apply (cancel_mono b).1
  rw [Category.assoc, hb, Category.comp_id, Category.id_comp]

/-- The union is an actual relative I-cell history on the unchanged
original ordinal, with exactly the selected original cell occurrences. -/
abbrev complex (h : EffectiveCofibrations C) :
    RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) (root t none) where
  F := F t
  isoBot := botIso t h
  isWellOrderContinuous := wellOrderContinuous t
  incl := (endpointCocone t).ι
  isColimit := endpointIsColimit t
  fac := root_map t (some ⊥) none trivial
  attachCells j hj := attachCells t j hj h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- This is the genuine union subcomplex, preserving the original root,
ordinal, generating arrows, selected occurrences and endpoint cocones. -/
abbrev unionSubcomplex (h : EffectiveCofibrations C) : CellularSubcomplex c where
  endpoint := obj t none
  hom := root t none
  inclusion := comparison t none
  complex := complex t h
  comparison :=
    { app j := comparison t (some j)
      naturality j k g := map_comparison t (some j) (some k) (leOfHom g) }
  comparison_bot := by
    change root t (some ⊥) ≫ comparison t (some ⊥) = c.isoBot.inv
    rw [root_comparison]
    change c.isoBot.inv ≫ c.F.map (𝟙 (⊥ : O)) = c.isoBot.inv
    rw [c.F.map_id, Category.comp_id]
  comparison_endpoint j := map_comparison t (some j) none trivial
  cellIndex j hj := ⟨Subtype.val, Subtype.val_injective⟩
  label_eq j hj k := rfl
  cell_eq j hj k := by
    change cells t j hj at k
    change ((targetCofan t j hj).inj k ≫ targetMap t j hj) ≫
        comparison t (some (Order.succ j)) = 𝟙 _ ≫ (c.attachCells j hj).cell k.1
    rw [targetMap_inj t j hj k, targetCell_comparison, Category.id_comp]

/-- Each original input is a genuine subcomplex of the actual union,
retaining its entire original history and occurrence embedding. -/
def pieceSubcomplex (h : EffectiveCofibrations C) (i : I) : CellularSubcomplex (complex t h) where
  endpoint := (t i).endpoint
  hom := (t i).hom
  inclusion := inclusion t i none
  complex := (t i).complex
  comparison :=
    { app j := inclusion t i (some j)
      naturality j k g := (inclusion_map t i (some j) (some k) (leOfHom g)).symm }
  comparison_bot := by
    change (t i).complex.isoBot.inv ≫ inclusion t i (some ⊥) = root t (some ⊥)
    simpa only [pieceRoot, RelativeCellComplex.rootAtStage, homOfLE_refl,
      CategoryTheory.Functor.map_id, Category.comp_id] using pieceRoot_inclusion t i (some ⊥)
  comparison_endpoint j := (inclusion_map t i (some j) none trivial).symm
  cellIndex j hj :=
    { toFun a := familyOccurrence t j hj i a
      inj' a b hab := (t i).cellIndex j hj |>.injective (congrArg Subtype.val hab) }
  label_eq j hj a := (t i).label_eq j hj a
  cell_eq j hj a := by
    change ((t i).complex.attachCells j hj).cell a ≫ inclusion t i (some (Order.succ j)) =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a)) ≫
        ((targetCofan t j hj).inj (familyOccurrence t j hj i a) ≫ targetMap t j hj)
    rw [targetMap_inj]
    exact (targetCell_family t j hj h i a).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The union selects exactly the union of the original occurrence supports. -/
theorem union_support (h : EffectiveCofibrations C) :
    (unionSubcomplex t h).support = ⋃ i : I, (t i).support := by
  ext a
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨i, k, hk⟩ := b.k.2
    apply Set.mem_iUnion.mpr
    refine ⟨i, ⟨⟨b.j, b.hj, k⟩, ?_⟩⟩
    exact (congrArg (fun k => ({ j := b.j, hj := b.hj, k := k } : c.Cells)) hk).trans hb
  · intro ha
    obtain ⟨i, b, hb⟩ := Set.mem_iUnion.mp ha
    refine ⟨⟨b.j, b.hj, familyOccurrence t b.j b.hj i b.k⟩, ?_⟩
    exact hb

/-- The exact number of original union cells is bounded by the sum of the
actual original input cell counts. -/
theorem union_cells_cardinal_le (h : EffectiveCofibrations C) :
    Cardinal.mk (complex t h).Cells ≤
      Cardinal.sum (fun i : I => Cardinal.mk (t i).complex.Cells) := by
  change Cardinal.mk (unionSubcomplex t h).complex.Cells ≤ _
  rw [← (unionSubcomplex t h).support_cardinal, union_support]
  simpa only [CellularSubcomplex.support_cardinal] using
    (Cardinal.mk_iUnion_le_sum_mk (f := fun i : I => (t i).support))

end HomotopicalAlgebra.EffectiveCellularUnion

namespace HomotopicalAlgebra.EffectiveCellularSubcomplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  {c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f}
  {I : Type w}

/-- Original generation and effective cofibrations construct the actual
same-ordinal union; no compactness or target-cellularity premise is used. -/
def union (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c) :
    CellularSubcomplex c := by
  letI : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact EffectiveCellularUnion.unionSubcomplex t eff

/-- Every supplied actual original subcomplex enters the constructed union. -/
def unionInclusion (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c) (i : I) :
    (t i).endpoint ⟶ (union d eff t).endpoint := by
  letI : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact EffectiveCellularUnion.inclusion t i none

@[reassoc]
theorem unionInclusion_root (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c) (i : I) :
    (t i).hom ≫ unionInclusion d eff t i = (union d eff t).hom := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact EffectiveCellularUnion.pieceRoot_inclusion t i none

@[reassoc]
theorem unionInclusion_ambient (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c)
    (i : I) :
    unionInclusion d eff t i ≫ (union d eff t).inclusion = (t i).inclusion := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact EffectiveCellularUnion.inclusion_comparison t i none

/-- The actual union support is the literal union of the original occurrence supports. -/
theorem union_support (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c) :
    (union d eff t).support = ⋃ i : I, (t i).support := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact EffectiveCellularUnion.union_support t eff

/-- The actual original cell counts bound the actual constructed union cell count. -/
theorem union_cells_cardinal_le (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c) :
    Cardinal.mk (union d eff t).complex.Cells ≤
      Cardinal.sum (fun i : I => Cardinal.mk (t i).complex.Cells) := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact EffectiveCellularUnion.union_cells_cardinal_le t eff

/-- Every actual input inclusion into the constructed union is a cofibration. -/
theorem unionInclusion_cofibration (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c)
    (i : I) :
    cofibrations C (unionInclusion d eff t i) := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  exact EffectiveCellularSubcomplexExtension.inclusionCofibration d
    (EffectiveCellularUnion.complex t eff) eff
    (EffectiveCellularUnion.pieceSubcomplex t eff i)

/-- Effective original cofibrations give the actual monomorphism of each input inclusion. -/
theorem unionInclusion_mono (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c) (i : I) :
    Mono (unionInclusion d eff t i) :=
  eff.mono_of_cofibration _ (unionInclusion_cofibration d eff t i)

/-- Every actual original inclusion carries its original regular-mono presentation. -/
def unionInclusionRegularMono (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c)
    (i : I) :
    RegularMono (unionInclusion d eff t i) :=
  eff.effectivePresentation _ (unionInclusion_cofibration d eff t i)

/-- The actual constructed union inclusion into the original endpoint is a cofibration. -/
theorem union_cofibration (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c) :
    cofibrations C (union d eff t).inclusion :=
  EffectiveCellularSubcomplexExtension.inclusionCofibration d c eff (union d eff t)

/-- The actual constructed union is an original monic subobject. -/
theorem union_mono (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c) :
    Mono (union d eff t).inclusion := eff.mono_of_cofibration _ (union_cofibration d eff t)

/-- The actual union inclusion has its original regular-mono presentation. -/
def unionRegularMono (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c) :
    RegularMono (union d eff t).inclusion := eff.effectivePresentation _ (union_cofibration d eff t)

/-- Literal original support cardinalities bound the actual union support cardinality. -/
theorem union_support_cardinal_le (eff : EffectiveCofibrations C) (t : I → CellularSubcomplex c) :
    Cardinal.mk (union d eff t).support ≤
      Cardinal.sum (fun i : I => Cardinal.mk (t i).support) := by
  rw [union_support]
  exact Cardinal.mk_iUnion_le_sum_mk

end HomotopicalAlgebra.EffectiveCellularSubcomplex

end EffectiveCellularUnionResearchPromotion

section OriginalCellularSourceStructuralAPI

open CategoryTheory.SmallObject

namespace HomotopicalAlgebra.CellularSubcomplexExtension

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.boundary]
abbrev boundary.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.boundary.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.boundary_cell]
theorem boundary_cell (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι) :
    boundary d c j hj k ≫ c.F.map (homOfLE (Order.le_succ j)) =
      d.I.homFamily ((c.attachCells j hj).π k) ≫ (c.attachCells j hj).cell k := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.boundary_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c j hj k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.originalSuccessorCofibration]
theorem originalSuccessorCofibration (j : O) (hj : ¬ IsMax j) :
    cofibrations C (c.F.map (homOfLE (Order.le_succ j))) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.originalSuccessorCofibration
    C _ _ κ _ _ d O _ _ _ _ X
    Y f c j hj

variable (h : CellularSource d)

include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.originalSuccessorMono]
theorem originalSuccessorMono (j : O) (hj : ¬ IsMax j) :
    Mono (c.F.map (homOfLE (Order.le_succ j))) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.originalSuccessorMono
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) j hj

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.generatorTransport]
theorem generatorTransport (p q : d.I.toSet) (e : p = q) :
    d.I.homFamily p ≫ eqToHom (congrArg (fun a : d.I.toSet => a.1.right) e) =
      eqToHom (congrArg (fun a : d.I.toSet => a.1.left) e) ≫ d.I.homFamily q := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.generatorTransport
    C _ _ κ _ _ d p q e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.subcomplexBoundary]
theorem subcomplexBoundary (t : CellularSubcomplex c) (j : O) (hj : ¬ IsMax j)
    (a : (t.complex.attachCells j hj).ι) :
    boundary d t.complex j hj a ≫ t.comparison.app j =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (t.label_eq j hj a)) ≫
        boundary d c j hj (t.cellIndex j hj a) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.subcomplexBoundary
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) t j hj a

section OriginalFamily

variable {T : Type w} (t : T → CellularSubcomplex c) {E B : C}
  (α : ∀ i : T, (t i).endpoint ⟶ E)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyCellImage]
abbrev familyCellImage.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyCellImage.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.FamilyCellCompatible]
abbrev FamilyCellCompatible.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.FamilyCellCompatible.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.Selected]
abbrev Selected.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.Selected.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage]
abbrev selectedCellImage.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage.{api_level_0,
    api_level_1, api_level_2}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage_eq]
theorem selectedCellImage_eq (hcells : FamilyCellCompatible d c t α)
    (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι)
    (hk : Selected d c t j hj k) (i : T) (a : ((t i).complex.attachCells j hj).ι)
    (e : (t i).cellIndex j hj a = k) :
    eqToHom (congrArg (fun a => ((c.attachCells j hj).π a).1.right) e) ≫
      selectedCellImage d c t α j hj k hk = familyCellImage d c t α j hj i a := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage_eq
    C _ _ κ _ _ d O _ _ _ _ X Y f c T
    t E α hcells j hj k hk i a e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyCellImage_boundary]
theorem familyCellImage_boundary (j : O) (hj : ¬ IsMax j) (m : c.F.obj j ⟶ E)
    (hext : ∀ i : T, (t i).comparison.app j ≫ m = (t i).complex.incl.app j ≫ α i)
    (i : T) (a : ((t i).complex.attachCells j hj).ι) :
    d.I.homFamily ((c.attachCells j hj).π ((t i).cellIndex j hj a)) ≫
      familyCellImage d c t α j hj i a =
        boundary d c j hj ((t i).cellIndex j hj a) ≫ m := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyCellImage_boundary
    C _ _ κ _ _ d O _ _ _ _ X Y f
    c (h.effectiveCofibrations) T t E α j hj m hext i a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyCellImage_right]
theorem familyCellImage_right (q : E ⟶ B) (β : Y ⟶ B)
    (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (j : O) (hj : ¬ IsMax j) (i : T) (a : ((t i).complex.attachCells j hj).ι) :
    familyCellImage d c t α j hj i a ≫ q =
      (c.attachCells j hj).cell ((t i).cellIndex j hj a) ≫ c.incl.app (Order.succ j) ≫ β := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyCellImage_right
    C _ _ κ _ _ d O _ _ _ _ X Y f c T
    t E B α q β hα j hj i a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage_boundary]
theorem selectedCellImage_boundary (hcells : FamilyCellCompatible d c t α)
    (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι) (hk : Selected d c t j hj k)
    (m : c.F.obj j ⟶ E)
    (hext : ∀ i : T, (t i).comparison.app j ≫ m = (t i).complex.incl.app j ≫ α i) :
    d.I.homFamily ((c.attachCells j hj).π k) ≫ selectedCellImage d c t α j hj k hk =
      boundary d c j hj k ≫ m := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage_boundary
    C _ _ κ _ _ d O _ _ _ _ X Y
    f c (h.effectiveCofibrations) T t E α hcells j hj k hk m hext

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage_right]
theorem selectedCellImage_right (hcells : FamilyCellCompatible d c t α)
    (q : E ⟶ B) (β : Y ⟶ B) (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (j : O) (hj : ¬ IsMax j) (k : (c.attachCells j hj).ι) (hk : Selected d c t j hj k) :
    selectedCellImage d c t α j hj k hk ≫ q =
      (c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j) ≫ β := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.selectedCellImage_right
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    T t E B α hcells q β hα j hj k hk

variable (q : E ⟶ B) (r : X ⟶ E) (β : Y ⟶ B)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState]
abbrev StageState.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.{api_level_0,
    api_level_1, api_level_2}



/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev StageState.casesOn.{api_level_0, api_level_1, api_level_2, api_level_3} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.casesOn.{api_level_0,
    api_level_1, api_level_2,
    api_level_3}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev StageState.ctorIdx.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.ctorIdx.{api_level_0,
    api_level_1, api_level_2}

alias StageState.ext := HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.ext

alias StageState.ext_iff :=
  HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.ext_iff

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev StageState.mk.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.mk.{api_level_0,
    api_level_1, api_level_2}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev StageState.noConfusion.{api_level_0, api_level_1, api_level_2, api_level_3} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.noConfusion.{api_level_0,
    api_level_1,
    api_level_2, api_level_3}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev StageState.noConfusionType.{api_level_0, api_level_1, api_level_2, api_level_3} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.noConfusionType.{api_level_0,
    api_level_1,
    api_level_2, api_level_3}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev StageState.rec.{api_level_0, api_level_1, api_level_2, api_level_3} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.rec.{api_level_0,
    api_level_1, api_level_2,
    api_level_3}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev StageState.recOn.{api_level_0, api_level_1, api_level_2, api_level_3} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.recOn.{api_level_0,
    api_level_1, api_level_2,
    api_level_3}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev StageState.subcomplex.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.subcomplex.{api_level_0,
    api_level_1, api_level_2}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev StageState.toSqStruct.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.toSqStruct.{api_level_0,
    api_level_1, api_level_2}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev StageState.mk._flat_ctor.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.mk._flat_ctor.{api_level_0,
    api_level_1,
    api_level_2}

alias StageState.mk.inj := HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.mk.inj

alias StageState.mk.injEq :=
  HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.mk.injEq

alias StageState.mk.noConfusion :=
  HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.mk.noConfusion

alias StageState.mk.sizeOf_spec :=
  HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.StageState.mk.sizeOf_spec

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.stageMap]
abbrev stageMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.stageMap.{api_level_0,
    api_level_1, api_level_2}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.stageFunctor]
abbrev stageFunctor.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.stageFunctor.{api_level_0,
    api_level_1, api_level_2}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.missingCellSquare]
theorem missingCellSquare (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j)
    (k : (c.attachCells j hj).ι) :
    CommSq (boundary d c j hj k ≫ s.f') (d.I.homFamily ((c.attachCells j hj).π k)) q
      ((c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j) ≫ β) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.missingCellSquare
    C _ _ κ _ _ d O _ _ _ _ X Y f c T t E
    B α q r β j hj s k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage]
abbrev completionCellImage.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage.{api_level_0,
    api_level_1, api_level_2}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage_boundary]
theorem completionCellImage_boundary (hq : d.I.rlp q)
    (hcells : FamilyCellCompatible d c t α) (j : O) (hj : ¬ IsMax j)
    (s : StageState d c t α q r β j) (k : (c.attachCells j hj).ι) :
    d.I.homFamily ((c.attachCells j hj).π k) ≫ completionCellImage d c t α q r β hq j hj s k =
      boundary d c j hj k ≫ s.f' := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage_boundary
    C _ _ κ _ _ d O _ _ _ _ X
    Y f c (h.effectiveCofibrations) T t E B α q r β hq hcells j hj s k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage_right]
theorem completionCellImage_right (hq : d.I.rlp q)
    (hcells : FamilyCellCompatible d c t α) (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j)
    (k : (c.attachCells j hj).ι) :
    completionCellImage d c t α q r β hq j hj s k ≫ q =
      (c.attachCells j hj).cell k ≫ c.incl.app (Order.succ j) ≫ β := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage_right
    C _ _ κ _ _ d O _ _ _ _ X Y f
    c T t E B α q r β hq hcells hα j hj s k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage_family]
theorem completionCellImage_family (hq : d.I.rlp q)
    (hcells : FamilyCellCompatible d c t α) (j : O) (hj : ¬ IsMax j)
    (s : StageState d c t α q r β j) (i : T) (a : ((t i).complex.attachCells j hj).ι) :
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a)) ≫
      completionCellImage d c t α q r β hq j hj s ((t i).cellIndex j hj a) =
        ((t i).complex.attachCells j hj).cell a ≫ (t i).complex.incl.app (Order.succ j) ≫ α i := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCellImage_family
    C _ _ κ _ _ d O _ _ _ _ X Y
    f c T t E B α q r β hq hcells j hj s i a

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCofanMap]
abbrev completionCofanMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCofanMap.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCofanMap_inj]
theorem completionCofanMap_inj (hq : d.I.rlp q) (j : O) (hj : ¬ IsMax j)
    (s : StageState d c t α q r β j) (k : (c.attachCells j hj).ι) :
    (c.attachCells j hj).cofan₂.inj k ≫ completionCofanMap d c t α q r β hq j hj s =
      completionCellImage d c t α q r β hq j hj s k := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.completionCofanMap_inj
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    T t E B α q r β hq j hj s k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorLift]
def successorLift (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) : c.F.obj (Order.succ j) ⟶ E := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorLift
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) T t E B α q r β hq hcells j hj s

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorLift_stage]
theorem successorLift_stage (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) :
    c.F.map (homOfLE (Order.le_succ j)) ≫ successorLift d c h t α q r β hq hcells j hj s =
      s.f' := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorLift_stage
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) T t E B α q r β hq hcells j hj s

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorLift_cell]
theorem successorLift_cell (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) (k : (c.attachCells j hj).ι) :
    (c.attachCells j hj).cell k ≫ successorLift d c h t α q r β hq hcells j hj s =
      completionCellImage d c t α q r β hq j hj s k := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorLift_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) T t E B α q r β hq hcells j hj s k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.bottomState]
abbrev bottomState.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.bottomState.{api_level_0,
    api_level_1, api_level_2}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorState]
def successorState (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) :
    StageState d c t α q r β (Order.succ j) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorState
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) T t E B α q r β hq hcells hα j hj s

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorState_restrict]
theorem successorState_restrict (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (j : O) (hj : ¬ IsMax j) (s : StageState d c t α q r β j) :
    (stageFunctor d c t α q r β).map (homOfLE (Order.le_succ j)).op
      (successorState d c h t α q r β hq hcells hα j hj s) = s := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.successorState_restrict
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) T t E B α q r β hq hcells hα j hj s

section OriginalLimit

variable {j : O} (hj : Order.IsSuccLimit j)
  (s : ((Set.principalSegIio j).monotone.functor.op ⋙ stageFunctor d c t α q r β).sections)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.ordinaryLimitFamily]
abbrev ordinaryLimitFamily.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.ordinaryLimitFamily.{api_level_0,
    api_level_1, api_level_2}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.limitState]
abbrev limitState.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.limitState.{api_level_0,
    api_level_1, api_level_2}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.limitState_restrict]
theorem limitState_restrict (a : O) (ha : a < j) :
    (stageFunctor d c t α q r β).map (homOfLE ha.le).op
      (limitState d c t α q r β hj s) = s.val (op ⟨a, ha⟩) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.limitState_restrict
    C _ _ κ _ _ d O _ _ _ _ X Y f c T t
    E B α q r β j hj s a ha

end OriginalLimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyInductionData]
def familyInductionData (hq : d.I.rlp q) (hcells : FamilyCellCompatible d c t α)
    (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β) :
    (stageFunctor d c t α q r β).WellOrderInductionData := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.familyInductionData
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) T t E B α q r β hq hcells hα

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.existsFamilyLift]
theorem existsFamilyLift (hq : d.I.rlp q) (hrq : r ≫ q = f ≫ β)
    (hroot : ∀ i : T, (t i).hom ≫ α i = r)
    (hα : ∀ i : T, α i ≫ q = (t i).inclusion ≫ β)
    (hcells : FamilyCellCompatible d c t α) :
    ∃ ℓ : Y ⟶ E, f ≫ ℓ = r ∧ ℓ ≫ q = β ∧ ∀ i : T, (t i).inclusion ≫ ℓ = α i := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.existsFamilyLift
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) T t E B α q r β hq hrq hroot hα hcells

end OriginalFamily

section OriginalInclusion

variable (t : CellularSubcomplex c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionCofibration]
theorem inclusionCofibration : cofibrations C t.inclusion := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionCofibration
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) t

include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionMono]
theorem inclusionMono : Mono t.inclusion := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionMono
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) t

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionRegularMono]
def inclusionRegularMono : RegularMono t.inclusion := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionRegularMono
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) t

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionPushoutEqualizer]
def inclusionPushoutEqualizer :
    IsLimit (Fork.ofι t.inclusion (pushout.condition (f := t.inclusion) (g := t.inclusion))) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.inclusionPushoutEqualizer
    C _ _ κ _ _ d O _ _ _ _ X Y f
    c (h.effectiveCofibrations) t

end OriginalInclusion

end HomotopicalAlgebra.CellularSubcomplexExtension

namespace HomotopicalAlgebra.CellularSubcomplexExtension

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)

omit [OrderBot O] [SuccOrder O] [WellFoundedLT O] in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixNotMax]
theorem prefixNotMax {j : O} (a : Set.Iic j) (ha : ¬ IsMax a) : ¬ IsMax a.1 := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixNotMax O _ j a ha

omit [OrderBot O] [SuccOrder O] [WellFoundedLT O] in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixStage_lt_endpoint]
theorem prefixStage_lt_endpoint {j : O} (a : Set.Iic j) (ha : ¬ IsMax a) : a.1 < j := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixStage_lt_endpoint O _ j a ha

omit [OrderBot O] [WellFoundedLT O] in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSuccessorEq]
theorem prefixSuccessorEq {j : O} (a : Set.Iic j) (ha : ¬ IsMax a) :
    (Order.succ a).1 = Order.succ a.1 := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSuccessorEq O _ _ j a ha

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixShape]
abbrev prefixShape.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixShape.{api_level_0,
    api_level_1, api_level_2}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixStepIso]
abbrev prefixStepIso.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixStepIso.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex]
abbrev prefixComplex.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_functor]
theorem prefixComplex_functor (j : O) :
    (prefixComplex d c j).F = (Set.initialSegIic j).monotone.functor ⋙ c.F := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_functor
    C _ _ κ _ _ d O _ _ _ _ X Y f c j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_isoBot]
theorem prefixComplex_isoBot (j : O) : (prefixComplex d c j).isoBot = c.isoBot := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_isoBot
    C _ _ κ _ _ d O _ _ _ _ X Y f c j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_incl]
theorem prefixComplex_incl (j : O) (a : Set.Iic j) :
    (prefixComplex d c j).incl.app a = c.F.map (homOfLE a.2) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_incl
    C _ _ κ _ _ d O _ _ _ _ X Y f c j a

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_sourceCofan]
theorem prefixComplex_sourceCofan (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).cofan₁ =
      (c.attachCells a.1 (prefixNotMax a ha)).cofan₁ := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_sourceCofan
    C _ _ κ _ _ d O _ _ _ _ X Y f
    c j a ha

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_targetCofan]
theorem prefixComplex_targetCofan (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).cofan₂ =
      (c.attachCells a.1 (prefixNotMax a ha)).cofan₂ := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_targetCofan
    C _ _ κ _ _ d O _ _ _ _ X Y f
    c j a ha

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_label]
theorem prefixComplex_label (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex d c j).attachCells a ha).π k = (c.attachCells a.1 (prefixNotMax a ha)).π k := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_label
    C _ _ κ _ _ d O _ _ _ _ X Y f c j a
    ha k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_attachingMap]
theorem prefixComplex_attachingMap (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex d c j).attachCells a ha).m = (c.attachCells a.1 (prefixNotMax a ha)).m := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_attachingMap
    C _ _ κ _ _ d O _ _ _ _ X Y
    f c j a ha

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_boundary]
theorem prefixComplex_boundary (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    boundary d (prefixComplex d c j) a ha k = boundary d c a.1 (prefixNotMax a ha) k := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_boundary
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    j a ha k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_cell]
theorem prefixComplex_cell (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex d c j).attachCells a ha).cell k =
      (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫
        c.F.map (eqToHom (prefixSuccessorEq a ha).symm) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c j a
    ha k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_cell_inclusion]
theorem prefixComplex_cell_inclusion (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    (({ j := a, hj := ha, k := k } : (prefixComplex d c j).Cells)).ι =
      (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫
        c.F.map (homOfLE (Order.succ_le_of_lt (prefixStage_lt_endpoint a ha))) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixComplex_cell_inclusion
    C _ _ κ _ _ d O _ _ _ _ X
    Y f c j a ha k

variable (t : CellularSubcomplex c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSubcomplex]
abbrev prefixSubcomplex (j : O) : CellularSubcomplex (prefixComplex d c j) where
  endpoint := t.complex.F.obj j
  hom := (EffectiveCellularSubcomplexExtension.prefixSubcomplex d c t j).hom
  inclusion := t.comparison.app j
  complex := (EffectiveCellularSubcomplexExtension.prefixSubcomplex d c t j).complex
  comparison := (EffectiveCellularSubcomplexExtension.prefixSubcomplex d c t j).comparison
  comparison_bot := (EffectiveCellularSubcomplexExtension.prefixSubcomplex d c t j).comparison_bot
  comparison_endpoint a :=
    (EffectiveCellularSubcomplexExtension.prefixSubcomplex d c t j).comparison_endpoint a
  cellIndex a ha := (EffectiveCellularSubcomplexExtension.prefixSubcomplex d c t j).cellIndex a ha
  label_eq a ha k := (EffectiveCellularSubcomplexExtension.prefixSubcomplex d c t j).label_eq a ha k
  cell_eq a ha k := (EffectiveCellularSubcomplexExtension.prefixSubcomplex d c t j).cell_eq a ha k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSubcomplex_endpoint]
theorem prefixSubcomplex_endpoint (j : O) :
    (prefixSubcomplex d c t j).endpoint = t.complex.F.obj j :=
  EffectiveCellularSubcomplexExtension.prefixSubcomplex_endpoint d c t j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSubcomplex_inclusion]
theorem prefixSubcomplex_inclusion (j : O) :
    (prefixSubcomplex d c t j).inclusion = t.comparison.app j :=
  EffectiveCellularSubcomplexExtension.prefixSubcomplex_inclusion d c t j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSubcomplex_cellIndex]
theorem prefixSubcomplex_cellIndex (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    (prefixSubcomplex d c t j).cellIndex a ha = t.cellIndex a.1 (prefixNotMax a ha) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexExtension.prefixSubcomplex_cellIndex
    C _ _ κ _ _ d O _ _ _ _ X Y
    f c t j a ha







end HomotopicalAlgebra.CellularSubcomplexExtension


open HomotopicalAlgebra.CellularSubcomplexExtension

namespace HomotopicalAlgebra.CellularSubcomplexContainment

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (t u : CellularSubcomplex c)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.SupportLE]
abbrev SupportLE.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.SupportLE.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportRefl]
theorem supportRefl : SupportLE d c t t := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportRefl
    C _ _ κ _ _ d O _ _ _ _ X Y f c t

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportTrans]
theorem supportTrans (v : CellularSubcomplex c) (H : SupportLE d c t u) (K : SupportLE d c u v) :
    SupportLE d c t v := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportTrans
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u v H
    K

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.originalCell_injective]
theorem originalCell_injective : Function.Injective t.originalCell := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.originalCell_injective
    C _ _ κ _ _ d O _ _ _ _ X Y f
    c t

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCell]
abbrev supportCell.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCell.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCell_original]
theorem supportCell_original (H : SupportLE d c t u) (a : t.complex.Cells) :
    u.originalCell (supportCell d c t u H a) = t.originalCell a := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCell_original
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    t u H a

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCell_stage]
theorem supportCell_stage (H : SupportLE d c t u) (a : t.complex.Cells) :
    (supportCell d c t u H a).j = a.j := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCell_stage
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    H a

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCellEmbedding]
abbrev supportCellEmbedding.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.supportCellEmbedding.{api_level_0,
    api_level_1,
    api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.cellLabelEq]
theorem cellLabelEq (a : t.complex.Cells) (b : u.complex.Cells)
    (hab : u.originalCell b = t.originalCell a) : a.i = b.i := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.cellLabelEq
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u a b
    hab

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.ambientCell_transport]
theorem ambientCell_transport (a b : c.Cells) (e : a = b) :
    eqToHom (congrArg (fun z : c.Cells => z.i.1.right) e) ≫ b.ι = a.ι := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.ambientCell_transport
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    a b e

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.cellMapInto]
abbrev cellMapInto.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.cellMapInto.{api_level_0,
    api_level_1, api_level_2}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.cellMapInto_ambient]
theorem cellMapInto_ambient (a : t.complex.Cells) (b : u.complex.Cells)
    (hab : u.originalCell b = t.originalCell a) :
    cellMapInto d c t u a b hab ≫ u.inclusion = a.ι ≫ t.inclusion := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.cellMapInto_ambient
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u a b hab

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.occurrenceEmbedding]
abbrev occurrenceEmbedding.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.occurrenceEmbedding.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.existsStageCell]
theorem existsStageCell (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) :
    ∃ a : (u.complex.attachCells j hj).ι, u.cellIndex j hj a = t.cellIndex j hj k := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.existsStageCell
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u H
    j hj k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCell]
abbrev stageCell.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCell.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCell_original]
theorem stageCell_original (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) :
    u.cellIndex j hj (stageCell d c t u H j hj k) = t.cellIndex j hj k := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCell_original
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u H j hj k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCellEmbedding]
abbrev stageCellEmbedding.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCellEmbedding.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCell_label]
theorem stageCell_label (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).π k =
      (u.complex.attachCells j hj).π (stageCell d c t u H j hj k) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCell_label
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u H
    j hj k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.prefixSupportLE]
theorem prefixSupportLE (H : SupportLE d c t u) (j : O) :
    SupportLE d (prefixComplex d c j) (prefixSubcomplex d c t j) (prefixSubcomplex d c u j) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.prefixSupportLE
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u H
    j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.ambientStageCell_transport]
theorem ambientStageCell_transport (j : O) (hj : ¬ IsMax j)
    (a b : (c.attachCells j hj).ι) (e : a = b) :
    eqToHom (congrArg (fun k => ((c.attachCells j hj).π k).1.right) e) ≫
      (c.attachCells j hj).cell b = (c.attachCells j hj).cell a := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.ambientStageCell_transport
    C _ _ κ _ _ d O _ _ _ _ X
    Y f c j hj a b e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCellMap_ambient]
theorem stageCellMap_ambient (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).cell k ≫ t.comparison.app (Order.succ j) =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (stageCell_label d c t u H j hj k)) ≫
        ((u.complex.attachCells j hj).cell (stageCell d c t u H j hj k) ≫
          u.comparison.app (Order.succ j)) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageCellMap_ambient
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    t u H j hj k

variable (h : CellularSource d)

include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.existsContainmentMap]
theorem existsContainmentMap (H : SupportLE d c t u) :
    ∃ m : t.endpoint ⟶ u.endpoint, m ≫ u.inclusion = t.inclusion := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.existsContainmentMap
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    t u (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap]
def containmentMap (H : SupportLE d c t u) : t.endpoint ⟶ u.endpoint := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_ambient]
theorem containmentMap_ambient (H : SupportLE d c t u) :
    containmentMap d c t u h H ≫ u.inclusion = t.inclusion := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_ambient
    C _ _ κ _ _ d O _ _ _ _ X Y f
    c t u (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_root]
theorem containmentMap_root (H : SupportLE d c t u) :
    t.hom ≫ containmentMap d c t u h H = u.hom := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_root
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_unique]
theorem containmentMap_unique (H : SupportLE d c t u) (m : t.endpoint ⟶ u.endpoint)
    (hm : m ≫ u.inclusion = t.inclusion) : m = containmentMap d c t u h H := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_unique
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    t u (h.effectiveCofibrations) H m hm

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_cell]
theorem containmentMap_cell (H : SupportLE d c t u) (a : t.complex.Cells) (b : u.complex.Cells)
    (hab : u.originalCell b = t.originalCell a) :
    a.ι ≫ containmentMap d c t u h H = cellMapInto d c t u a b hab := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u (h.effectiveCofibrations) H a b hab

include h in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageComparisonMono]
theorem stageComparisonMono (v : CellularSubcomplex c) (j : O) : Mono (v.comparison.app j) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageComparisonMono
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    (h.effectiveCofibrations) v j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap]
def stageMap (H : SupportLE d c t u) (j : O) : t.complex.F.obj j ⟶ u.complex.F.obj j := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_ambient]
theorem stageMap_ambient (H : SupportLE d c t u) (j : O) :
    stageMap d c t u h H j ≫ u.comparison.app j = t.comparison.app j := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_ambient
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_unique]
theorem stageMap_unique (H : SupportLE d c t u) (j : O) (m : t.complex.F.obj j ⟶ u.complex.F.obj j)
    (hm : m ≫ u.comparison.app j = t.comparison.app j) : m = stageMap d c t u h H j := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_unique
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H j m hm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_cell]
theorem stageMap_cell (H : SupportLE d c t u) (j : O) (hj : ¬ IsMax j)
    (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).cell k ≫ stageMap d c t u h H (Order.succ j) =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (stageCell_label d c t u H j hj k)) ≫
        (u.complex.attachCells j hj).cell (stageCell d c t u H j hj k) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H j hj k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_naturality]
theorem stageMap_naturality (H : SupportLE d c t u) {j k : O} (a : j ⟶ k) :
    t.complex.F.map a ≫ stageMap d c t u h H k =
      stageMap d c t u h H j ≫ u.complex.F.map a := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_naturality
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u (h.effectiveCofibrations) H j k a

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison]
def comparison (H : SupportLE d c t u) : t.complex.F ⟶ u.complex.F := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_ambient]
theorem comparison_ambient (H : SupportLE d c t u) :
    comparison d c t u h H ≫ u.comparison = t.comparison := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_ambient
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_endpoint]
theorem comparison_endpoint (H : SupportLE d c t u) (j : O) :
    t.complex.incl.app j ≫ containmentMap d c t u h H =
      (comparison d c t u h H).app j ≫ u.complex.incl.app j := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_endpoint
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u (h.effectiveCofibrations) H j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_bot]
theorem comparison_bot (H : SupportLE d c t u) :
    t.complex.isoBot.inv ≫ (comparison d c t u h H).app ⊥ = u.complex.isoBot.inv := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_bot
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_unique]
theorem comparison_unique (H : SupportLE d c t u) (a : t.complex.F ⟶ u.complex.F)
    (ha : a ≫ u.comparison = t.comparison) : a = comparison d c t u h H := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_unique
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H a ha

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex]
def asSubcomplex (H : SupportLE d c t u) : CellularSubcomplex u.complex := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex_complex]
theorem asSubcomplex_complex (H : SupportLE d c t u) :
    (asSubcomplex d c t u h H).complex = t.complex := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex_complex
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    t u (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex_inclusion]
theorem asSubcomplex_inclusion (H : SupportLE d c t u) :
    (asSubcomplex d c t u h H).inclusion = containmentMap d c t u h H := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex_inclusion
    C _ _ κ _ _ d O _ _ _ _ X Y f
    c t u (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex_comparison]
theorem asSubcomplex_comparison (H : SupportLE d c t u) :
    (asSubcomplex d c t u h H).comparison = comparison d c t u h H := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.asSubcomplex_comparison
    C _ _ κ _ _ d O _ _ _ _ X Y f
    c t u (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_cofibration]
theorem containmentMap_cofibration (H : SupportLE d c t u) :
    cofibrations C (containmentMap d c t u h H) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_cofibration
    C _ _ κ _ _ d O _ _ _ _ X
    Y f c t u (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_mono]
theorem containmentMap_mono (H : SupportLE d c t u) : Mono (containmentMap d c t u h H) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_mono
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMapRegularMono]
def containmentMapRegularMono (H : SupportLE d c t u) :
    RegularMono (containmentMap d c t u h H) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMapRegularMono
    C _ _ κ _ _ d O _ _ _ _ X Y
    f c t u (h.effectiveCofibrations) H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_cofibration]
theorem stageMap_cofibration (H : SupportLE d c t u) (j : O) :
    cofibrations C (stageMap d c t u h H j) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_cofibration
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    t u (h.effectiveCofibrations) H j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_mono]
theorem stageMap_mono (H : SupportLE d c t u) (j : O) : Mono (stageMap d c t u h H j) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_mono
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMapRegularMono]
def stageMapRegularMono (H : SupportLE d c t u) (j : O) : RegularMono (stageMap d c t u h H j) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMapRegularMono
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u (h.effectiveCofibrations) H j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_root]
theorem stageMap_root (H : SupportLE d c t u) (j : O) :
    (t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫
      stageMap d c t u h H j =
        u.complex.isoBot.inv ≫ u.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j)) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_root
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) H j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_refl]
theorem containmentMap_refl (H : SupportLE d c t t) :
    containmentMap d c t t h H = 𝟙 t.endpoint := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_refl
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    (h.effectiveCofibrations) H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_comp]
theorem containmentMap_comp (v : CellularSubcomplex c) (H : SupportLE d c t u)
    (K : SupportLE d c u v) :
    containmentMap d c t u h H ≫ containmentMap d c u v h K =
      containmentMap d c t v h (supportTrans d c t u v H K) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.containmentMap_comp
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u (h.effectiveCofibrations) v H K

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_refl]
theorem stageMap_refl (H : SupportLE d c t t) (j : O) :
    stageMap d c t t h H j = 𝟙 (t.complex.F.obj j) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_refl
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    (h.effectiveCofibrations) H j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_comp]
theorem stageMap_comp (v : CellularSubcomplex c) (H : SupportLE d c t u) (K : SupportLE d c u v)
    (j : O) :
    stageMap d c t u h H j ≫ stageMap d c u v h K j =
      stageMap d c t v h (supportTrans d c t u v H K) j := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageMap_comp
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) v H K j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_refl]
theorem comparison_refl (H : SupportLE d c t t) : comparison d c t t h H = 𝟙 t.complex.F := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_refl
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    (h.effectiveCofibrations) H

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_comp]
theorem comparison_comp (v : CellularSubcomplex c) (H : SupportLE d c t u) (K : SupportLE d c u v) :
    comparison d c t u h H ≫ comparison d c u v h K =
      comparison d c t v h (supportTrans d c t u v H K) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparison_comp
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) v H K

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso]
def endpointIso (e : Set.range t.originalCell = Set.range u.originalCell) :
    t.endpoint ≅ u.endpoint := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso]
def stageIso (e : Set.range t.originalCell = Set.range u.originalCell) (j : O) :
    t.complex.F.obj j ≅ u.complex.F.obj j := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) e j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparisonIso]
def comparisonIso (e : Set.range t.originalCell = Set.range u.originalCell) :
    t.complex.F ≅ u.complex.F := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparisonIso
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) e

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso_root]
theorem endpointIso_root (e : Set.range t.originalCell = Set.range u.originalCell) :
    t.hom ≫ (endpointIso d c t u h e).hom = u.hom := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso_root
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) e

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso_ambient]
theorem endpointIso_ambient (e : Set.range t.originalCell = Set.range u.originalCell) :
    (endpointIso d c t u h e).hom ≫ u.inclusion = t.inclusion := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso_ambient
    C _ _ κ _ _ d O _ _ _ _ X Y f c t
    u (h.effectiveCofibrations) e

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso_ambient]
theorem stageIso_ambient (e : Set.range t.originalCell = Set.range u.originalCell) (j : O) :
    (stageIso d c t u h e j).hom ≫ u.comparison.app j = t.comparison.app j := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso_ambient
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) e j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparisonIso_ambient]
theorem comparisonIso_ambient (e : Set.range t.originalCell = Set.range u.originalCell) :
    (comparisonIso d c t u h e).hom ≫ u.comparison = t.comparison := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.comparisonIso_ambient
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    t u (h.effectiveCofibrations) e

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.isomorphism_endpoint]
theorem isomorphism_endpoint (e : Set.range t.originalCell = Set.range u.originalCell) (j : O) :
    t.complex.incl.app j ≫ (endpointIso d c t u h e).hom =
      (stageIso d c t u h e j).hom ≫ u.complex.incl.app j := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.isomorphism_endpoint
    C _ _ κ _ _ d O _ _ _ _ X Y f c
    t u (h.effectiveCofibrations) e j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso_cell]
theorem endpointIso_cell (e : Set.range t.originalCell = Set.range u.originalCell)
    (a : t.complex.Cells) (b : u.complex.Cells) (hab : u.originalCell b = t.originalCell a) :
    a.ι ≫ (endpointIso d c t u h e).hom = cellMapInto d c t u a b hab := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.endpointIso_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) e a b hab

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso_root]
theorem stageIso_root (e : Set.range t.originalCell = Set.range u.originalCell) (j : O) :
    (t.complex.isoBot.inv ≫ t.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))) ≫
      (stageIso d c t u h e j).hom =
        u.complex.isoBot.inv ≫ u.complex.F.map (homOfLE (bot_le : (⊥ : O) ≤ j)) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso_root
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) e j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso_cell]
theorem stageIso_cell (e : Set.range t.originalCell = Set.range u.originalCell)
    (j : O) (hj : ¬ IsMax j) (k : (t.complex.attachCells j hj).ι) :
    (t.complex.attachCells j hj).cell k ≫ (stageIso d c t u h e (Order.succ j)).hom =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (stageCell_label d c t u e.le j hj k)) ≫
        (u.complex.attachCells j hj).cell (stageCell d c t u e.le j hj k) := by
  exact @HomotopicalAlgebra.EffectiveCellularSubcomplexContainment.stageIso_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c t u
    (h.effectiveCofibrations) e j hj k



end HomotopicalAlgebra.CellularSubcomplexContainment


open HomotopicalAlgebra.CellularSubcomplexExtension

namespace HomotopicalAlgebra.CellularCofibrationPushout

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {A B L P : C} (f : A ⟶ B) (g : A ⟶ L) (i : B ⟶ P) (j : L ⟶ P)
  (sq : IsPushout f g i j)

/-- The actual original root of the duplicated top target. -/
def duplicateSourceRoot : A ⟶ pushout f f := f ≫ pushout.inl f f

/-- The actual original left-root map into the duplicated pushout target. -/
def duplicateTargetRoot : L ⟶ pushout j j := j ≫ pushout.inl j j

/-- Both original top maps construct the actual comparison of the two duplicate pushouts. -/
def duplicateMap : pushout f f ⟶ pushout j j :=
  pushout.desc (i ≫ pushout.inl j j) (i ≫ pushout.inr j j) (by
    calc
      f ≫ (i ≫ pushout.inl j j) = (f ≫ i) ≫ pushout.inl j j := (Category.assoc _ _ _).symm
      _ = (g ≫ j) ≫ pushout.inl j j := congrArg (fun z => z ≫ pushout.inl j j) sq.w
      _ = g ≫ (j ≫ pushout.inl j j) := Category.assoc _ _ _
      _ = g ≫ (j ≫ pushout.inr j j) := congrArg (fun z => g ≫ z) pushout.condition
      _ = (f ≫ i) ≫ pushout.inr j j := by rw [← Category.assoc, sq.w]
      _ = f ≫ (i ≫ pushout.inr j j) := Category.assoc _ _ _)

/-- The first original duplicated inclusion remains the same original top composite. -/
theorem duplicateMap_left : pushout.inl f f ≫ duplicateMap f g i j sq = i ≫ pushout.inl j j :=
  pushout.inl_desc _ _ _

/-- The second original duplicated inclusion remains the same original top composite. -/
theorem duplicateMap_right : pushout.inr f f ≫ duplicateMap f g i j sq = i ≫ pushout.inr j j :=
  pushout.inr_desc _ _ _

/-- The actual original root square of the duplicate comparison commutes. -/
theorem duplicateMap_root :
    duplicateSourceRoot f ≫ duplicateMap f g i j sq = g ≫ duplicateTargetRoot j := by
  dsimp only [duplicateSourceRoot, duplicateTargetRoot]
  rw [Category.assoc, duplicateMap_left, ← Category.assoc, sq.w, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The duplicate comparison is an actual cobase change of the original left arrow. -/
theorem duplicateIsPushout :
    IsPushout (duplicateSourceRoot f) g (duplicateMap f g i j sq) (duplicateTargetRoot j) := by
  refine IsPushout.mk' (duplicateMap_root f g i j sq) ?_ ?_
  · intro Z a b hab hl
    apply pushout.hom_ext
    · apply sq.hom_ext
      · simpa only [← Category.assoc, duplicateMap_left] using
          congrArg (fun z => pushout.inl f f ≫ z) hab
      · simpa only [duplicateTargetRoot, ← Category.assoc] using hl
    · apply sq.hom_ext
      · simpa only [← Category.assoc, duplicateMap_right] using
          congrArg (fun z => pushout.inr f f ≫ z) hab
      · simpa only [duplicateTargetRoot, ← Category.assoc, pushout.condition] using hl
  · intro Z a b hab
    have h₀ : f ≫ (pushout.inl f f ≫ a) = g ≫ b := by
      simpa only [duplicateSourceRoot, Category.assoc] using hab
    have h₁ : f ≫ (pushout.inr f f ≫ a) = g ≫ b := by
      rw [← Category.assoc, ← pushout.condition]
      exact hab
    let a₀ := sq.desc (pushout.inl f f ≫ a) b h₀
    let a₁ := sq.desc (pushout.inr f f ≫ a) b h₁
    have hleft : j ≫ a₀ = b := sq.inr_desc _ _ _
    have hright : j ≫ a₁ = b := sq.inr_desc _ _ _
    let m := pushout.desc a₀ a₁ (hleft.trans hright.symm)
    refine ⟨m, ?_, ?_⟩
    · apply pushout.hom_ext
      · rw [← Category.assoc, duplicateMap_left, Category.assoc, pushout.inl_desc]
        exact sq.inl_desc _ _ _
      · rw [← Category.assoc, duplicateMap_right, Category.assoc, pushout.inr_desc]
        exact sq.inl_desc _ _ _
    · dsimp only [duplicateTargetRoot]
      rw [Category.assoc, pushout.inl_desc]
      exact hleft

/-- The original left cofibration gives the actual duplicate comparison cofibration. -/
theorem duplicateMap_cofibration (hg : cofibrations C g) :
    cofibrations C (duplicateMap f g i j sq) :=
  (cofibrations C).of_isPushout (duplicateIsPushout f g i j sq) hg

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)

include d h in
/-- Cellularity proves monicity of the actual duplicate comparison. -/
theorem duplicateMap_mono (hg : cofibrations C g) : Mono (duplicateMap f g i j sq) :=
  h.mono_of_cofibration _ (duplicateMap_cofibration f g i j sq hg)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include d h sq in
/-- Any actual pushout of two original cellular cofibrations is the same actual pullback square. -/
theorem isPullback (hf : cofibrations C f) (hg : cofibrations C g) : IsPullback f g i j := by
  let _ : Mono f := h.mono_of_cofibration f hf
  let _ : Mono j := h.mono_of_cofibration j ((cofibrations C).of_isPushout sq.flip hf)
  let _ : Mono (duplicateMap f g i j sq) := duplicateMap_mono f g i j sq d h hg
  refine IsPullback.mk' sq.w ?_ ?_
  · intro Z a b hab _hgb
    exact (cancel_mono f).1 hab
  · intro Z a b hab
    have hdup : a ≫ pushout.inl f f = a ≫ pushout.inr f f := by
      apply (cancel_mono (duplicateMap f g i j sq)).1
      rw [Category.assoc, duplicateMap_left, Category.assoc, duplicateMap_right]
      simp only [← Category.assoc]
      rw [hab]
      simp only [Category.assoc]
      rw [pushout.condition]
    let eqf := h.originalPushoutEqualizer f hf
    let m := Fork.IsLimit.lift eqf a hdup
    have hmf : m ≫ f = a := Fork.IsLimit.lift_ι' eqf a hdup
    have hmg : m ≫ g = b := by
      apply (cancel_mono j).1
      rw [Category.assoc, ← sq.w, ← Category.assoc, hmf, hab]
    exact ⟨m, hmf, hmg⟩

end HomotopicalAlgebra.CellularCofibrationPushout


open HomotopicalAlgebra.CellularSubcomplexExtension

namespace HomotopicalAlgebra.CellularAttachmentComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

section OriginalAttachment

variable {S X : C} {f : S ⟶ X} (a : AttachCells.{w} d.I.homFamily f)

/-- The actual original attaching-domain map of one original occurrence. -/
def boundary (k : a.ι) : (a.π k).1.left ⟶ S := a.cofan₁.inj k ≫ a.g₁

/-- Every original occurrence retains its original attaching square. -/
theorem boundary_cell (k : a.ι) : boundary d a k ≫ f = d.I.homFamily (a.π k) ≫ a.cell k := by
  dsimp only [boundary, AttachCells.cell]
  rw [Category.assoc, a.isPushout.w, ← Category.assoc, a.hm]
  exact Category.assoc _ _ _

include d a in
/-- Any given actual original I attachment is an actual original cofibration. -/
theorem attachmentCofibration : cofibrations C f := by
  rw [← trivialFibrations_llp, ← d.I_rlp]
  exact d.I.transfiniteCompositions_pushouts_coproducts_le_llp_rlp _
    (CategoryTheory.SmallObject.attachCells_mem_relativeCellMaps d.I a)

end OriginalAttachment

variable (h : CellularSource d)
  {S T X Y : C} (δ : S ⟶ T) (f : S ⟶ X) (g : T ⟶ Y) (u : X ⟶ Y)
  (a : AttachCells.{w} d.I.homFamily f) (b : AttachCells.{w} d.I.homFamily g)
  (cellIndex : a.ι ↪ b.ι)
  (labelEq : ∀ k : a.ι, a.π k = b.π (cellIndex k))
  (rootEq : f ≫ u = δ ≫ g)
  (cellEq : ∀ k : a.ι, a.cell k ≫ u =
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (labelEq k)) ≫ b.cell (cellIndex k))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h rootEq cellEq in
/-- The original selected codomain squares determine the original attaching-domain comparison. -/
theorem selectedBoundary (k : a.ι) :
    boundary d a k ≫ δ =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (labelEq k)) ≫
        boundary d b (cellIndex k) := by
  let _ : Mono g := h.mono_of_cofibration g (attachmentCofibration d b)
  apply (cancel_mono g).1
  calc
    _ = boundary d a k ≫ (f ≫ u) := by rw [Category.assoc, rootEq]
    _ = (d.I.homFamily (a.π k) ≫ a.cell k) ≫ u := by rw [← Category.assoc, boundary_cell]
    _ = d.I.homFamily (a.π k) ≫
        (eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (labelEq k)) ≫
          b.cell (cellIndex k)) := by
          rw [Category.assoc, cellEq k]
    _ = (eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (labelEq k)) ≫
        d.I.homFamily (b.π (cellIndex k))) ≫ b.cell (cellIndex k) := by
          rw [← Category.assoc, generatorTransport d _ _ (labelEq k)]
    _ = (eqToHom (congrArg (fun p : d.I.toSet => p.1.left) (labelEq k)) ≫
        boundary d b (cellIndex k)) ≫ g := by
          rw [Category.assoc, ← boundary_cell d b (cellIndex k), ← Category.assoc]

section OriginalComparisonLift

variable {E B : C} (p : E ⟶ B) (hp : d.I.rlp p) (α : X ⟶ E) (β : Y ⟶ B)
  (sq : CommSq α u p β) (m : T ⟶ E)
  (hm : δ ≫ m = f ≫ α) (hmp : m ≫ p = g ≫ β)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h rootEq cellEq hp sq hm hmp in
/-- Every original large occurrence is filled, while all selected original codomain maps are
prescribed. -/
theorem cellLiftExists (i : b.ι) :
    ∃ n : (b.π i).1.right ⟶ E,
      d.I.homFamily (b.π i) ≫ n = boundary d b i ≫ m ∧ n ≫ p = b.cell i ≫ β ∧
        ∀ (k : a.ι) (e : cellIndex k = i),
          eqToHom (congrArg (fun x : d.I.toSet => x.1.right)
            ((labelEq k).trans (congrArg b.π e))) ≫ n = a.cell k ≫ α := by
  classical
  by_cases hi : ∃ k : a.ι, cellIndex k = i
  · obtain ⟨k, rfl⟩ := hi
    let n : (b.π (cellIndex k)).1.right ⟶ E :=
      eqToHom (congrArg (fun x : d.I.toSet => x.1.right) (labelEq k).symm) ≫ a.cell k ≫ α
    refine ⟨n, ?_, ?_, ?_⟩
    · let Li := eqToHom (congrArg (fun x : d.I.toSet => x.1.left) (labelEq k).symm)
      calc
        _ = (Li ≫ d.I.homFamily (a.π k)) ≫ (a.cell k ≫ α) := by
          dsimp only [n]
          rw [← Category.assoc, generatorTransport d _ _ (labelEq k).symm]
        _ = Li ≫ ((d.I.homFamily (a.π k) ≫ a.cell k) ≫ α) := by simp only [Category.assoc]
        _ = Li ≫ ((boundary d a k ≫ f) ≫ α) := by rw [← boundary_cell d a k]
        _ = Li ≫ ((boundary d a k ≫ δ) ≫ m) := by
          rw [Category.assoc, ← hm]
          simp only [Category.assoc]
        _ = Li ≫ ((eqToHom (congrArg (fun x : d.I.toSet => x.1.left) (labelEq k)) ≫
            boundary d b (cellIndex k)) ≫ m) := by
              rw [selectedBoundary d h δ f g u a b cellIndex labelEq rootEq cellEq k]
        _ = boundary d b (cellIndex k) ≫ m := by
          dsimp only [Li]
          simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    · dsimp only [n]
      simp only [Category.assoc]
      rw [sq.w, ← Category.assoc (a.cell k), cellEq k]
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    · intro k' e
      have hk' : k' = k := cellIndex.injective e
      subst k'
      dsimp only [n]
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  · let _ : HasLiftingProperty (d.I.homFamily (b.π i)) p := hp _ (b.π i).2
    have sqi : CommSq (boundary d b i ≫ m) (d.I.homFamily (b.π i)) p (b.cell i ≫ β) :=
      ⟨by rw [Category.assoc, hmp, ← Category.assoc, boundary_cell, Category.assoc]⟩
    exact ⟨sqi.lift, sqi.fac_left, sqi.fac_right, fun k e => (hi ⟨k, e⟩).elim⟩

end OriginalComparisonLift

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include h rootEq cellEq in
/-- The original root cofibration and original I lifts extend the whole actual attachment
comparison. -/
theorem comparisonHasLiftingProperty (hδ : cofibrations C δ) {E B : C} (p : E ⟶ B)
    (hp : d.I.rlp p) :
    HasLiftingProperty u p := by
  have hδI : d.I.rlp.llp δ := by rw [d.I_rlp, trivialFibrations_llp]; exact hδ
  let _ : HasLiftingProperty δ p := hδI _ hp
  refine ⟨fun {α} {β} sq => ?_⟩
  have rootSq : CommSq (f ≫ α) δ p (g ≫ β) :=
    ⟨by rw [Category.assoc, sq.w, ← Category.assoc, rootEq, Category.assoc]⟩
  let m := rootSq.lift
  have hm : δ ≫ m = f ≫ α := rootSq.fac_left
  have hmp : m ≫ p = g ≫ β := rootSq.fac_right
  let target (i : b.ι) : (b.π i).1.right ⟶ E :=
    (cellLiftExists d h δ f g u a b cellIndex labelEq rootEq cellEq p hp α β sq m hm hmp i).choose
  have htarget (i : b.ι) :=
    (cellLiftExists d h δ f g u a b cellIndex labelEq
      rootEq cellEq p hp α β sq m hm hmp i).choose_spec
  let n : b.cofan₂.pt ⟶ E := b.isColimit₂.desc (Cofan.mk E target)
  have hn (i : b.ι) : b.cofan₂.inj i ≫ n = target i := b.isColimit₂.fac _ ⟨i⟩
  have hmn : b.g₁ ≫ m = b.m ≫ n := by
    apply b.isColimit₁.hom_ext
    intro i
    change b.cofan₁.inj i.as ≫ (b.g₁ ≫ m) = b.cofan₁.inj i.as ≫ (b.m ≫ n)
    rw [← Category.assoc, ← Category.assoc, b.hm]
    simp only [Category.assoc]
    rw [hn]
    simpa only [target, boundary, Category.assoc] using (htarget i.as).1.symm
  let ℓ := b.isPushout.desc m n hmn
  have hℓroot : g ≫ ℓ = m := b.isPushout.inl_desc _ _ _
  have hℓcell (i : b.ι) : b.cell i ≫ ℓ = target i := by
    rw [AttachCells.cell, Category.assoc, b.isPushout.inr_desc, hn]
  have hℓp : ℓ ≫ p = β := by
    apply b.hom_ext
    · rw [← Category.assoc, hℓroot]
      exact hmp
    · intro i
      rw [← Category.assoc, hℓcell]
      exact (htarget i).2.1
  have huℓ : u ≫ ℓ = α := by
    apply a.hom_ext
    · rw [← Category.assoc, rootEq, Category.assoc, hℓroot]
      exact hm
    · intro k
      rw [← Category.assoc, cellEq k, Category.assoc, hℓcell]
      exact (htarget (cellIndex k)).2.2 k rfl
  exact CommSq.HasLift.mk' { l := ℓ, fac_left := huℓ, fac_right := hℓp }

include h rootEq cellEq in
/-- The actual subset-attachment comparison is a cofibration with its original root and
occurrences. -/
theorem comparisonCofibration (hδ : cofibrations C δ) : cofibrations C u := by
  rw [← trivialFibrations_llp, ← d.I_rlp]
  intro E B p hp
  exact comparisonHasLiftingProperty d h δ f g u a b cellIndex labelEq rootEq cellEq hδ p hp

include h rootEq cellEq in
/-- Original cellularity gives the actual monomorphism of the proved comparison cofibration. -/
theorem comparisonMono (hδ : cofibrations C δ) : Mono u :=
  h.mono_of_cofibration u
    (comparisonCofibration d h δ f g u a b cellIndex labelEq rootEq cellEq hδ)

/-- The proved original comparison cofibration has its actual regular-mono presentation. -/
def comparisonRegularMono (hδ : cofibrations C δ) : RegularMono u :=
  h.effectivePresentation u
    (comparisonCofibration d h δ f g u a b cellIndex labelEq rootEq cellEq hδ)

end HomotopicalAlgebra.CellularAttachmentComparison



namespace HomotopicalAlgebra.CellularUnion

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  {c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f}
  {I : Type w} (t : I → CellularSubcomplex c)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.before]
abbrev before.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.before.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.ambient]
abbrev ambient.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.ambient.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.ambientRoot]
abbrev ambientRoot.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.ambientRoot.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.ambientCell]
abbrev ambientCell.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.ambientCell.{api_level_0, api_level_1, api_level_2}

private abbrev ambientCell_congr := @HomotopicalAlgebra.EffectiveCellularUnion.ambientCell_congr

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.piece]
abbrev piece.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.piece.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceRoot]
abbrev pieceRoot.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.pieceRoot.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceComparison]
abbrev pieceComparison.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.pieceComparison.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceCell]
abbrev pieceCell.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.pieceCell.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem pieceRoot_comparison (i : I) (cut : Option O) :
    pieceRoot t i cut ≫ pieceComparison t i cut = ambientRoot (c := c) cut := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceRoot_comparison
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t i cut

@[reassoc]
theorem pieceCell_comparison (i : I) (a : (t i).complex.Cells) (cut : Option O)
    (ha : before cut ((t i).originalCell a)) :
    pieceCell t i a cut ha ≫ pieceComparison t i cut =
      ambientCell ((t i).originalCell a) cut ha := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceCell_comparison
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t i a cut ha

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.CutLE]
abbrev CutLE.{api_level_0} := @HomotopicalAlgebra.EffectiveCellularUnion.CutLE.{api_level_0}

theorem before_mono {a b : Option O} (hab : CutLE a b) {z : c.Cells}
    (hz : before a z) : before b z := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.before_mono
    C _ _ κ _ _ d O _ _ _ _ X Y f c a b hab z hz

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceMap]
abbrev pieceMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.pieceMap.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.ambientMap]
abbrev ambientMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.ambientMap.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem pieceRoot_map (i : I) (a b : Option O) (hab : CutLE a b) :
    pieceRoot t i a ≫ pieceMap t i a b hab = pieceRoot t i b := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceRoot_map
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t i a b hab

@[reassoc]
theorem pieceCell_map (i : I) (z : (t i).complex.Cells) (a b : Option O)
    (hab : CutLE a b) (hz : before a ((t i).originalCell z)) :
    pieceCell t i z a hz ≫ pieceMap t i a b hab =
      pieceCell t i z b (before_mono hab hz) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceCell_map
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t i z a b hab hz

@[reassoc]
theorem pieceMap_comparison (i : I) (a b : Option O) (hab : CutLE a b) :
    pieceMap t i a b hab ≫ pieceComparison t i b =
      pieceComparison t i a ≫ ambientMap (c := c) a b hab := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceMap_comparison
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t i a b hab

@[reassoc]
theorem ambientRoot_map (a b : Option O) (hab : CutLE a b) :
    ambientRoot (c := c) a ≫ ambientMap (c := c) a b hab = ambientRoot (c := c) b := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.ambientRoot_map
    C _ _ κ _ _ d O _ _ _ _ X Y f c a b hab

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.SharedCell]
abbrev SharedCell.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.{api_level_0, api_level_1, api_level_2}

/-- The left family member of a shared cellular occurrence. -/
abbrev SharedCell.left.{api_level_0, api_level_1, api_level_2}
    {C : Type api_level_1} [Category.{api_level_2} C] [ModelCategory C]
    {κ : Cardinal.{api_level_0}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {d : CofibrantGenerationData C κ}
    {O : Type api_level_0} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y}
    {c : RelativeCellComplex.{api_level_0} (fun _ : O => d.I.homFamily) f}
    {I : Type api_level_0} {t : I → CellularSubcomplex c} {cut : Option O}
    (self : SharedCell t cut) :
    I :=
  HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.left self

/-- The right family member of a shared cellular occurrence. -/
abbrev SharedCell.right.{api_level_0, api_level_1, api_level_2}
    {C : Type api_level_1} [Category.{api_level_2} C] [ModelCategory C]
    {κ : Cardinal.{api_level_0}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {d : CofibrantGenerationData C κ}
    {O : Type api_level_0} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y}
    {c : RelativeCellComplex.{api_level_0} (fun _ : O => d.I.homFamily) f}
    {I : Type api_level_0} {t : I → CellularSubcomplex c} {cut : Option O}
    (self : SharedCell t cut) :
    I :=
  HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.right self

/-- The occurrence in the left subcomplex. -/
abbrev SharedCell.leftCell.{api_level_0, api_level_1, api_level_2}
    {C : Type api_level_1} [Category.{api_level_2} C] [ModelCategory C]
    {κ : Cardinal.{api_level_0}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {d : CofibrantGenerationData C κ}
    {O : Type api_level_0} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y}
    {c : RelativeCellComplex.{api_level_0} (fun _ : O => d.I.homFamily) f}
    {I : Type api_level_0} {t : I → CellularSubcomplex c} {cut : Option O}
    (self : SharedCell t cut) :
    (t self.left).complex.Cells :=
  HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.leftCell self

/-- The occurrence in the right subcomplex. -/
abbrev SharedCell.rightCell.{api_level_0, api_level_1, api_level_2}
    {C : Type api_level_1} [Category.{api_level_2} C] [ModelCategory C]
    {κ : Cardinal.{api_level_0}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {d : CofibrantGenerationData C κ}
    {O : Type api_level_0} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y}
    {c : RelativeCellComplex.{api_level_0} (fun _ : O => d.I.homFamily) f}
    {I : Type api_level_0} {t : I → CellularSubcomplex c} {cut : Option O}
    (self : SharedCell t cut) :
    (t self.right).complex.Cells :=
  HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.rightCell self

/-- The two occurrences give the same ambient cell. -/
abbrev SharedCell.same.{api_level_0, api_level_1, api_level_2}
    {C : Type api_level_1} [Category.{api_level_2} C] [ModelCategory C]
    {κ : Cardinal.{api_level_0}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {d : CofibrantGenerationData C κ}
    {O : Type api_level_0} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y}
    {c : RelativeCellComplex.{api_level_0} (fun _ : O => d.I.homFamily) f}
    {I : Type api_level_0} {t : I → CellularSubcomplex c} {cut : Option O}
    (self : SharedCell t cut) :
    (t self.left).originalCell self.leftCell = (t self.right).originalCell self.rightCell :=
  HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.same self

/-- The left occurrence lies before the chosen cut. -/
abbrev SharedCell.leftBefore.{api_level_0, api_level_1, api_level_2}
    {C : Type api_level_1} [Category.{api_level_2} C] [ModelCategory C]
    {κ : Cardinal.{api_level_0}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {d : CofibrantGenerationData C κ}
    {O : Type api_level_0} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y}
    {c : RelativeCellComplex.{api_level_0} (fun _ : O => d.I.homFamily) f}
    {I : Type api_level_0} {t : I → CellularSubcomplex c} {cut : Option O}
    (self : SharedCell t cut) :
    before cut ((t self.left).originalCell self.leftCell) :=
  HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.leftBefore self

/-- The right occurrence lies before the chosen cut. -/
abbrev SharedCell.rightBefore.{api_level_0, api_level_1, api_level_2}
    {C : Type api_level_1} [Category.{api_level_2} C] [ModelCategory C]
    {κ : Cardinal.{api_level_0}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    {d : CofibrantGenerationData C κ}
    {O : Type api_level_0} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y}
    {c : RelativeCellComplex.{api_level_0} (fun _ : O => d.I.homFamily) f}
    {I : Type api_level_0} {t : I → CellularSubcomplex c} {cut : Option O}
    (self : SharedCell t cut) :
    before cut ((t self.right).originalCell self.rightCell) :=
  HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.rightBefore self



/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev SharedCell.casesOn.{api_level_0, api_level_1, api_level_2, api_level_3} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.casesOn.{api_level_0,
    api_level_1, api_level_2, api_level_3}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev SharedCell.ctorIdx.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.ctorIdx.{api_level_0,
    api_level_1, api_level_2}




/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev SharedCell.mk.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.mk.{api_level_0, api_level_1, api_level_2}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev SharedCell.noConfusion.{api_level_0, api_level_1, api_level_2, api_level_3} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.noConfusion.{api_level_0,
    api_level_1, api_level_2, api_level_3}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev SharedCell.noConfusionType.{api_level_0, api_level_1, api_level_2, api_level_3} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.noConfusionType.{api_level_0,
    api_level_1, api_level_2,
    api_level_3}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev SharedCell.rec.{api_level_0, api_level_1, api_level_2, api_level_3} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.rec.{api_level_0,
    api_level_1, api_level_2, api_level_3}

/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev SharedCell.recOn.{api_level_0, api_level_1, api_level_2, api_level_3} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.recOn.{api_level_0,
    api_level_1, api_level_2, api_level_3}





/-- Compatibility alias for the corresponding effective cellular construction. -/
abbrev SharedCell.mk._flat_ctor.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.mk._flat_ctor.{api_level_0,
    api_level_1, api_level_2}

alias SharedCell.mk.inj := HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.mk.inj

alias SharedCell.mk.injEq := HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.mk.injEq

alias SharedCell.mk.noConfusion :=
  HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.mk.noConfusion

alias SharedCell.mk.sizeOf_spec :=
  HomotopicalAlgebra.EffectiveCellularUnion.SharedCell.mk.sizeOf_spec

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.shape]
abbrev shape.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.shape.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.index]
abbrev index.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.index.{api_level_0, api_level_1, api_level_2}

variable [HasColimitsOfSize.{w, w} C]

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.obj]
abbrev obj.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.obj.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.root]
abbrev root.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.root.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.inclusion]
abbrev inclusion.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.inclusion.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem pieceRoot_inclusion (i : I) (cut : Option O) :
    pieceRoot t i cut ≫ inclusion t i cut = root t cut := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceRoot_inclusion
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ i cut

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.sharedCell_inclusion, reassoc]
theorem sharedCell_inclusion (cut : Option O) (a : SharedCell t cut) :
    pieceCell t a.left a.leftCell cut a.leftBefore ≫ inclusion t a.left cut =
      eqToHom (congrArg (fun z : c.Cells => z.i.1.right) a.same) ≫
        pieceCell t a.right a.rightCell cut a.rightBefore ≫ inclusion t a.right cut := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.sharedCell_inclusion
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ cut a

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.ambientCoconeMap]
abbrev ambientCoconeMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.ambientCoconeMap.{api_level_0,
    api_level_1, api_level_2}

omit [HasColimitsOfSize.{w, w} C] in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.ambientCoconeCondition]
theorem ambientCoconeCondition (cut : Option O) (a : (shape t cut).L) :
    (index t cut).fst a ≫ ambientCoconeMap t cut ((shape t cut).fst a) =
      (index t cut).snd a ≫ ambientCoconeMap t cut ((shape t cut).snd a) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.ambientCoconeCondition
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t cut a

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.comparison]
abbrev comparison.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.comparison.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem root_comparison (cut : Option O) :
    root t cut ≫ comparison t cut = ambientRoot (c := c) cut := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.root_comparison
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ cut

@[reassoc]
theorem inclusion_comparison (i : I) (cut : Option O) :
    inclusion t i cut ≫ comparison t cut = pieceComparison t i cut := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.inclusion_comparison
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ i cut

include t in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.hom_ext]
theorem hom_ext (cut : Option O) {Z : C} {f g : obj t cut ⟶ Z}
    (hr : root t cut ≫ f = root t cut ≫ g)
    (ht : ∀ i : I, inclusion t i cut ≫ f = inclusion t i cut ≫ g) : f = g := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.hom_ext
    C _ _ κ _ _ d O _ _ _ _ X Y _ c I t _ cut Z f g hr ht

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.mapCoconeMap]
abbrev mapCoconeMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.mapCoconeMap.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.mapCoconeCondition]
theorem mapCoconeCondition (a b : Option O) (hab : CutLE a b) (z : (shape t a).L) :
    (index t a).fst z ≫ mapCoconeMap t a b hab ((shape t a).fst z) =
      (index t a).snd z ≫ mapCoconeMap t a b hab ((shape t a).snd z) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.mapCoconeCondition
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ a b hab z

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.map]
abbrev map.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.map.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem root_map (a b : Option O) (hab : CutLE a b) : root t a ≫ map t a b hab = root t b := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.root_map
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ a b hab

@[reassoc]
theorem inclusion_map (i : I) (a b : Option O) (hab : CutLE a b) :
    inclusion t i a ≫ map t a b hab = pieceMap t i a b hab ≫ inclusion t i b := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.inclusion_map
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ i a b hab

@[reassoc]
theorem map_comparison (a b : Option O) (hab : CutLE a b) :
    map t a b hab ≫ comparison t b = comparison t a ≫ ambientMap (c := c) a b hab := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.map_comparison
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ a b hab

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.F]
abbrev F.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.F.{api_level_0, api_level_1, api_level_2}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.endpointCocone]
abbrev endpointCocone.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.endpointCocone.{api_level_0, api_level_1, api_level_2}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceCocone]
abbrev pieceCocone.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.pieceCocone.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceDesc]
abbrev pieceDesc.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.pieceDesc.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem pieceDesc_fac (s : Cocone (F t)) (i : I) (j : O) :
    (t i).complex.incl.app j ≫ pieceDesc t s i = inclusion t i (some j) ≫ s.ι.app j := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceDesc_fac
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ s i j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceCell_desc, reassoc]
theorem pieceCell_desc (s : Cocone (F t)) (i : I) (z : (t i).complex.Cells)
    (j : O) (hz : before (some j) ((t i).originalCell z)) :
    pieceCell t i z none trivial ≫ pieceDesc t s i =
      pieceCell t i z (some j) hz ≫ inclusion t i (some j) ≫ s.ι.app j := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceCell_desc
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ s i z j hz

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.root_cocone, reassoc]
theorem root_cocone (s : Cocone (F t)) (j : O) :
    root t (some j) ≫ s.ι.app j = root t (some ⊥) ≫ s.ι.app ⊥ := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.root_cocone
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ s j

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.wholeCoconeMap]
abbrev wholeCoconeMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.wholeCoconeMap.{api_level_0, api_level_1, api_level_2}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.wholeCoconeCondition]
theorem wholeCoconeCondition (s : Cocone (F t)) (a : (shape t none).L) :
    (index t none).fst a ≫ wholeCoconeMap t s ((shape t none).fst a) =
      (index t none).snd a ≫ wholeCoconeMap t s ((shape t none).snd a) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.wholeCoconeCondition
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ s a

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.wholeDesc]
abbrev wholeDesc.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.wholeDesc.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem wholeDesc_root (s : Cocone (F t)) :
    root t none ≫ wholeDesc t s = root t (some ⊥) ≫ s.ι.app ⊥ := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.wholeDesc_root
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ s

@[reassoc]
theorem wholeDesc_piece (s : Cocone (F t)) (i : I) :
    inclusion t i none ≫ wholeDesc t s = pieceDesc t s i := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.wholeDesc_piece
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ s i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.endpointIsColimit]
abbrev endpointIsColimit.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.endpointIsColimit.{api_level_0,
    api_level_1, api_level_2}

open CellularSubcomplexExtension

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.wholeFamilyCompatible]
theorem wholeFamilyCompatible {E : C} (α : obj t none ⟶ E) :
    FamilyCellCompatible d c t (fun i => inclusion t i none ≫ α) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.wholeFamilyCompatible
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ E α

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.endpointComparisonCofibration]
theorem endpointComparisonCofibration (h : CellularSource d) :
    cofibrations C (comparison t none) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.endpointComparisonCofibration
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _
    (h.effectiveCofibrations)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.prefixFamilyImage]
theorem prefixFamilyImage {E : C} (j : O) (α : obj t (some j) ⟶ E)
    (a : Set.Iic j) (ha : ¬ IsMax a) (i : I)
    (k : ((t i).complex.attachCells a.1 (prefixNotMax a ha)).ι) :
    familyCellImage d (prefixComplex d c j)
      (fun i => prefixSubcomplex d c (t i) j)
      (fun i => inclusion t i (some j) ≫ α) a ha i k =
    pieceCell t i ⟨a.1, prefixNotMax a ha, k⟩ (some j)
      (prefixStage_lt_endpoint a ha) ≫ inclusion t i (some j) ≫ α := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.prefixFamilyImage
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ E j α a ha i
    k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.prefixFamilyCompatible]
theorem prefixFamilyCompatible {E : C} (j : O) (α : obj t (some j) ⟶ E) :
    FamilyCellCompatible d (prefixComplex d c j)
      (fun i => prefixSubcomplex d c (t i) j)
      (fun i => inclusion t i (some j) ≫ α) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.prefixFamilyCompatible
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ E j α

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.stageComparisonCofibration]
theorem stageComparisonCofibration (h : CellularSource d) (j : O) :
    cofibrations C (comparison t (some j)) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.stageComparisonCofibration
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _
    (h.effectiveCofibrations) j

section OriginalLimit

variable {j : O} (hj : Order.IsSuccLimit j)
  (s : Cocone ((Set.principalSegIio j).monotone.functor ⋙ F t))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.limitPieceCocone]
abbrev limitPieceCocone.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.limitPieceCocone.{api_level_0,
    api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.limitPieceDesc]
abbrev limitPieceDesc.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.limitPieceDesc.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem limitPieceDesc_fac (i : I) (a : O) (ha : a < j) :
    (t i).complex.F.map (homOfLE ha.le) ≫ limitPieceDesc t hj s i =
      inclusion t i (some a) ≫ s.ι.app ⟨a, ha⟩ := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.limitPieceDesc_fac
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s i a
    ha

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.root_limit_cocone, reassoc]
theorem root_limit_cocone (a : Set.Iio j) :
    root t (some a.1) ≫ s.ι.app a =
      root t (some ⊥) ≫ s.ι.app ⟨⊥, hj.bot_lt⟩ := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.root_limit_cocone
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.limitPieceCell_desc, reassoc]
theorem limitPieceCell_desc (i : I) (z : (t i).complex.Cells)
    (hz : before (some j) ((t i).originalCell z)) (a : O) (ha : a < j)
    (hza : before (some a) ((t i).originalCell z)) :
    pieceCell t i z (some j) hz ≫ limitPieceDesc t hj s i =
      pieceCell t i z (some a) hza ≫ inclusion t i (some a) ≫ s.ι.app ⟨a, ha⟩ := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.limitPieceCell_desc
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s i z
    hz a ha hza

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.limitCoconeMap]
abbrev limitCoconeMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.limitCoconeMap.{api_level_0, api_level_1, api_level_2}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.limitCoconeCondition]
theorem limitCoconeCondition (a : (shape t (some j)).L) :
    (index t (some j)).fst a ≫ limitCoconeMap t hj s ((shape t (some j)).fst a) =
      (index t (some j)).snd a ≫ limitCoconeMap t hj s ((shape t (some j)).snd a) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.limitCoconeCondition
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s a

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.limitDesc]
abbrev limitDesc.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.limitDesc.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem limitDesc_root :
    root t (some j) ≫ limitDesc t hj s = root t (some ⊥) ≫ s.ι.app ⟨⊥, hj.bot_lt⟩ := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.limitDesc_root
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s

@[reassoc]
theorem limitDesc_piece (i : I) :
    inclusion t i (some j) ≫ limitDesc t hj s = limitPieceDesc t hj s i := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.limitDesc_piece
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s i

end OriginalLimit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.wellOrderContinuous]
theorem wellOrderContinuous : (F t).IsWellOrderContinuous := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.wellOrderContinuous
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _

section OriginalAttachments

variable (j : O) (hj : ¬ IsMax j)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.cells]
abbrev cells.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.cells.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.witnessPiece]
abbrev witnessPiece.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.witnessPiece.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.witnessCell]
abbrev witnessCell.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.witnessCell.{api_level_0, api_level_1, api_level_2}

omit [HasColimitsOfSize.{w, w} C] in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.witnessCell_eq]
theorem witnessCell_eq (k : cells t j hj) :
    (t (witnessPiece t j hj k)).cellIndex j hj (witnessCell t j hj k) = k.1 := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.witnessCell_eq
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t j hj k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.cellLabel]
abbrev cellLabel.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.cellLabel.{api_level_0, api_level_1, api_level_2}

omit [HasColimitsOfSize.{w, w} C] in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.witnessLabel_eq]
theorem witnessLabel_eq (k : cells t j hj) :
    ((t (witnessPiece t j hj k)).complex.attachCells j hj).π (witnessCell t j hj k) =
      cellLabel t j hj k := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.witnessLabel_eq
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t j hj k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.sourceCell]
abbrev sourceCell.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.sourceCell.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.targetCell]
abbrev targetCell.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.targetCell.{api_level_0, api_level_1, api_level_2}

omit [HasColimitsOfSize.{w, w} C] in
private abbrev boundary_congr := @HomotopicalAlgebra.EffectiveCellularUnion.boundary_congr

omit [HasColimitsOfSize.{w, w} C] in
private abbrev cell_congr := @HomotopicalAlgebra.EffectiveCellularUnion.cell_congr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.sourceCell_comparison, reassoc]
theorem sourceCell_comparison (h : CellularSource d) (k : cells t j hj) :
    sourceCell t j hj k ≫ comparison t (some j) = boundary d c j hj k.1 := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.sourceCell_comparison
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj
    (h.effectiveCofibrations) k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.targetCell_comparison, reassoc]
theorem targetCell_comparison (k : cells t j hj) :
    targetCell t j hj k ≫ comparison t (some (Order.succ j)) = (c.attachCells j hj).cell k.1 := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.targetCell_comparison
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.cell_square]
theorem cell_square (h : CellularSource d) (k : cells t j hj) :
    sourceCell t j hj k ≫ (F t).map (homOfLE (Order.le_succ j)) =
      d.I.homFamily (cellLabel t j hj k) ≫ targetCell t j hj k := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.cell_square
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj
    (h.effectiveCofibrations) k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.sourceCofan]
abbrev sourceCofan.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.sourceCofan.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.targetCofan]
abbrev targetCofan.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.targetCofan.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.cellMap]
abbrev cellMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.cellMap.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem cellMap_inj (k : cells t j hj) :
    (sourceCofan t j hj).inj k ≫ cellMap t j hj =
      d.I.homFamily (cellLabel t j hj k) ≫ (targetCofan t j hj).inj k := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.cellMap_inj
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.sourceMap]
abbrev sourceMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.sourceMap.{api_level_0, api_level_1, api_level_2}

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.targetMap]
abbrev targetMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.targetMap.{api_level_0, api_level_1, api_level_2}

@[reassoc]
theorem sourceMap_inj (k : cells t j hj) :
    (sourceCofan t j hj).inj k ≫ sourceMap t j hj = sourceCell t j hj k := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.sourceMap_inj
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj k

@[reassoc]
theorem targetMap_inj (k : cells t j hj) :
    (targetCofan t j hj).inj k ≫ targetMap t j hj = targetCell t j hj k := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.targetMap_inj
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.attaching_square]
theorem attaching_square (h : CellularSource d) :
    sourceMap t j hj ≫ (F t).map (homOfLE (Order.le_succ j)) =
      cellMap t j hj ≫ targetMap t j hj := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.attaching_square
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj
    (h.effectiveCofibrations)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.familyOccurrence]
abbrev familyOccurrence.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.familyOccurrence.{api_level_0,
    api_level_1, api_level_2}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.sourceCell_family]
theorem sourceCell_family (h : CellularSource d) (i : I)
    (a : ((t i).complex.attachCells j hj).ι) :
    eqToHom (congrArg (fun p : d.I.toSet => p.1.left) ((t i).label_eq j hj a)) ≫
      sourceCell t j hj (familyOccurrence t j hj i a) =
        boundary d (t i).complex j hj a ≫ inclusion t i (some j) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.sourceCell_family
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj
    (h.effectiveCofibrations) i a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.targetCell_family]
theorem targetCell_family (h : CellularSource d) (i : I)
    (a : ((t i).complex.attachCells j hj).ι) :
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) ((t i).label_eq j hj a)) ≫
      targetCell t j hj (familyOccurrence t j hj i a) =
        ((t i).complex.attachCells j hj).cell a ≫ inclusion t i (some (Order.succ j)) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.targetCell_family
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj
    (h.effectiveCofibrations) i a

variable (s : PushoutCocone (sourceMap t j hj) (cellMap t j hj))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.testCell_square]
theorem testCell_square (k : cells t j hj) :
    sourceCell t j hj k ≫ s.inl =
      d.I.homFamily (cellLabel t j hj k) ≫ (targetCofan t j hj).inj k ≫ s.inr := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.testCell_square
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s k

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceStepCell]
abbrev pieceStepCell.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.pieceStepCell.{api_level_0, api_level_1, api_level_2}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceStepCell_boundary]
theorem pieceStepCell_boundary (h : CellularSource d) (i : I)
    (a : ((t i).complex.attachCells j hj).ι) :
    boundary d (t i).complex j hj a ≫ (inclusion t i (some j) ≫ s.inl) =
      d.I.homFamily (((t i).complex.attachCells j hj).π a) ≫ pieceStepCell t j hj s i a := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceStepCell_boundary
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) i a

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceStepCofanMap]
abbrev pieceStepCofanMap.{api_level_0, api_level_1, api_level_2} :=
  @HomotopicalAlgebra.EffectiveCellularUnion.pieceStepCofanMap.{api_level_0,
    api_level_1, api_level_2}

@[reassoc]
theorem pieceStepCofanMap_inj (i : I) (a : ((t i).complex.attachCells j hj).ι) :
    ((t i).complex.attachCells j hj).cofan₂.inj a ≫ pieceStepCofanMap t j hj s i =
      pieceStepCell t j hj s i a := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceStepCofanMap_inj
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s i
    a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceStepMap]
def pieceStepMap (h : CellularSource d) (i : I) : (t i).complex.F.obj (Order.succ j) ⟶ s.pt := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceStepMap
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) i

@[reassoc]
theorem pieceStepMap_stage (h : CellularSource d) (i : I) :
    (t i).complex.F.map (homOfLE (Order.le_succ j)) ≫ pieceStepMap t j hj s h i =
      inclusion t i (some j) ≫ s.inl := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceStepMap_stage
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) i

@[reassoc]
theorem pieceStepMap_cell (h : CellularSource d) (i : I)
    (a : ((t i).complex.attachCells j hj).ι) :
    ((t i).complex.attachCells j hj).cell a ≫ pieceStepMap t j hj s h i =
      pieceStepCell t j hj s i a := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceStepMap_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) i a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceStepMap_root]
theorem pieceStepMap_root (h : CellularSource d) (i : I) :
    pieceRoot t i (some (Order.succ j)) ≫ pieceStepMap t j hj s h i = root t (some j) ≫ s.inl := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceStepMap_root
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceStepMap_before_cell]
theorem pieceStepMap_before_cell (h : CellularSource d) (i : I) (z : (t i).complex.Cells)
    (hz : before (some (Order.succ j)) ((t i).originalCell z))
    (hzj : before (some j) ((t i).originalCell z)) :
    pieceCell t i z (some (Order.succ j)) hz ≫ pieceStepMap t j hj s h i =
      pieceCell t i z (some j) hzj ≫ inclusion t i (some j) ≫ s.inl := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceStepMap_before_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) i z hz hzj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceStepMap_current_cell]
theorem pieceStepMap_current_cell (h : CellularSource d) (i : I)
    (a : ((t i).complex.attachCells j hj).ι) :
    pieceCell t i ⟨j, hj, a⟩ (some (Order.succ j)) (Order.lt_succ_of_not_isMax hj) ≫
        pieceStepMap t j hj s h i =
      (targetCofan t j hj).inj (familyOccurrence t j hj i a) ≫ s.inr := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceStepMap_current_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj
    s (h.effectiveCofibrations) i a

private abbrev targetCofan_inj_congr :=
  @HomotopicalAlgebra.EffectiveCellularUnion.targetCofan_inj_congr

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.stepCoconeMap]
def stepCoconeMap (h : CellularSource d) (i : Option I) :
    (index t (some (Order.succ j))).right i ⟶ s.pt := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.stepCoconeMap
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.stepCoconeCondition]
theorem stepCoconeCondition (h : CellularSource d) (z : (shape t (some (Order.succ j))).L) :
    (index t (some (Order.succ j))).fst z ≫ stepCoconeMap t j hj s h
        ((shape t (some (Order.succ j))).fst z) =
      (index t (some (Order.succ j))).snd z ≫ stepCoconeMap t j hj s h
        ((shape t (some (Order.succ j))).snd z) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.stepCoconeCondition
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) z

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.stepDesc]
def stepDesc (h : CellularSource d) : obj t (some (Order.succ j)) ⟶ s.pt := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.stepDesc
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations)

@[reassoc]
theorem stepDesc_root (h : CellularSource d) :
    root t (some (Order.succ j)) ≫ stepDesc t j hj s h = root t (some j) ≫ s.inl := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.stepDesc_root
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations)

@[reassoc]
theorem stepDesc_piece (h : CellularSource d) (i : I) :
    inclusion t i (some (Order.succ j)) ≫ stepDesc t j hj s h = pieceStepMap t j hj s h i := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.stepDesc_piece
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.stepDesc_stage, reassoc]
theorem stepDesc_stage (h : CellularSource d) :
    (F t).map (homOfLE (Order.le_succ j)) ≫ stepDesc t j hj s h = s.inl := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.stepDesc_stage
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.stepDesc_cell, reassoc]
theorem stepDesc_cell (h : CellularSource d) (k : cells t j hj) :
    targetCell t j hj k ≫ stepDesc t j hj s h = (targetCofan t j hj).inj k ≫ s.inr := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.stepDesc_cell
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.stepDesc_target, reassoc]
theorem stepDesc_target (h : CellularSource d) :
    targetMap t j hj ≫ stepDesc t j hj s h = s.inr := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.stepDesc_target
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.stepDesc_unique]
theorem stepDesc_unique (h : CellularSource d) (m : obj t (some (Order.succ j)) ⟶ s.pt)
    (hm₀ : (F t).map (homOfLE (Order.le_succ j)) ≫ m = s.inl)
    (hm₁ : targetMap t j hj ≫ m = s.inr) : m = stepDesc t j hj s h := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.stepDesc_unique
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj s
    (h.effectiveCofibrations) m hm₀ hm₁

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.attachingIsPushout]
theorem attachingIsPushout (h : CellularSource d) :
    IsPushout (sourceMap t j hj) (cellMap t j hj)
      ((F t).map (homOfLE (Order.le_succ j))) (targetMap t j hj) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.attachingIsPushout
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj
    (h.effectiveCofibrations)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.attachCells]
abbrev attachCells (h : CellularSource d) :
    AttachCells.{w} d.I.homFamily ((F t).map (homOfLE (Order.le_succ j))) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.attachCells
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _ j hj
    (h.effectiveCofibrations)

end OriginalAttachments

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.botIso]
abbrev botIso (h : CellularSource d) : (F t).obj ⊥ ≅ X := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.botIso C _ _ κ _ _ d O _ _ _ _ X Y f c I t _
    (h.effectiveCofibrations)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.complex]
abbrev complex (h : CellularSource d) :
    RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) (root t none) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.complex C _ _ κ _ _ d O _ _ _ _ X Y f c I t _
    (h.effectiveCofibrations)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.unionSubcomplex]
abbrev unionSubcomplex (h : CellularSource d) : CellularSubcomplex c := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.unionSubcomplex
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _
    (h.effectiveCofibrations)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.pieceSubcomplex]
def pieceSubcomplex (h : CellularSource d) (i : I) : CellularSubcomplex (complex t h) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.pieceSubcomplex
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _
    (h.effectiveCofibrations) i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.union_support]
theorem union_support (h : CellularSource d) :
    (unionSubcomplex t h).support = ⋃ i : I, (t i).support := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.union_support
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _
    (h.effectiveCofibrations)

@[inherit_doc HomotopicalAlgebra.EffectiveCellularUnion.union_cells_cardinal_le]
theorem union_cells_cardinal_le (h : CellularSource d) :
    Cardinal.mk (complex t h).Cells ≤
      Cardinal.sum (fun i : I => Cardinal.mk (t i).complex.Cells) := by
  exact @HomotopicalAlgebra.EffectiveCellularUnion.union_cells_cardinal_le
    C _ _ κ _ _ d O _ _ _ _ X Y f c I t _
    (h.effectiveCofibrations)













end HomotopicalAlgebra.CellularUnion

namespace HomotopicalAlgebra.CellularSubcomplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {d : CofibrantGenerationData C κ}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  {c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f}
  {I : Type w}

/-- The original source data construct an actual union on the unchanged
ordinal, with all original cell labels, root and endpoint maps. -/
def union (h : CellularSource d) (t : I → CellularSubcomplex c) : CellularSubcomplex c := by
  exact EffectiveCellularSubcomplex.union d h.effectiveCofibrations t

/-- Every supplied original subcomplex enters the actual constructed union. -/
def unionInclusion (h : CellularSource d) (t : I → CellularSubcomplex c) (i : I) :
    (t i).endpoint ⟶ (union h t).endpoint := by
  exact EffectiveCellularSubcomplex.unionInclusion d h.effectiveCofibrations t i

@[reassoc]
theorem unionInclusion_root (h : CellularSource d) (t : I → CellularSubcomplex c) (i : I) :
    (t i).hom ≫ unionInclusion h t i = (union h t).hom := by
  exact EffectiveCellularSubcomplex.unionInclusion_root d h.effectiveCofibrations t i

@[reassoc]
theorem unionInclusion_ambient (h : CellularSource d) (t : I → CellularSubcomplex c) (i : I) :
    unionInclusion h t i ≫ (union h t).inclusion = (t i).inclusion := by
  exact EffectiveCellularSubcomplex.unionInclusion_ambient d h.effectiveCofibrations t i

/-- The actual union occurrence support is the literal union of the original supports. -/
theorem union_support (h : CellularSource d) (t : I → CellularSubcomplex c) :
    (union h t).support = ⋃ i : I, (t i).support := by
  exact EffectiveCellularSubcomplex.union_support d h.effectiveCofibrations t

/-- The original cell counts bound the actual constructed union cell count. -/
theorem union_cells_cardinal_le (h : CellularSource d) (t : I → CellularSubcomplex c) :
    Cardinal.mk (union h t).complex.Cells ≤
      Cardinal.sum (fun i : I => Cardinal.mk (t i).complex.Cells) := by
  exact EffectiveCellularSubcomplex.union_cells_cardinal_le d h.effectiveCofibrations t

/-- Every original inclusion into the constructed union is an actual cofibration. -/
theorem unionInclusion_cofibration (h : CellularSource d) (t : I → CellularSubcomplex c) (i : I) :
    cofibrations C (unionInclusion h t i) := by
  exact EffectiveCellularSubcomplex.unionInclusion_cofibration d h.effectiveCofibrations t i

end HomotopicalAlgebra.CellularSubcomplex


end OriginalCellularSourceStructuralAPI


section GenericRelativeCellPrefixResearchCanonicalPromotion

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra.CellularSubcomplexExtension

namespace HomotopicalAlgebra.RelativeCellComplex.GenericPrefix

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)

/-- The actual original root arrow to the unchanged original stage. -/
def root (j : O) : X ⟶ c.F.obj j :=
  c.isoBot.inv ≫ c.F.map (homOfLE (bot_le : (⊥ : O) ≤ j))

/-- The actual closed-prefix transfinite composition keeps the original root. -/
def prefixShape (j : O) : TransfiniteCompositionOfShape (Set.Iic j) (root c j) where
  F := (Set.initialSegIic j).monotone.functor ⋙ c.F
  isoBot := c.isoBot
  isWellOrderContinuous := (c.toTransfiniteCompositionOfShape.iic j).isWellOrderContinuous
  incl := (c.toTransfiniteCompositionOfShape.iic j).incl
  isColimit := (c.toTransfiniteCompositionOfShape.iic j).isColimit
  fac := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The exact original successor equality is the only attaching-target transport. -/
def prefixStepIso (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    Arrow.mk (c.F.map (homOfLE (Order.le_succ a.1))) ≅
      Arrow.mk ((prefixShape c j).F.map (homOfLE (Order.le_succ a))) :=
  Arrow.isoMk (Iso.refl _)
    (c.F.mapIso (eqToIso (prefixSuccessorEq a ha).symm)) (by
      change 𝟙 _ ≫ c.F.map
        ((Set.initialSegIic j).monotone.functor.map (homOfLE (Order.le_succ a))) =
          c.F.map (homOfLE (Order.le_succ a.1)) ≫ c.F.map (eqToHom (prefixSuccessorEq a ha).symm)
      rw [Category.id_comp, ← c.F.map_comp]
      congr 1)

/-- The generic original relative-cell history restricts to its actual closed prefix. -/
def prefixComplex (j : O) :
    RelativeCellComplex.{w} (fun _ : Set.Iic j => P.homFamily) (root c j) where
  __ := prefixShape c j
  attachCells a ha := (c.attachCells a.1 (prefixNotMax a ha)).ofArrowIso (prefixStepIso c j a ha)

/-- The whole prefix functor is the exact original stage restriction. -/
theorem prefixComplex_functor (j : O) :
    (prefixComplex c j).F = (Set.initialSegIic j).monotone.functor ⋙ c.F := rfl

/-- The original bottom isomorphism is retained literally. -/
theorem prefixComplex_isoBot (j : O) : (prefixComplex c j).isoBot = c.isoBot := rfl

/-- Every actual prefix endpoint leg is the same original stage map. -/
theorem prefixComplex_incl (j : O) (a : Set.Iic j) :
    (prefixComplex c j).incl.app a = c.F.map (homOfLE a.2) := rfl

/-- Every original source cofan remains literal original attaching data. -/
theorem prefixComplex_sourceCofan (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).cofan₁ =
      (c.attachCells a.1 (prefixNotMax a ha)).cofan₁ := rfl

/-- Every original target cofan remains literal original attaching data. -/
theorem prefixComplex_targetCofan (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).cofan₂ =
      (c.attachCells a.1 (prefixNotMax a ha)).cofan₂ := rfl

/-- The original occurrence index family is retained at the same original stage. -/
theorem prefixComplex_occurrences (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).ι = (c.attachCells a.1 (prefixNotMax a ha)).ι := rfl

/-- Every selected original generator label is retained literally. -/
theorem prefixComplex_label (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex c j).attachCells a ha).π k = (c.attachCells a.1 (prefixNotMax a ha)).π k := rfl

/-- The original coproduct of generating arrows is retained literally. -/
theorem prefixComplex_attachingMap (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).m = (c.attachCells a.1 (prefixNotMax a ha)).m := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original generator-domain map enters the same original source stage. -/
theorem prefixComplex_sourceMap (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).g₁ = (c.attachCells a.1 (prefixNotMax a ha)).g₁ := by
  change (c.attachCells a.1 (prefixNotMax a ha)).g₁ ≫ 𝟙 _ = _
  rw [Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each target cofan uses only the exact original successor transport. -/
theorem prefixComplex_targetMap (j : O) (a : Set.Iic j) (ha : ¬ IsMax a) :
    ((prefixComplex c j).attachCells a ha).g₂ =
      (c.attachCells a.1 (prefixNotMax a ha)).g₂ ≫
        c.F.map (eqToHom (prefixSuccessorEq a ha).symm) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The exact original boundary map is retained before every original cell. -/
theorem prefixComplex_boundary (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex c j).attachCells a ha).cofan₁.inj k ≫
      ((prefixComplex c j).attachCells a ha).g₁ =
      (c.attachCells a.1 (prefixNotMax a ha)).cofan₁.inj k ≫
        (c.attachCells a.1 (prefixNotMax a ha)).g₁ := by
  change (c.attachCells a.1 (prefixNotMax a ha)).cofan₁.inj k ≫
    ((c.attachCells a.1 (prefixNotMax a ha)).g₁ ≫ 𝟙 _) =
      (c.attachCells a.1 (prefixNotMax a ha)).cofan₁.inj k ≫
        (c.attachCells a.1 (prefixNotMax a ha)).g₁
  rw [Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual prefix cell keeps its original cell map and exact successor target. -/
theorem prefixComplex_cell (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    ((prefixComplex c j).attachCells a ha).cell k =
      (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫
        c.F.map (eqToHom (prefixSuccessorEq a ha).symm) := by
  change (c.attachCells a.1 (prefixNotMax a ha)).cofan₂.inj k ≫
    ((c.attachCells a.1 (prefixNotMax a ha)).g₂ ≫
      c.F.map (eqToHom (prefixSuccessorEq a ha).symm)) = _
  exact (Category.assoc _ _ _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each prefix occurrence includes by the original map into the actual endpoint stage j. -/
theorem prefixComplex_cell_inclusion (j : O) (a : Set.Iic j) (ha : ¬ IsMax a)
    (k : (c.attachCells a.1 (prefixNotMax a ha)).ι) :
    (({ j := a, hj := ha, k := k } : (prefixComplex c j).Cells)).ι =
      (c.attachCells a.1 (prefixNotMax a ha)).cell k ≫
        c.F.map (homOfLE (Order.succ_le_of_lt (prefixStage_lt_endpoint a ha))) := by
  dsimp only [RelativeCellComplex.Cells.ι]
  rw [prefixComplex_cell, prefixComplex_incl, Category.assoc, ← c.F.map_comp]
  congr 1

/-- The same original occurrence is retained by the actual prefix. -/
def originalCell (j : O) (a : (prefixComplex c j).Cells) : c.Cells where
  j := a.j.1
  hj := prefixNotMax a.j a.hj
  k := a.k

/-- A selected original cell is strictly before its actual original prefix endpoint. -/
theorem originalCell_stage_lt (j : O) (a : (prefixComplex c j).Cells) :
    (originalCell c j a).j < j := prefixStage_lt_endpoint a.j a.hj

/-- The actual cells are exactly the ORIGINAL occurrences strictly before j. -/
def cellsEquiv (j : O) : (prefixComplex c j).Cells ≃ {a : c.Cells // a.j < j} where
  toFun a := ⟨originalCell c j a, originalCell_stage_lt c j a⟩
  invFun a :=
    { j := ⟨a.1.j, a.2.le⟩
      hj := not_isMax_of_lt (show (⟨a.1.j, a.2.le⟩ : Set.Iic j) < ⟨j, le_rfl⟩ from a.2)
      k := a.1.k }
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

/-- Its original occurrence embedding is the same original cell map. -/
def cellEmbedding (j : O) : (prefixComplex c j).Cells ↪ c.Cells :=
  (cellsEquiv c j).toEmbedding.trans (Function.Embedding.subtype (fun a : c.Cells => a.j < j))

theorem cellEmbedding_original (j : O) (a : (prefixComplex c j).Cells) :
    cellEmbedding c j a = originalCell c j a := rfl

/-- The exact original labels are preserved by this actual occurrence equivalence. -/
theorem originalCell_label (j : O) (a : (prefixComplex c j).Cells) :
    a.i = (originalCell c j a).i := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual prefix inclusion is the same original cell map into original stage j. -/
theorem originalCell_toStage (j : O) (a : (prefixComplex c j).Cells) :
    a.ι = (originalCell c j a).toStage j (originalCell_stage_lt c j a) :=
  prefixComplex_cell_inclusion c j a.j a.hj a.k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Returning to the original endpoint retains the same actual original cell inclusion. -/
@[reassoc]
theorem originalCell_inclusion (j : O) (a : (prefixComplex c j).Cells) :
    a.ι ≫ c.incl.app j = (originalCell c j a).ι := by
  rw [originalCell_toStage]
  exact (originalCell c j a).toStage_incl j (originalCell_stage_lt c j a)

/-- The actual prefix cell cardinal is exactly the original strict-stage occurrence cardinal. -/
theorem cells_cardinal (j : O) :
    Cardinal.mk (prefixComplex c j).Cells = Cardinal.mk {a : c.Cells // a.j < j} :=
  Cardinal.mk_congr (cellsEquiv c j)

/-- The actual original occurrence embedding bounds every prefix count by the original count. -/
theorem cells_cardinal_le (j : O) : Cardinal.mk (prefixComplex c j).Cells ≤ Cardinal.mk c.Cells :=
  (cellEmbedding c j).cardinal_le

/-- The original root and original endpoint cocone recover the unchanged original arrow. -/
@[reassoc]
theorem root_endpoint (j : O) : root c j ≫ c.incl.app j = f := c.rootAtStage_incl j

end HomotopicalAlgebra.RelativeCellComplex.GenericPrefix

end GenericRelativeCellPrefixResearchCanonicalPromotion

section GenericRelativeCellCompletionResearchCanonicalPromotion

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.RelativeCellComplex.GenericCompletion

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C}
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)

theorem attachmentLabel_of_eq {U V : C} {g : U ⟶ V}
    (a b : AttachCells.{w} P.homFamily g) (e : a = b) (k : b.ι) :
    a.π (cast (congrArg (fun z : AttachCells.{w} P.homFamily g => z.ι) e).symm k) = b.π k := by
  cases e
  rfl

theorem attachmentCell_of_eq {U V : C} {g : U ⟶ V}
    (a b : AttachCells.{w} P.homFamily g) (e : a = b) (k : b.ι) :
    a.cell (cast (congrArg (fun z : AttachCells.{w} P.homFamily g => z.ι) e).symm k) =
      eqToHom (congrArg (fun p : P.toSet => p.1.right) (attachmentLabel_of_eq a b e k)) ≫
        b.cell k := by
  cases e
  simp only [cast_eq, eqToHom_refl, Category.id_comp]

/-- The transfinite composition on `WithTop O` obtained by adjoining the original endpoint. -/
abbrev completedShape : TransfiniteCompositionOfShape (WithTop O) f :=
  CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.shape
    c.toTransfiniteCompositionOfShape

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Each nonmaximal original arrow retains only its exact original successor target transport. -/
def stepIso (a : O) (ha : ¬ IsMax a) :
    Arrow.mk (c.F.map (homOfLE (Order.le_succ a))) ≅
      Arrow.mk ((completedShape c).F.map (homOfLE (Order.le_succ (a : WithTop O)))) :=
  Arrow.isoMk (Iso.refl _)
    ((completedShape c).F.mapIso (eqToIso (WithTop.succ_coe_of_not_isMax ha).symm)) (by
      change 𝟙 _ ≫ (completedShape c).F.map (homOfLE (Order.le_succ (a : WithTop O))) =
        (completedShape c).F.map (homOfLE (WithTop.coe_le_coe.mpr (Order.le_succ a))) ≫
          (completedShape c).F.map (eqToHom (WithTop.succ_coe_of_not_isMax ha).symm)
      rw [Category.id_comp, ← (completedShape c).F.map_comp]
      congr 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An old maximal stage joins its actual original endpoint by the original endpoint arrow. -/
def maxStepIso (a : O) (ha : IsMax a) :
    Arrow.mk (c.incl.app a) ≅
      Arrow.mk ((completedShape c).F.map (homOfLE (Order.le_succ (a : WithTop O)))) :=
  Arrow.isoMk (Iso.refl _)
    ((completedShape c).F.mapIso (eqToIso (WithTop.succ_coe_of_isMax ha).symm)) (by
      change 𝟙 _ ≫ (completedShape c).F.map (homOfLE (Order.le_succ (a : WithTop O))) =
        (completedShape c).F.map (homOfLE (le_top : (a : WithTop O) ≤ ⊤)) ≫
          (completedShape c).F.map (eqToHom (WithTop.succ_coe_of_isMax ha).symm)
      rw [Category.id_comp, ← (completedShape c).F.map_comp]
      congr 1)

section SuppliedEmptyCofans

variable {D₁ D₂ : PEmpty.{w + 1} → C} (e₁ : Cofan D₁) (e₂ : Cofan D₂)
  (he₁ : IsColimit e₁) (he₂ : IsColimit e₂)

/-- The original relative-cell history is completed at its actual original endpoint.
Old maximal joins attach precisely the supplied empty cell family. -/
def complex : RelativeCellComplex.{w} (fun _ : WithTop O => P.homFamily) f where
  __ := completedShape c
  attachCells a ha := by
    classical
    cases a with
    | top => exact False.elim (ha isMax_top)
    | coe a =>
      by_cases hmax : IsMax a
      · letI : IsIso (c.incl.app a) :=
          CategoryTheory.TransfiniteCompositionOfShape.GenericCompletion.originalMaxEndpoint_isIso
            c.toTransfiniteCompositionOfShape a hmax
        exact (CategoryTheory.SmallObject.CellularNormalization.emptyAttachCells P.homFamily
          (c.incl.app a) e₁ e₂ he₁ he₂).ofArrowIso (maxStepIso c a hmax)
      · exact (c.attachCells a hmax).ofArrowIso (stepIso c a hmax)

/-- Every original object is literal in the completed relative-cell history. -/
theorem complex_obj_coe (a : O) : (complex c e₁ e₂ he₁ he₂).F.obj (a : WithTop O) = c.F.obj a := rfl

/-- The actual added top is exactly the original endpoint object. -/
theorem complex_obj_top : (complex c e₁ e₂ he₁ he₂).F.obj ⊤ = Y := rfl

theorem complex_isoBot : (complex c e₁ e₂ he₁ he₂).isoBot = c.isoBot := rfl

theorem complex_incl_coe (a : O) :
    (complex c e₁ e₂ he₁ he₂).incl.app (a : WithTop O) = c.incl.app a := rfl

theorem complex_incl_top : (complex c e₁ e₂ he₁ he₂).incl.app ⊤ = 𝟙 Y := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The exact original attaching record is retained at every old nonmaximal stage. -/
theorem attach_nonmax (a : O) (ha : ¬ IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    (complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew =
      (c.attachCells a ha).ofArrowIso (stepIso c a ha) := by
  classical
  simp only [complex, WithTop.recTopCoe, dite_eq_right ha]

theorem cells_nonmax (a : O) (ha : ¬ IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    ((complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew).ι = (c.attachCells a ha).ι := by
  rw [attach_nonmax c e₁ e₂ he₁ he₂ a ha hnew]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An old maximal join has an actual empty occurrence family and adds no original cell. -/
theorem cells_max (a : O) (ha : IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    ((complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew).ι = PEmpty.{w + 1} := by
  classical
  simp only [complex, WithTop.recTopCoe, dite_eq_left ha]
  rfl

/-- Every completed cell still comes from one actual original nonmaximal stage. -/
def originalCell (a : (complex c e₁ e₂ he₁ he₂).Cells) : c.Cells := by
  classical
  rcases a with ⟨a, ha, k⟩
  cases a with
  | top => exact False.elim (ha isMax_top)
  | coe a =>
    by_cases hmax : IsMax a
    · exact (cast (cells_max c e₁ e₂ he₁ he₂ a hmax ha) k).elim
    · exact ⟨a, hmax, cast (cells_nonmax c e₁ e₂ he₁ he₂ a hmax ha) k⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem originalCell_coe (a : O) (ha : ¬ IsMax (a : WithTop O))
    (k : ((complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) ha).ι) (hold : ¬ IsMax a) :
    originalCell c e₁ e₂ he₁ he₂ ⟨(a : WithTop O), ha, k⟩ =
      ⟨a, hold, cast (cells_nonmax c e₁ e₂ he₁ he₂ a hold ha) k⟩ := by
  classical
  simp [originalCell, WithTop.recTopCoe, hold]

/-- Every original occurrence enters the completed history at its original tagged stage. -/
def completedCell (a : c.Cells) : (complex c e₁ e₂ he₁ he₂).Cells where
  j := (a.j : WithTop O)
  hj := not_isMax_of_lt (WithTop.coe_lt_top a.j)
  k := cast (cells_nonmax c e₁ e₂ he₁ he₂ a.j a.hj
    (not_isMax_of_lt (WithTop.coe_lt_top a.j))).symm a.k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Completing the original endpoint adds no actual original cell occurrence. -/
def cellsEquiv : (complex c e₁ e₂ he₁ he₂).Cells ≃ c.Cells where
  toFun := originalCell c e₁ e₂ he₁ he₂
  invFun := completedCell c e₁ e₂ he₁ he₂
  left_inv a := by
    classical
    rcases a with ⟨a, ha, k⟩
    cases a with
    | top => exact False.elim (ha isMax_top)
    | coe a =>
      by_cases hmax : IsMax a
      · exact (cast (cells_max c e₁ e₂ he₁ he₂ a hmax ha) k).elim
      · rw [originalCell_coe c e₁ e₂ he₁ he₂ a ha k hmax]
        simp only [completedCell, cast_cast, cast_eq]
  right_inv a := by
    classical
    rcases a with ⟨a, ha, k⟩
    dsimp only [completedCell]
    rw [originalCell_coe c e₁ e₂ he₁ he₂ a _ _ ha]
    simp only [cast_cast, cast_eq]

theorem cells_cardinal : Cardinal.mk (complex c e₁ e₂ he₁ he₂).Cells = Cardinal.mk c.Cells :=
  Cardinal.mk_congr (cellsEquiv c e₁ e₂ he₁ he₂)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem completedCell_label (a : c.Cells) : (completedCell c e₁ e₂ he₁ he₂ a).i = a.i := by
  classical
  rcases a with ⟨a, ha, k⟩
  exact attachmentLabel_of_eq _ _ (attach_nonmax c e₁ e₂ he₁ he₂ a ha _) k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem completedCell_inclusion (a : c.Cells) :
    (completedCell c e₁ e₂ he₁ he₂ a).ι =
      eqToHom (congrArg (fun p : P.toSet => p.1.right) (completedCell_label c e₁ e₂ he₁ he₂ a)) ≫
        a.ι := by
  classical
  rcases a with ⟨a, ha, k⟩
  have hcell := attachmentCell_of_eq _ _ (attach_nonmax c e₁ e₂ he₁ he₂ a ha
    (not_isMax_of_lt (WithTop.coe_lt_top a))) k
  have hpost := congrArg
    (fun z => z ≫ (completedShape c).incl.app (Order.succ (a : WithTop O))) hcell
  refine hpost.trans ?_
  rw [Category.assoc]
  congr 1
  change ((c.attachCells a ha).cofan₂.inj k ≫
    ((c.attachCells a ha).g₂ ≫ (completedShape c).F.map
      (eqToHom (WithTop.succ_coe_of_not_isMax ha).symm))) ≫
      (completedShape c).incl.app (Order.succ (a : WithTop O)) =
        (c.attachCells a ha).cell k ≫ c.incl.app (Order.succ a)
  rw [Category.assoc, Category.assoc, (Cocone.mk Y (completedShape c).incl).w]
  exact (Category.assoc _ _ _).symm

theorem originalCell_stage (a : (complex c e₁ e₂ he₁ he₂).Cells) :
    ((cellsEquiv c e₁ e₂ he₁ he₂ a).j : WithTop O) = a.j := by
  have h := congrArg (fun z : (complex c e₁ e₂ he₁ he₂).Cells => z.j)
    ((cellsEquiv c e₁ e₂ he₁ he₂).symm_apply_apply a)
  exact h

theorem originalCell_label (a : (complex c e₁ e₂ he₁ he₂).Cells) :
    a.i = (cellsEquiv c e₁ e₂ he₁ he₂ a).i := by
  have h := completedCell_label c e₁ e₂ he₁ he₂ (cellsEquiv c e₁ e₂ he₁ he₂ a)
  change ((cellsEquiv c e₁ e₂ he₁ he₂).symm (cellsEquiv c e₁ e₂ he₁ he₂ a)).i = _ at h
  simpa only [Equiv.symm_apply_apply] using h

theorem sourceCofan_nonmax_heq (a : O) (ha : ¬ IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    ((complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew).cofan₁ ≍
      (c.attachCells a ha).cofan₁ := by
  rw [attach_nonmax]
  rfl

theorem targetCofan_nonmax_heq (a : O) (ha : ¬ IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    ((complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew).cofan₂ ≍
      (c.attachCells a ha).cofan₂ := by
  rw [attach_nonmax]
  rfl

theorem attachingMap_nonmax_heq (a : O) (ha : ¬ IsMax a) (hnew : ¬ IsMax (a : WithTop O)) :
    ((complex c e₁ e₂ he₁ he₂).attachCells (a : WithTop O) hnew).m ≍ (c.attachCells a ha).m := by
  rw [attach_nonmax]
  rfl

end SuppliedEmptyCofans

section OriginalNoMaximum

variable [NoMaxOrder O]

/-- An original no-maximum history completes at its actual endpoint using only its original
cells. -/
def noMaxComplex : RelativeCellComplex.{w} (fun _ : WithTop O => P.homFamily) f where
  __ := completedShape c
  attachCells a ha := by
    cases a with
    | top => exact False.elim (ha isMax_top)
    | coe a => exact (c.attachCells a (not_isMax a)).ofArrowIso (stepIso c a (not_isMax a))

theorem noMaxComplex_obj_coe (a : O) : (noMaxComplex c).F.obj (a : WithTop O) = c.F.obj a := rfl

theorem noMaxComplex_obj_top : (noMaxComplex c).F.obj ⊤ = Y := rfl

theorem noMaxComplex_isoBot : (noMaxComplex c).isoBot = c.isoBot := rfl

theorem noMaxComplex_incl_coe (a : O) :
    (noMaxComplex c).incl.app (a : WithTop O) = c.incl.app a := rfl

theorem noMaxComplex_incl_top : (noMaxComplex c).incl.app ⊤ = 𝟙 Y := rfl

/-- The same actual original cell occurrence is selected in a no-maximum completion. -/
def originalNoMaxCell (a : (noMaxComplex c).Cells) : c.Cells := by
  rcases a with ⟨a, ha, k⟩
  cases a with
  | top => exact False.elim (ha isMax_top)
  | coe a => exact ⟨a, not_isMax a, k⟩

/-- Every original occurrence has the same actual no-maximum completed occurrence. -/
def completedNoMaxCell (a : c.Cells) : (noMaxComplex c).Cells where
  j := (a.j : WithTop O)
  hj := not_isMax_of_lt (WithTop.coe_lt_top a.j)
  k := a.k

/-- The original and no-maximum completed cell carriers are actually equivalent. -/
def noMaxCellsEquiv : (noMaxComplex c).Cells ≃ c.Cells where
  toFun := originalNoMaxCell c
  invFun := completedNoMaxCell c
  left_inv a := by
    rcases a with ⟨a, ha, k⟩
    cases a with
    | top => exact False.elim (ha isMax_top)
    | coe a => rfl
  right_inv a := by cases a; rfl

theorem noMaxCells_cardinal : Cardinal.mk (noMaxComplex c).Cells = Cardinal.mk c.Cells :=
  Cardinal.mk_congr (noMaxCellsEquiv c)

theorem noMaxComplex_sourceCofan (a : O) (hnew : ¬ IsMax (a : WithTop O)) :
    ((noMaxComplex c).attachCells (a : WithTop O) hnew).cofan₁ =
      (c.attachCells a (not_isMax a)).cofan₁ := rfl

theorem noMaxComplex_targetCofan (a : O) (hnew : ¬ IsMax (a : WithTop O)) :
    ((noMaxComplex c).attachCells (a : WithTop O) hnew).cofan₂ =
      (c.attachCells a (not_isMax a)).cofan₂ := rfl

theorem noMaxComplex_attachingMap (a : O) (hnew : ¬ IsMax (a : WithTop O)) :
    ((noMaxComplex c).attachCells (a : WithTop O) hnew).m = (c.attachCells a (not_isMax a)).m := rfl

theorem noMaxComplex_label (a : O) (hnew : ¬ IsMax (a : WithTop O))
    (k : (c.attachCells a (not_isMax a)).ι) :
    ((noMaxComplex c).attachCells (a : WithTop O) hnew).π k =
      (c.attachCells a (not_isMax a)).π k := rfl

theorem completedNoMaxCell_label (a : c.Cells) : (completedNoMaxCell c a).i = a.i := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem completedNoMaxCell_inclusion (a : c.Cells) : (completedNoMaxCell c a).ι = a.ι := by
  rcases a with ⟨a, ha, k⟩
  change ((c.attachCells a ha).cofan₂.inj k ≫
    ((c.attachCells a ha).g₂ ≫ (completedShape c).F.map
      (eqToHom (WithTop.succ_coe_of_not_isMax ha).symm))) ≫
      (completedShape c).incl.app (Order.succ (a : WithTop O)) =
        (c.attachCells a ha).cell k ≫ c.incl.app (Order.succ a)
  rw [Category.assoc, Category.assoc, (Cocone.mk Y (completedShape c).incl).w]
  exact (Category.assoc _ _ _).symm

theorem originalNoMaxCell_stage (a : (noMaxComplex c).Cells) :
    ((noMaxCellsEquiv c a).j : WithTop O) = a.j :=
  congrArg (fun z : (noMaxComplex c).Cells => z.j) ((noMaxCellsEquiv c).symm_apply_apply a)

theorem originalNoMaxCell_label (a : (noMaxComplex c).Cells) : a.i = (noMaxCellsEquiv c a).i := by
  have h := completedNoMaxCell_label c (noMaxCellsEquiv c a)
  change ((noMaxCellsEquiv c).symm (noMaxCellsEquiv c a)).i = _ at h
  simpa only [Equiv.symm_apply_apply] using h

end OriginalNoMaximum

end HomotopicalAlgebra.RelativeCellComplex.GenericCompletion

end GenericRelativeCellCompletionResearchCanonicalPromotion

section PlateauResearchCanonicalPromotion

open CategoryTheory Limits MorphismProperty Opposite
open HomotopicalAlgebra.CellularSubcomplexExtension

namespace HomotopicalAlgebra.CellularPlateau

section CappedOrder

variable {O : Type w} [LinearOrder O] (cap : O)

/-- The original order is capped at the same original closed-prefix endpoint. -/
def capIndex : O →o Set.Iic cap where
  toFun i := ⟨min i cap, min_le_right _ _⟩
  monotone' _ _ h := min_le_min_right _ h

/-- Original stages already in the prefix retain their exact original index. -/
theorem capIndex_of_le (i : O) (hi : i ≤ cap) : capIndex cap i = ⟨i, hi⟩ :=
  Subtype.ext (min_eq_left hi)

/-- Every later original stage uses the same greatest original prefix stage. -/
theorem capIndex_of_ge (i : O) (hi : cap ≤ i) : capIndex cap i = ⊤ :=
  Subtype.ext (min_eq_right hi)

/-- The actual capped original order functor. -/
abbrev capFunctor : O ⥤ Set.Iic cap := (capIndex cap).monotone.functor

/-- The capped original index has its original transition into the unchanged index. -/
def capTransition : capFunctor cap ⋙ (Set.initialSegIic cap).monotone.functor ⟶ 𝟭 O where
  app i := homOfLE (min_le_left i cap)
  naturality _ _ _ := Subsingleton.elim _ _

/-- The original cap vertex proves finality of the capped original functor. -/
theorem capFunctor_final : (capFunctor cap).Final := by
  rw [Monotone.final_functor_iff]
  intro i
  refine ⟨cap, ?_⟩
  change i.1 ≤ min cap cap
  simpa only [min_self, Set.mem_Iic] using i.2

/-- An original lower interval before the cap maps into the same original prefix lower interval. -/
def beforeCapIndex (j : O) (hj : j ≤ cap) : Set.Iio j →o Set.Iio (capIndex cap j) where
  toFun a := ⟨capIndex cap a.1, by
    change min a.1 cap < min j cap
    rw [min_eq_left (a.2.le.trans hj), min_eq_left hj]
    exact a.2⟩
  monotone' _ _ h := (capIndex cap).monotone h

/-- Each actual original lower vertex witnesses finality of the lower-interval map. -/
theorem beforeCapIndex_final (j : O) (hj : j ≤ cap) :
    (beforeCapIndex cap j hj).monotone.functor.Final := by
  rw [Monotone.final_functor_iff]
  intro a
  let b : Set.Iio j := ⟨a.1.1, by
    have ha : a.1.1 < min j cap := a.2
    simpa only [min_eq_left hj, Set.mem_Iio] using ha⟩
  refine ⟨b, ?_⟩
  change a.1.1 ≤ min a.1.1 cap
  rw [min_eq_left a.1.2]

/-- A later original lower interval caps into the entire original closed prefix. -/
def afterCapIndex (j : O) : Set.Iio j →o Set.Iic cap where
  toFun a := capIndex cap a.1
  monotone' _ _ h := (capIndex cap).monotone h

/-- The actual cap vertex is present in every strictly later original lower interval. -/
theorem afterCapIndex_final (j : O) (hj : cap < j) :
    (afterCapIndex cap j).monotone.functor.Final := by
  rw [Monotone.final_functor_iff]
  intro a
  refine ⟨⟨cap, hj⟩, ?_⟩
  change a.1 ≤ min cap cap
  simpa only [min_self, Set.mem_Iic] using a.2

end CappedOrder

section CappedDiagram

variable {C : Type u} [Category.{v} C] {O : Type w} [LinearOrder O]
  (cap : O) (G : Set.Iic cap ⥤ C)

/-- The actual original prefix diagram is unchanged below the cap and constant thereafter. -/
abbrev F : O ⥤ C := capFunctor cap ⋙ G

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Original prefix limits and the actual constant tail prove complete original-order continuity. -/
theorem wellOrderContinuous [G.IsWellOrderContinuous] : (F cap G).IsWellOrderContinuous where
  nonempty_isColimit j hj := by
    by_cases hjcap : j ≤ cap
    · have hlim : Order.IsSuccLimit (capIndex cap j) := by
        rw [capIndex_of_le cap j hjcap]
        exact (Set.initialSegIic cap).isSuccLimit_apply_iff.mp hj
      let _ : (beforeCapIndex cap j hjcap).monotone.functor.Final :=
        beforeCapIndex_final cap j hjcap
      exact ⟨(Functor.Final.isColimitWhiskerEquiv
        (beforeCapIndex cap j hjcap).monotone.functor _).symm
          (G.isColimitOfIsWellOrderContinuous (capIndex cap j) hlim)⟩
    · have hcapj : cap < j := lt_of_not_ge hjcap
      let _ : (afterCapIndex cap j).monotone.functor.Final := afterCapIndex_final cap j hcapj
      let terminal : IsTerminal (capIndex cap j) := IsTerminal.ofUniqueHom
        (fun a => homOfLE (by rw [capIndex_of_ge cap j hcapj.le]; exact le_top))
        (fun _ _ => Subsingleton.elim _ _)
      exact ⟨(Functor.Final.isColimitWhiskerEquiv
        (afterCapIndex cap j).monotone.functor _).symm
          (colimitOfDiagramTerminal terminal G)⟩

end CappedDiagram

section OneSuccessorExtension

variable {C : Type u} [Category.{v} C] {O : Type w} [LinearOrder O] [SuccOrder O]
  {j : O} (hj : ¬ IsMax j) (G : Set.Iic j ⥤ C) [G.IsWellOrderContinuous]
  {E : C} (τ : G.obj ⟨j, le_rfl⟩ ⟶ E)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Adding one actual original successor arrow preserves the original prefix limit cocones. -/
theorem extendToSuccContinuous :
    (CategoryTheory.SmallObject.SuccStruct.extendToSucc hj G τ).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    let H := CategoryTheory.SmallObject.SuccStruct.extendToSucc hj G τ
    let R := CategoryTheory.SmallObject.restrictionLE H (Order.le_succ j)
    let e : R ≅ G := CategoryTheory.SmallObject.SuccStruct.extendToSuccRestrictionLEIso hj G τ
    let _ : R.IsWellOrderContinuous := CategoryTheory.Functor.isWellOrderContinuous_of_iso e.symm
    have hmO : Order.IsSuccLimit m.1 := (Set.initialSegIic (Order.succ j)).map_isSuccLimit hm
    have hmj : m.1 ≤ j := (Order.IsSuccLimit.le_succ_iff hmO).1 m.2
    let m₀ : Set.Iic j := ⟨m.1, hmj⟩
    have hm₀ : Order.IsSuccLimit m₀ := (Set.initialSegIic j).isSuccLimit_apply_iff.mp hmO
    let q : Set.Iio m₀ → Set.Iio m := fun a =>
      ⟨⟨a.1.1, a.1.2.trans (Order.le_succ j)⟩, a.2⟩
    have hq : Monotone q := fun _ _ h => h
    let _ : hq.functor.Final := by
      rw [Monotone.final_functor_iff]
      intro a
      refine ⟨⟨⟨a.1.1, (show a.1.1 ≤ m.1 from a.2.le).trans hmj⟩, a.2⟩, ?_⟩
      exact le_rfl
    exact ⟨(Functor.Final.isColimitWhiskerEquiv hq.functor
      ((Set.principalSegIio m).cocone H))
        (R.isColimitOfIsWellOrderContinuous m₀ hm₀)⟩

end OneSuccessorExtension

section OriginalEmptyAttachments

variable {C : Type u} [Category.{v} C] [HasInitial C]
  (P : MorphismProperty C)

/-- The actual original initial object is the empty source and target cofan. -/
def emptyCofan : Cofan (fun i : PEmpty.{w + 1} => (i.elim : C)) :=
  Cofan.mk (⊥_ C) (fun i => i.elim)

/-- The actual empty cofan has its genuine initial-object universal property. -/
def emptyCofanIsColimit : IsColimit (emptyCofan.{w} (C := C)) :=
  (isColimitEquivIsInitialOfIsEmpty C _).symm initialIsInitial

/-- Every constant-tail step is an actual empty original P attachment. -/
def emptyAttach {X Y : C} (f : X ⟶ Y) [IsIso f] : AttachCells.{w} P.homFamily f :=
  CategoryTheory.SmallObject.CellularNormalization.emptyAttachCells P.homFamily f
    (emptyCofan.{w} (C := C)) (emptyCofan.{w} (C := C))
      (emptyCofanIsColimit.{w} (C := C)) (emptyCofanIsColimit.{w} (C := C))

end OriginalEmptyAttachments

section OriginalPlateau

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f) (cap : O)
  (s : CellularSubcomplex (prefixComplex d c cap))

omit [SuccOrder O] [WellFoundedLT O] in
/-- The original bottom stays the actual bottom of the original prefix. -/
theorem capIndex_bot : capIndex cap (⊥ : O) = (⊥ : Set.Iic cap) :=
  Subtype.ext (min_eq_left bot_le)

omit [OrderBot O] [SuccOrder O] [WellFoundedLT O] in
/-- An actual cell before the cap is a nonmaximal original prefix stage. -/
theorem oldIndex_notMax (i : O) (hi : i < cap) : ¬ IsMax (⟨i, hi.le⟩ : Set.Iic cap) := by
  rw [not_isMax_iff]
  exact ⟨⊤, hi⟩

omit [OrderBot O] [WellFoundedLT O] in
/-- Every pre-cap successor keeps the exact actual original prefix successor. -/
theorem capSuccessorEq (i : O) (hi : i < cap) :
    capIndex cap (Order.succ i) = Order.succ (⟨i, hi.le⟩ : Set.Iic cap) := by
  apply Subtype.ext
  change min (Order.succ i) cap = (Order.succ (⟨i, hi.le⟩ : Set.Iic cap)).1
  rw [min_eq_left (Order.succ_le_of_lt hi), prefixSuccessorEq _ (oldIndex_notMax cap i hi)]

/-- The original root isomorphism is transported only by the exact original bottom equality. -/
def botIso : (F cap s.complex.F).obj ⊥ ≅ X :=
  s.complex.F.mapIso (eqToIso (capIndex_bot cap)) ≪≫ s.complex.isoBot

/-- The plateau endpoint cocone uses only the original prefix endpoint legs. -/
abbrev endpointCocone : Cocone (F cap s.complex.F) :=
  (Cocone.mk s.endpoint s.complex.incl).whisker (capFunctor cap)

/-- Finality of the actual capped index retains the original endpoint universal property. -/
def endpointIsColimit : IsColimit (endpointCocone d c cap s) := by
  let _ : (capFunctor cap).Final := capFunctor_final cap
  exact (Functor.Final.isColimitWhiskerEquiv (capFunctor cap) _).symm s.complex.isColimit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Before the cap, both original objects and the original whole successor arrow are retained. -/
def beforeStepIso (i : O) (hi : i < cap) :
    Arrow.mk (s.complex.F.map (homOfLE (Order.le_succ (⟨i, hi.le⟩ : Set.Iic cap)))) ≅
      Arrow.mk ((F cap s.complex.F).map (homOfLE (Order.le_succ i))) :=
  Arrow.isoMk
    (s.complex.F.mapIso (eqToIso (capIndex_of_le cap i hi.le).symm))
    (s.complex.F.mapIso (eqToIso (capSuccessorEq cap i hi).symm)) (by
      change s.complex.F.map (eqToHom (capIndex_of_le cap i hi.le).symm) ≫
        s.complex.F.map ((capFunctor cap).map (homOfLE (Order.le_succ i))) =
          s.complex.F.map (homOfLE (Order.le_succ (⟨i, hi.le⟩ : Set.Iic cap))) ≫
            s.complex.F.map (eqToHom (capSuccessorEq cap i hi).symm)
      rw [← s.complex.F.map_comp, ← s.complex.F.map_comp]
      congr 1)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every later plateau transition is an actual identity transported by the same prefix-top
equality. -/
theorem afterStep_isIso (i : O) (hi : cap ≤ i) :
    IsIso ((F cap s.complex.F).map (homOfLE (Order.le_succ i))) := by
  have e : capIndex cap i = capIndex cap (Order.succ i) :=
    (capIndex_of_ge cap i hi).trans
      (capIndex_of_ge cap (Order.succ i) (hi.trans (Order.le_succ i))).symm
  have hmap : (capFunctor cap).map (homOfLE (Order.le_succ i)) = eqToHom e := Subsingleton.elim _ _
  change IsIso (s.complex.F.map ((capFunctor cap).map (homOfLE (Order.le_succ i))))
  rw [hmap]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original closed prefix becomes a full original-ordinal history with an actual empty tail. -/
def complex : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) s.hom where
  F := F cap s.complex.F
  isoBot := botIso d c cap s
  isWellOrderContinuous := wellOrderContinuous cap s.complex.F
  incl := (endpointCocone d c cap s).ι
  isColimit := endpointIsColimit d c cap s
  fac := by
    change (s.complex.isoBot.inv ≫ s.complex.F.map (eqToHom (capIndex_bot cap).symm)) ≫
      s.complex.incl.app (capIndex cap ⊥) = s.hom
    rw [Category.assoc, (Cocone.mk s.endpoint s.complex.incl).w]
    exact s.complex.fac
  attachCells i hi := by
    classical
    by_cases hicap : i < cap
    · exact (s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).ofArrowIso
        (beforeStepIso d c cap s i hicap)
    · let _ : IsIso ((F cap s.complex.F).map (homOfLE (Order.le_succ i))) :=
        afterStep_isIso d c cap s i (le_of_not_gt hicap)
      exact emptyAttach d.I _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original prefix attaching cofan and label is retained before the cap. -/
theorem attach_before (i : O) (hi : ¬ IsMax i) (hicap : i < cap) :
    (complex d c cap s).attachCells i hi =
      (s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).ofArrowIso
        (beforeStepIso d c cap s i hicap) := by
  simp only [complex, dite_eq_left hicap]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- After the cap the original attaching family has exactly no occurrences. -/
theorem attach_after_empty (i : O) (hi : ¬ IsMax i) (hicap : cap ≤ i) :
    ((complex d c cap s).attachCells i hi).ι = PEmpty.{w + 1} := by
  simp only [complex, dite_eq_right (not_lt_of_ge hicap)]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual original prefix comparisons extend along the original ambient stage maps. -/
def comparison : (F cap s.complex.F) ⟶ c.F :=
  Functor.whiskerLeft (capFunctor cap) s.comparison ≫ Functor.whiskerRight (capTransition cap) c.F

/-- The actual comparison retains the original prefix map and original ambient transition. -/
theorem comparison_app (i : O) : (comparison d c cap s).app i =
    s.comparison.app (capIndex cap i) ≫ c.F.map (homOfLE (min_le_left i cap)) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual empty-tail endpoint comparison keeps every original prefix cocone leg. -/
theorem comparison_endpoint (i : O) :
    (complex d c cap s).incl.app i ≫ (s.inclusion ≫ c.incl.app cap) =
      (comparison d c cap s).app i ≫ c.incl.app i := by
  change s.complex.incl.app (capIndex cap i) ≫ (s.inclusion ≫ c.incl.app cap) =
    (s.comparison.app (capIndex cap i) ≫ c.F.map (homOfLE (min_le_left i cap))) ≫ c.incl.app i
  rw [← Category.assoc, s.comparison_endpoint, Category.assoc, prefixComplex_incl]
  rw [(Cocone.mk Y c.incl).w]
  rw [Category.assoc, (Cocone.mk Y c.incl).w]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual extended comparison keeps the original root isomorphism. -/
theorem comparison_bot :
    (complex d c cap s).isoBot.inv ≫ (comparison d c cap s).app ⊥ = c.isoBot.inv := by
  change (s.complex.isoBot.inv ≫ s.complex.F.map (eqToHom (capIndex_bot cap).symm)) ≫
    (s.comparison.app (capIndex cap ⊥) ≫ c.F.map (homOfLE (min_le_left (⊥ : O) cap))) = c.isoBot.inv
  rw [Category.assoc, ← Category.assoc (s.complex.F.map _), s.comparison.naturality, Category.assoc]
  change s.complex.isoBot.inv ≫
    (s.comparison.app (⊥ : Set.Iic cap) ≫
      (c.F.map ((Set.initialSegIic cap).monotone.functor.map (eqToHom (capIndex_bot cap).symm)) ≫
        c.F.map (homOfLE (min_le_left (⊥ : O) cap)))) = _
  rw [← c.F.map_comp]
  have h : (Set.initialSegIic cap).monotone.functor.map (eqToHom (capIndex_bot cap).symm) ≫
      homOfLE (min_le_left (⊥ : O) cap) = 𝟙 (⊥ : O) := Subsingleton.elim _ _
  rw [h]
  rw [← Category.assoc, s.comparison_bot]
  change c.isoBot.inv ≫ c.F.map (𝟙 (⊥ : O)) = c.isoBot.inv
  rw [c.F.map_id, Category.comp_id]

private theorem attachLabelOfEq {A B : C} {g : A ⟶ B}
    (a b : AttachCells.{w} d.I.homFamily g) (e : a = b) (k : a.ι) :
    a.π k = b.π ((Equiv.cast (congrArg (fun a => a.ι) e)) k) := by
  cases e
  rfl

private theorem attachCellOfEq {A B : C} {g : A ⟶ B}
    (a b : AttachCells.{w} d.I.homFamily g) (e : a = b) (k : a.ι) :
    a.cell k = eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (attachLabelOfEq d a b e k)) ≫
      b.cell ((Equiv.cast (congrArg (fun a => a.ι) e)) k) := by
  cases e
  change a.cell k = 𝟙 _ ≫ a.cell k
  rw [Category.id_comp]

/-- The exact attachment equality transports only the original occurrence carrier. -/
def beforeIndexEquiv (i : O) (hi : ¬ IsMax i) (hicap : i < cap) :
    ((complex d c cap s).attachCells i hi).ι ≃
      (s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).ι :=
  Equiv.cast (congrArg (fun a => a.ι) (attach_before d c cap s i hi hicap))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original generating label is unchanged under the exact occurrence transport. -/
theorem beforeIndex_label (i : O) (hi : ¬ IsMax i) (hicap : i < cap)
    (k : ((complex d c cap s).attachCells i hi).ι) :
    ((complex d c cap s).attachCells i hi).π k =
      (s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).π
        (beforeIndexEquiv d c cap s i hi hicap k) :=
  attachLabelOfEq d _ _ (attach_before d c cap s i hi hicap) k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual prefix cell map keeps only its exact original successor target transport. -/
theorem cell_before (i : O) (hi : ¬ IsMax i) (hicap : i < cap)
    (k : ((complex d c cap s).attachCells i hi).ι) :
    ((complex d c cap s).attachCells i hi).cell k =
      eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
        (beforeIndex_label d c cap s i hi hicap k)) ≫
        (s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).cell
          (beforeIndexEquiv d c cap s i hi hicap k) ≫
            s.complex.F.map (eqToHom (capSuccessorEq cap i hicap).symm) := by
  have hk := attachCellOfEq d _ _ (attach_before d c cap s i hi hicap) k
  change ((complex d c cap s).attachCells i hi).cell k =
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (beforeIndex_label d c cap s i hi hicap k)) ≫
      ((s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).cofan₂.inj
          (beforeIndexEquiv d c cap s i hi hicap k) ≫
        ((s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).g₂ ≫
          s.complex.F.map (eqToHom (capSuccessorEq cap i hicap).symm))) at hk
  change ((complex d c cap s).attachCells i hi).cell k =
    eqToHom (congrArg (fun p : d.I.toSet => p.1.right) (beforeIndex_label d c cap s i hi hicap k)) ≫
      ((s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).cofan₂.inj
          (beforeIndexEquiv d c cap s i hi hicap k) ≫
        (s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).g₂) ≫
          s.complex.F.map (eqToHom (capSuccessorEq cap i hicap).symm)
  simpa only [Category.assoc] using hk

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each full original stage has its literal original prefix occurrence embedding, or an empty
family. -/
theorem cells_before (i : O) (hi : ¬ IsMax i)
    (k : ((complex d c cap s).attachCells i hi).ι) : i < cap := by
  by_contra hicap
  exact ((Equiv.cast (attach_after_empty d c cap s i hi (le_of_not_gt hicap))) k).elim

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual occurrence retains its literal original prefix embedding. -/
def cellEmbedding (i : O) (hi : ¬ IsMax i) :
    ((complex d c cap s).attachCells i hi).ι ↪ (c.attachCells i hi).ι where
  toFun k :=
    s.cellIndex ⟨i, (cells_before d c cap s i hi k).le⟩
      (oldIndex_notMax cap i (cells_before d c cap s i hi k))
        (beforeIndexEquiv d c cap s i hi (cells_before d c cap s i hi k) k)
  inj' k l hkl := by
    apply (beforeIndexEquiv d c cap s i hi (cells_before d c cap s i hi k)).injective
    exact (s.cellIndex ⟨i, (cells_before d c cap s i hi k).le⟩
      (oldIndex_notMax cap i (cells_before d c cap s i hi k))).injective hkl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual occurrence embedding retains the original generating arrow. -/
theorem cellEmbedding_label (i : O) (hi : ¬ IsMax i)
    (k : ((complex d c cap s).attachCells i hi).ι) :
    ((complex d c cap s).attachCells i hi).π k =
      (c.attachCells i hi).π (cellEmbedding d c cap s i hi k) := by
  exact (beforeIndex_label d c cap s i hi (cells_before d c cap s i hi k) k).trans
    (s.label_eq ⟨i, (cells_before d c cap s i hi k).le⟩
      (oldIndex_notMax cap i (cells_before d c cap s i hi k))
        (beforeIndexEquiv d c cap s i hi (cells_before d c cap s i hi k) k))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Target comparisons commute with precisely the same original prefix successor equality. -/
theorem beforeComparison_target (i : O) (hicap : i < cap) :
    s.complex.F.map (eqToHom (capSuccessorEq cap i hicap).symm) ≫
      (comparison d c cap s).app (Order.succ i) =
        s.comparison.app (Order.succ (⟨i, hicap.le⟩ : Set.Iic cap)) ≫
          c.F.map (eqToHom (prefixSuccessorEq _ (oldIndex_notMax cap i hicap))) := by
  rw [comparison_app]
  change s.complex.F.map (eqToHom (capSuccessorEq cap i hicap).symm) ≫
      (s.comparison.app (capIndex cap (Order.succ i)) ≫
        c.F.map (homOfLE (min_le_left (Order.succ i) cap))) = _
  rw [← Category.assoc, s.comparison.naturality, Category.assoc]
  change s.comparison.app (Order.succ (⟨i, hicap.le⟩ : Set.Iic cap)) ≫
    (c.F.map ((Set.initialSegIic cap).monotone.functor.map
      (eqToHom (capSuccessorEq cap i hicap).symm)) ≫
        c.F.map (homOfLE (min_le_left (Order.succ i) cap))) = _
  rw [← c.F.map_comp]
  congr 1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original closed-prefix subcomplex extends as a genuine full original-ordinal subcomplex. -/
def subcomplex : CellularSubcomplex c where
  endpoint := s.endpoint
  hom := s.hom
  inclusion := s.inclusion ≫ c.incl.app cap
  complex := complex d c cap s
  comparison := comparison d c cap s
  comparison_bot := comparison_bot d c cap s
  comparison_endpoint i := comparison_endpoint d c cap s i
  cellIndex i hi := cellEmbedding d c cap s i hi
  label_eq i hi k := cellEmbedding_label d c cap s i hi k
  cell_eq i hi k := by
    classical
    by_cases hicap : i < cap
    · rw [cell_before d c cap s i hi hicap]
      simp only [Category.assoc]
      have ht := beforeComparison_target d c cap s i hicap
      have htc := congrArg
        (fun z => eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
            (beforeIndex_label d c cap s i hi hicap k)) ≫
          (s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).cell
            (beforeIndexEquiv d c cap s i hi hicap k) ≫ z) ht
      rw [show eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
            (beforeIndex_label d c cap s i hi hicap k)) ≫
          (s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).cell
            (beforeIndexEquiv d c cap s i hi hicap k) ≫
              s.complex.F.map (eqToHom (capSuccessorEq cap i hicap).symm) ≫
                (comparison d c cap s).app (Order.succ i) = _ by
        simpa only [Category.assoc] using htc]
      have hs := s.cell_eq ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)
        (beforeIndexEquiv d c cap s i hi hicap k)
      have hsc := congrArg
        (fun z => eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
            (beforeIndex_label d c cap s i hi hicap k)) ≫ z ≫
          c.F.map (eqToHom (prefixSuccessorEq (⟨i, hicap.le⟩ : Set.Iic cap)
            (oldIndex_notMax cap i hicap)))) hs
      simp only [Category.assoc] at hsc
      rw [show eqToHom (congrArg (fun p : d.I.toSet => p.1.right)
            (beforeIndex_label d c cap s i hi hicap k)) ≫
          (s.complex.attachCells ⟨i, hicap.le⟩ (oldIndex_notMax cap i hicap)).cell
            (beforeIndexEquiv d c cap s i hi hicap k) ≫
              s.comparison.app (Order.succ (⟨i, hicap.le⟩ : Set.Iic cap)) ≫
                c.F.map (eqToHom (prefixSuccessorEq (⟨i, hicap.le⟩ : Set.Iic cap)
                  (oldIndex_notMax cap i hicap))) = _ by
        exact hsc]
      rw [prefixComplex_cell]
      simp only [Category.assoc]
      rw [← c.F.map_comp]
      have hmap : eqToHom (prefixSuccessorEq (⟨i, hicap.le⟩ : Set.Iic cap)
          (oldIndex_notMax cap i hicap)).symm ≫
        eqToHom (prefixSuccessorEq (⟨i, hicap.le⟩ : Set.Iic cap)
          (oldIndex_notMax cap i hicap)) = 𝟙 (Order.succ i) := by simp
      rw [hmap, c.F.map_id, Category.comp_id]
      simp only [cellEmbedding, ← Category.assoc, eqToHom_trans]
      rfl
    · exact ((Equiv.cast (attach_after_empty d c cap s i hi (le_of_not_gt hicap))) k).elim

/-- The original prefix ambient occurrence retains its original stage and original attaching
index. -/
def ambientOccurrence (a : (prefixComplex d c cap).Cells) : c.Cells where
  j := a.j.1
  hj := prefixNotMax a.j a.hj
  k := a.k

/-- Every actual original prefix occurrence embeds into the unchanged original ambient
presentation. -/
def ambientOccurrenceEmbedding : (prefixComplex d c cap).Cells ↪ c.Cells where
  toFun := ambientOccurrence d c cap
  inj' := by
    intro a b hab
    rcases a with ⟨⟨i, hi⟩, hi', k⟩
    rcases b with ⟨⟨j, hj⟩, hj', l⟩
    have hij : i = j := congrArg (fun a : c.Cells => a.j) hab
    subst j
    have hkl : k = l := by
      apply (HomotopicalAlgebra.CellularSubcomplexContainment.occurrenceEmbedding d c i
        (prefixNotMax (⟨i, hi⟩ : Set.Iic cap) hi')).injective
      exact hab
    subst l
    rfl

/-- An actual original prefix cell is the same actual cell in the full plateau history. -/
def originalCell (a : s.complex.Cells) : (complex d c cap s).Cells where
  j := a.j.1
  hj := prefixNotMax a.j a.hj
  k := (beforeIndexEquiv d c cap s a.j.1 (prefixNotMax a.j a.hj)
    (prefixStage_lt_endpoint a.j a.hj)).symm a.k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The full plateau selects exactly the same original ambient occurrence as the prefix. -/
theorem originalCell_ambient (a : s.complex.Cells) :
    (subcomplex d c cap s).originalCell (originalCell d c cap s a) =
      ambientOccurrence d c cap (s.originalCell a) := by
  rcases a with ⟨⟨i, hi⟩, hj, k⟩
  simp only [CellularSubcomplex.originalCell, originalCell, subcomplex, ambientOccurrence,
    cellEmbedding]
  let e := beforeIndexEquiv d c cap s i (prefixNotMax (⟨i, hi⟩ : Set.Iic cap) hj)
    (prefixStage_lt_endpoint (⟨i, hi⟩ : Set.Iic cap) hj)
  change ({ j := i, hj := _, k := s.cellIndex ⟨i, hi⟩ hj (e (e.symm k)) } : c.Cells) = _
  rw [Equiv.apply_symm_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual plateau occurrence comes from an original prefix occurrence. -/
theorem exists_originalCell (a : (complex d c cap s).Cells) :
    ∃ b : s.complex.Cells,
      (subcomplex d c cap s).originalCell a = ambientOccurrence d c cap (s.originalCell b) := by
  let hicap := cells_before d c cap s a.j a.hj a.k
  let b : s.complex.Cells :=
    { j := ⟨a.j, hicap.le⟩
      hj := oldIndex_notMax cap a.j hicap
      k := beforeIndexEquiv d c cap s a.j a.hj hicap a.k }
  refine ⟨b, ?_⟩
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual support is exactly the original ambient image of the original prefix support. -/
theorem support : (subcomplex d c cap s).support =
    ambientOccurrenceEmbedding d c cap '' s.support := by
  ext a
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨q, hq⟩ := exists_originalCell d c cap s b
    exact ⟨s.originalCell q, ⟨q, rfl⟩, hq.symm.trans hb⟩
  · rintro ⟨q, ⟨b, hb⟩, hq⟩
    refine ⟨originalCell d c cap s b, ?_⟩
    exact (originalCell_ambient d c cap s b).trans
      ((congrArg (ambientOccurrence d c cap) hb).trans hq)

/-- The plateau keeps the actual original prefix endpoint. -/
theorem endpoint : (subcomplex d c cap s).endpoint = s.endpoint := rfl

/-- The plateau keeps the actual original root arrow. -/
theorem hom : (subcomplex d c cap s).hom = s.hom := rfl

/-- The actual endpoint comparison is the original prefix comparison and original ambient
endpoint leg. -/
theorem inclusion : (subcomplex d c cap s).inclusion = s.inclusion ≫ c.incl.app cap := rfl

end OriginalPlateau

end HomotopicalAlgebra.CellularPlateau

end PlateauResearchCanonicalPromotion

section PlateauCardinalityResearchCanonicalPromotion

open CategoryTheory Limits MorphismProperty Opposite

namespace HomotopicalAlgebra.CellularPlateau

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun _ : O => d.I.homFamily) f)
  (cap : O) (s : CellularSubcomplex (CellularSubcomplexExtension.prefixComplex d c cap))

/-- Full original-ordinal plateau extension retains exactly the original prefix cell count. -/
theorem cells_cardinal : Cardinal.mk (subcomplex d c cap s).complex.Cells =
    Cardinal.mk s.complex.Cells := by
  calc
    Cardinal.mk (subcomplex d c cap s).complex.Cells =
        Cardinal.mk (subcomplex d c cap s).support :=
      (subcomplex d c cap s).support_cardinal.symm
    _ = Cardinal.mk (ambientOccurrenceEmbedding d c cap '' s.support) :=
      congrArg (fun z : Set c.Cells => Cardinal.mk z) (support d c cap s)
    _ = Cardinal.mk s.support := Cardinal.mk_image_embedding _ _
    _ = Cardinal.mk s.complex.Cells := s.support_cardinal

end HomotopicalAlgebra.CellularPlateau

end PlateauCardinalityResearchCanonicalPromotion

namespace HomotopicalAlgebra.CellularLocalizationSmallness

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- Every original relative I-cell map is an original cofibration. -/
theorem relativeCellMaps_le_cofibrations :
    SmallObject.relativeCellMaps.{w} d.I ≤ cofibrations C := by
  have hleft : d.I.rlp.llp = cofibrations C := by
    rw [d.I_rlp, trivialFibrations_llp]
  rw [← hleft]
  exact d.I.transfiniteCompositions_pushouts_coproducts_le_llp_rlp


end HomotopicalAlgebra.CellularLocalizationSmallness
