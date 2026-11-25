/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerComparisonCocone
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerRestrictionComparison
public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData

/-!
# Original good-prefix states and strict histories

Complete prefix states retain every original lower comparison cocone and all original tree maps.
Preservation and literal restriction retain the full data. The empty prefix and the inverse functor
of histories are constructed here.

## Source and scope

This is intermediate infrastructure for Jacob Lurie's *Higher Topos Theory*,
Lemma A.1.5.7, in the author PDF dated April 9, 2017: printed pages 801–802
(PDF pages 819–820). The chosen original tree, lower colimits and root remain
explicit. These modules formalize complete prefix data, original comparison
maps and compatible prefix unions. Complete cell-tree goodification is the
separate construction in `OriginalCellTreeGoodification`.
-/

@[expose] public section

set_option autoImplicit false

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject Opposite

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P]
  {C : Type u} [cCategory : Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- The SAME original label function on a literal original lower carrier. -/
def prefixLabels (B : LowerSet P) (ord : PartialOrder B)
    (below : ∀ a b : B, @LE.le B ord.toLE a b → a.1 ≤ b.1) :
    @OrderHom B P ord.toPreorder pOrder.toPreorder :=
  @OrderHom.mk B P ord.toPreorder pOrder.toPreorder Subtype.val (fun _ _ h => below _ _ h)

/-- Complete original prefixes retain their actual tree and every original lower-colimit UP. -/
structure Prefix (B : LowerSet P) where
  /-- The actual new order on the SAME original carrier. -/
  ord : PartialOrder B
  /-- Every new comparison remains an original comparison. -/
  below : ∀ a b : B, @LE.le B ord.toLE a b → a.1 ≤ b.1
  /-- The actual tree under the original arbitrary root. -/
  tree : let _ : PartialOrder B := ord; CellTree s X (P := B)
  /-- Every original attaching label is retained. -/
  labels : ∀ a : B, (let _ : PartialOrder B := ord; tree.label a) = O.label a.1
  /-- The entire original natural comparison function. -/
  comparison :
    let _ : PartialOrder B := ord
    let _ : Preorder B := ord.toPreorder
    tree.diagram ⟶ (prefixLabels B ord below).monotone.functor ⋙ O.diagram
  /-- Cell compactness and individual predecessor bounds at the original rank. -/
  good : let _ : PartialOrder B := ord; tree.IsGood chi
  /-- The chosen original point and all original comparison-cocone legs have their genuine UP. -/
  lowerUP : ∀ (D : LowerSet P), D ≤ B →
    let _ : PartialOrder B := ord
    let _ : Preorder B := ord.toPreorder
    IsColimit (OriginalLowerComparisonCocone.cocone (prefixLabels B ord below)
      tree.diagram O.diagram comparison M D)

/-- The actual empty prefix uses the original empty lower colimit, with no compact-root premise. -/
def emptyPrefix : Prefix O M chi (⊥ : LowerSet P) where
  ord := inferInstance
  below _ _ h := h
  tree := CellTreeLowerRestriction.tree O M ⊥
  labels _ := rfl
  comparison := OriginalLowerRestrictionComparison.comparison O M ⊥
  good := {
    presentable_source a := False.elim (LowerSet.notMem_bot a.2)
    presentable_target a := False.elim (LowerSet.notMem_bot a.2)
    predecessor_lt a := False.elim (LowerSet.notMem_bot a.2) }
  lowerUP D hD := OriginalLowerRestrictionComparison.lowerIsColimit O M ⊥ D hD

/-- Preservation keeps every actual old order, cell, predecessor and original comparison field. -/
structure Preserves {B D : LowerSet P} (hBD : B ≤ D)
    (b : Prefix O M chi B) (d : Prefix O M chi D) : Prop where
  /-- The full old order restriction. -/
  order_restrict : ∀ a a' : B, @LE.le B b.ord.toLE a a' ↔
    @LE.le D d.ord.toLE ⟨a.1, hBD a.2⟩ ⟨a'.1, hBD a'.2⟩
  /-- Original old carriers remain initial in the new order. -/
  initial : ∀ a a' : D, a'.1 ∈ B → @LE.le D d.ord.toLE a a' → a.1 ∈ B
  /-- Every old vertex object. -/
  vertices : ∀ a : B, (let _ : PartialOrder B := b.ord; b.tree.vertex a) =
    (let _ : PartialOrder D := d.ord; d.tree.vertex ⟨a.1, hBD a.2⟩)
  /-- Every old original diagram map. -/
  maps : ∀ (a a' : B) (haa' : @LE.le B b.ord.toLE a a'),
    (let _ : PartialOrder B := b.ord
     let _ : Preorder B := b.ord.toPreorder
     b.tree.diagram.map (homOfLE haa' : a ⟶ a')) ≍
    (let _ : PartialOrder D := d.ord
     let _ : Preorder D := d.ord.toPreorder
     d.tree.diagram.map (homOfLE ((order_restrict a a').1 haa') :
       (⟨a.1, hBD a.2⟩ : D) ⟶ ⟨a'.1, hBD a'.2⟩))
  /-- Every selected old strict-predecessor point. -/
  predecessorPoints : ∀ a : B, (let _ : PartialOrder B := b.ord; b.tree.predecessorObj a) =
    (let _ : PartialOrder D := d.ord; d.tree.predecessorObj ⟨a.1, hBD a.2⟩)
  /-- Every original strict-predecessor cofan leg. -/
  predecessorLegs : ∀ (a z : B) (hza : @LT.lt B b.ord.toLT z a)
    (hza' : @LT.lt D d.ord.toLT ⟨z.1, hBD z.2⟩ ⟨a.1, hBD a.2⟩),
    (let _ : PartialOrder B := b.ord
     let _ : Preorder B := b.ord.toPreorder
     (b.tree.predecessor a).cocone.ι.app ⟨z, hza⟩) ≍
    (let _ : PartialOrder D := d.ord
     let _ : Preorder D := d.ord.toPreorder
     (d.tree.predecessor ⟨a.1, hBD a.2⟩).cocone.ι.app ⟨⟨z.1, hBD z.2⟩, hza'⟩)
  /-- Every original cell-source attaching map. -/
  attaching : ∀ a : B, (let _ : PartialOrder B := b.ord; b.tree.attaching a) ≍
    (let _ : PartialOrder D := d.ord; d.tree.attaching ⟨a.1, hBD a.2⟩)
  /-- Every original cell-target map. -/
  cells : ∀ a : B, (let _ : PartialOrder B := b.ord; b.tree.cell a) ≍
    (let _ : PartialOrder D := d.ord; d.tree.cell ⟨a.1, hBD a.2⟩)
  /-- Every old original natural comparison component. -/
  comparisons : ∀ a : B,
    (let _ : PartialOrder B := b.ord
     let _ : Preorder B := b.ord.toPreorder
     b.comparison.app a) ≍
    (let _ : PartialOrder D := d.ord
     let _ : Preorder D := d.ord.toPreorder
     d.comparison.app ⟨a.1, hBD a.2⟩)

/-- Full old-order preservation retains every actual strict comparison. -/
theorem Preserves.strict {B D : LowerSet P} {hBD : B ≤ D}
    {b : Prefix O M chi B} {d : Prefix O M chi D}
    (h : Preserves O M chi hBD b d) {a z : B}
    (hza : @LT.lt B b.ord.toLT z a) :
    @LT.lt D d.ord.toLT ⟨z.1, hBD z.2⟩ ⟨a.1, hBD a.2⟩ := by
  obtain ⟨hle, hnot⟩ := (@lt_iff_le_not_ge B b.ord.toPreorder z a).1 hza
  exact (@lt_iff_le_not_ge D d.ord.toPreorder _ _).2
    ⟨(h.order_restrict z a).1 hle, fun hn => hnot ((h.order_restrict a z).2 hn)⟩

/-- The same actual prefix preserves all its original fields. -/
theorem Preserves.refl {B : LowerSet P} (b : Prefix O M chi B) :
    Preserves O M chi (le_refl B) b b where
  order_restrict _ _ := Iff.rfl
  initial a _ _ _ := a.2
  vertices _ := rfl
  maps _ _ _ := HEq.rfl
  predecessorPoints _ := rfl
  predecessorLegs _ _ _ _ := HEq.rfl
  attaching _ := HEq.rfl
  cells _ := HEq.rfl
  comparisons _ := HEq.rfl

/-- The literal original inclusion composes every old-field preservation law. -/
theorem Preserves.trans {B D E : LowerSet P} {hBD : B ≤ D} {hDE : D ≤ E}
    {b : Prefix O M chi B} {d : Prefix O M chi D} {e : Prefix O M chi E}
    (h : Preserves O M chi hBD b d) (k : Preserves O M chi hDE d e) :
    Preserves O M chi (hBD.trans hDE) b e where
  order_restrict a a' := (h.order_restrict a a').trans
    (k.order_restrict ⟨a.1, hBD a.2⟩ ⟨a'.1, hBD a'.2⟩)
  initial a a' ha' haa' := by
    have haD : a.1 ∈ D := k.initial a a' (hBD ha') haa'
    have haaD := (k.order_restrict ⟨a.1, haD⟩ ⟨a'.1, hBD ha'⟩).2 haa'
    exact h.initial ⟨a.1, haD⟩ ⟨a'.1, hBD ha'⟩ ha' haaD
  vertices a := (h.vertices a).trans (k.vertices ⟨a.1, hBD a.2⟩)
  maps a a' haa' := (h.maps a a' haa').trans
    (k.maps ⟨a.1, hBD a.2⟩ ⟨a'.1, hBD a'.2⟩ ((h.order_restrict a a').1 haa'))
  predecessorPoints a := (h.predecessorPoints a).trans (k.predecessorPoints ⟨a.1, hBD a.2⟩)
  predecessorLegs a z hza hza' :=
    (h.predecessorLegs a z hza (h.strict O M chi hza)).trans
      (k.predecessorLegs ⟨a.1, hBD a.2⟩ ⟨z.1, hBD z.2⟩ (h.strict O M chi hza) hza')
  attaching a := (h.attaching a).trans (k.attaching ⟨a.1, hBD a.2⟩)
  cells a := (h.cells a).trans (k.cells ⟨a.1, hBD a.2⟩)
  comparisons a := (h.comparisons a).trans (k.comparisons ⟨a.1, hBD a.2⟩)

variable {J : Type w} [Preorder J] (S : J → LowerSet P) (hMono : Monotone S)

/-- Actual complete prefix histories, with every literal original preservation law. -/
structure History (j : J) where
  /-- The actual prefix at each preceding original index. -/
  state : ∀ i : J, i ≤ j → Prefix O M chi (S i)
  /-- The full original compatibility of all stored prefixes. -/
  preserves : ∀ (i k : J) (hik : i ≤ k) (hkj : k ≤ j),
    Preserves O M chi (hMono hik) (state i (hik.trans hkj)) (state k hkj)

/-- Restriction truncates the entire stored original history and all its fields. -/
def History.restrict {i j : J} (hij : i ≤ j)
    (H : History O M chi S hMono j) : History O M chi S hMono i where
  state k hki := H.state k (hki.trans hij)
  preserves k l hkl hli := H.preserves k l hkl (hli.trans hij)

/-- History restriction retains the actual whole identity. -/
theorem History.restrict_id (j : J) (H : History O M chi S hMono j) :
    H.restrict O M chi S hMono (le_refl j) = H := by cases H; rfl

/-- History restriction retains the actual whole composition. -/
theorem History.restrict_comp {i j k : J} (hij : i ≤ j) (hjk : j ≤ k)
    (H : History O M chi S hMono k) :
    (H.restrict O M chi S hMono hjk).restrict O M chi S hMono hij =
      H.restrict O M chi S hMono (hij.trans hjk) := by cases H; rfl

/-- Complete original histories form their actual inverse-system functor. -/
def historyFunctor : Jᵒᵖ ⥤ Type (max w t u v) where
  obj j := History O M chi S hMono j.unop
  map f := ↾fun H => H.restrict O M chi S hMono (leOfHom f.unop)
  map_id j := by ext H; exact History.restrict_id O M chi S hMono j.unop H
  map_comp f g := by
    ext H
    exact (History.restrict_comp O M chi S hMono (leOfHom g.unop) (leOfHom f.unop) H).symm

variable (j : J)
  (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
    historyFunctor O M chi S hMono).sections)

/-- A compatible prior section supplies its actual self-index original prefix. -/
def previousPrefix (i : Set.Iio j) : Prefix O M chi (S i.1) :=
  (x.val (op i)).state i.1 (le_refl i.1)

/-- Prior-section compatibility derives every old field equation between actual prefixes. -/
theorem previousPrefix_preserves (i k : Set.Iio j) (hik : i ≤ k) :
    Preserves O M chi (hMono hik) (previousPrefix O M chi S hMono j x i)
      (previousPrefix O M chi S hMono j x k) := by
  have hx : (x.val (op k)).restrict O M chi S hMono hik = x.val (op i) :=
    x.property (homOfLE hik : i ⟶ k).op
  have hState : (x.val (op k)).state i.1 hik = (x.val (op i)).state i.1 (le_refl i.1) :=
    congrArg (fun H : History O M chi S hMono i.1 => H.state i.1 (le_refl i.1)) hx
  have h := (x.val (op k)).preserves i.1 k.1 hik (le_refl k.1)
  rw [hState] at h
  exact h

end

end CategoryTheory.SmallObject.OriginalGoodification
