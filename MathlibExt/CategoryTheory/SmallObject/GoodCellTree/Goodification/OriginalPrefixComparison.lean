/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalPrefixData
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCellVertexLowerComparison
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OrderIsoLowerColimitTransport
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.CellTreeOrderReindex
public import Mathlib.CategoryTheory.EqToHom

/-!
# Original lower and predecessor comparisons of complete good prefixes

The actual chosen prefix colimits and original comparison cocones construct lower isomorphisms
on every original lower subset. Their forward maps are the universal descenders, and both cofan
leg equations and inclusion naturality are retained. Original predecessor comparisons use the
same vertex components and strict original labels; every leg, root, vertex square and literal
old-prefix transport is derived from the recorded colimit and preservation data.

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
  {B : LowerSet P} (r : Prefix O M chi B)
  (N : letI := r.ord
    letI : Preorder B := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)

/-- Actual lower-colimit universal properties give the comparison at every original lower set. -/
def Prefix.originalIso (D : LowerSet P) (hD : D ≤ B) :
    letI := r.ord
    letI : Preorder B := r.ord.toPreorder
    N.obj (OriginalLowerComparisonCocone.carrier (prefixLabels B r.ord r.below) D) ≅ M.obj D := by
  letI := r.ord
  letI : Preorder B := r.ord.toPreorder
  exact (N.isColimit (OriginalLowerComparisonCocone.carrier
    (prefixLabels B r.ord r.below) D)).coconePointUniqueUpToIso (r.lowerUP D hD)

/-- Every forward lower-comparison leg is the original component followed by its original leg. -/
theorem Prefix.originalIso_hom_fac (D : LowerSet P) (hD : D ≤ B)
    (p : letI := r.ord
      letI : Preorder B := r.ord.toPreorder
      OriginalLowerComparisonCocone.carrier (prefixLabels B r.ord r.below) D) :
    letI := r.ord
    letI : Preorder B := r.ord.toPreorder
    N.ι (OriginalLowerComparisonCocone.carrier (prefixLabels B r.ord r.below) D) p ≫
        (r.originalIso O M chi N D hD).hom =
      r.comparison.app p.1 ≫ M.ι D ⟨p.1.1, p.2⟩ := by
  let _ := r.ord
  let _ : Preorder B := r.ord.toPreorder
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (N.isColimit (OriginalLowerComparisonCocone.carrier (prefixLabels B r.ord r.below) D))
    (r.lowerUP D hD) p

/-- The inverse comparison recovers every actual chosen prefix-colimit leg. -/
theorem Prefix.originalIso_inv_fac (D : LowerSet P) (hD : D ≤ B)
    (p : letI := r.ord
      letI : Preorder B := r.ord.toPreorder
      OriginalLowerComparisonCocone.carrier (prefixLabels B r.ord r.below) D) :
    letI := r.ord
    letI : Preorder B := r.ord.toPreorder
    (r.comparison.app p.1 ≫ M.ι D ⟨p.1.1, p.2⟩) ≫
        (r.originalIso O M chi N D hD).inv =
      N.ι (OriginalLowerComparisonCocone.carrier (prefixLabels B r.ord r.below) D) p := by
  let _ := r.ord
  let _ : Preorder B := r.ord.toPreorder
  rw [← r.originalIso_hom_fac O M chi N D hD p,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The forward map is precisely the original comparison cocone's universal descender. -/
theorem Prefix.originalIso_hom_eq_desc (D : LowerSet P) (hD : D ≤ B) :
    letI := r.ord
    letI : Preorder B := r.ord.toPreorder
    (r.originalIso O M chi N D hD).hom =
      (N.isColimit (OriginalLowerComparisonCocone.carrier (prefixLabels B r.ord r.below) D)).desc
        (OriginalLowerComparisonCocone.cocone (prefixLabels B r.ord r.below)
          r.tree.diagram O.diagram r.comparison M D) := by
  let _ := r.ord
  let _ : Preorder B := r.ord.toPreorder
  apply (N.isColimit (OriginalLowerComparisonCocone.carrier
    (prefixLabels B r.ord r.below) D)).hom_ext
  intro p
  exact (r.originalIso_hom_fac O M chi N D hD p).trans
    ((N.isColimit (OriginalLowerComparisonCocone.carrier (prefixLabels B r.ord r.below) D)).fac
      (OriginalLowerComparisonCocone.cocone (prefixLabels B r.ord r.below)
        r.tree.diagram O.diagram r.comparison M D) p).symm

/-- Every original lower inclusion commutes with both chosen lower-colimit map functions. -/
theorem Prefix.originalIso_naturality (D E : LowerSet P)
    (hDE : D ≤ E) (hE : E ≤ B) :
    letI := r.ord
    letI : Preorder B := r.ord.toPreorder
    let f := prefixLabels B r.ord r.below
    let hPre : OriginalLowerComparisonCocone.carrier f D ≤
        OriginalLowerComparisonCocone.carrier f E := fun _ h => hDE h
    (r.originalIso O M chi N D (hDE.trans hE)).hom ≫ M.map hDE =
      N.map hPre ≫ (r.originalIso O M chi N E hE).hom := by
  let _ := r.ord
  let _ : Preorder B := r.ord.toPreorder
  let f := prefixLabels B r.ord r.below
  let hPre : OriginalLowerComparisonCocone.carrier f D ≤
      OriginalLowerComparisonCocone.carrier f E := fun _ h => hDE h
  apply (N.isColimit (OriginalLowerComparisonCocone.carrier f D)).hom_ext
  intro p
  calc
    N.ι (OriginalLowerComparisonCocone.carrier f D) p ≫
        ((r.originalIso O M chi N D (hDE.trans hE)).hom ≫ M.map hDE) =
      OriginalLowerComparisonCocone.leg f r.tree.diagram O.diagram r.comparison M D p ≫
        M.map hDE := by
      rw [← Category.assoc, r.originalIso_hom_fac O M chi N D (hDE.trans hE) p]
      rfl
    _ = OriginalLowerComparisonCocone.leg f r.tree.diagram O.diagram r.comparison M E
        ⟨p.1, hDE p.2⟩ :=
      OriginalLowerComparisonCocone.leg_map f r.tree.diagram O.diagram r.comparison M hDE p
    _ = N.ι (OriginalLowerComparisonCocone.carrier f D) p ≫
        (N.map hPre ≫ (r.originalIso O M chi N E hE).hom) := by
      rw [← Category.assoc, N.ι_map, r.originalIso_hom_fac O M chi N E hE]
      rfl

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P Q : Type w} [PartialOrder P] [PartialOrder Q]
  {C : Type u} [Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (G : CellTree s X (P := Q)) (O : CellTree s X (P := P))
  (f : Q →o P) (hf : StrictMono f) (beta : G.diagram ⟶ f.monotone.functor ⋙ O.diagram)

/-- The actual refined predecessor cofan maps to the original predecessor object. -/
def predecessorComparison (q : Q) : G.predecessorObj q ⟶ O.predecessorObj (f q) :=
  (G.predecessor q).isColimit.desc
    (OriginalCellVertexLowerComparison.cocone G O f beta (f q) (LowerSet.Iio q)
      (fun _p hp => hf hp))

/-- Every new predecessor leg uses the same vertex component and original strict label. -/
theorem predecessorComparison_fac (q : Q) (p : LowerSet.Iio q) :
    (G.predecessor q).cocone.ι.app p ≫ predecessorComparison G O f hf beta q =
      beta.app p.1 ≫ (O.predecessor (f q)).cocone.ι.app ⟨f p.1, hf p.2⟩ :=
  (G.predecessor q).isColimit.fac _ p

/-- The genuine predecessor UP and whole vertex naturality give the original predecessor square. -/
theorem predecessorComparison_square (q : Q) :
    predecessorComparison G O f hf beta q ≫ O.predecessorMap (f q) =
      G.predecessorMap q ≫ beta.app q := by
  apply (G.predecessor q).isColimit.hom_ext
  intro p
  rw [← Category.assoc, predecessorComparison_fac, Category.assoc,
    O.predecessorMap_fac, ← Category.assoc, G.predecessorMap_fac]
  exact (beta.naturality (homOfLE p.2.le)).symm

/-- The actual predecessor comparison keeps the arbitrary original root. -/
theorem predecessorComparison_root (q : Q) :
    (G.predecessorObj q).hom ≫ (predecessorComparison G O f hf beta q).right =
      (O.predecessorObj (f q)).hom := Under.w _

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section


variable {P : Type w} [pOrder : PartialOrder P]
  {C : Type u} [cCategory : Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- The literal prefix-label inclusion sends every new strict comparison to an original one. -/
theorem prefixLabels_strict {B : LowerSet P} (r : Prefix O M chi B) :
    @StrictMono B P r.ord.toPreorder pOrder.toPreorder (prefixLabels B r.ord r.below) := by
  let _ := r.ord
  let _ : Preorder B := r.ord.toPreorder
  intro a b hab
  have hab0 := r.below a b hab.le
  have hne : a.1 ≠ b.1 := fun he => (ne_of_lt hab) (Subtype.ext he)
  exact lt_of_le_of_ne hab0 hne

/-- The actual prefix predecessor maps to the predecessor at its same original label. -/
def prefixPredecessorComparison {B : LowerSet P} (r : Prefix O M chi B) (a : B) :
    (letI := r.ord; r.tree.predecessorObj a) ⟶ O.predecessorObj a.1 := by
  let _ := r.ord
  let _ : Preorder B := r.ord.toPreorder
  exact @predecessorComparison P B pOrder r.ord C cCategory A s X r.tree O
    (prefixLabels B r.ord r.below) (prefixLabels_strict O M chi r) r.comparison a

/-- Every complete prefix predecessor leg retains its original comparison and original cofan leg. -/
theorem prefixPredecessorComparison_fac {B : LowerSet P} (r : Prefix O M chi B)
    (a : B) (z : letI := r.ord
      letI : Preorder B := r.ord.toPreorder
      LowerSet.Iio a) :
    letI := r.ord
    letI : Preorder B := r.ord.toPreorder
    (r.tree.predecessor a).cocone.ι.app z ≫ prefixPredecessorComparison O M chi r a =
      r.comparison.app z.1 ≫ (O.predecessor a.1).cocone.ι.app
        ⟨z.1.1, prefixLabels_strict O M chi r z.2⟩ :=
  by
  let _ := r.ord
  let _ : Preorder B := r.ord.toPreorder
  exact @predecessorComparison_fac P B pOrder r.ord C cCategory A s X r.tree O
    (prefixLabels B r.ord r.below) (prefixLabels_strict O M chi r) r.comparison a z

/-- The canonical prefix predecessor comparison commutes with the original vertex map. -/
theorem prefixPredecessorComparison_square {B : LowerSet P} (r : Prefix O M chi B) (a : B) :
    prefixPredecessorComparison O M chi r a ≫ O.predecessorMap a.1 =
      (letI := r.ord
       letI : Preorder B := r.ord.toPreorder
       r.tree.predecessorMap a ≫ r.comparison.app a) := by
  let _ := r.ord
  let _ : Preorder B := r.ord.toPreorder
  exact predecessorComparison_square r.tree O (prefixLabels B r.ord r.below)
    (prefixLabels_strict O M chi r) r.comparison a

/-- The actual prefix predecessor comparison retains its original arbitrary root equation. -/
theorem prefixPredecessorComparison_root {B : LowerSet P} (r : Prefix O M chi B) (a : B) :
    (letI := r.ord; r.tree.predecessorObj a).hom ≫
      (prefixPredecessorComparison O M chi r a).right = (O.predecessorObj a.1).hom :=
  Under.w _

/-- The source-square invariant uses the actual prefix predecessor comparison. -/
def PrefixAttachingSquares {B : LowerSet P} (r : Prefix O M chi B) : Prop :=
  ∀ a : B, (letI := r.ord
    r.tree.attaching a ≫ (prefixPredecessorComparison O M chi r a).right) ≍ O.attaching a.1


end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section


variable {P : Type w} [pOrder : PartialOrder P]
  {C : Type u} [cCategory : Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- Complete preservation retains the predecessor comparison on the same original label. -/
theorem predecessorComparison_of_preserves {B D : LowerSet P} {hBD : B ≤ D}
    (b : Prefix O M chi B) (d : Prefix O M chi D) (h : Preserves O M chi hBD b d) (a : B) :
    prefixPredecessorComparison O M chi b a ≍
      prefixPredecessorComparison O M chi d ⟨a.1, hBD a.2⟩ := by
  have hp := h.predecessorPoints a
  let e := eqToIso hp
  have hEq : prefixPredecessorComparison O M chi b a =
      e.hom ≫ prefixPredecessorComparison O M chi d ⟨a.1, hBD a.2⟩ := by
    let _ := b.ord
    let _ : Preorder B := b.ord.toPreorder
    apply (b.tree.predecessor a).isColimit.hom_ext
    intro z
    have hz := h.strict O M chi z.2
    have hLeg := h.predecessorLegs a z.1 z.2 hz
    have hBeta := h.comparisons z.1
    have hv := h.vertices z.1
    let ev := eqToIso hv
    let zd := (⟨z.1.1, hBD z.1.2⟩ : D)
    let ad := (⟨a.1, hBD a.2⟩ : D)
    have hLegEq :
        (b.tree.predecessor a).cocone.ι.app z ≫ e.hom =
          ev.hom ≫ (letI := d.ord
            letI : Preorder D := d.ord.toPreorder
            (d.tree.predecessor ad).cocone.ι.app ⟨zd, hz⟩) := by
      exact eq_of_heq ((comp_eqToHom_heq _ hp).trans
        (hLeg.trans (eqToHom_comp_heq _ hv).symm))
    have hBetaEq : b.comparison.app z.1 = ev.hom ≫
        (letI := d.ord
         letI : Preorder D := d.ord.toPreorder
         d.comparison.app zd) := by
      exact eq_of_heq (hBeta.trans (eqToHom_comp_heq _ hv).symm)
    have hFacB := prefixPredecessorComparison_fac O M chi b a z
    have hFacD := prefixPredecessorComparison_fac O M chi d ad
      (letI := d.ord
       letI : Preorder D := d.ord.toPreorder
       (⟨zd, hz⟩ : LowerSet.Iio ad))
    calc
      (b.tree.predecessor a).cocone.ι.app z ≫ prefixPredecessorComparison O M chi b a =
        b.comparison.app z.1 ≫ (O.predecessor a.1).cocone.ι.app
          ⟨z.1.1, prefixLabels_strict O M chi b z.2⟩ := hFacB
      _ = ev.hom ≫
          ((letI := d.ord
            letI : Preorder D := d.ord.toPreorder
            d.comparison.app zd) ≫ (O.predecessor a.1).cocone.ι.app
            ⟨z.1.1, prefixLabels_strict O M chi b z.2⟩) :=
          (congrArg (fun k => k ≫ (O.predecessor a.1).cocone.ι.app
            ⟨z.1.1, prefixLabels_strict O M chi b z.2⟩) hBetaEq).trans (Category.assoc _ _ _)
      _ = ev.hom ≫
          ((letI := d.ord
            letI : Preorder D := d.ord.toPreorder
            (d.tree.predecessor ad).cocone.ι.app ⟨zd, hz⟩) ≫
              prefixPredecessorComparison O M chi d ad) := congrArg (fun k => ev.hom ≫ k) hFacD.symm
      _ = (b.tree.predecessor a).cocone.ι.app z ≫
          (e.hom ≫ prefixPredecessorComparison O M chi d ad) :=
        ((Category.assoc _ _ _).symm).trans
          ((congrArg (fun k => k ≫ prefixPredecessorComparison O M chi d ad) hLegEq.symm).trans
            (Category.assoc _ _ _))
  exact (heq_of_eq hEq).trans (eqToHom_comp_heq _ hp)

/-- The preserved predecessor map has its literal source-point transport and original target. -/
theorem predecessorComparison_transport {B D : LowerSet P} {hBD : B ≤ D}
    (b : Prefix O M chi B) (d : Prefix O M chi D) (h : Preserves O M chi hBD b d) (a : B) :
    prefixPredecessorComparison O M chi b a =
      eqToHom (h.predecessorPoints a) ≫
        prefixPredecessorComparison O M chi d ⟨a.1, hBD a.2⟩ := by
  exact eq_of_heq ((predecessorComparison_of_preserves O M chi b d h a).trans
    (eqToHom_comp_heq (prefixPredecessorComparison O M chi d ⟨a.1, hBD a.2⟩)
      (h.predecessorPoints a)).symm)

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open CellTreeOrderReindex OrderIsoLowerColimitTransport

variable {P Q R : Type w} [PartialOrder P] [PartialOrder Q] [PartialOrder R]
  {C : Type u} [Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (G : CellTree s X (P := Q)) (O : CellTree s X (P := P))
  (f : Q →o P) (hf : StrictMono f) (beta : G.diagram ⟶ f.monotone.functor ⋙ O.diagram)
  (e : R ≃o Q)

/-- Literal label order reindexing retains the actual whole predecessor comparison map. -/
theorem predecessorComparison_orderTransport (q : R) :
    predecessorComparison (CellTreeOrderReindex.tree e G) O
      (OrderIsoLowerColimitTransport.labels e f) (hf.comp e.strictMono)
      (OrderIsoLowerColimitTransport.comparison e f G.diagram O.diagram beta) q =
      predecessorComparison G O f hf beta (e q) := by
  apply (G.predecessor (e q)).isColimit.hom_ext
  intro z
  obtain ⟨z', rfl⟩ := (CellTreeOrderReindex.predecessorOrderIso e q).surjective z
  have h := predecessorComparison_fac (CellTreeOrderReindex.tree e G) O
    (OrderIsoLowerColimitTransport.labels e f) (hf.comp e.strictMono)
    (OrderIsoLowerColimitTransport.comparison e f G.diagram O.diagram beta) q z'
  exact h.trans (predecessorComparison_fac G O f hf beta (e q)
    ((CellTreeOrderReindex.predecessorOrderIso e q) z')).symm

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section


variable {P : Type w} [pOrder : PartialOrder P]
  {C : Type u} [cCategory : Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- Actual prefix-field equalities retain the full original attaching comparison expression. -/
theorem prefix_attaching_projection {B : LowerSet P} (d : Prefix O M chi B)
    (ord : PartialOrder B) (T : letI := ord; CellTree s X (P := B))
    (f : @OrderHom B P ord.toPreorder pOrder.toPreorder)
    (hs : @StrictMono B P ord.toPreorder pOrder.toPreorder f)
    (beta : letI := ord
      letI : Preorder B := ord.toPreorder
      T.diagram ⟶ f.monotone.functor ⋙ O.diagram)
    (ho : d.ord = ord) (hT : d.tree ≍ T)
    (hf : prefixLabels B d.ord d.below ≍ f) (hb : d.comparison ≍ beta) (a : B) :
    (letI := d.ord
     d.tree.attaching a ≫ (prefixPredecessorComparison O M chi d a).right) ≍
    (letI := ord
     letI : Preorder B := ord.toPreorder
     T.attaching a ≫ (predecessorComparison T O f hs beta a).right) := by
  cases ho
  cases hT
  cases hf
  cases hb
  exact HEq.rfl

/-- All old attaching squares propagate through the full original preservation fields. -/
theorem attachingSquare_of_preserves {B D : LowerSet P} {hBD : B ≤ D}
    (b : Prefix O M chi B) (d : Prefix O M chi D) (h : Preserves O M chi hBD b d) (a : B)
    (ha : (letI := b.ord
      b.tree.attaching a ≫ (prefixPredecessorComparison O M chi b a).right) ≍ O.attaching a.1) :
    (letI := d.ord
     d.tree.attaching ⟨a.1, hBD a.2⟩ ≫
       (prefixPredecessorComparison O M chi d ⟨a.1, hBD a.2⟩).right) ≍ O.attaching a.1 := by
  have hp := h.predecessorPoints a
  have hPred := predecessorComparison_of_preserves O M chi b d h a
  have hRight : (prefixPredecessorComparison O M chi b a).right ≍
      (prefixPredecessorComparison O M chi d ⟨a.1, hBD a.2⟩).right := by
    have hr {U V U' V' : Under X} {f : U ⟶ V} {g : U' ⟶ V'}
        (hU : U = U') (hV : V = V') (hfg : f ≍ g) : f.right ≍ g.right := by
      cases hU
      cases hV
      cases hfg
      exact HEq.rfl
    exact hr hp rfl hPred
  have hs := congrArg (fun i => (s i).left) ((b.labels a).trans (d.labels ⟨a.1, hBD a.2⟩).symm)
  exact (heq_comp hs (congrArg Under.right hp) (by rfl) (h.attaching a) hRight).symm.trans ha

end

end CategoryTheory.SmallObject.OriginalGoodification
