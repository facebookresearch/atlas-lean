/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalPrefixComparison
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.RestrictedCellExtensionColimit
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCellExtensionComparison
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.CellTreeLabelAdjoin
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.CellTreeLabelTransport
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCellWellOrderEnumeration
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.ActualCoconeColimitTransport
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CellTreeIncrement

/-!
# Original predecessor-local successors with every original lower universal property

The actual predecessor comparison lifts the original attaching map. Compact capture takes place
inside its original strict predecessors. The original remainder pushout and the old lower
comparison construct the full original lower universal property both with and without the newborn.
The literal original after-prefix retains its original labels, root and complete comparison.

## Source and scope

This formalizes the one-cell successor step in Jacob Lurie's *Higher Topos Theory*,
Lemma A.1.5.7, in the author PDF dated April 9, 2017 (2017-04-09): printed pages
801–802 (PDF pages 819–820). Starting with a good original BEFORE prefix and
its chosen lower colimits, it constructs one AFTER prefix and proves every
original lower comparison universal property, both with and without the newborn.
The source proof is expressed through abstract cell-tree and chosen-colimit data.
The transfinite history and complete cell-tree goodification are separate
constructions outside this module's successor-only scope.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject Opposite
open CategoryTheory.SmallObject.GoodCellExtensionOrder
open CategoryTheory.SmallObject.GoodCellExtensionDiagram
open CategoryTheory.SmallObject.GoodCellExtensionTree
open CategoryTheory.SmallObject.GoodCellExtensionColimits
open CategoryTheory.SmallObject.LowerSetColimits
open CategoryTheory.SmallObject.OriginalPredecessorCellCapture
open CategoryTheory.SmallObject.OriginalGoodification.RestrictedCellExtension

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)

theorem originalPredBefore : LowerSet.Iio (labels.symm gamma) ≤ before gamma := by
  intro p hp
  change labels p < gamma
  simpa only [Equiv.apply_symm_apply] using toWellOrderExtension_strictMono hp

/-- The actual predecessor lower descender is the composite of the two original colimit isos. -/
theorem predecessorLift_comparison :
    letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    let f := prefixLabels (before gamma) r.ord r.below
    let t := labels.symm gamma
    let B := OriginalLowerComparisonCocone.carrier f (LowerSet.Iio t)
    lowerMap r.tree N O f r.comparison t B (fun _ h => h) =
      (r.originalIso O M chi N (LowerSet.Iio t) (originalPredBefore gamma)).hom ≫
        (O.predecessorIso M t).hom := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let f := prefixLabels (before gamma) r.ord r.below
  let t := labels.symm gamma
  let B := OriginalLowerComparisonCocone.carrier f (LowerSet.Iio t)
  apply (N.isColimit B).hom_ext
  intro p
  exact (lowerMap_fac r.tree N O f r.comparison t B (fun _ h => h) p).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (O.predecessorIso M t).hom)
        (r.originalIso_hom_fac O M chi N (LowerSet.Iio t) (originalPredBefore gamma) p)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => r.comparison.app p.1 ≫ k)
            (O.ι_predecessorIso_hom M t ⟨p.1.1, p.2⟩))))).symm

/-- The genuine predecessor comparison lifts the actual original cell attaching map. -/
def liftedOriginalAttaching :
    letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    let t := labels.symm gamma
    (s (O.label t)).left ⟶
      (N.obj (OriginalLowerComparisonCocone.carrier
        (prefixLabels (before gamma) r.ord r.below) (LowerSet.Iio t))).right := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let t := labels.symm gamma
  exact O.attaching t ≫ (O.predecessorIso M t).inv.right ≫
    (r.originalIso O M chi N (LowerSet.Iio t) (originalPredBefore gamma)).inv.right

theorem liftedOriginalAttaching_factor :
    letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    let f := prefixLabels (before gamma) r.ord r.below
    let t := labels.symm gamma
    let B := OriginalLowerComparisonCocone.carrier f (LowerSet.Iio t)
    liftedOriginalAttaching O M chi gamma r N ≫
      (lowerMap r.tree N O f r.comparison t B (fun _ h => h)).right = O.attaching t := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let t := labels.symm gamma
  let e := r.originalIso O M chi N (LowerSet.Iio t) (originalPredBefore gamma)
  dsimp only
  rw [predecessorLift_comparison O M chi gamma r N]
  unfold liftedOriginalAttaching
  dsimp only
  rw [Under.comp_right]
  change (O.attaching t ≫ ((O.predecessorIso M t).inv.right ≫ e.inv.right)) ≫
    (e.hom.right ≫ (O.predecessorIso M t).hom.right) = _
  rw [Category.assoc, Category.assoc, ← Category.assoc e.inv.right, ← Under.comp_right,
    e.inv_hom_id, Under.id_right, Category.id_comp, ← Under.comp_right,
    Iso.inv_hom_id, Under.id_right, Category.comp_id]

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification.OriginalExtension

noncomputable section

open OriginalCellVertexLowerComparison OriginalCapturedCellVertexMap

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {Q P : Type w} [PartialOrder Q] [PartialOrder P]
  {A : Type t} {s : A → Arrow C} {X : C}
  (G : CellTree s X (P := Q)) (L : LowerSetColimitData G.diagram)
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram) (f : Q →o P)
  (beta : G.diagram ⟶ f.monotone.functor ⋙ O.diagram)
  (t : P) (B : LowerSet Q) (hPred : ∀ q : Q, q ∈ B → f q < t)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  [IsCardinalPresentable (s (O.label t)).left chi] (good : G.IsGood chi)
  (g : (s (O.label t)).left ⟶ (L.obj B).right)
  (hOriginal : g ≫ (lowerMap G L O f beta t B hPred).right = O.attaching t)
  (D : LowerSet P) (ht : t ∈ D)

/-- The old part of the literal original lower set and its internally captured local support. -/
abbrev originalOldLower (f : Q →o P) (D : LowerSet P) : LowerSet Q :=
  OriginalLowerComparisonCocone.carrier f D

include hPred ht in
omit [HasPushouts C] in
theorem capturedSupport_below :
    (capture G L O t B chi good g).support ≤ originalOldLower f D := by
  intro q hq
  exact D.lower' (hPred q ((capture G L O t B chi good g).below hq)).le ht

omit [HasPushouts C] in
theorem extendedLabel_mem
    (p : letI := extensionOrder (capture G L O t B chi good g).support
      extendedLower (capture G L O t B chi good g).support (originalOldLower f D)
        (capturedSupport_below G L O f t B hPred chi good g D ht)) :
    letI := extensionOrder (capture G L O t B chi good g).support
    OriginalLocalizedCellExtension.labels f t p.1 ∈ D := by
  rcases p with ⟨⟨p⟩, hp⟩
  cases p with
  | some p => exact hp
  | none => exact ht

/-- The actual original actualExtendedCocone construction retains its original objects and maps. -/
def actualExtendedCocone :
    letI := extensionOrder (capture G L O t B chi good g).support
    Cocone (restriction
      (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram
      (extendedLower (capture G L O t B chi good g).support (originalOldLower f D)
        (capturedSupport_below G L O f t B hPred chi good g D ht))) := by
  letI := extensionOrder (capture G L O t B chi good g).support
  let b := OriginalCellExtensionComparison.comparison G L O f beta t B hPred chi good g hOriginal
  let j := OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g
  let D' := extendedLower (capture G L O t B chi good g).support (originalOldLower f D)
    (capturedSupport_below G L O f t B hPred chi good g D ht)
  let u : D' ⥤ OriginalLowerComparisonCocone.carrier j D := {
    obj p := ⟨p.1, extendedLabel_mem G L O f t B hPred chi good g D ht p⟩
    map h := homOfLE (leOfHom h) }
  exact (OriginalLowerComparisonCocone.cocone j
    (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram
    O.diagram b M D).whisker u

/-- The actual new cell leg is the original cell target followed by the same original lower leg. -/
theorem actualExtendedCocone_cell :
    letI := extensionOrder (capture G L O t B chi good g).support
    newCell G L (capture G L O t B chi good g).support (O.label t)
        (capture G L O t B chi good g).attaching ≫
      ((actualExtendedCocone G L O M f beta t B hPred chi good g hOriginal D ht).ι.app
        ⟨Index.new, by trivial⟩).right = O.cell t ≫ (M.ι D ⟨t, ht⟩).right := by
  let _ := extensionOrder (capture G L O t B chi good g).support
  have hLeg : ((actualExtendedCocone G L O M f beta t B hPred chi good g hOriginal D ht).ι.app
      ⟨Index.new, by trivial⟩).right =
      (newVertexMap G L O f beta t B hPred chi good g hOriginal).right ≫
        (M.ι D ⟨t, ht⟩).right := rfl
  exact (congrArg (fun k =>
      newCell G L (capture G L O t B chi good g).support (O.label t)
        (capture G L O t B chi good g).attaching ≫ k) hLeg).trans
    (((Category.assoc _ _ _).symm).trans
      (congrArg (fun k => k ≫ (M.ι D ⟨t, ht⟩).right)
        (newVertexMap_cell G L O f beta t B hPred chi good g hOriginal)))


/-- The old original lower comparison iso and the genuine original remainder square derive the new
UP. -/
def actualExtendedCoconeIsColimit
    (E : LowerSet P) (hED : E ≤ D)
    (hPredE : LowerSet.Iio t ≤ E)
    (hOldE : ∀ q : Q, f q ∈ D ↔ f q ∈ E)
    (e : L.obj (originalOldLower f D) ≅ M.obj E)
    (he : ∀ p : originalOldLower f D,
      L.ι (originalOldLower f D) p ≫ e.hom = beta.app p.1 ≫ M.ι E ⟨f p.1, (hOldE p.1).1 p.2⟩)
    (sq : IsPushout
      (O.attaching t ≫ (O.predecessorIso M t).inv.right ≫ (M.map hPredE).right)
      (s (O.label t)).hom (M.map hED).right
      (O.cell t ≫ (M.ι D ⟨t, ht⟩).right)) :
    letI := extensionOrder (capture G L O t B chi good g).support
    IsColimit (actualExtendedCocone G L O M f beta t B hPred chi good g hOriginal D ht) := by
  letI := extensionOrder (capture G L O t B chi good g).support
  let S := (capture G L O t B chi good g).support
  let E' := originalOldLower f D
  let hSE : S ≤ E' := capturedSupport_below G L O f t B hPred chi good g D ht
  let a := (capture G L O t B chi good g).attaching
  let k := e.hom ≫ M.map hED
  have hPredMap :
      L.map hSE ≫ e.hom = capturedPredMap G L O f beta t B hPred chi good g ≫
        (O.predecessorIso M t).inv ≫ M.map hPredE := by
    apply (L.isColimit S).hom_ext
    intro p
    have hx := he ⟨p.1, hSE p.2⟩
    have hp : f p.1 < t := hPred p.1 ((capture G L O t B chi good g).below p.2)
    have hCancel : (O.predecessor t).cocone.ι.app ⟨f p.1, hp⟩ ≫
        (O.predecessorIso M t).inv = M.ι (LowerSet.Iio t) ⟨f p.1, hp⟩ := by
      exact (congrArg (fun k => k ≫ (O.predecessorIso M t).inv)
        (O.ι_predecessorIso_hom M t ⟨f p.1, hp⟩).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => M.ι (LowerSet.Iio t) ⟨f p.1, hp⟩ ≫ k)
            (O.predecessorIso M t).hom_inv_id).trans (Category.comp_id _)))
    calc
      L.ι S p ≫ (L.map hSE ≫ e.hom) =
        L.ι E' ⟨p.1, hSE p.2⟩ ≫ e.hom := by rw [← Category.assoc, L.ι_map]
      _ = beta.app p.1 ≫ M.ι E ⟨f p.1, (hOldE p.1).1 (hSE p.2)⟩ := hx
      _ = L.ι S p ≫
          (capturedPredMap G L O f beta t B hPred chi good g ≫
            (O.predecessorIso M t).inv ≫ M.map hPredE) := by
        change _ = L.ι S p ≫
          (lowerMap G L O f beta t S
            (fun q hq => hPred q ((capture G L O t B chi good g).below hq)) ≫
            (O.predecessorIso M t).inv ≫ M.map hPredE)
        have hMap := lowerMap_fac G L O f beta t S
          (fun q hq => hPred q ((capture G L O t B chi good g).below hq)) p
        have hRight : L.ι S p ≫
            (lowerMap G L O f beta t S
              (fun q hq => hPred q ((capture G L O t B chi good g).below hq)) ≫
              (O.predecessorIso M t).inv ≫ M.map hPredE) =
            beta.app p.1 ≫ M.ι E ⟨f p.1, hPredE hp⟩ := by
          calc
            _ = (L.ι S p ≫ lowerMap G L O f beta t S
                (fun q hq => hPred q ((capture G L O t B chi good g).below hq))) ≫
                ((O.predecessorIso M t).inv ≫ M.map hPredE) := (Category.assoc _ _ _).symm
            _ = (beta.app p.1 ≫ (O.predecessor t).cocone.ι.app ⟨f p.1, hp⟩) ≫
                ((O.predecessorIso M t).inv ≫ M.map hPredE) :=
              congrArg (fun k => k ≫ ((O.predecessorIso M t).inv ≫ M.map hPredE)) hMap
            _ = beta.app p.1 ≫
                (((O.predecessor t).cocone.ι.app ⟨f p.1, hp⟩ ≫
                  (O.predecessorIso M t).inv) ≫ M.map hPredE) := by
                    rw [Category.assoc, Category.assoc]
            _ = beta.app p.1 ≫ (M.ι (LowerSet.Iio t) ⟨f p.1, hp⟩ ≫ M.map hPredE) :=
              congrArg (fun k => beta.app p.1 ≫ (k ≫ M.map hPredE)) hCancel
            _ = beta.app p.1 ≫ M.ι E ⟨f p.1, hPredE hp⟩ :=
              congrArg (fun k => beta.app p.1 ≫ k) (M.ι_map hPredE ⟨f p.1, hp⟩)
        exact hRight.symm
  have hAtt : a ≫ (L.map hSE).right ≫ e.hom.right =
      O.attaching t ≫ (O.predecessorIso M t).inv.right ≫ (M.map hPredE).right := by
    have hp := congrArg Under.Hom.right hPredMap
    exact (congrArg (fun k => a ≫ k) hp).trans
      (((Category.assoc _ _ _).symm).trans
        (congrArg (fun k => k ≫
          ((O.predecessorIso M t).inv.right ≫ (M.map hPredE).right))
          (capturedPredMap_attaching G L O f beta t B hPred chi good g hOriginal)))
  have hSq : IsPushout (a ≫ (L.map hSE).right) (s (O.label t)).hom k.right
      (O.cell t ≫ (M.ι D ⟨t, ht⟩).right) := by
    refine sq.of_iso (Iso.refl _) ((Under.forget X).mapIso e.symm)
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · change (O.attaching t ≫ (O.predecessorIso M t).inv.right ≫ (M.map hPredE).right) ≫
        e.inv.right = 𝟙 _ ≫ (a ≫ (L.map hSE).right)
      have hId : e.hom.right ≫ e.inv.right = 𝟙 _ := by
        rw [← Under.comp_right, e.hom_inv_id, Under.id_right]
      rw [Category.id_comp, ← hAtt, Category.assoc, Category.assoc, hId, Category.comp_id]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    · change (M.map hED).right ≫ 𝟙 _ = e.inv.right ≫ k.right
      rw [Category.comp_id]
      change (M.map hED).right = e.inv.right ≫ (e.hom.right ≫ (M.map hED).right)
      rw [← Category.assoc, ← Under.comp_right, e.inv_hom_id, Under.id_right, Category.id_comp]
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  refine restrictedExtensionIsColimit G L S E' hSE (O.label t) a
    (actualExtendedCocone G L O M f beta t B hPred chi good g hOriginal D ht)
    k (O.cell t ≫ (M.ι D ⟨t, ht⟩).right) hSq ?_ ?_
  · intro p
    have hLeg : (actualExtendedCocone G L O M f beta t B hPred chi good g hOriginal D ht).ι.app
        ⟨Index.old p.1, p.2⟩ = beta.app p.1 ≫ M.ι D ⟨f p.1, p.2⟩ := rfl
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ M.map hED) (he p)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => beta.app p.1 ≫ k)
            (M.ι_map hED ⟨f p.1, (hOldE p.1).1 p.2⟩))))).trans hLeg.symm
  · exact actualExtendedCocone_cell G L O M f beta t B hPred chi good g hOriginal D ht


/-- When the original lower set omits the newborn, its entire carrier is the old original
carrier. -/
def oldOnlyCarrierIso (ht0 : t ∉ D) :
    letI := extensionOrder (capture G L O t B chi good g).support
    OriginalLowerComparisonCocone.carrier
      (OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g) D ≃o
      originalOldLower f D := by
  letI := extensionOrder (capture G L O t B chi good g).support
  refine {
    toFun := ?_
    invFun := fun q => ⟨Index.old q.1, q.2⟩
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · rintro ⟨⟨q⟩, hq⟩
    cases q with
    | some q => exact ⟨q, hq⟩
    | none => exact False.elim (ht0 hq)
  · rintro ⟨⟨q⟩, hq⟩
    cases q with
    | some q => rfl
    | none => exact False.elim (ht0 hq)
  · intro q
    rfl
  · rintro ⟨⟨q⟩, hq⟩ ⟨⟨r⟩, hr⟩
    cases q with
    | none => exact False.elim (ht0 hq)
    | some q =>
      cases r with
      | none => exact False.elim (ht0 hr)
      | some r => rfl

/-- The actual original oldOnlyOriginalIsColimit construction retains its original objects and
maps. -/
def oldOnlyOriginalIsColimit (ht0 : t ∉ D)
    (hOld : IsColimit (OriginalLowerComparisonCocone.cocone f G.diagram O.diagram beta M D)) :
    letI := extensionOrder (capture G L O t B chi good g).support
    IsColimit (OriginalLowerComparisonCocone.cocone
      (OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g)
      (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram
      O.diagram
          (OriginalCellExtensionComparison.comparison G L O f beta t B hPred chi good g hOriginal)
      M D) := by
  letI := extensionOrder (capture G L O t B chi good g).support
  let e := oldOnlyCarrierIso G L O f t B hPred chi good g D ht0
  let z := OriginalLowerComparisonCocone.cocone
    (OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g)
    (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram
    O.diagram
        (OriginalCellExtensionComparison.comparison G L O f beta t B hPred chi good g hOriginal)
    M D
  apply IsColimit.ofWhiskerEquivalence e.symm.equivalence
  change IsColimit (z.whisker e.symm.equivalence.functor)
  let zOld := OriginalLowerComparisonCocone.cocone f G.diagram O.diagram beta M D
  have hDiagram : e.symm.equivalence.functor ⋙
      restriction (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram
        (OriginalLowerComparisonCocone.carrier
          (OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g) D) =
      restriction G.diagram (OriginalLowerComparisonCocone.carrier f D) := rfl
  exact ActualCoconeColimitTransport.isColimit hDiagram
    (z.whisker e.symm.equivalence.functor) zOld rfl (fun _ => HEq.rfl) hOld

/-- With the newborn present, the actual restricted support carrier is the full original
preimage. -/
def actualCarrierIso :
    letI := extensionOrder (capture G L O t B chi good g).support
    OriginalLowerComparisonCocone.carrier
      (OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g) D ≃o
      extendedLower (capture G L O t B chi good g).support (originalOldLower f D)
        (capturedSupport_below G L O f t B hPred chi good g D ht) := by
  letI := extensionOrder (capture G L O t B chi good g).support
  let j := OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g
  let S := (capture G L O t B chi good g).support
  let E' := extendedLower S (originalOldLower f D)
    (capturedSupport_below G L O f t B hPred chi good g D ht)
  have hMem (p : Index Q) : p ∈ OriginalLowerComparisonCocone.carrier j D → p ∈ E' := by
    rcases p with ⟨p⟩
    cases p with
    | some p => exact id
    | none => exact fun _ => True.intro
  exact {
    toFun p := ⟨p.1, hMem p.1 p.2⟩
    invFun p := ⟨p.1, extendedLabel_mem G L O f t B hPred chi good g D ht p⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl }

/-- The original newborn UP keeps the whole original comparison cocone on its actual preimage. -/
def withNewOriginalIsColimit
    (E : LowerSet P) (hED : E ≤ D)
    (hPredE : LowerSet.Iio t ≤ E)
    (hOldE : ∀ q : Q, f q ∈ D ↔ f q ∈ E)
    (e : L.obj (originalOldLower f D) ≅ M.obj E)
    (he : ∀ p : originalOldLower f D,
      L.ι (originalOldLower f D) p ≫ e.hom = beta.app p.1 ≫ M.ι E ⟨f p.1, (hOldE p.1).1 p.2⟩)
    (sq : IsPushout
      (O.attaching t ≫ (O.predecessorIso M t).inv.right ≫ (M.map hPredE).right)
      (s (O.label t)).hom (M.map hED).right
      (O.cell t ≫ (M.ι D ⟨t, ht⟩).right)) :
    letI := extensionOrder (capture G L O t B chi good g).support
    IsColimit (OriginalLowerComparisonCocone.cocone
      (OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g)
      (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram
      O.diagram
          (OriginalCellExtensionComparison.comparison G L O f beta t B hPred chi good g hOriginal)
      M D) := by
  letI := extensionOrder (capture G L O t B chi good g).support
  let iso := actualCarrierIso G L O f t B hPred chi good g D ht
  let z := OriginalLowerComparisonCocone.cocone
    (OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g)
    (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram
    O.diagram
        (OriginalCellExtensionComparison.comparison G L O f beta t B hPred chi good g hOriginal)
    M D
  apply IsColimit.ofWhiskerEquivalence iso.symm.equivalence
  let za := actualExtendedCocone G L O M f beta t B hPred chi good g hOriginal D ht
  have hDiagram : iso.symm.equivalence.functor ⋙
      restriction (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram
        (OriginalLowerComparisonCocone.carrier
          (OriginalCellExtensionComparison.labelOrderHom G L O f t B hPred chi good g) D) =
      restriction (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram
        (extendedLower (capture G L O t B chi good g).support (originalOldLower f D)
          (capturedSupport_below G L O f t B hPred chi good g D ht)) := rfl
  exact ActualCoconeColimitTransport.isColimit hDiagram
    (z.whisker iso.symm.equivalence.functor) za rfl (fun _ => HEq.rfl)
    (actualExtendedCoconeIsColimit G L O M f beta t B hPred chi good g hOriginal D ht
      E hED hPredE hOldE e he sq)

end

end CategoryTheory.SmallObject.OriginalGoodification.OriginalExtension

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open CategoryTheory.SmallObject.GoodCellExtensionDiagram

variable {C : Type u} [Category.{v} C] [HasPushouts C] {P : Type w} [PartialOrder P]
  {A : Type t} {s : A → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)

section OriginalLowerPieces

open OriginalCellWellOrderEnumeration

variable [WellFoundedLT P]

theorem originalRemainder_pred (D : LowerSet P)
    (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
    (ht : labels.symm gamma ∈ D) :
    LowerSet.Iio (labels.symm gamma) ≤ D ⊓ before gamma := by
  intro p hp
  refine ⟨D.lower' hp.le ht, ?_⟩
  change labels p < gamma
  simpa only [Equiv.apply_symm_apply] using toWellOrderExtension_strictMono hp

theorem originalRemainder_notMem (D : LowerSet P)
    (gamma : OriginalCellWellOrderEnumeration.Index (P := P)) :
    labels.symm gamma ∉ D ⊓ before gamma := by
  rintro ⟨_, h⟩
  change labels (labels.symm gamma) < gamma at h
  rw [Equiv.apply_symm_apply] at h
  exact (lt_irrefl gamma) h

theorem originalRemainder_union (D : LowerSet P)
    (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
    (hD : D ≤ after gamma) (ht : labels.symm gamma ∈ D) :
    (D ⊓ before gamma) ⊔ LowerSet.Iic (labels.symm gamma) = D := by
  apply le_antisymm
  · exact sup_le inf_le_left (fun _ hp => D.lower' hp ht)
  · intro p hp
    rcases (mem_after_iff gamma p).1 (hD hp) with hb | he
    · exact Or.inl ⟨hp, hb⟩
    · exact Or.inr he.le

-- The original cell and the original lower-union UP produce the real square at every such D.
theorem originalRemainderIsPushout (D : LowerSet P)
    (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
    (hD : D ≤ after gamma) (ht : labels.symm gamma ∈ D) :
    let E := D ⊓ before gamma
    let t := labels.symm gamma
    IsPushout
      (T.attaching t ≫ (T.predecessorIso L t).inv.right ≫
        (L.map (originalRemainder_pred D gamma ht)).right)
      (s (T.label t)).hom
      (L.map (inf_le_left : E ≤ D)).right
      (T.cell t ≫ (L.principalIso t).inv.right ≫
        (L.map (show LowerSet.Iic t ≤ D from fun _ hp => D.lower' hp ht)).right) := by
  let E := D ⊓ before gamma
  let t := labels.symm gamma
  let z : CellTreeIncrement.Label E D := ⟨t, ht, originalRemainder_notMem D gamma⟩
  have hPred : E ⊔ LowerSet.Iio t = E :=
    sup_eq_left.mpr (originalRemainder_pred D gamma ht)
  have hWhole : E ⊔ LowerSet.Iic t = D := originalRemainder_union D gamma hD ht
  have hU := (CellTreeIncrement.successorUnionIsPushout T L E D z).map (Under.forget X)
  have hP := (CellTreeIncrement.originalSelectedIsPushout T L t).paste_horiz hU.flip
  let eE : L.obj (E ⊔ LowerSet.Iio t) ≅ L.obj E := L.functor.mapIso (eqToIso hPred)
  let eD : L.obj (E ⊔ LowerSet.Iic t) ≅ L.obj D := L.functor.mapIso (eqToIso hWhole)
  have eE_hom : eE.hom = L.map (leOfHom (eqToHom hPred)) := rfl
  have eD_hom : eD.hom = L.map (leOfHom (eqToHom hWhole)) := rfl
  refine hP.of_iso (Iso.refl _) ((Under.forget X).mapIso eE)
    (Iso.refl _) ((Under.forget X).mapIso eD) ?_ ?_ ?_ ?_
  · change ((T.attaching t ≫ (T.predecessorIso L t).inv.right) ≫
      (L.map (le_sup_right : LowerSet.Iio t ≤ E ⊔ LowerSet.Iio t)).right) ≫
      eE.hom.right = 𝟙 _ ≫ _
    rw [Category.id_comp, eE_hom, Category.assoc, Category.assoc,
      ← Under.comp_right, L.map_comp]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · change (L.map (sup_le_sup_left
      (show LowerSet.Iio t ≤ LowerSet.Iic t from fun _ hp => hp.le) E)).right ≫
      eD.hom.right = eE.hom.right ≫ (L.map (inf_le_left : E ≤ D)).right
    rw [eE_hom, eD_hom, ← Under.comp_right, ← Under.comp_right, L.map_comp, L.map_comp]
  · change ((T.cell t ≫ (L.principalIso t).inv.right) ≫
      (L.map (le_sup_right : LowerSet.Iic t ≤ E ⊔ LowerSet.Iic t)).right) ≫
      eD.hom.right = 𝟙 _ ≫ _
    rw [Category.id_comp, eD_hom, Category.assoc, Category.assoc,
      ← Under.comp_right, L.map_comp]

end OriginalLowerPieces

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison
open OriginalCapturedCellVertexMap CellTreeLabelAdjoin CellTreeLabelTransport
open GoodCellExtensionOrder OriginalExtension

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi]

/-- The actual original predecessor support on the complete BEFORE prefix. -/
abbrev successorPred : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    @LowerSet (before gamma) r.ord.toLE := by
  letI := r.ord
  letI : Preorder (before gamma) := r.ord.toPreorder
  exact OriginalLowerComparisonCocone.carrier
    (prefixLabels (before gamma) r.ord r.below) (LowerSet.Iio (labels.symm gamma))

/-- Compactness captures the original attaching map inside its original predecessors. -/
abbrev successorCapture : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    OriginalPredecessorCellCapture.LocalCaptureData r.tree N
      (successorPred O M chi gamma r) (O.label (labels.symm gamma))
      (liftedOriginalAttaching O M chi gamma r N) chi := by
  letI := r.ord
  letI : Preorder (before gamma) := r.ord.toPreorder
  exact capture r.tree N O (labels.symm gamma) (successorPred O M chi gamma r)
    chi r.good (liftedOriginalAttaching O M chi gamma r N)

/-- The new order lives on the literal original AFTER carrier. -/
@[instance_reducible]
def successorOrder : PartialOrder (after gamma) := by
  letI := r.ord
  letI : Preorder (before gamma) := r.ord.toPreorder
  letI := extensionOrder (successorCapture O M chi gamma r N).support
  exact pulledOrder (prefixEquiv gamma).symm

/-- The captured one-cell tree keeps the same original AFTER labels and root. -/
def successorTree : letI := successorOrder O M chi gamma r N
    CellTree s X (P := after gamma) := by
  letI := r.ord
  letI : Preorder (before gamma) := r.ord.toPreorder
  letI := extensionOrder (successorCapture O M chi gamma r N).support
  exact CellTreeLabelTransport.tree (prefixEquiv gamma).symm
    (OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
      (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good)

/-- The actual AFTER comparison uses the literal original label function. -/
def successorLabelHom :
    @OrderHom (after gamma) P
      (successorOrder O M chi gamma r N).toPreorder pOrder.toPreorder := by
  letI := r.ord
  letI : Preorder (before gamma) := r.ord.toPreorder
  letI := extensionOrder (successorCapture O M chi gamma r N).support
  letI := successorOrder O M chi gamma r N
  let j := OriginalCellExtensionComparison.labelOrderHom r.tree N O
    (prefixLabels (before gamma) r.ord r.below) (labels.symm gamma)
    (successorPred O M chi gamma r) (fun _ h => h)
    chi r.good (liftedOriginalAttaching O M chi gamma r N)
  exact OrderIsoLowerColimitTransport.labels (pulledIso (prefixEquiv gamma).symm) j

/-- The full AFTER natural comparison is constructed from the original vertex maps. -/
def successorComparison :
    letI := successorOrder O M chi gamma r N
    letI : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
    (successorTree O M chi gamma r N).diagram ⟶
      (successorLabelHom O M chi gamma r N).monotone.functor ⋙ O.diagram := by
  letI := r.ord
  letI : Preorder (before gamma) := r.ord.toPreorder
  letI := extensionOrder (successorCapture O M chi gamma r N).support
  letI := successorOrder O M chi gamma r N
  exact OrderIsoLowerColimitTransport.comparison (pulledIso (prefixEquiv gamma).symm)
    (OriginalCellExtensionComparison.labelOrderHom r.tree N O
      (prefixLabels (before gamma) r.ord r.below) (labels.symm gamma)
      (successorPred O M chi gamma r) (fun _ h => h)
      chi r.good (liftedOriginalAttaching O M chi gamma r N))
    (OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
      (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good).diagram
    O.diagram
    (OriginalCellExtensionComparison.comparison r.tree N O
      (prefixLabels (before gamma) r.ord r.below) r.comparison (labels.symm gamma)
      (successorPred O M chi gamma r) (fun _ h => h)
      chi r.good (liftedOriginalAttaching O M chi gamma r N)
      (liftedOriginalAttaching_factor O M chi gamma r N))

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison
open OriginalCapturedCellVertexMap CellTreeLabelAdjoin CellTreeLabelTransport
open GoodCellExtensionOrder OriginalExtension

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi]

theorem prefixEquiv_label (x : GoodCellExtensionOrder.Index (before gamma)) :
    (prefixEquiv gamma x).1 =
      OriginalLocalizedCellExtension.labels (Subtype.val : before gamma → P)
          (labels.symm gamma) x := by
  rcases x with ⟨x⟩
  cases x <;> rfl

omit [HasPushouts C] [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorLabelHom_value (q : after gamma) :
    successorLabelHom O M chi gamma r N q = q.1 := by
  let _ := r.ord
  let _ : Preorder (before gamma) := r.ord.toPreorder
  let _ := extensionOrder (successorCapture O M chi gamma r N).support
  change OriginalLocalizedCellExtension.labels (Subtype.val : before gamma → P)
    (labels.symm gamma) ((prefixEquiv gamma).symm q) = q.1
  exact (prefixEquiv_label gamma ((prefixEquiv gamma).symm q)).symm.trans
    (congrArg Subtype.val ((prefixEquiv gamma).apply_symm_apply q))

/-- Every original lower subset has its actual original chosen comparison universal property. -/
def successorLowerIsColimit (D : LowerSet P) (hD : D ≤ after gamma) :
    letI := successorOrder O M chi gamma r N
    letI : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
    IsColimit (OriginalLowerComparisonCocone.cocone
      (successorLabelHom O M chi gamma r N) (successorTree O M chi gamma r N).diagram
      O.diagram (successorComparison O M chi gamma r N) M D) := by
  letI := r.ord
  letI : Preorder (before gamma) := r.ord.toPreorder
  let f := prefixLabels (before gamma) r.ord r.below
  let t := labels.symm gamma
  let B := successorPred O M chi gamma r
  let hPred : ∀ q : before gamma, q ∈ B → f q < t := fun _ h => h
  let g := liftedOriginalAttaching O M chi gamma r N
  let cap := successorCapture O M chi gamma r N
  letI := extensionOrder cap.support
  let j := OriginalCellExtensionComparison.labelOrderHom r.tree N O f t B hPred chi r.good g
  let T' := OriginalLocalizedCellExtension.tree r.tree N B (O.label t) g chi r.good
  let beta' := OriginalCellExtensionComparison.comparison r.tree N O f r.comparison t B hPred
    chi r.good g (liftedOriginalAttaching_factor O M chi gamma r N)
  have hOld : IsColimit (OriginalLowerComparisonCocone.cocone j T'.diagram
      O.diagram beta' M D) := by
    by_cases ht : t ∈ D
    · let E := D ⊓ before gamma
      have hE : E ≤ before gamma := inf_le_right
      have hSame : ∀ q : before gamma, f q ∈ D ↔ f q ∈ E :=
        fun q => ⟨fun h => ⟨h, q.2⟩, fun h => h.1⟩
      have hCar : OriginalLowerComparisonCocone.carrier f D =
          OriginalLowerComparisonCocone.carrier f E := by
        apply SetLike.coe_injective
        apply Set.ext
        exact hSame
      let e0 := r.originalIso O M chi N E hE
      let e : N.obj (OriginalLowerComparisonCocone.carrier f D) ≅ M.obj E :=
        N.functor.mapIso (eqToIso hCar) ≪≫ e0
      have he : ∀ p : OriginalLowerComparisonCocone.carrier f D,
          N.ι (OriginalLowerComparisonCocone.carrier f D) p ≫ e.hom =
            r.comparison.app p.1 ≫ M.ι E ⟨f p.1, (hSame p.1).1 p.2⟩ := by
        intro p
        change N.ι (OriginalLowerComparisonCocone.carrier f D) p ≫
          (N.map (leOfHom (eqToHom hCar)) ≫ e0.hom) = _
        rw [← Category.assoc, N.ι_map]
        exact r.originalIso_hom_fac O M chi N E hE ⟨p.1, (hSame p.1).1 p.2⟩
      have hSquare0 := originalRemainderIsPushout O M D gamma hD ht
      have hSquare : IsPushout
          (O.attaching t ≫ (O.predecessorIso M t).inv.right ≫
            (M.map (originalRemainder_pred D gamma ht)).right)
          (s (O.label t)).hom (M.map (inf_le_left : E ≤ D)).right
          (O.cell t ≫ (M.ι D ⟨t, ht⟩).right) := by
        have hLeg : (M.principalIso t).inv ≫
            M.map (show LowerSet.Iic t ≤ D from fun _ hp => D.lower' hp ht) = M.ι D ⟨t, ht⟩ := by
          exact M.ι_map (show LowerSet.Iic t ≤ D from fun _ hp => D.lower' hp ht) ⟨t, le_rfl⟩
        have hCellEq : O.cell t ≫ (M.principalIso t).inv.right ≫
            (M.map (show LowerSet.Iic t ≤ D from fun _ hp => D.lower' hp ht)).right =
            O.cell t ≫ (M.ι D ⟨t, ht⟩).right := by
          have hLegR : (M.principalIso t).inv.right ≫
              (M.map (show LowerSet.Iic t ≤ D from fun _ hp => D.lower' hp ht)).right =
              (M.ι D ⟨t, ht⟩).right := by
            rw [← Under.comp_right]
            exact congrArg Under.Hom.right hLeg
          exact congrArg (fun k => O.cell t ≫ k) hLegR
        have hFirstEq : O.attaching t ≫ (O.predecessorIso M t).inv.right ≫
            (M.map (originalRemainder_pred D gamma ht)).right =
            O.attaching t ≫ ((O.predecessorIso M t).inv ≫
              M.map (originalRemainder_pred D gamma ht)).right := by
          rw [Under.comp_right]
        exact hCellEq ▸ hFirstEq.symm ▸ hSquare0
      exact withNewOriginalIsColimit r.tree N O M f r.comparison t B hPred chi r.good g
        (liftedOriginalAttaching_factor O M chi gamma r N) D ht E inf_le_left
        (originalRemainder_pred D gamma ht) hSame e he hSquare
    · have hDB : D ≤ before gamma := by
        intro p hp
        rcases (mem_after_iff gamma p).1 (hD hp) with hb | he
        · exact hb
        · exact False.elim (ht (show t ∈ D from (congrArg (fun p => p ∈ D) he).mp hp))
      exact oldOnlyOriginalIsColimit r.tree N O M f r.comparison t B hPred chi r.good g
        (liftedOriginalAttaching_factor O M chi gamma r N) D ht (r.lowerUP D hDB)
  letI := successorOrder O M chi gamma r N
  letI : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
  exact OrderIsoLowerColimitTransport.isColimit (pulledIso (prefixEquiv gamma).symm) j
    T'.diagram O.diagram beta' M D hOld

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison
open OriginalCapturedCellVertexMap CellTreeLabelAdjoin CellTreeLabelTransport
open GoodCellExtensionOrder

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi]

omit [HasPushouts C] [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorBelow : ∀ a b : after gamma,
    @LE.le (after gamma) (successorOrder O M chi gamma r N).toLE a b → a.1 ≤ b.1 := by
  let _ := successorOrder O M chi gamma r N
  let _ : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
  intro a b h
  exact (congrArg₂ (fun p q : P => p ≤ q)
    (successorLabelHom_value O M chi gamma r N a)
    (successorLabelHom_value O M chi gamma r N b)).mp
      ((successorLabelHom O M chi gamma r N).monotone h)

omit [HasPushouts C] [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi] in
theorem successorLiteralLabels :
    successorLabelHom O M chi gamma r N =
      prefixLabels (after gamma) (successorOrder O M chi gamma r N)
        (successorBelow O M chi gamma r N) := by
  apply DFunLike.ext
  exact successorLabelHom_value O M chi gamma r N

/-- Bundle the actual original-label tree and proved original lower universal properties. -/
def prefixFromLabelComparison (B : LowerSet P) (ord : PartialOrder B)
    (tree : letI := ord; CellTree s X (P := B))
    (below : ∀ a b : B, @LE.le B ord.toLE a b → a.1 ≤ b.1)
    (hLabels : ∀ a : B, (letI := ord; tree.label a) = O.label a.1)
    (hGood : letI := ord; tree.IsGood chi)
    (f : @OrderHom B P ord.toPreorder pOrder.toPreorder)
    (beta : letI := ord
      letI : Preorder B := ord.toPreorder
      tree.diagram ⟶ f.monotone.functor ⋙ O.diagram)
    (hUP : ∀ D : LowerSet P, D ≤ B →
      letI := ord
      letI : Preorder B := ord.toPreorder
      IsColimit (OriginalLowerComparisonCocone.cocone f tree.diagram O.diagram beta M D))
    (hf : f = prefixLabels B ord below) : Prefix O M chi B := by
  subst f
  exact {
    ord := ord
    below := below
    tree := tree
    labels := hLabels
    comparison := beta
    good := hGood
    lowerUP := hUP }

omit [WellFoundedLT P] [HasPushouts C] [IsCardinalLocallyPresentable C chi] in
theorem prefixFromLabelComparison_ord (B : LowerSet P) (ord : PartialOrder B)
    (tree : letI := ord; CellTree s X (P := B))
    (below : ∀ a b : B, @LE.le B ord.toLE a b → a.1 ≤ b.1)
    (hLabels : ∀ a : B, (letI := ord; tree.label a) = O.label a.1)
    (hGood : letI := ord; tree.IsGood chi)
    (f : @OrderHom B P ord.toPreorder pOrder.toPreorder)
    (beta : letI := ord
      letI : Preorder B := ord.toPreorder
      tree.diagram ⟶ f.monotone.functor ⋙ O.diagram)
    (hUP : ∀ D : LowerSet P, D ≤ B →
      letI := ord
      letI : Preorder B := ord.toPreorder
      IsColimit (OriginalLowerComparisonCocone.cocone f tree.diagram O.diagram beta M D))
    (hf : f = prefixLabels B ord below) :
    (prefixFromLabelComparison O M chi B ord tree below hLabels hGood f beta hUP hf).ord = ord := by
  subst f
  rfl

omit [WellFoundedLT P] [HasPushouts C] [IsCardinalLocallyPresentable C chi] in
theorem prefixFromLabelComparison_tree (B : LowerSet P) (ord : PartialOrder B)
    (tree : letI := ord; CellTree s X (P := B))
    (below : ∀ a b : B, @LE.le B ord.toLE a b → a.1 ≤ b.1)
    (hLabels : ∀ a : B, (letI := ord; tree.label a) = O.label a.1)
    (hGood : letI := ord; tree.IsGood chi)
    (f : @OrderHom B P ord.toPreorder pOrder.toPreorder)
    (beta : letI := ord
      letI : Preorder B := ord.toPreorder
      tree.diagram ⟶ f.monotone.functor ⋙ O.diagram)
    (hUP : ∀ D : LowerSet P, D ≤ B →
      letI := ord
      letI : Preorder B := ord.toPreorder
      IsColimit (OriginalLowerComparisonCocone.cocone f tree.diagram O.diagram beta M D))
    (hf : f = prefixLabels B ord below) :
    (prefixFromLabelComparison O M chi B ord tree below hLabels hGood f beta hUP hf).tree
        ≍ tree := by
  subst f
  exact HEq.rfl

omit [WellFoundedLT P] [HasPushouts C] [IsCardinalLocallyPresentable C chi] in
theorem prefixFromLabelComparison_comparison (B : LowerSet P) (ord : PartialOrder B)
    (tree : letI := ord; CellTree s X (P := B))
    (below : ∀ a b : B, @LE.le B ord.toLE a b → a.1 ≤ b.1)
    (hLabels : ∀ a : B, (letI := ord; tree.label a) = O.label a.1)
    (hGood : letI := ord; tree.IsGood chi)
    (f : @OrderHom B P ord.toPreorder pOrder.toPreorder)
    (beta : letI := ord
      letI : Preorder B := ord.toPreorder
      tree.diagram ⟶ f.monotone.functor ⋙ O.diagram)
    (hUP : ∀ D : LowerSet P, D ≤ B →
      letI := ord
      letI : Preorder B := ord.toPreorder
      IsColimit (OriginalLowerComparisonCocone.cocone f tree.diagram O.diagram beta M D))
    (hf : f = prefixLabels B ord below) :
    (prefixFromLabelComparison O M chi B ord tree below hLabels hGood f beta hUP hf).comparison
        ≍ beta := by
  subst f
  exact HEq.rfl

omit [WellFoundedLT P] [HasPushouts C] [IsCardinalLocallyPresentable C chi] in
theorem prefixFromLabelComparison_labels (B : LowerSet P) (ord : PartialOrder B)
    (tree : letI := ord; CellTree s X (P := B))
    (below : ∀ a b : B, @LE.le B ord.toLE a b → a.1 ≤ b.1)
    (hLabels : ∀ a : B, (letI := ord; tree.label a) = O.label a.1)
    (hGood : letI := ord; tree.IsGood chi)
    (f : @OrderHom B P ord.toPreorder pOrder.toPreorder)
    (beta : letI := ord
      letI : Preorder B := ord.toPreorder
      tree.diagram ⟶ f.monotone.functor ⋙ O.diagram)
    (hUP : ∀ D : LowerSet P, D ≤ B →
      letI := ord
      letI : Preorder B := ord.toPreorder
      IsColimit (OriginalLowerComparisonCocone.cocone f tree.diagram O.diagram beta M D))
    (hf : f = prefixLabels B ord below) :
    prefixLabels B
        (prefixFromLabelComparison O M chi B ord tree below hLabels hGood f beta hUP hf).ord
      (prefixFromLabelComparison O M chi B ord tree below hLabels hGood f beta hUP
          hf).below ≍ f := by
  subst f
  exact HEq.rfl

/-- The actual original compact-cell successor constructs its complete good prefix. -/
def successorPrefix : Prefix O M chi (after gamma) := by
  letI := r.ord
  letI : Preorder (before gamma) := r.ord.toPreorder
  letI := extensionOrder (successorCapture O M chi gamma r N).support
  letI := successorOrder O M chi gamma r N
  letI : Preorder (after gamma) := (successorOrder O M chi gamma r N).toPreorder
  let ord := successorOrder O M chi gamma r N
  let tree := successorTree O M chi gamma r N
  let below := successorBelow O M chi gamma r N
  have hLabels : ∀ a : after gamma, tree.label a = O.label a.1 := by
    intro a
    let x := (prefixEquiv gamma).symm a
    have hx : prefixEquiv gamma x = a := (prefixEquiv gamma).apply_symm_apply a
    have hLabel : tree.label (prefixEquiv gamma x) = O.label (prefixEquiv gamma x).1 := by
      change (OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
        (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good).label
        ((prefixEquiv gamma).symm (prefixEquiv gamma x)) = _
      rw [Equiv.symm_apply_apply]
      rcases x with ⟨x⟩
      cases x with
      | some x => exact r.labels x
      | none => rfl
    exact hx ▸ hLabel
  have hGood : tree.IsGood chi :=
    CellTreeLabelTransport.tree_good (prefixEquiv gamma).symm
      (OriginalLocalizedCellExtension.tree r.tree N (successorPred O M chi gamma r)
        (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good)
      chi (OriginalLocalizedCellExtension.tree_good r.tree N (successorPred O M chi gamma r)
        (O.label (labels.symm gamma)) (liftedOriginalAttaching O M chi gamma r N) chi r.good)
  exact prefixFromLabelComparison O M chi (after gamma) ord tree below hLabels hGood
    (successorLabelHom O M chi gamma r N) (successorComparison O M chi gamma r N)
    (successorLowerIsColimit O M chi gamma r N) (successorLiteralLabels O M chi gamma r N)

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration OriginalCellVertexLowerComparison
open OriginalCapturedCellVertexMap CellTreeLabelAdjoin CellTreeLabelTransport
open GoodCellExtensionOrder

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  (gamma : OriginalCellWellOrderEnumeration.Index (P := P))
  (r : Prefix O M chi (before gamma))
  (N : letI := r.ord
    letI : Preorder (before gamma) := r.ord.toPreorder
    LowerSetColimitData r.tree.diagram)
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).left chi]
  [IsCardinalPresentable (s (O.label (labels.symm gamma))).right chi]

theorem successorPrefix_order :
    (successorPrefix O M chi gamma r N).ord = successorOrder O M chi gamma r N := by
  unfold successorPrefix
  exact prefixFromLabelComparison_ord _ _ _ _ _ _ _ _ _ _ _ _ _

theorem successorPrefix_tree :
    (successorPrefix O M chi gamma r N).tree ≍ successorTree O M chi gamma r N := by
  unfold successorPrefix
  exact prefixFromLabelComparison_tree _ _ _ _ _ _ _ _ _ _ _ _ _

theorem successorPrefix_comparison :
    (successorPrefix O M chi gamma r N).comparison ≍ successorComparison O M chi gamma r N := by
  unfold successorPrefix
  exact prefixFromLabelComparison_comparison _ _ _ _ _ _ _ _ _ _ _ _ _

theorem successorPrefix_labels :
    prefixLabels (after gamma) (successorPrefix O M chi gamma r N).ord
      (successorPrefix O M chi gamma r N).below ≍ successorLabelHom O M chi gamma r N := by
  unfold successorPrefix
  exact prefixFromLabelComparison_labels _ _ _ _ _ _ _ _ _ _ _ _ _

end

end CategoryTheory.SmallObject.OriginalGoodification
