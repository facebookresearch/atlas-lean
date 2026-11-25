/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalRefiningHistory

/-!
# Complete original lower, predecessor and endpoint comparisons from actual histories

The actual compatible local histories and their original cell/source laws construct the whole
same-label refining tree. Every original lower subset retains its chosen colimit, universal
descender, forward and inverse cofan equations and inclusion naturality. The actual predecessor,
attaching, cell, vertex and endpoint maps retain the same arbitrary original root.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject Opposite

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open OriginalCellWellOrderEnumeration

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [cColimits : HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] (H : CompleteRefiningHistory O M chi)

/-- The actual complete history constructs its whole original same-carrier prefix. -/
def assemblyPrefix : Prefix O M chi (⊤ : LowerSet P) :=
  limitPrefix O M chi after after_monotone (H.prefix O M chi)
    (fun i j => ⟨max i j, le_max_left _ _, le_max_right _ _⟩)
    fullAfter_cover (H.preserves O M chi)

/-- Every actual old prefix retains all its original fields inside the assembled whole prefix. -/
theorem assemblyPrefix_preserves (i : OriginalCellWellOrderEnumeration.Index (P := P)) :
    Preserves O M chi (le_top : after i ≤ ⊤) (H.prefix O M chi i)
      (assemblyPrefix O M chi H) :=
  limitPrefix_preserves O M chi after after_monotone (H.prefix O M chi)
    (fun i j => ⟨max i j, le_max_left _ _, le_max_right _ _⟩)
    fullAfter_cover (H.preserves O M chi) i

/-- Actual local original cell-target laws give the whole original cell-target law. -/
theorem assemblyPrefix_cell_squares : PrefixCellSquares O M chi (assemblyPrefix O M chi H) := by
  intro a
  let i := labels a.1
  have hPres := assemblyPrefix_preserves O M chi H i
  exact cellSquare_of_preserves O M chi hPres
    (⟨a.1, by change labels a.1 ≤ i; exact le_rfl⟩ : after i)
    (H.cellSquares i _)

/-- Actual local original attaching laws give the whole law at the original predecessor points. -/
theorem assemblyPrefix_attaching_squares :
    PrefixAttachingSquares O M chi (assemblyPrefix O M chi H) := by
  intro a
  let i := labels a.1
  have hPres := assemblyPrefix_preserves O M chi H i
  exact attachingSquare_of_preserves O M chi _ _ hPres
    (⟨a.1, by change labels a.1 ≤ i; exact le_rfl⟩ : after i)
    (H.attachingSquares i _)

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P] [WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [cColimits : HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (H : CompleteRefiningHistory O M chi)

/-- The actual history constructs sameLabels on the same original objects and labels. -/
def sameLabels : P ≃ (⊤ : LowerSet P) where
  toFun p := ⟨p, by trivial⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual history constructs sameLabelOrder on the same original objects and labels. -/
@[instance_reducible]
def sameLabelOrder : PartialOrder P := by
  let r := assemblyPrefix O M chi H
  letI := r.ord
  exact CellTreeLabelTransport.pulledOrder (sameLabels (P := P))

/-- Given an original cell tree `O`, chosen lower-set colimits `M`, regular
`chi`, working-size colimits in `C`, and a complete compatible history `H`,
assemble a cell tree on the same carrier `P` with the refining order
`sameLabelOrder`. Its label at `p` is `O.label p` (`sameLabelTree_labels`).

Sharing the original objects means sharing that index carrier and those
labels, not that the `Under X` vertex values agree with `O`'s. The vertices
are related by `sameLabelComparison`, a natural transformation from the new
diagram to `O.diagram` pulled back along the monotone identity `sameLabelHom`
from the new order to the old one. The endpoint comparison
`sameLabelEndpointIso` is an isomorphism in `Under X` from the new endpoint
to `O.endpointObj`, with `new.hom ≫ endpointIso.hom.right = O.hom`
(`sameLabelEndpoint_root`). -/
def sameLabelTree : letI := sameLabelOrder O M chi H
    CellTree s X (P := P) := by
  let r := assemblyPrefix O M chi H
  letI := r.ord
  exact CellTreeLabelTransport.tree (sameLabels (P := P)) r.tree

/-- The actual history constructs sameLabelHom on the same original objects and labels. -/
def sameLabelHom :
    @OrderHom P P (sameLabelOrder O M chi H).toPreorder pOrder.toPreorder := by
  let r := assemblyPrefix O M chi H
  let e : @OrderIso P (⊤ : @LowerSet P pOrder.toLE)
      (sameLabelOrder O M chi H).toLE r.ord.toLE :=
    @CellTreeLabelTransport.pulledIso (⊤ : @LowerSet P pOrder.toLE) P r.ord (sameLabels (P := P))
  exact @OrderIsoLowerColimitTransport.labels P (⊤ : @LowerSet P pOrder.toLE) P
    (sameLabelOrder O M chi H) r.ord pOrder.toPreorder
    e (prefixLabels ⊤ r.ord r.below)

/-- The actual history constructs sameLabelComparison on the same original objects and labels. -/
def sameLabelComparison :
    @NatTrans P (@Preorder.smallCategory P (sameLabelOrder O M chi H).toPreorder)
      (Under X) (inferInstance : Category.{v} (Under X))
      (@CellTree.diagram C cCategory P (sameLabelOrder O M chi H) A s X
        (sameLabelTree O M chi H))
      (@Functor.comp P
        (@Preorder.smallCategory P (sameLabelOrder O M chi H).toPreorder)
        P (@Preorder.smallCategory P pOrder.toPreorder)
        (Under X) (inferInstance : Category.{v} (Under X))
        (@Monotone.functor P P (sameLabelOrder O M chi H).toPreorder pOrder.toPreorder
          (sameLabelHom O M chi H)
          (@OrderHom.monotone' P P (sameLabelOrder O M chi H).toPreorder pOrder.toPreorder
            (sameLabelHom O M chi H)))
        O.diagram) := by
  let r := assemblyPrefix O M chi H
  let e : @OrderIso P (⊤ : @LowerSet P pOrder.toLE)
      (sameLabelOrder O M chi H).toLE r.ord.toLE :=
    @CellTreeLabelTransport.pulledIso (⊤ : @LowerSet P pOrder.toLE) P r.ord (sameLabels (P := P))
  exact @OrderIsoLowerColimitTransport.comparison P (⊤ : @LowerSet P pOrder.toLE) P
    (sameLabelOrder O M chi H) r.ord pOrder.toPreorder
    (Under X) (inferInstance : Category.{v} (Under X)) e (prefixLabels ⊤ r.ord r.below)
    (@CellTree.diagram C cCategory (⊤ : @LowerSet P pOrder.toLE) r.ord A s X r.tree)
    O.diagram r.comparison

theorem sameLabelHom_value (p : P) : sameLabelHom O M chi H p = p := rfl

theorem sameLabelOrder_below (p q : P)
    (h : @LE.le P (sameLabelOrder O M chi H).toLE p q) : p ≤ q :=
  @OrderHom.monotone' P P (sameLabelOrder O M chi H).toPreorder pOrder.toPreorder
    (sameLabelHom O M chi H) p q h

theorem sameLabelTree_labels (p : P) :
    (@CellTree.label C cCategory P (sameLabelOrder O M chi H) A s X
      (sameLabelTree O M chi H) p) = O.label p :=
  (assemblyPrefix O M chi H).labels ((sameLabels (P := P)) p)

theorem sameLabelTree_good :
    @CellTree.IsGood C cCategory P (sameLabelOrder O M chi H) A s X
      (sameLabelTree O M chi H) chi (inferInstance : Fact chi.IsRegular) := by
  let r := assemblyPrefix O M chi H
  exact @CellTreeLabelTransport.tree_good C cCategory (⊤ : @LowerSet P pOrder.toLE) P
    r.ord A s X (sameLabels (P := P)) r.tree chi (inferInstance : Fact chi.IsRegular) r.good

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P] [originalWellFounded : WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [cColimits : HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (H : CompleteRefiningHistory O M chi)

/-- The actual history constructs sameLabelLowerIsColimit on the same original objects and
labels. -/
def sameLabelLowerIsColimit (D : LowerSet P) :
    letI := @sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H
    letI : Preorder P :=
        (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H).toPreorder
    IsColimit (@OriginalLowerComparisonCocone.cocone P P
      (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H).toPreorder pOrder.toPreorder
      (Under X) (inferInstance : Category.{v} (Under X))
      (@sameLabelHom P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H)
      (@CellTree.diagram C cCategory P
          (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
            (inferInstance : Fact chi.IsRegular)  H) A s X
        (@sameLabelTree P pOrder originalWellFounded C cCategory cColimits A s X O M chi
            (inferInstance : Fact chi.IsRegular)  H))
      (@CellTree.diagram C cCategory P pOrder A s X O)
          (@sameLabelComparison P pOrder originalWellFounded C cCategory cColimits A s X O M chi
            (inferInstance : Fact chi.IsRegular)  H) M D) := by
  let r := @assemblyPrefix P pOrder originalWellFounded C cCategory cColimits A s X O M chi
      (inferInstance : Fact chi.IsRegular)  H
  let e : @OrderIso P (⊤ : @LowerSet P pOrder.toLE)
      (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H).toLE r.ord.toLE :=
    @CellTreeLabelTransport.pulledIso (⊤ : @LowerSet P pOrder.toLE) P r.ord (sameLabels (P := P))
  exact @OrderIsoLowerColimitTransport.isColimit P (⊤ : @LowerSet P pOrder.toLE) P
    (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H) r.ord pOrder.toPreorder
    (Under X) (inferInstance : Category.{v} (Under X)) e (prefixLabels ⊤ r.ord r.below)
    (@CellTree.diagram C cCategory (⊤ : @LowerSet P pOrder.toLE) r.ord A s X r.tree)
    (@CellTree.diagram C cCategory P pOrder A s X O) r.comparison M D (r.lowerUP D le_top)

/-- The actual history constructs sameLabelLowerData on the same original objects and labels. -/
def sameLabelLowerData :
    @LowerSetColimitData P
        (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H).toPreorder
      (Under X) (inferInstance : Category.{v} (Under X))
      (@CellTree.diagram C cCategory P
          (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
            (inferInstance : Fact chi.IsRegular)  H) A s X
        (@sameLabelTree P pOrder originalWellFounded C cCategory cColimits A s X O M chi
            (inferInstance : Fact chi.IsRegular)  H)) := by
  let r := @assemblyPrefix P pOrder originalWellFounded C cCategory cColimits A s X O M chi
      (inferInstance : Fact chi.IsRegular)  H
  let ord := @sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
      (inferInstance : Fact chi.IsRegular)  H
  let tree : @CellTree C cCategory P ord A s X :=
      @sameLabelTree P pOrder originalWellFounded C cCategory cColimits A s X O M chi
      (inferInstance : Fact chi.IsRegular)  H
  letI := ord
  letI : Preorder P := ord.toPreorder
  exact tree.lowerData

/-- The actual history constructs sameLabelLowerCarrier on the same original objects and labels. -/
def sameLabelLowerCarrier (D : LowerSet P) :
    @LowerSet P (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H).toLE :=
  @OriginalLowerComparisonCocone.carrier P P
    (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H).toPreorder pOrder.toPreorder
    (@sameLabelHom P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H) D

/-- The actual original lower UPs give the full comparison iso on each original lower label set. -/
def sameLabelLowerIso (D : LowerSet P) :
    letI := @sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H
    letI : Preorder P :=
        (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H).toPreorder
    (@sameLabelLowerData P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H).obj
        (@sameLabelLowerCarrier P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H D) ≅
      (@LowerSetColimitData.obj P pOrder.toPreorder (Under X)
          (inferInstance : Category.{v} (Under X))
        (@CellTree.diagram C cCategory P pOrder A s X O) M D) := by
  let N := @sameLabelLowerData P pOrder originalWellFounded C cCategory cColimits A s X O M chi
      (inferInstance : Fact chi.IsRegular)  H
  let car := @sameLabelLowerCarrier P pOrder originalWellFounded C cCategory cColimits A s X O M chi
      (inferInstance : Fact chi.IsRegular)  H D
  let hUP := @sameLabelLowerIsColimit P pOrder originalWellFounded C cCategory cColimits A s X O M
      chi (inferInstance : Fact chi.IsRegular)  H D
  letI := @sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
      (inferInstance : Fact chi.IsRegular)  H
  letI : Preorder P :=
      (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H).toPreorder
  exact (N.isColimit car).coconePointUniqueUpToIso hUP

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P] [originalWellFounded : WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [cColimits : HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData
      (@CellTree.diagram C cCategory P pOrder A s X O))
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (H : CompleteRefiningHistory O M chi)


local notation "finalOrder" => @sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A
                                s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalTree" => @sameLabelTree P pOrder originalWellFounded C cCategory cColimits A s
                               X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalMap" => @sameLabelHom P pOrder originalWellFounded C cCategory cColimits A s X
                              O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalBeta" => @sameLabelComparison P pOrder originalWellFounded C cCategory
                               cColimits A s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalData" => @sameLabelLowerData P pOrder originalWellFounded C cCategory cColimits
                               A s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalCarrier" => @sameLabelLowerCarrier P pOrder originalWellFounded C cCategory
                                  cColimits A s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalIso" => @sameLabelLowerIso P pOrder originalWellFounded C cCategory cColimits A
                              s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "oldDiagram" => @CellTree.diagram C cCategory P pOrder A s X O

theorem sameLabelLowerCarrier_mem (D : LowerSet P) (p : P) :
    p ∈ finalCarrier D ↔ p ∈ D := Iff.rfl

theorem sameLabelLowerIso_hom_fac (D : LowerSet P) (p : finalCarrier D) :
    letI := finalOrder
    letI : Preorder P := (finalOrder).toPreorder
    (finalData).ι (finalCarrier D) p ≫ (finalIso D).hom =
      (finalBeta).app p.1 ≫
        (@LowerSetColimitData.ι P pOrder.toPreorder (Under X)
            (inferInstance : Category.{v} (Under X))
          oldDiagram M D ⟨p.1, p.2⟩) := by
  let _ := finalOrder
  let _ : Preorder P := (finalOrder).toPreorder
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    ((finalData).isColimit (finalCarrier D))
        (@sameLabelLowerIsColimit P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H D) p

theorem sameLabelLowerIso_inv_fac (D : LowerSet P) (p : finalCarrier D) :
    letI := finalOrder
    letI : Preorder P := (finalOrder).toPreorder
    ((finalBeta).app p.1 ≫
        (@LowerSetColimitData.ι P pOrder.toPreorder (Under X)
            (inferInstance : Category.{v} (Under X))
          oldDiagram M D ⟨p.1, p.2⟩)) ≫ (finalIso D).inv =
      (finalData).ι (finalCarrier D) p := by
  let _ := finalOrder
  let _ : Preorder P := (finalOrder).toPreorder
  rw
      [← @sameLabelLowerIso_hom_fac P pOrder originalWellFounded C cCategory cColimits A s X O M
        chi (inferInstance : Fact chi.IsRegular)  H D p, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]

/-- The actual history constructs sameLabelLowerMap on the same original objects and labels. -/
def sameLabelLowerMap {D E : LowerSet P} (hDE : D ≤ E) :
    letI := finalOrder
    letI : Preorder P := (finalOrder).toPreorder
    (finalData).obj (finalCarrier D) ⟶ (finalData).obj (finalCarrier E) := by
  let _ := finalOrder
  let _ : Preorder P := (finalOrder).toPreorder
  exact (finalData).map (fun _ h => hDE h)

theorem sameLabelLowerIso_naturality (D E : LowerSet P) (hDE : D ≤ E) :
    letI := finalOrder
    letI : Preorder P := (finalOrder).toPreorder
    (finalIso D).hom ≫
      (@LowerSetColimitData.map P pOrder.toPreorder (Under X)
          (inferInstance : Category.{v} (Under X))
        oldDiagram M D E hDE) =
      @sameLabelLowerMap P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H D E hDE ≫ (finalIso E).hom := by
  let _ := finalOrder
  let _ : Preorder P := (finalOrder).toPreorder
  let k := @LowerSetColimitData.map P pOrder.toPreorder (Under X)
      (inferInstance : Category.{v} (Under X))
    oldDiagram M D E hDE
  apply ((finalData).isColimit (finalCarrier D)).hom_ext
  intro p
  have hOld := @LowerSetColimitData.ι_map P pOrder.toPreorder (Under X)
    (inferInstance : Category.{v} (Under X)) oldDiagram M D E hDE ⟨p.1, p.2⟩
  have hD := @sameLabelLowerIso_hom_fac P pOrder originalWellFounded C cCategory cColimits A s X O M
      chi (inferInstance : Fact chi.IsRegular)  H D p
  have hE := @sameLabelLowerIso_hom_fac P pOrder originalWellFounded C cCategory cColimits A s X O M
      chi (inferInstance : Fact chi.IsRegular)  H E ⟨p.1, hDE p.2⟩
  calc
    (finalData).ι (finalCarrier D) p ≫ ((finalIso D).hom ≫ k) =
      ((finalBeta).app p.1 ≫
        @LowerSetColimitData.ι P pOrder.toPreorder (Under X)
            (inferInstance : Category.{v} (Under X))
          oldDiagram M D ⟨p.1, p.2⟩) ≫ k :=
      ((Category.assoc _ _ _).symm).trans (congrArg (fun z => z ≫ k) hD)
    _ = (finalBeta).app p.1 ≫
        @LowerSetColimitData.ι P pOrder.toPreorder (Under X)
            (inferInstance : Category.{v} (Under X))
          oldDiagram M E ⟨p.1, hDE p.2⟩ :=
      (Category.assoc _ _ _).trans (congrArg (fun z => (finalBeta).app p.1 ≫ z) hOld)
    _ = (finalData).ι (finalCarrier D) p ≫
        ((finalData).map (fun _ h => hDE h) ≫ (finalIso E).hom) :=
      hE.symm.trans
        ((congrArg (fun z => z ≫ (finalIso E).hom)
          ((finalData).ι_map (show finalCarrier D ≤ finalCarrier E from fun _ h =>
              hDE h) p).symm).trans
          (Category.assoc _ _ _))

theorem sameLabelLowerIso_hom_eq_desc (D : LowerSet P) :
    letI := finalOrder
    letI : Preorder P := (finalOrder).toPreorder
    (finalIso D).hom = ((finalData).isColimit (finalCarrier D)).desc
      (@OriginalLowerComparisonCocone.cocone P P (finalOrder).toPreorder pOrder.toPreorder
        (Under X) (inferInstance : Category.{v} (Under X)) finalMap
        (@CellTree.diagram C cCategory P finalOrder A s X finalTree)
        oldDiagram finalBeta M D) := by
  let _ := finalOrder
  let _ : Preorder P := (finalOrder).toPreorder
  apply ((finalData).isColimit (finalCarrier D)).hom_ext
  intro p
  exact (@sameLabelLowerIso_hom_fac P pOrder originalWellFounded C cCategory cColimits A s X O M chi
      (inferInstance : Fact chi.IsRegular)  H D p).trans
    (((finalData).isColimit (finalCarrier D)).fac
      (@OriginalLowerComparisonCocone.cocone P P (finalOrder).toPreorder pOrder.toPreorder
        (Under X) (inferInstance : Category.{v} (Under X)) finalMap
        (@CellTree.diagram C cCategory P finalOrder A s X finalTree)
        oldDiagram finalBeta M D) p).symm

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P] [originalWellFounded : WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [cColimits : HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (H : CompleteRefiningHistory O M chi)

local notation "finalOrder" => @sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A
                                s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalTree" => @sameLabelTree P pOrder originalWellFounded C cCategory cColimits A s
                               X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalMap" => @sameLabelHom P pOrder originalWellFounded C cCategory cColimits A s X
                              O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalBeta" => @sameLabelComparison P pOrder originalWellFounded C cCategory
                               cColimits A s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalData" => @sameLabelLowerData P pOrder originalWellFounded C cCategory cColimits
                               A s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalCarrier" => @sameLabelLowerCarrier P pOrder originalWellFounded C cCategory
                                  cColimits A s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalIso" => @sameLabelLowerIso P pOrder originalWellFounded C cCategory cColimits A
                              s X O M chi (inferInstance : Fact chi.IsRegular)  H

theorem sameLabelLowerCarrier_top : finalCarrier (⊤ : LowerSet P) =
    (letI := finalOrder; (⊤ : LowerSet P)) := by
  apply SetLike.coe_injective
  apply Set.ext
  exact fun _ => Iff.rfl

/-- The actual history constructs sameLabelEndpointIso on the same original objects and labels. -/
def sameLabelEndpointIso :
    (@CellTree.endpointObj C cCategory P finalOrder A s X finalTree) ≅ O.endpointObj := by
  let tree := finalTree
  let N := finalData
  let oldEndpoint := O.endpointIso M
  let hTop := @sameLabelLowerCarrier_top P pOrder originalWellFounded C cCategory cColimits A s X O
      M chi (inferInstance : Fact chi.IsRegular)  H
  letI := finalOrder
  letI : Preorder P := (finalOrder).toPreorder
  exact (tree.endpointIso N).symm ≪≫ N.functor.mapIso (eqToIso hTop.symm) ≪≫
    finalIso ⊤ ≪≫ oldEndpoint

theorem sameLabelEndpoint_root :
    (@CellTree.hom C cCategory P finalOrder A s X finalTree) ≫
      (@sameLabelEndpointIso P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H).hom.right = O.hom :=
  Under.w (@sameLabelEndpointIso P pOrder originalWellFounded C cCategory cColimits A s X O M chi
      (inferInstance : Fact chi.IsRegular)  H).hom

theorem sameLabelEndpoint_inv_root :
    O.hom ≫
        (@sameLabelEndpointIso P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H).inv.right =
      (@CellTree.hom C cCategory P finalOrder A s X finalTree) :=
  Under.w (@sameLabelEndpointIso P pOrder originalWellFounded C cCategory cColimits A s X O M chi
      (inferInstance : Fact chi.IsRegular)  H).inv

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P] [originalWellFounded : WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [cColimits : HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (H : CompleteRefiningHistory O M chi)

local notation "finalOrder" => @sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A
                                s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalTree" => @sameLabelTree P pOrder originalWellFounded C cCategory cColimits A s
                               X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalMap" => @sameLabelHom P pOrder originalWellFounded C cCategory cColimits A s X
                              O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalBeta" => @sameLabelComparison P pOrder originalWellFounded C cCategory
                               cColimits A s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalData" => @sameLabelLowerData P pOrder originalWellFounded C cCategory cColimits
                               A s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalCarrier" => @sameLabelLowerCarrier P pOrder originalWellFounded C cCategory
                                  cColimits A s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalIso" => @sameLabelLowerIso P pOrder originalWellFounded C cCategory cColimits A
                              s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "endIso" => @sameLabelEndpointIso P pOrder originalWellFounded C cCategory cColimits
                            A s X O M chi (inferInstance : Fact chi.IsRegular)  H

theorem sameLabelEndpoint_fac (p : P) :
    letI := finalOrder
    letI : Preorder P := (finalOrder).toPreorder
    (@CellTree.inclusion C cCategory P finalOrder A s X finalTree p) ≫ (endIso).hom =
      (finalBeta).app p ≫ (@CellTree.inclusion C cCategory P pOrder A s X O p) := by
  let tree := finalTree
  let N := finalData
  let originalLeg := O.ι_endpointIso_hom M p
  let originalEnd := O.endpointIso M
  let hTop := @sameLabelLowerCarrier_top P pOrder originalWellFounded C cCategory cColimits A s X O
      M chi (inferInstance : Fact chi.IsRegular)  H
  let _ := finalOrder
  let _ : Preorder P := (finalOrder).toPreorder
  have hNew : tree.inclusion p ≫ (tree.endpointIso N).inv = N.ι ⊤ ⟨p, by trivial⟩ := by
    exact (congrArg (fun k => k ≫ (tree.endpointIso N).inv)
      (tree.ι_endpointIso_hom N p).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => N.ι ⊤ ⟨p, by trivial⟩ ≫ k)
          (tree.endpointIso N).hom_inv_id).trans (Category.comp_id _)))
  change tree.inclusion p ≫
    ((tree.endpointIso N).inv ≫ N.map (leOfHom (eqToHom hTop.symm)) ≫
      (finalIso ⊤).hom ≫ originalEnd.hom) = _
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hNew,
    N.ι_map,
        @sameLabelLowerIso_hom_fac P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H ⊤]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => (finalBeta).app p ≫ k) originalLeg)

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P] [originalWellFounded : WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [cColimits : HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (H : CompleteRefiningHistory O M chi)

theorem sameLabelTree_cell_square (p : P) :
    letI := @sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H
    letI : Preorder P :=
        (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H).toPreorder
    (@CellTree.cell C cCategory P
        (@sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H) A s X
          (@sameLabelTree P pOrder originalWellFounded C cCategory cColimits A s X O M chi
            (inferInstance : Fact chi.IsRegular)  H) p) ≫
      ((@sameLabelComparison P pOrder originalWellFounded C cCategory cColimits A s X O M chi
          (inferInstance : Fact chi.IsRegular)  H).app p).right ≍
          (@CellTree.cell C cCategory P pOrder A s X O p) := by
  let r := assemblyPrefix O M chi H
  exact assemblyPrefix_cell_squares O M chi H ((sameLabels (P := P)) p)

end

end CategoryTheory.SmallObject.OriginalGoodification

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

open TreeProjection

variable {P : Type w} [pOrder : PartialOrder P] [originalWellFounded : WellFoundedLT P]
  {C : Type u} [cCategory : Category.{v} C] [cColimits : HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]
  (H : CompleteRefiningHistory O M chi)

local notation "finalOrder" => @sameLabelOrder P pOrder originalWellFounded C cCategory cColimits A
                                s X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalTree" => @sameLabelTree P pOrder originalWellFounded C cCategory cColimits A s
                               X O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalMap" => @sameLabelHom P pOrder originalWellFounded C cCategory cColimits A s X
                              O M chi (inferInstance : Fact chi.IsRegular)  H
local notation "finalBeta" => @sameLabelComparison P pOrder originalWellFounded C cCategory
                               cColimits A s X O M chi (inferInstance : Fact chi.IsRegular)  H

theorem sameLabelHom_strict :
    @StrictMono P P (finalOrder).toPreorder pOrder.toPreorder finalMap := by
  let _ := finalOrder
  let _ : Preorder P := (finalOrder).toPreorder
  intro p q hpq
  exact @lt_of_le_of_ne P pOrder p q
    (@OrderHom.monotone' P P (finalOrder).toPreorder pOrder.toPreorder finalMap p q hpq.le)
    (ne_of_lt hpq)

/-- The actual history constructs sameLabelPredecessorComparison on the same original objects and
labels. -/
def sameLabelPredecessorComparison (p : P) :
    (@CellTree.predecessorObj C cCategory P finalOrder A s X finalTree p) ⟶ O.predecessorObj p :=
  @predecessorComparison P P pOrder finalOrder C cCategory A s X finalTree O finalMap
    (@sameLabelHom_strict P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H) finalBeta p

/-- Every actual new predecessor leg retains its original vertex component and original cofan
leg. -/
theorem sameLabelPredecessorComparison_fac (p : P)
    (z : letI := finalOrder
      letI : Preorder P := (finalOrder).toPreorder
      LowerSet.Iio p) :
    letI := finalOrder
    letI : Preorder P := (finalOrder).toPreorder
    ((finalTree).predecessor p).cocone.ι.app z ≫
        (@sameLabelPredecessorComparison P pOrder originalWellFounded C cCategory
          cColimits A s X O M chi (inferInstance : Fact chi.IsRegular) H p) =
      (finalBeta).app z.1 ≫
        (letI : PartialOrder P := pOrder
         letI : Preorder P := pOrder.toPreorder
         (O.predecessor p).cocone.ι.app
           ⟨z.1, @sameLabelHom_strict P pOrder originalWellFounded C cCategory cColimits
             A s X O M chi (inferInstance : Fact chi.IsRegular) H z.1 p z.2⟩) := by
  let _ := finalOrder
  let _ : Preorder P := (finalOrder).toPreorder
  exact @predecessorComparison_fac P P pOrder finalOrder C cCategory A s X finalTree O
    finalMap (@sameLabelHom_strict P pOrder originalWellFounded C cCategory cColimits
      A s X O M chi (inferInstance : Fact chi.IsRegular) H) finalBeta p z

theorem sameLabelTree_attaching_square (p : P) :
    (@CellTree.attaching C cCategory P finalOrder A s X finalTree p) ≫
      (@sameLabelPredecessorComparison P pOrder originalWellFounded C cCategory cColimits A s X O M
          chi (inferInstance : Fact chi.IsRegular)  H p).right ≍ O.attaching p := by
  let r := assemblyPrefix O M chi H
  let e : @OrderIso P (⊤ : @LowerSet P pOrder.toLE) (finalOrder).toLE r.ord.toLE :=
    @CellTreeLabelTransport.pulledIso (⊤ : @LowerSet P pOrder.toLE) P r.ord (sameLabels (P := P))
  have hPred := @predecessorComparison_orderTransport P (⊤ : @LowerSet P pOrder.toLE) P
    pOrder r.ord finalOrder C cCategory A s X r.tree O (prefixLabels ⊤ r.ord r.below)
    (prefixLabels_strict O M chi r) r.comparison e p
  have hAtt := @assemblyPrefix_attaching_squares P pOrder originalWellFounded C cCategory cColimits
      A s X O M chi (inferInstance : Fact chi.IsRegular)  H (e p)
  exact
      (heq_of_eq
        (congrArg
          (fun k =>
            (@CellTree.attaching C cCategory (⊤ : @LowerSet P pOrder.toLE) r.ord A s X r.tree
              (e p)) ≫ k.right) hPred)).trans hAtt

theorem sameLabelPredecessor_square (p : P) :
    letI := finalOrder
    letI : Preorder P := (finalOrder).toPreorder
    @sameLabelPredecessorComparison P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H p ≫
        (@CellTree.predecessorMap C cCategory P pOrder A s X O p) =
      (finalTree).predecessorMap p ≫ (finalBeta).app p :=
  @predecessorComparison_square P P pOrder finalOrder C cCategory A s X finalTree O finalMap
    (@sameLabelHom_strict P pOrder originalWellFounded C cCategory cColimits A s X O M chi
        (inferInstance : Fact chi.IsRegular)  H) finalBeta p

theorem sameLabelPredecessor_root (p : P) :
    (@CellTree.predecessorObj C cCategory P finalOrder A s X finalTree p).hom ≫
      (@sameLabelPredecessorComparison P pOrder originalWellFounded C cCategory cColimits A s X O M
          chi (inferInstance : Fact chi.IsRegular)  H p).right = (O.predecessorObj p).hom :=
  Under.w _

end

end CategoryTheory.SmallObject.OriginalGoodification
