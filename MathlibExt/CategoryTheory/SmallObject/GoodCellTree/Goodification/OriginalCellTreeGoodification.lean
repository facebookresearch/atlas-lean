/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalGoodificationComparison

/-!
# Complete original cell-tree goodification

Original compact-cell geometry constructs the entire refining history and all its comparisons.
The resulting goodification keeps the same P, original labels, arbitrary root and whole arrow.
Every original lower subset, predecessor cofan and attaching/cell/vertex square is retained.
No completed history, goodification or endpoint isomorphism is an input to the producer.
-/

@[expose] public section

set_option autoImplicit false

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

namespace CategoryTheory.SmallObject.OriginalGoodification

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P]
  {C : Type u} [cCategory : Category.{v} C] {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- A produced goodification stores the actual constructed local histories; all global data is
derived. -/
structure CellTreeGoodification where
  /-- The actual complete history on original labels, using the original tree's well-foundedness. -/
  history : letI : WellFoundedLT P := O.wellFoundedLT
    CompleteRefiningHistory O M chi

variable [HasPushouts C] [IsCardinalLocallyPresentable C chi]
  (hSource : ∀ p : P, IsCardinalPresentable (s (O.label p)).left chi)
  (hTarget : ∀ p : P, IsCardinalPresentable (s (O.label p)).right chi)

/-- The original cell tree and compact cell ends construct its complete goodification. -/
def cellTreeGoodification : CellTreeGoodification O M chi := by
  letI : WellFoundedLT P := O.wellFoundedLT
  exact ⟨constructedRefiningHistory O M chi hSource hTarget⟩

include hSource hTarget in
/-- A goodification of `O` exists for these inputs alone: a cell tree `O` on
the carrier `P`, chosen lower-set colimit data `M` for `O.diagram`, a regular
cardinal `chi`, pushouts in `C`, `chi`-local presentability of `C`, and
`chi`-presentability of both endpoints `(s (O.label p)).left` and
`(s (O.label p)).right` of the label arrow of every vertex `p`. Neither a
compact root, nor a bound on the original vertex carrier, nor an already built
refining history is required: the witness is `cellTreeGoodification`, whose
history is constructed from those inputs. -/
theorem exists_cellTreeGoodification : Nonempty (CellTreeGoodification O M chi) :=
  ⟨cellTreeGoodification O M chi hSource hTarget⟩

end

noncomputable section

variable {P : Type w} [pOrder : PartialOrder P]
  {C : Type u} [cCategory : Category.{v} C] [cColimits : HasColimitsOfSize.{w, w} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (O : CellTree s X (P := P)) (M : LowerSetColimitData O.diagram)
  (chi : Cardinal.{w}) [regular : Fact chi.IsRegular]
  (G : CellTreeGoodification O M chi)

/-- The refining partial order the goodification puts on the same carrier `P`.

Refining deletes comparabilities: `p ≤ q` in this order implies `p ≤ q` in the
original order of `O` (`sameLabelOrder_below`), equivalently the identity
function on `P` is monotone from this order to the original one
(`sameLabelHom`, whose value at `p` is `p`). The converse implication is not
claimed, the two orders are not asserted equivalent, and this is not a freedom
to extend or refine a partial order arbitrarily. -/
abbrev CellTreeGoodification.order := @sameLabelOrder P pOrder
    (O.wellFoundedLT) C cCategory cColimits A s X O M chi regular G.history

/-- The produced goodification exposes the actual good tree under the SAME arbitrary original
root. -/
abbrev CellTreeGoodification.tree := @sameLabelTree P pOrder
    (O.wellFoundedLT) C cCategory cColimits A s X O M chi regular G.history

/-- The produced goodification exposes the actual identity function on the SAME original labels. -/
abbrev CellTreeGoodification.labelHom :=
    @sameLabelHom P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi regular G.history

/-- The produced goodification exposes the complete actual original natural vertex comparison. -/
abbrev CellTreeGoodification.comparison :=
    @sameLabelComparison P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi
    regular G.history

/-- The produced goodification exposes the actual chosen new lower-colimit data. -/
abbrev CellTreeGoodification.lowerData :=
    @sameLabelLowerData P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi
    regular G.history

/-- The produced goodification exposes both actual endpoint maps under the SAME original root. -/
abbrev CellTreeGoodification.endpointIso :=
    @sameLabelEndpointIso P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi
    regular G.history

/-- The produced goodification retains the complete actual original lowerCarrier data. -/
abbrev CellTreeGoodification.lowerCarrier (D : LowerSet P) :=
    @sameLabelLowerCarrier P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi
    regular G.history D

/-- The produced goodification retains the complete actual original lowerIso data. -/
abbrev CellTreeGoodification.lowerIso (D : LowerSet P) :=
    @sameLabelLowerIso P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi
    regular G.history D

/-- The produced goodification retains the complete actual original predecessorComparison data. -/
abbrev CellTreeGoodification.predecessorComparison (p : P) :=
    @sameLabelPredecessorComparison P pOrder
    (O.wellFoundedLT) C cCategory cColimits A s X O M chi regular G.history p

local notation "outOrder" => @CellTreeGoodification.order P pOrder C cCategory cColimits A s X O M
                              chi regular G
local notation "outTree" => @CellTreeGoodification.tree P pOrder C cCategory cColimits A s X O M
                             chi regular G
local notation "outBeta" => @CellTreeGoodification.comparison P pOrder C cCategory cColimits A s X O
                             M chi regular G
local notation "outEndpoint" => @CellTreeGoodification.endpointIso P pOrder C cCategory cColimits A
                                 s X O M chi regular G
local notation "outPred" => @CellTreeGoodification.predecessorComparison P pOrder C cCategory
                             cColimits A s X O M chi regular G

/-- The actual produced same-carrier tree is genuinely good at the original rank. -/
theorem CellTreeGoodification.good :
    @CellTree.IsGood C cCategory P outOrder A s X outTree chi regular :=
  @sameLabelTree_good P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi
      regular G.history

/-- Every literal original attaching-cell label is retained. -/
theorem CellTreeGoodification.labels (p : P) :
    @CellTree.label C cCategory P outOrder A s X outTree p = O.label p :=
  @sameLabelTree_labels P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi
      regular G.history p

/-- The actual endpoint comparison retains the original source arrow. -/
theorem CellTreeGoodification.root :
    @CellTree.hom C cCategory P outOrder A s X outTree ≫ (outEndpoint).hom.right = O.hom :=
  @sameLabelEndpoint_root P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi
      regular G.history

/-- The actual inverse endpoint comparison retains the original source arrow. -/
theorem CellTreeGoodification.inv_root :
    O.hom ≫ (outEndpoint).inv.right = @CellTree.hom C cCategory P outOrder A s X outTree :=
  @sameLabelEndpoint_inv_root P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi
      regular G.history

/-- The original attaching map is retained at the actual predecessor object. -/
theorem CellTreeGoodification.attaching_square (p : P) :
    @CellTree.attaching C cCategory P outOrder A s X outTree p ≫ (outPred p).right ≍
      O.attaching p :=
  @sameLabelTree_attaching_square P pOrder
      (O.wellFoundedLT) C cCategory cColimits A s X O M chi regular G.history p

/-- The actual original cell-target map is retained by the full vertex comparison. -/
theorem CellTreeGoodification.cell_square (p : P) :
    letI := outOrder
    letI : Preorder P := (outOrder).toPreorder
    @CellTree.cell C cCategory P outOrder A s X outTree p ≫ ((outBeta).app p).right ≍
      @CellTree.cell C cCategory P pOrder A s X O p :=
  @sameLabelTree_cell_square P pOrder (O.wellFoundedLT) C cCategory cColimits A s X O M chi
      regular G.history p

end

end CategoryTheory.SmallObject.OriginalGoodification
