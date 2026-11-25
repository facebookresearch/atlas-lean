/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCellExtensionComparison

/-!
# Whole original-cell refinement infrastructure owner

The owner retains actual original lower-choice/capture functions,
localized complete trees, original vertex maps and the constructed
extended natural comparison. Full recursive/limit goodification,
retract removal and objectwise diagram saturation remain separate work.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace MathlibExtTest.OriginalCellRefinement

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.CategoryTheory.SmallObject
open _root_.CategoryTheory.SmallObject.GoodCellExtensionOrder
open _root_.CategoryTheory.SmallObject.GoodCellExtensionDiagram
open _root_.CategoryTheory.SmallObject.OriginalPredecessorCellCapture
open _root_.CategoryTheory.SmallObject.OriginalCellVertexLowerComparison
open _root_.CategoryTheory.SmallObject.OriginalCapturedCellVertexMap
open _root_.CategoryTheory.SmallObject.OriginalCellExtensionComparison

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {Q P : Type w} [PartialOrder Q] [PartialOrder P]
  {A : Type t} {s : A → Arrow C} {X : C}
  (G : CellTree s X (P := Q)) (L : LowerSetColimitData G.diagram)
  (O : CellTree s X (P := P)) (f : Q →o P)
  (beta : G.diagram ⟶ f.monotone.functor ⋙ O.diagram)
  (t : P) (B : LowerSet Q) (hPred : ∀ q : Q, q ∈ B → f q < t)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  [IsCardinalPresentable (s (O.label t)).left chi] (good : G.IsGood chi)
  (g : (s (O.label t)).left ⟶ (L.obj B).right)
  (hOriginal : g ≫ (lowerMap G L O f beta t B hPred).right = O.attaching t)

/-- The entire actual localized tree uses only the internally captured original support. -/
def wholeOriginalLocalizedTree :
    letI := extensionOrder (capture G L O t B chi good g).support
    CellTree s X (P := GoodCellExtensionOrder.Index Q) :=
  OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good

/-- The actual complete original new-vertex comparison map is retained literally. -/
def wholeOriginalNewVertexMap :
    newPoint G L (capture G L O t B chi good g).support (O.label t)
      (capture G L O t B chi good g).attaching ⟶ O.vertex t :=
  newVertexMap G L O f beta t B hPred chi good g hOriginal

/-- The entire original extended comparison is the actually constructed natural transformation. -/
def wholeOriginalComparison :
    letI := extensionOrder (capture G L O t B chi good g).support
    (wholeOriginalLocalizedTree G L O t B chi good g).diagram ⟶
      (labelOrderHom G L O f t B hPred chi good g).monotone.functor ⋙ O.diagram :=
  comparison G L O f beta t B hPred chi good g hOriginal

/-- The whole actual comparison-component function retains every actual original vertex map. -/
theorem whole_original_comparison_components :
    letI := extensionOrder (capture G L O t B chi good g).support
    (wholeOriginalComparison G L O f beta t B hPred chi good g hOriginal).app =
      component G L O f beta t B hPred chi good g hOriginal := rfl

include hOriginal in
omit [HasPushouts C] in
/-- The actual compact-source lower factor retains its full original attaching equation. -/
theorem whole_original_attaching_square :
    (capture G L O t B chi good g).attaching ≫
      (capturedPredMap G L O f beta t B hPred chi good g).right = O.attaching t :=
  capturedPredMap_attaching G L O f beta t B hPred chi good g hOriginal

/-- Every whole actual new-cell map lands in the same original attaching-family cell inclusion. -/
theorem whole_original_new_cell_map :
    newCell G L (capture G L O t B chi good g).support (O.label t)
        (capture G L O t B chi good g).attaching ≫
      (wholeOriginalNewVertexMap G L O f beta t B hPred chi good g hOriginal).right = O.cell t :=
  newVertexMap_cell G L O f beta t B hPred chi good g hOriginal

omit [HasPushouts C] in
/-- The real internally captured support lies in the original predecessor lower subset. -/
theorem whole_original_support_below :
    (capture G L O t B chi good g).support ≤ B :=
  (capture G L O t B chi good g).below

omit [HasPushouts C] in
/-- The actual support bound is the internally derived compact-source capture bound. -/
theorem whole_original_support_bound :
    HasCardinalLT (capture G L O t B chi good g).support chi :=
  (capture G L O t B chi good g).bound

end MathlibExtTest.OriginalCellRefinement
