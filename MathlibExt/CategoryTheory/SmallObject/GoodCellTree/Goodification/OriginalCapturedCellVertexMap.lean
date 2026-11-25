/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCellVertexLowerComparison
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionDiagram
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalPredecessorCellCapture

/-!
# Actual original vertex maps for localized captured extensions

The old actual vertex comparison determines the original predecessor
descender. Internal local capture retains the original attaching square.
The actual local pushout then constructs the new vertex map into the
original cell vertex, with both original lower and cell factor equations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalCapturedCellVertexMap

open Limits LowerSetColimits GoodCellExtensionOrder GoodCellExtensionDiagram
  OriginalPredecessorCellCapture OriginalCellVertexLowerComparison

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

/-- The actual original-predecessor localized compact-source capture. -/
abbrev capture := localCapture G L B (O.label t) g chi good

/-- The full original predecessor descender on the actual captured support. -/
def capturedPredMap : L.obj (capture G L O t B chi good g).support ⟶ O.predecessorObj t :=
  lowerMap G L O f beta t (capture G L O t B chi good g).support
    (fun q hq => hPred q ((capture G L O t B chi good g).below hq))

include hOriginal in
omit [HasPushouts C] in
/-- Internal source capture recovers the same actual original attaching square. -/
theorem capturedPredMap_attaching :
    (capture G L O t B chi good g).attaching ≫
        (capturedPredMap G L O f beta t B hPred chi good g).right = O.attaching t := by
  let E := capture G L O t B chi good g
  have hMaps := lowerMap_inclusion G L O f beta t B hPred E.support E.below
  change E.attaching ≫ (lowerMap G L O f beta t E.support
    (fun q hq => hPred q (E.below hq))).right = _
  rw [← hMaps]
  change E.attaching ≫ ((L.map E.below).right ≫
    (lowerMap G L O f beta t B hPred).right) = _
  rw [← Category.assoc, E.factor]
  exact hOriginal

/-- The actual new vertex map is the local pushout descender into the original cell vertex. -/
def newVertexMap :
    newPoint G L (capture G L O t B chi good g).support (O.label t)
      (capture G L O t B chi good g).attaching ⟶ O.vertex t :=
  Under.homMk
    (pushout.desc
      ((capturedPredMap G L O f beta t B hPred chi good g).right ≫ (O.predecessorMap t).right)
      (O.cell t) (by
        rw [← Category.assoc, capturedPredMap_attaching G L O f beta t B hPred chi good g hOriginal]
        exact O.attaching_square t))
    (by
      change ((L.obj (capture G L O t B chi good g).support).hom ≫
        pushout.inl (capture G L O t B chi good g).attaching (s (O.label t)).hom) ≫ _ =
          (O.vertex t).hom
      rw [Category.assoc, pushout.inl_desc, ← Category.assoc, Under.w]
      exact O.root_predecessorMap t)

/-- The actual selected lower-to-new-vertex map retains its original predecessor factor equation. -/
theorem newVertexMap_step :
    newStep G L (capture G L O t B chi good g).support (O.label t)
        (capture G L O t B chi good g).attaching ≫
      newVertexMap G L O f beta t B hPred chi good g hOriginal =
        capturedPredMap G L O f beta t B hPred chi good g ≫ O.predecessorMap t := by
  apply Under.UnderMorphism.ext
  exact pushout.inl_desc _ _ _

/-- The complete new cell-target map lands in its original cell-target inclusion. -/
@[reassoc]
theorem newVertexMap_cell :
    newCell G L (capture G L O t B chi good g).support (O.label t)
        (capture G L O t B chi good g).attaching ≫
      (newVertexMap G L O f beta t B hPred chi good g hOriginal).right = O.cell t :=
  pushout.inr_desc _ _ _

end CategoryTheory.SmallObject.OriginalCapturedCellVertexMap
