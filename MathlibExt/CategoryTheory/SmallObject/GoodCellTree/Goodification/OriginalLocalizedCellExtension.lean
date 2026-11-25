/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalPredecessorCellCapture
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionTree

/-!
# Genuine original-predecessor localized cell extensions

Compactness captures the attaching source inside the given original
predecessor lower subset. The resulting complete tree uses that actual
support. Its new comparisons refine the original cell-label precedence
through the same original label function, and its endpoint retains the
original attaching map into the same old whole endpoint.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalLocalizedCellExtension

open Limits LowerSetColimits GoodCellExtensionOrder GoodCellExtensionDiagram
  GoodCellExtensionTree OriginalPredecessorCellCapture

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {Q P : Type w} [PartialOrder Q] [PartialOrder P]
  {A : Type t} {s : A → Arrow C} {X : C}
  (T : CellTree s X (P := Q)) (L : LowerSetColimitData T.diagram)
  (B : LowerSet Q) (i : A) (g : (s i).left ⟶ (L.obj B).right)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  [IsCardinalPresentable (s i).left chi] [IsCardinalPresentable (s i).right chi]
  (good : T.IsGood chi)

/-- The actual localized captured support, retaining the original predecessor constraint. -/
abbrev capture := localCapture T L B i g chi good

/-- The complete actual extension tree uses only the internally captured original support. -/
def tree :
    letI := extensionOrder (capture T L B i g chi good).support
    CellTree s X (P := GoodCellExtensionOrder.Index Q) := by
  letI := extensionOrder (capture T L B i g chi good).support
  exact extensionTree T L (capture T L B i g chi good).support i
    (capture T L B i g chi good).attaching

/-- The actual captured support bound gives the whole localized extension its local goodness. -/
theorem tree_good :
    letI := extensionOrder (capture T L B i g chi good).support
    (tree T L B i g chi good).IsGood chi := by
  let : PartialOrder (GoodCellExtensionOrder.Index Q) :=
    extensionOrder (capture T L B i g chi good).support
  exact extensionTree_good T L (capture T L B i g chi good).support i
    (capture T L B i g chi good).attaching chi good (capture T L B i g chi good).bound

omit [HasPushouts C] [IsCardinalPresentable (s i).right chi] in
/-- Both actual lower-comparison paths retain the original whole-endpoint attaching map. -/
theorem globalAttaching_original :
    globalAttaching T L (capture T L B i g chi good).support i
        (capture T L B i g chi good).attaching =
      g ≫ (lowerToEndpoint T L B).right := by
  let E := capture T L B i g chi good
  have hMaps : lowerToEndpoint T L E.support = L.map E.below ≫ lowerToEndpoint T L B := by
    change L.map (le_top : E.support ≤ ⊤) ≫ (T.endpointIso L).hom =
      L.map E.below ≫ (L.map (le_top : B ≤ ⊤) ≫ (T.endpointIso L).hom)
    rw [← Category.assoc, L.map_comp]
  change E.attaching ≫ (lowerToEndpoint T L E.support).right =
    g ≫ (lowerToEndpoint T L B).right
  rw [hMaps]
  change E.attaching ≫ ((L.map E.below).right ≫ (lowerToEndpoint T L B).right) = _
  rw [← Category.assoc, E.factor]

/-- The complete localized tree retains its original rooted attaching-map endpoint comparison. -/
def presentation :
    letI := extensionOrder (capture T L B i g chi good).support
    CellTree.Presentation (s := s) (P := GoodCellExtensionOrder.Index Q)
      (T.hom ≫ pushout.inl (g ≫ (lowerToEndpoint T L B).right) (s i).hom) := by
  letI := extensionOrder (capture T L B i g chi good).support
  exact {
    tree := tree T L B i g chi good
    endpointIso := eqToIso (congrArg
      (fun h => Under.mk (T.hom ≫ pushout.inl h (s i).hom))
      (globalAttaching_original T L B i g chi good)) }

variable (f : Q → P) (next : P) (hMono : Monotone f)
  (hPred : ∀ q : Q, q ∈ B → f q < next)

/-- The complete old/new original-label function is literal. -/
def labels (x : GoodCellExtensionOrder.Index Q) : P :=
  match x.val with
  | some q => f q
  | none => next

include hMono hPred in
omit [HasPushouts C] [IsCardinalPresentable (s i).right chi] in
/-- Every actual localized new comparison refines the same original label precedence. -/
theorem refining :
    letI := extensionOrder (capture T L B i g chi good).support
    Monotone (labels f next) := by
  let : PartialOrder (GoodCellExtensionOrder.Index Q) :=
    extensionOrder (capture T L B i g chi good).support
  rintro ⟨x⟩ ⟨y⟩ h
  cases x with
  | none =>
    cases y with
    | none => exact le_rfl
    | some y => exact False.elim h
  | some x =>
    cases y with
    | some y => exact hMono h
    | none => exact (hPred x ((capture T L B i g chi good).below h)).le

end CategoryTheory.SmallObject.OriginalLocalizedCellExtension
