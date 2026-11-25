/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCapturedCellVertexMap
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLocalizedCellExtension

/-!
# Actual natural original-vertex comparisons for localized extensions

The new vertex map and every old comparison assemble into the actual
whole natural transformation to the original cell-vertex diagram.
The original lower cofan and predecessor descenders prove each mixed
old/new naturality square. The prior comparison is reused; the extended
comparison is constructed from these actual source maps.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalCellExtensionComparison

open Limits LowerSetColimits GoodCellExtensionOrder GoodCellExtensionDiagram
  GoodCellExtensionTree OriginalPredecessorCellCapture OriginalCellVertexLowerComparison
  OriginalCapturedCellVertexMap

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

/-- The actual original-label order homomorphism for the constructed extension. -/
def labelOrderHom :
    letI := extensionOrder (capture G L O t B chi good g).support
    GoodCellExtensionOrder.Index Q →o P := by
  letI := extensionOrder (capture G L O t B chi good g).support
  exact {
    toFun := OriginalLocalizedCellExtension.labels f t
    monotone' := OriginalLocalizedCellExtension.refining G L B (O.label t) g chi good
      f t f.monotone hPred }

/-- Every actual mixed old/new comparison keeps its original cell-predecessor factor equation. -/
theorem oldNew_factor (q : (capture G L O t B chi good g).support) :
    (L.ι (capture G L O t B chi good g).support q ≫
      newStep G L (capture G L O t B chi good g).support (O.label t)
        (capture G L O t B chi good g).attaching) ≫
      newVertexMap G L O f beta t B hPred chi good g hOriginal =
    beta.app q.1 ≫ O.diagram.map
      (homOfLE (hPred q.1 ((capture G L O t B chi good g).below q.2)).le) := by
  rw [Category.assoc, newVertexMap_step, ← Category.assoc]
  have hLower := lowerMap_fac G L O f beta t
    (capture G L O t B chi good g).support
    (fun q hq => hPred q ((capture G L O t B chi good g).below hq)) q
  change L.ι (capture G L O t B chi good g).support q ≫
      capturedPredMap G L O f beta t B hPred chi good g = _ at hLower
  rw [hLower, Category.assoc, O.predecessorMap_fac]

/-- The actual original whole vertex-map function retains every old map and the new pushout map. -/
def component :
    letI := extensionOrder (capture G L O t B chi good g).support
    ∀ x : GoodCellExtensionOrder.Index Q,
      (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).vertex x ⟶
        O.vertex (labelOrderHom G L O f t B hPred chi good g x) := by
  letI := extensionOrder (capture G L O t B chi good g).support
  rintro ⟨x⟩
  cases x with
  | some q => exact beta.app q
  | none => exact newVertexMap G L O f beta t B hPred chi good g hOriginal

/-- All actual original extension comparisons satisfy their complete naturality squares. -/
theorem component_naturality :
    letI := extensionOrder (capture G L O t B chi good g).support
    ∀ (x y : GoodCellExtensionOrder.Index Q) (h : x ⟶ y),
      (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram.map h ≫
        component G L O f beta t B hPred chi good g hOriginal y =
      component G L O f beta t B hPred chi good g hOriginal x ≫
        O.diagram.map ((labelOrderHom G L O f t B hPred chi good g).monotone.functor.map h) := by
  let : PartialOrder (GoodCellExtensionOrder.Index Q) :=
    extensionOrder (capture G L O t B chi good g).support
  rintro ⟨x⟩ ⟨y⟩ h
  cases x with
  | none =>
    cases y with
    | some y => exact False.elim (leOfHom h)
    | none =>
      change 𝟙 _ ≫ newVertexMap G L O f beta t B hPred chi good g hOriginal =
        newVertexMap G L O f beta t B hPred chi good g hOriginal ≫ O.diagram.map (𝟙 t)
      rw [O.diagram.map_id, Category.id_comp, Category.comp_id]
  | some x =>
    cases y with
    | some y =>
      have hxy : x ≤ y := leOfHom h
      exact beta.naturality (homOfLE hxy)
    | none =>
      have hx : x ∈ (capture G L O t B chi good g).support := leOfHom h
      exact oldNew_factor G L O f beta t B hPred chi good g hOriginal ⟨x, hx⟩

/-- The complete actual natural comparison extends the original old vertex comparison. -/
def comparison :
    letI := extensionOrder (capture G L O t B chi good g).support
    (OriginalLocalizedCellExtension.tree G L B (O.label t) g chi good).diagram ⟶
      (labelOrderHom G L O f t B hPred chi good g).monotone.functor ⋙ O.diagram := by
  letI := extensionOrder (capture G L O t B chi good g).support
  exact {
    app := component G L O f beta t B hPred chi good g hOriginal
    naturality := fun {x y} h =>
      component_naturality G L O f beta t B hPred chi good g hOriginal x y h }

end CategoryTheory.SmallObject.OriginalCellExtensionComparison
