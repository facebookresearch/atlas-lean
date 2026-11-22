/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedTopMarkedCylinder
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkedTensorEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalizationEnrichment

/-!
# The original top-marking pushout of whole enriched diagrams

The entire coefficient cylinder and its original maximally marked top
copy form an actual pushout in the category of marked enriched diagrams.
The universal map preserves every original Hom prism, not just the
underlying ordinary naturality squares. All coefficient objects,
selected marks and the minimal interval remain the original ones.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable {C : Type v} [EnrichedCategory SSet.{u} C]

/-- The original top endpoint includes into the full enriched minimal-interval tensor. -/
def enrichedDiagramCylinderTop (F : EnrichedDiagram C) :
    F ⟶ (enrichedDiagramMarkedTensor C (min (Δ[1] : SSet.{u}))).obj F where
  app x := markedCylinderTop (F.obj x) ≫
    (prodSwapIso (F.obj x) (min (Δ[1] : SSet.{u}))).hom
  naturality x y := by
    ext n h
    apply Hom.ext
    rfl

/-- The original minimal cylinder includes into its actual top-marking upgrade with the native coordinate swap. -/
def enrichedDiagramTopCylinderInl (F : EnrichedDiagram C) :
    (enrichedDiagramMarkedTensor C (min (Δ[1] : SSet.{u}))).obj F ⟶
      (enrichedDiagramTopMarkedCylinder C).obj F where
  app x := (prodSwapIso (min (Δ[1] : SSet.{u})) (F.obj x)).hom ≫
    topMarkedCylinderInl (F.obj x)
  naturality x y := by
    ext n h
    apply Hom.ext
    rfl

/-- The entire original maximally marked top diagram includes by the original interval endpoint. -/
def enrichedDiagramTopCylinderInr (F : EnrichedDiagram C) :
    maximalizedDiagram F ⟶ (enrichedDiagramTopMarkedCylinder C).obj F where
  app x := topMarkedCylinderInr (F.obj x)
  naturality x y := by
    ext n h
    apply Hom.ext
    rfl

/-- The two whole original top maps agree as enriched natural marked maps. -/
theorem enrichedDiagramTopCylinder_condition (F : EnrichedDiagram C) :
    enrichedDiagramCylinderTop F ≫ enrichedDiagramTopCylinderInl F =
      diagramMaximalization F ≫ enrichedDiagramTopCylinderInr F := by
  apply EnrichedDiagramMap.ext
  funext x
  exact Hom.ext rfl

/-- An actual commuting enriched square descends to the top-marked cylinder with all original Hom naturality
  retained. -/
def enrichedDiagramTopCylinderDesc {F Y : EnrichedDiagram C}
    (f : (enrichedDiagramMarkedTensor C (min (Δ[1] : SSet.{u}))).obj F ⟶ Y)
    (g : maximalizedDiagram F ⟶ Y)
    (hw : enrichedDiagramCylinderTop F ≫ f = diagramMaximalization F ≫ g) :
    (enrichedDiagramTopMarkedCylinder C).obj F ⟶ Y where
  app x := topMarkedCylinderDesc
    ((prodSwapIso (F.obj x) (min (Δ[1] : SSet.{u}))).hom ≫ f.app x)
    (g.app x) (by
      have h := congrArg (fun a : F ⟶ Y => a.app x) hw
      exact (Category.assoc _ _ _).symm.trans h)
  naturality x y := by
    ext n h
    apply Hom.ext
    ext q z
    have hn := congr($(f.naturality x y).app n h)
    exact congrArg (fun a => a.hom.app q (z.1, (z.2.2, z.2.1))) hn

/-- The complete original minimal cylinder map factors through the enriched descent. -/
theorem enrichedDiagramTopCylinderDesc_inl {F Y : EnrichedDiagram C}
    (f : (enrichedDiagramMarkedTensor C (min (Δ[1] : SSet.{u}))).obj F ⟶ Y)
    (g : maximalizedDiagram F ⟶ Y)
    (hw : enrichedDiagramCylinderTop F ≫ f = diagramMaximalization F ≫ g) :
    enrichedDiagramTopCylinderInl F ≫ enrichedDiagramTopCylinderDesc f g hw = f := by
  apply EnrichedDiagramMap.ext
  funext x
  exact Hom.ext rfl

/-- The whole original top copy has its exact enriched descent equation. -/
theorem enrichedDiagramTopCylinderDesc_inr {F Y : EnrichedDiagram C}
    (f : (enrichedDiagramMarkedTensor C (min (Δ[1] : SSet.{u}))).obj F ⟶ Y)
    (g : maximalizedDiagram F ⟶ Y)
    (hw : enrichedDiagramCylinderTop F ≫ f = diagramMaximalization F ≫ g) :
    enrichedDiagramTopCylinderInr F ≫ enrichedDiagramTopCylinderDesc f g hw = g := by
  apply EnrichedDiagramMap.ext
  funext x
  exact topMarkedCylinderDesc_inr
    ((prodSwapIso (F.obj x) (min (Δ[1] : SSet.{u}))).hom ≫ f.app x)
    (g.app x) (by
      have h := congrArg (fun a : F ⟶ Y => a.app x) hw
      exact (Category.assoc _ _ _).symm.trans h)

/-- The actual top-marked cylinder is the genuine pushout in the category of whole enriched marked diagrams. -/
def enrichedDiagramTopCylinderIsColimit (F : EnrichedDiagram C) :
    IsColimit (PushoutCocone.mk (enrichedDiagramTopCylinderInl F)
      (enrichedDiagramTopCylinderInr F) (enrichedDiagramTopCylinder_condition F)) :=
  PushoutCocone.IsColimit.mk (enrichedDiagramTopCylinder_condition F)
    (fun s => enrichedDiagramTopCylinderDesc s.inl s.inr s.condition)
    (fun s => enrichedDiagramTopCylinderDesc_inl s.inl s.inr s.condition)
    (fun s => enrichedDiagramTopCylinderDesc_inr s.inl s.inr s.condition)
    (fun s m h _ => by
      apply EnrichedDiagramMap.ext
      funext x
      apply Hom.ext
      ext q z
      have hx := congrArg (fun a => (a.app x).hom.app q (z.2, z.1)) h
      exact hx)

end SSet.Marked
