/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCoordinateBoundary
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SubcomplexFunctor

/-!
# The full original marked coordinate-boundary colimit

Both original faces of every tail coordinate and their actual full
intersections form the native subcomplex multicoequalizer diagram.
It has exactly the whole original coordinate-boundary colimit. Every
original marked edge lies on its supplied face and retains its original
maximum-preserving mark there, so the same cocone is a true marked
colimit rather than only an underlying or core comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- Every original tail coordinate has its two actual original face labels. -/
abbrev ConeCoordinateFaceIndex {n : ℕ} (i : Vertex.{u} n) :=
  {j : Vertex.{u} n // i < j} × Bool

/-- The actual whole original coordinate face, with its original vertex label and membership value retained. -/
def coneCoordinateFaceAt {n : ℕ} (i : Vertex.{u} n) (j : ConeCoordinateFaceIndex i) :
    (nerve (ConeSubset i)).Subcomplex := coneCoordinateFace i j.1.val j.2

/-- Both original coordinate faces and every actual full intersection present precisely the whole original
coordinate boundary. -/
theorem coneCoordinateBoundaryDiagram {n : ℕ} (i : Vertex.{u} n) :
    Subcomplex.MulticoequalizerDiagram (coneCoordinateBoundary i)
      (coneCoordinateFaceAt i) (fun j k => coneCoordinateFaceAt i j ⊓ coneCoordinateFaceAt i k) where
  iSup_eq := iSup_prod
  eq_inf _ _ := rfl

/-- The whole original underlying coordinate-face/intersection cocone is genuinely colimiting. -/
def coneCoordinateBoundaryIsColimit {n : ℕ} (i : Vertex.{u} n) :
    IsColimit ((coneCoordinateBoundaryDiagram i).multicofork.map Subcomplex.toSSetFunctor) :=
  (coneCoordinateBoundaryDiagram i).isColimit

/-- The same actual full coordinate-face/intersection cocone is a genuine marked colimit, preserving all original
maximum-preserving marked edges. -/
def coneCoordinateBoundaryMarkedIsColimit {n : ℕ} (i : Vertex.{u} n) :
    IsColimit ((coneCoordinateBoundaryDiagram i).multicofork.map (subcomplexFunctor (coneWeight i))) := by
  apply isColimitOfUnderlyingMarking
  · exact (Multicofork.isColimitMapEquiv _ forget).symm (coneCoordinateBoundaryIsColimit i)
  · intro e he
    obtain ⟨j, ε, h⟩ := (mem_coneCoordinateBoundary_iff i e.val).mp e.property
    let s : ConeCoordinateFaceIndex i := (j, ε)
    let a : (coneCoordinateFaceAt i s : SSet.{u}) _⦋1⦌ := ⟨e.val, h⟩
    exact ⟨.right s, a, he, rfl⟩

end SSet.Marked.CoherentWeight
