/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeUpperPairMaps
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SubcomplexFunctor

/-!
# Whole marked upper faces for an original ordered vertex family

The upper faces at the designated original vertices, together with
their actual intersections, present their union. Each marked edge of
the union already lies in a single original marked face. This proves
the whole marked colimit without a change to any original marking.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

variable {n : ℕ} {ι : Type v} [LinearOrder ι] (e : ι →o Vertex.{u} n) (i : Vertex.{u} n)

/-- The actual upper face at a designated original vertex. -/
def coneVertexUpperFace (j : ι) : (nerve (ConeSubset i)).Subcomplex := coneCoordinateFace i (e j) true

/-- The full union of these same original upper faces. -/
def coneVertexUpperSupport : (nerve (ConeSubset i)).Subcomplex := ⨆ j : ι, coneVertexUpperFace e i j

/-- The original upper faces and their actual pairwise intersections give the native union multicoequalizer. -/
theorem coneVertexUpperDiagram :
    Subcomplex.MulticoequalizerDiagram (coneVertexUpperSupport e i)
      (coneVertexUpperFace e i) (fun j k => coneVertexUpperFace e i j ⊓ coneVertexUpperFace e i k) where
  iSup_eq := rfl
  eq_inf _ _ := rfl

/-- The entire ordered upper-face diagram retains exactly its original two marked intersection inclusions. -/
def coneVertexUpperMarkedSpan : MultispanIndex (.ofLinearOrder ι) Marked.{u} where
  left p := coneUpperPairMarked i (e p.val.1) (e p.val.2)
  right j := coneUpperFaceMarked i (e j)
  fst p := coneUpperPairFirst i (e p.val.1) (e p.val.2)
  snd p := coneUpperPairSecond i (e p.val.1) (e p.val.2)

/-- The marked upper-face union has the original whole inclusion cocone. -/
def coneVertexUpperMarkedCocone : Multicofork (coneVertexUpperMarkedSpan e i) :=
  (coneVertexUpperDiagram e i).multicofork.toLinearOrder.map (subcomplexFunctor (coneWeight i))

/-- Every whole marked union edge is covered by the same original marked upper face, proving the actual
  marked colimit. -/
def coneVertexUpperMarkedIsColimit : IsColimit (coneVertexUpperMarkedCocone e i) := by
  apply isColimitOfUnderlyingMarking
  · exact (Multicofork.isColimitMapEquiv _ forget).symm (coneVertexUpperDiagram e i).isColimit'
  · intro a ha
    have h : a.val ∈ (coneVertexUpperSupport e i).obj (op ⦋1⦌) := a.property
    obtain ⟨j, hj⟩ : ∃ j : ι, a.val ∈ (coneVertexUpperFace e i j).obj (op ⦋1⦌) := by
      simp only [coneVertexUpperSupport, Subfunctor.iSup_obj] at h
      exact Set.mem_iUnion.mp h
    let b : (coneVertexUpperFace e i j : SSet.{u}) _⦋1⦌ := ⟨a.val, hj⟩
    exact ⟨.right j, b, ha, rfl⟩

end SSet.Marked.CoherentWeight
