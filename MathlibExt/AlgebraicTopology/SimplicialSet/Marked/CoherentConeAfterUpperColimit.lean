/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterUpperCover
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeUpperFacePrism
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SubcomplexFunctor

/-!
# Whole marked upper-face colimits at every cone coefficient

The actual upper faces and pairwise intersections form an ordered
multicoequalizer for each original positive-maximum coefficient.
Every marked edge comes from one of the same marked faces. The
support isomorphism then gives the colimit on the original coefficient
itself, retaining all original face maps and scalar operators.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The upper face at an original vertex beyond the cutoff. -/
def coneAfterUpperFace {n : ℕ} (i k : Vertex.{u} n) (j : AfterVertex k) :
    (nerve (ConeSubset i)).Subcomplex := coneCoordinateFace i j.val true

/-- The whole upper faces and their whole intersections present the original positive-maximum support. -/
theorem coneAfterUpperDiagram {n : ℕ} (i k : Vertex.{u} n) :
    Subcomplex.MulticoequalizerDiagram (coneAfterSubcomplex i k)
      (coneAfterUpperFace i k) (fun j l => coneAfterUpperFace i k j ⊓ coneAfterUpperFace i k l) where
  iSup_eq := (coneAfterSubcomplex_eq_upper i k).symm
  eq_inf _ _ := rfl

/-- The actual ordered face/intersection cocone is colimiting on the entire underlying simplicial set. -/
def coneAfterUpperUnderlyingIsColimit {n : ℕ} (i k : Vertex.{u} n) :
    IsColimit ((coneAfterUpperDiagram i k).multicofork.toLinearOrder.map Subcomplex.toSSetFunctor) :=
  (coneAfterUpperDiagram i k).isColimit'

/-- Original marked edges are covered by the same marked upper faces, proving the whole marked support colimit. -/
def coneAfterUpperSupportIsColimit {n : ℕ} (i k : Vertex.{u} n) :
    IsColimit ((coneAfterUpperDiagram i k).multicofork.toLinearOrder.map
      (subcomplexFunctor (coneWeight i))) := by
  apply isColimitOfUnderlyingMarking
  · exact (Multicofork.isColimitMapEquiv _ forget).symm (coneAfterUpperUnderlyingIsColimit i k)
  · intro e he
    have h : e.val ∈ (coneAfterUpperSupport i k).obj (op ⦋1⦌) :=
      Eq.mp (congrArg (fun A : (nerve (ConeSubset i)).Subcomplex => e.val ∈ A.obj (op ⦋1⦌))
        (coneAfterSubcomplex_eq_upper i k)) e.property
    obtain ⟨j, hj⟩ : ∃ j : AfterVertex k, e.val ∈ (coneAfterUpperFace i k j).obj (op ⦋1⦌) := by
      simp only [coneAfterUpperSupport, Subfunctor.iSup_obj] at h
      exact Set.mem_iUnion.mp h
    let a : (coneAfterUpperFace i k j : SSet.{u}) _⦋1⦌ := ⟨e.val, hj⟩
    exact ⟨.right j, a, he, rfl⟩

/-- The same original ordered face cocone has the actual positive-maximum coefficient as its point. -/
def coneAfterUpperCocone {n : ℕ} (i k : Vertex.{u} n) :=
  ((coneAfterUpperDiagram i k).multicofork.toLinearOrder.map
    (subcomplexFunctor (coneWeight i))).extend (coneAfterSupportIso i k).inv

/-- Every original coefficient is the genuine whole marked colimit of these same upper faces and intersections. -/
def coneAfterUpperIsColimit {n : ℕ} (i k : Vertex.{u} n) :
    IsColimit (coneAfterUpperCocone i k) := by
  exact IsColimit.ofIsoColimit (coneAfterUpperSupportIsColimit i k)
    (Cocone.ext (coneAfterSupportIso i k).symm (fun _ => rfl))

/-- The whole original upper face enters the original positive-maximum coefficient through its unchanged
  support inclusion. -/
def coneUpperFaceToAfter {n : ℕ} (i k : Vertex.{u} n) (j : AfterVertex k) :
    coneUpperFaceMarked i j.val ⟶ coneAfterWeight i k :=
  ((coneAfterUpperDiagram i k).multicofork.toLinearOrder.map
    (subcomplexFunctor (coneWeight i))).π j ≫ (coneAfterSupportIso i k).inv

/-- Each cocone injection is the same original full upper-face map. -/
theorem coneAfterUpperCocone_leg {n : ℕ} (i k : Vertex.{u} n) (j : AfterVertex k) :
    (coneAfterUpperCocone i k).ι.app (.right j) = coneUpperFaceToAfter i k j := rfl

end SSet.Marked.CoherentWeight
