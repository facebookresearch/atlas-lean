/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCoordinateFaces
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Monomorphisms

/-!
# Actual original cone coordinate boundary and marked inclusion

The complete coordinate boundary is the union of both original faces
for every actual tail vertex. Its marking is literally the pullback
of the original maximum-preserving cone marking. The original scalar
word, selected coordinate and membership value characterize the whole
boundary; its genuine inclusion is a marked monomorphism. No equation
with a straightened simplex boundary is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- All original tail-coordinate lower and upper faces form the actual complete coordinate boundary. -/
def coneCoordinateBoundary {n : ℕ} (i : Vertex.{u} n) : (nerve (ConeSubset i)).Subcomplex :=
  ⨆ j : {j : Vertex.{u} n // i < j}, ⨆ ε : Bool, coneCoordinateFace i j.val ε

/-- A whole original boundary simplex has one actual tail-coordinate membership constant throughout its complete
scalar word. -/
theorem mem_coneCoordinateBoundary_iff {n : ℕ} (i : Vertex.{u} n)
    {q : SimplexCategoryᵒᵖ} (x : (nerve (ConeSubset i)).obj q) :
    x ∈ (coneCoordinateBoundary i).obj q ↔
      ∃ j : {j : Vertex.{u} n // i < j}, ∃ ε : Bool,
        ∀ t, (j.val ∈ (x.obj t).vertices) ↔ ε = true := by
  simp only [coneCoordinateBoundary, Subfunctor.iSup_obj, Set.mem_iUnion,
    coneCoordinateFace, Set.mem_ofPred_eq]

/-- The whole original coordinate-boundary carrier has exactly the marking pulled back from its original
maximum-preserving cone. -/
def coneCoordinateBoundaryMarked {n : ℕ} (i : Vertex.{u} n) : Marked.{u} :=
  comap (coneWeight i) (coneCoordinateBoundary i).ι

/-- The actual complete marked coordinate-boundary inclusion retains every original simplex and its pulled-back
marking. -/
def coneCoordinateBoundaryMap {n : ℕ} (i : Vertex.{u} n) :
    coneCoordinateBoundaryMarked i ⟶ coneWeight i :=
  comapHom (coneWeight i) (coneCoordinateBoundary i).ι

/-- This actual original marked coordinate-boundary inclusion is monic on the complete underlying simplicial carrier. -/
instance {n : ℕ} (i : Vertex.{u} n) : Mono (coneCoordinateBoundaryMap i) :=
  (mono_iff_underlying _).mpr (inferInstance : Mono (coneCoordinateBoundary i).ι)

/-- The original boundary marking is exactly the same maximum-preserving condition on its whole retained edge. -/
theorem coneCoordinateBoundary_marked_iff {n : ℕ} (i : Vertex.{u} n)
    (e : (coneCoordinateBoundaryMarked i).toSSet _⦋1⦌) :
    e ∈ (coneCoordinateBoundaryMarked i).marking ↔
      (e.val.obj 0).maximum = (e.val.obj 1).maximum := Iff.rfl

end SSet.Marked.CoherentWeight
