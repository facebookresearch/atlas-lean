/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeOperators
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Whole original coordinate faces of the coherent cone

Each original tail vertex is a genuine subset-membership coordinate.
Its lower face excludes that vertex at every point of the entire scalar
simplex; its upper face includes it at every point. Both conditions are
stable under every original face and degeneracy. These are actual
subcomplexes of the original cone nerve, before any model class or
boundary-latching identification is asserted.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- An original coordinate face retains a constant membership value at every vertex of the whole supplied
  scalar simplex. -/
def coneCoordinateFace {n : ℕ} (i j : Vertex.{u} n) (ε : Bool) :
    (nerve (ConeSubset i)).Subcomplex where
  obj q := {x | ∀ t, (j ∈ (x.obj t).vertices) ↔ ε = true}
  map f := by
    intro x hx t
    exact hx (f.unop.toOrderHom t)

/-- Lower-face membership is exactly exclusion of the same original coordinate from the whole scalar word. -/
theorem mem_coneCoordinateFace_false {n : ℕ} (i j : Vertex.{u} n)
    {q : SimplexCategoryᵒᵖ} (x : (nerve (ConeSubset i)).obj q) :
    x ∈ (coneCoordinateFace i j false).obj q ↔ ∀ t, j ∉ (x.obj t).vertices := by
  simp only [coneCoordinateFace, Set.mem_ofPred_eq, Bool.false_eq_true, iff_false]

/-- Upper-face membership is exactly retention of the same original coordinate throughout the full scalar word. -/
theorem mem_coneCoordinateFace_true {n : ℕ} (i j : Vertex.{u} n)
    {q : SimplexCategoryᵒᵖ} (x : (nerve (ConeSubset i)).obj q) :
    x ∈ (coneCoordinateFace i j true).obj q ↔ ∀ t, j ∈ (x.obj t).vertices := by
  simp only [coneCoordinateFace, Set.mem_ofPred_eq, iff_true]

/-- The designated least vertex is retained in every whole cone simplex; its upper coordinate face is the
  entire original nerve. -/
theorem coneCoordinateFace_self_true {n : ℕ} (i : Vertex.{u} n) :
    coneCoordinateFace i i true = ⊤ := by
  ext q x
  simp only [mem_coneCoordinateFace_true, Subfunctor.top_obj, Set.mem_univ, iff_true]
  exact fun t => (x.obj t).mem

/-- Every original scalar operator retains the same complete coordinate-face condition. -/
theorem coneCoordinateFace_operator {n : ℕ} (i j : Vertex.{u} n) (ε : Bool)
    {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) {x : (nerve (ConeSubset i)).obj q}
    (hx : x ∈ (coneCoordinateFace i j ε).obj q) :
    (nerve (ConeSubset i)).map f x ∈ (coneCoordinateFace i j ε).obj r :=
  (coneCoordinateFace i j ε).map f hx

end SSet.Marked.CoherentWeight
