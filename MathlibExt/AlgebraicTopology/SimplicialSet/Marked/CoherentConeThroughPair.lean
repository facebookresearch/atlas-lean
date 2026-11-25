/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeThroughSplit

/-!
# Actual ordered two-pivot cone intersection data

A whole original subset retaining two ordered pivots splits at the
first pivot into its original lower path and the original upper cone
still containing the second pivot. Whole native path union reconstructs
it, with both exact inverse equations and the original maximum retained.
The order hypothesis selects the actual ordered pair; equal pivots are
included without deleting their original self-path data.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The entire original cone subset retaining both supplied original pivots. -/
abbrev ConeThroughPair {n : ℕ} (i j k : Vertex.{u} n) :=
  {a : ConeSubset i // j ∈ a.vertices ∧ k ∈ a.vertices}

/-- The two-pivot subset retains its same complete original first through-subset. -/
def pairFirstThrough {n : ℕ} {i j k : Vertex.{u} n} (a : ConeThroughPair i j k) : ConeThrough i j :=
  ⟨a.val, a.property.1⟩

/-- The original ordered second pivot remains in the entire upper split cone. -/
def pairUpperThrough {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) (a : ConeThroughPair i j k) :
    ConeThrough j k :=
  ⟨throughUpperCone (pairFirstThrough a), Finset.mem_filter.mpr ⟨a.property.2, hjk⟩⟩

/-- The whole original path and second-through-cone reconstruct their complete original two-pivot subset. -/
def pathThroughPair {n : ℕ} {i j k : Vertex.{u} n} (p : SimplicialThickening.Path i j)
    (a : ConeThrough j k) : ConeThroughPair i j k :=
  ⟨(pathThrough p a.val).val, (pathThrough p a.val).property, Finset.mem_union_right _ a.property⟩

/-- Both actual ordered split pieces recover the original entire two-pivot subset. -/
theorem pathThroughPair_split {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k)
    (a : ConeThroughPair i j k) :
    pathThroughPair (throughLowerPath (pairFirstThrough a)) (pairUpperThrough hjk a) = a := by
  exact Subtype.ext (congrArg (fun x : ConeThrough i j => x.val)
    (pathThrough_split (pairFirstThrough a)))

/-- The original reconstructed first lower path is exactly the whole supplied path. -/
theorem pairFirstThrough_lower_path {n : ℕ} {i j k : Vertex.{u} n}
    (p : SimplicialThickening.Path i j) (a : ConeThrough j k) :
    throughLowerPath (pairFirstThrough (pathThroughPair p a)) = p :=
  throughLowerPath_pathThrough p a.val

/-- The reconstructed ordered upper through-cone is exactly the original whole supplied second-through subset. -/
theorem pairUpperThrough_path {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k)
    (p : SimplicialThickening.Path i j) (a : ConeThrough j k) :
    pairUpperThrough hjk (pathThroughPair p a) = a := by
  apply Subtype.ext
  exact throughUpperCone_pathThrough p a.val

/-- The actual entire ordered two-pivot subset is its original full lower path and original remaining
  through-cone data. -/
def coneThroughPairSplitEquiv {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k) :
    ConeThroughPair i j k ≃ SimplicialThickening.Path i j × ConeThrough j k where
  toFun a := (throughLowerPath (pairFirstThrough a), pairUpperThrough hjk a)
  invFun a := pathThroughPair a.1 a.2
  left_inv := pathThroughPair_split hjk
  right_inv a := Prod.ext (pairFirstThrough_lower_path a.1 a.2) (pairUpperThrough_path hjk a.1 a.2)

/-- The actual ordered upper-through split retains the maximum of the whole original two-pivot subset. -/
theorem pairUpperThrough_maximum {n : ℕ} {i j k : Vertex.{u} n} (hjk : j ≤ k)
    (a : ConeThroughPair i j k) : (pairUpperThrough hjk a).val.maximum = a.val.maximum :=
  throughUpperCone_maximum (pairFirstThrough a)

end SSet.Marked.CoherentWeight
