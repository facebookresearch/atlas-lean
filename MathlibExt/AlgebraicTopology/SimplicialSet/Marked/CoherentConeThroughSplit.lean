/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDiagram

/-!
# Whole original cone subset splitting at a retained vertex

A supplied cone subset containing the retained vertex splits into its
entire original lower coherent path and its entire original upper cone.
Reconstruction uses the original full path union. Both inverse equations
keep every original vertex, including both shared pivot endpoints; the
upper component retains precisely the original maximum. These are the
actual vertex data for the upper-coordinate free-chart comparison.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- An actual original cone subset with its supplied original retained pivot. -/
abbrev ConeThrough {n : ℕ} (i j : Vertex.{u} n) := {a : ConeSubset i // j ∈ a.vertices}

/-- The entire original lower endpoint-containing path of the supplied subset. -/
def throughLowerPath {n : ℕ} {i j : Vertex.{u} n} (a : ConeThrough i j) : SimplicialThickening.Path i j where
  I := {t | t ∈ a.val.vertices ∧ t ≤ j}
  left := ⟨a.val.mem, a.val.lower j a.property⟩
  right := ⟨a.property, le_rfl⟩
  left_le t ht := a.val.lower t ht.1
  le_right _ ht := ht.2

/-- The whole original upper cone subset, including the same retained pivot. -/
def throughUpperCone {n : ℕ} {i j : Vertex.{u} n} (a : ConeThrough i j) : ConeSubset j where
  vertices := a.val.vertices.filter (fun t => j ≤ t)
  mem := Finset.mem_filter.mpr ⟨a.property, le_rfl⟩
  lower _ ht := (Finset.mem_filter.mp ht).2

/-- Reconstruct the original whole through-subset by its full path union and original upper cone. -/
def pathThrough {n : ℕ} {i j : Vertex.{u} n} (p : SimplicialThickening.Path i j) (a : ConeSubset j) :
    ConeThrough i j := ⟨a.prepend p, Finset.mem_union_right _ a.mem⟩

/-- Both original split pieces recover exactly the whole supplied original subset. -/
theorem pathThrough_split {n : ℕ} {i j : Vertex.{u} n} (a : ConeThrough i j) :
    pathThrough (throughLowerPath a) (throughUpperCone a) = a := by
  apply Subtype.ext
  apply ConeSubset.ext
  ext t
  change t ∈ (throughLowerPath a).I.toFinite.toFinset ∪ a.val.vertices.filter (fun t => j ≤ t) ↔ t ∈ a.val.vertices
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact ((throughLowerPath a).I.toFinite.mem_toFinset.mp h).1
    · exact (Finset.mem_filter.mp h).1
  · intro h
    rcases le_total t j with ht | ht
    · exact Finset.mem_union_left _ ((throughLowerPath a).I.toFinite.mem_toFinset.mpr ⟨h, ht⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, ht⟩)

/-- The reconstructed lower path is exactly the original full supplied path, with the shared pivot retained. -/
theorem throughLowerPath_pathThrough {n : ℕ} {i j : Vertex.{u} n}
    (p : SimplicialThickening.Path i j) (a : ConeSubset j) :
    throughLowerPath (pathThrough p a) = p := by
  apply SimplicialThickening.Path.ext
  ext t
  change (t ∈ p.I.toFinite.toFinset ∪ a.vertices ∧ t ≤ j) ↔ t ∈ p.I
  constructor
  · rintro ⟨ht, hj⟩
    rcases Finset.mem_union.mp ht with ht | ht
    · exact p.I.toFinite.mem_toFinset.mp ht
    · have h : t = j := le_antisymm hj (a.lower t ht)
      exact h.symm ▸ p.right
  · intro ht
    exact ⟨Finset.mem_union_left _ (p.I.toFinite.mem_toFinset.mpr ht), p.le_right t ht⟩

/-- The reconstructed upper cone is exactly the original whole supplied upper subset, without losing the
  pivot or any later vertex. -/
theorem throughUpperCone_pathThrough {n : ℕ} {i j : Vertex.{u} n}
    (p : SimplicialThickening.Path i j) (a : ConeSubset j) :
    throughUpperCone (pathThrough p a) = a := by
  apply ConeSubset.ext
  ext t
  change t ∈ (p.I.toFinite.toFinset ∪ a.vertices).filter (fun t => j ≤ t) ↔ t ∈ a.vertices
  constructor
  · intro ht
    obtain ⟨ht, hj⟩ := Finset.mem_filter.mp ht
    rcases Finset.mem_union.mp ht with ht | ht
    · have h : t = j := le_antisymm (p.le_right t (p.I.toFinite.mem_toFinset.mp ht)) hj
      exact h.symm ▸ a.mem
    · exact ht
  · intro ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ ht, a.lower t ht⟩

/-- The entire original through-subset is equivalent to its actual full lower-path and upper-cone data. -/
def coneThroughSplitEquiv {n : ℕ} (i j : Vertex.{u} n) :
    ConeThrough i j ≃ SimplicialThickening.Path i j × ConeSubset j where
  toFun a := (throughLowerPath a, throughUpperCone a)
  invFun a := pathThrough a.1 a.2
  left_inv := pathThrough_split
  right_inv a := Prod.ext (throughLowerPath_pathThrough a.1 a.2) (throughUpperCone_pathThrough a.1 a.2)

/-- The actual original split upper cone retains precisely the maximum of the original full subset. -/
theorem throughUpperCone_maximum {n : ℕ} {i j : Vertex.{u} n} (a : ConeThrough i j) :
    (throughUpperCone a).maximum = a.val.maximum := by
  apply le_antisymm
  · exact a.val.le_maximum _ (Finset.mem_filter.mp (throughUpperCone a).maximum_mem).1
  · exact (throughUpperCone a).le_maximum _
      (Finset.mem_filter.mpr ⟨a.val.maximum_mem, a.val.le_maximum j a.property⟩)

end SSet.Marked.CoherentWeight
