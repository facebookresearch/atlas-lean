/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeUpperHomIso

/-!
# The actual maximum filtration of original coherent cone subsets

The bounded stages retain every original subset and inclusion. Below a
new terminal vertex, deleting that vertex recovers the preceding stage;
inserting it gives exactly the maximally marked new upper layer. The
operations preserve all other vertices, not just their endpoints.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- An original cone subset belongs to this stage precisely when its actual maximum has not passed the
  selected vertex. -/
abbrev ConeAtMost {n : ℕ} (i k : Vertex.{u} n) := {a : ConeSubset i // a.maximum ≤ k}

/-- The preceding stage consists of the same original subsets whose maximum is strictly below the new vertex. -/
abbrev ConeBefore {n : ℕ} (i k : Vertex.{u} n) := {a : ConeSubset i // a.maximum < k}

/-- Delete only the new maximum from a whole original bounded subset, retaining its original least vertex. -/
def coneEraseTop {n : ℕ} {i k : Vertex.{u} n} (hi : i < k)
    (a : ConeAtMost i k) : ConeBefore i k :=
  ⟨{ vertices := a.val.vertices.erase k
     mem := Finset.mem_erase.mpr ⟨hi.ne, a.val.mem⟩
     lower j hj := a.val.lower j (Finset.mem_of_mem_erase hj) }, by
    apply lt_of_le_of_ne
    · apply Finset.max'_le
      intro j hj
      exact (a.val.le_maximum j (Finset.mem_of_mem_erase hj)).trans a.property
    · exact (Finset.mem_erase.mp (Finset.max'_mem _ _)).1⟩

/-- Inserting precisely the selected new vertex makes the original whole subset an upper-layer coherent path. -/
def coneInsertTop {n : ℕ} {i k : Vertex.{u} n} (hi : i < k)
    (a : ConeBefore i k) : UpperCone i k :=
  ⟨{ vertices := insert k a.val.vertices
     mem := Finset.mem_insert_of_mem a.val.mem
     lower j hj := by
       rcases Finset.mem_insert.mp hj with rfl | hj
       · exact hi.le
       · exact a.val.lower j hj }, by
    apply le_antisymm
    · apply Finset.max'_le
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact le_rfl
      · exact (a.val.le_maximum j hj).trans a.property.le
    · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)⟩

/-- Every preceding-stage vertex is strictly below the new original terminal vertex. -/
theorem coneBefore_vertex_lt {n : ℕ} {i k : Vertex.{u} n}
    (a : ConeBefore i k) (j : Vertex.{u} n) (hj : j ∈ a.val.vertices) : j < k :=
  (a.val.le_maximum j hj).trans_lt a.property

/-- Erasing the inserted new maximum recovers all original preceding-stage vertices. -/
theorem coneEraseTop_insert {n : ℕ} {i k : Vertex.{u} n} (hi : i < k)
    (a : ConeBefore i k) :
    coneEraseTop hi ⟨(coneInsertTop hi a).val, (coneInsertTop hi a).property.le⟩ = a := by
  apply Subtype.ext
  apply ConeSubset.ext
  change (insert k a.val.vertices).erase k = a.val.vertices
  rw [Finset.erase_insert]
  exact fun h => (coneBefore_vertex_lt a k h).false

/-- A bounded subset at the new maximum is exactly the old erased subset with that original maximum reinserted. -/
theorem coneInsertTop_erase {n : ℕ} {i k : Vertex.{u} n} (hi : i < k)
    (a : ConeAtMost i k) (ha : a.val.maximum = k) :
    (coneInsertTop hi (coneEraseTop hi a)).val = a.val := by
  apply ConeSubset.ext
  change insert k (a.val.vertices.erase k) = a.val.vertices
  apply Finset.insert_erase
  exact Eq.mp (congrArg (fun j : Vertex.{u} n => j ∈ a.val.vertices) ha) a.val.maximum_mem

/-- An original bounded subset already below the new maximum is unchanged by erasing it. -/
theorem coneEraseTop_before {n : ℕ} {i k : Vertex.{u} n} (hi : i < k)
    (a : ConeAtMost i k) (ha : a.val.maximum < k) : (coneEraseTop hi a).val = a.val := by
  apply ConeSubset.ext
  change a.val.vertices.erase k = a.val.vertices
  exact Finset.erase_eq_of_notMem (fun h => ((a.val.le_maximum k h).trans_lt ha).false)

/-- The actual vertex deletion preserves every original inclusion in the bounded stage. -/
theorem coneEraseTop_mono {n : ℕ} {i k : Vertex.{u} n} (hi : i < k) :
    Monotone (coneEraseTop hi) := by
  intro a b h
  exact Finset.erase_subset_erase k h

/-- The actual vertex insertion preserves every original preceding-stage inclusion. -/
theorem coneInsertTop_mono {n : ℕ} {i k : Vertex.{u} n} (hi : i < k) :
    Monotone (coneInsertTop hi) := by
  intro a b h
  exact Finset.insert_subset_insert k h

/-- The bounded stage retains the original marking, rather than replacing all of its edges by marked edges. -/
def coneAtMostWeight {n : ℕ} (i k : Vertex.{u} n) : Marked.{u} where
  toSSet := nerve (ConeAtMost i k)
  marking := {e | (e.obj 0).val.maximum = (e.obj 1).val.maximum}
  degenerate_mem _ := rfl

/-- The preceding stage retains exactly the same original constant-maximum marking. -/
def coneBeforeWeight {n : ℕ} (i k : Vertex.{u} n) : Marked.{u} where
  toSSet := nerve (ConeBefore i k)
  marking := {e | (e.obj 0).val.maximum = (e.obj 1).val.maximum}
  degenerate_mem _ := rfl

end SSet.Marked.CoherentWeight
