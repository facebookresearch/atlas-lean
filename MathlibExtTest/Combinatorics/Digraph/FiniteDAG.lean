/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Digraph.FiniteDAG
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.FinCases

/-!
# Tests for finite DAGs

The examples check the directed path and the directed 3-cycle, the empty and edgeless
digraphs, parents, rooted trees and subgraphs of DAGs, and the undirected acyclicity
criterion.
-/

@[expose] public section

open Digraph

namespace MathlibExtTest.Combinatorics.FiniteDAG

/-- The directed path `0 → 1 → 2`. -/
def path3 : Digraph (Fin 3) where
  Adj i j := i.val + 1 = j.val

instance : DecidableRel path3.Adj := fun i j => inferInstanceAs (Decidable (i.val + 1 = j.val))
instance : DecidableRel cycle3.Adj := fun i j => inferInstanceAs (Decidable (j = i + 1))

/-- The identity is a topological order of the directed path (positive instance). -/
example : path3.IsTopologicalOrder (finCongr (Fintype.card_fin 3).symm) := by
  intro u v huv
  simp only [path3] at huv
  rw [Fin.lt_def]
  simp only [finCongr_apply, Fin.val_cast]
  omega

theorem path3_isAcyclic : path3.IsAcyclic :=
  IsTopologicalOrder.isAcyclic (σ := finCongr (Fintype.card_fin 3).symm) (by
    intro u v huv
    simp only [path3] at huv
    rw [Fin.lt_def]
    simp only [finCongr_apply, Fin.val_cast]
    omega)

/-- Roots and leaves of the directed path are exactly `{0}` and `{2}`. -/
example : path3.roots = {0} := by decide
example : path3.leaves = {2} := by decide

/-- Every vertex of the 3-cycle has an in-edge and an out-edge: no roots, no leaves, so
acyclicity is necessary in `roots_nonempty` / `leaves_nonempty`. -/
example : cycle3.roots = ∅ := by decide
example : cycle3.leaves = ∅ := by decide

/-- A walk that repeats a vertex in the 3-cycle: `nodup_of_isChain` needs acyclicity. -/
example : [(0 : Fin 3), 1, 2, 0].IsChain cycle3.Adj ∧ ¬ [(0 : Fin 3), 1, 2, 0].Nodup := by
  decide

/-- Empty vertex type: the unique digraph is acyclic with a (vacuous) topological order. -/
example (G : Digraph Empty) : G.IsAcyclic := fun v => v.elim

/-- The edgeless digraph is acyclic. -/
example {V : Type*} : (⊥ : Digraph V).IsAcyclic := by
  intro v hv
  cases hv with
  | single h => exact h
  | tail _ h => exact h

/-- A loop is a cycle: the complete digraph on one vertex is not acyclic. -/
example : ¬ (⊤ : Digraph Unit).IsAcyclic := fun h => h.irrefl () trivial

/-- The record's undirected notion is Mathlib's `SimpleGraph.IsAcyclic` (no cycle walks). -/
example {W : Type*} (H : SimpleGraph W) :
    H.IsAcyclic ↔ ∀ ⦃v : W⦄ (c : H.Walk v v), ¬ c.IsCycle := Iff.rfl

example {W : Type*} : (⊥ : SimpleGraph W).IsAcyclic := SimpleGraph.isAcyclic_bot

/-- The diamond `0 → 1, 0 → 2, 1 → 3, 2 → 3`: vertex `3` has two parents. -/
def diamond : Digraph (Fin 4) where
  Adj i j := (i.val, j.val) = (0, 1) ∨ (i.val, j.val) = (0, 2) ∨ (i.val, j.val) = (1, 3) ∨
    (i.val, j.val) = (2, 3)

instance : DecidableRel diamond.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) = (0, 1) ∨ (i.val, j.val) = (0, 2) ∨
    (i.val, j.val) = (1, 3) ∨ (i.val, j.val) = (2, 3)))

/-- `parentsOf` collects exactly the direct predecessors (restated definition). -/
example {V : Type*} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) :
    G.parentsOf v = ({u | G.Adj u v} : Finset V) := rfl

example {V : Type*} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] {u v : V} :
    u ∈ G.parentsOf v ↔ G.Adj u v := mem_parentsOf

/-- `IsRootedTree` is the four-part arborescence predicate (restated definition). -/
example {V : Type*} (G : Digraph V) (r : V) :
    G.IsRootedTree r ↔ G.IsAcyclic ∧ (∀ u, ¬ G.Adj u r) ∧
      (∀ v, v ≠ r → ∃! u, G.Adj u v) ∧ ∀ v, Relation.ReflTransGen G.Adj r v := Iff.rfl

/-- Subgraphs of DAGs are DAGs (restated theorem). -/
example {V : Type*} {G H : Digraph V} (hGH : ∀ u v, H.Adj u v → G.Adj u v) (hG : G.IsAcyclic) :
    H.IsAcyclic := isAcyclic_of_le hGH hG

/-- Parents in the directed path and the 3-cycle: each vertex has at most one. -/
example : path3.parentsOf 0 = ∅ := by decide
example : path3.parentsOf 1 = {0} := by decide
example : path3.parentsOf 2 = {1} := by decide
example : cycle3.parentsOf 0 = {2} := by decide

/-- In the diamond, `3` has the two parents `1, 2` and the root `0` has none. -/
example : diamond.parentsOf 3 = {1, 2} := by decide
example : diamond.parentsOf 0 = ∅ := by decide

/-- The one-vertex edgeless digraph is a rooted tree. -/
example : (⊥ : Digraph Unit).IsRootedTree () := by
  refine ⟨fun v hv => ?_, fun u h => h, fun v hv => ?_, fun v => ?_⟩
  · cases hv with
    | single h => exact h
    | tail _ h => exact h
  · exact absurd (Subsingleton.elim v ()) hv
  · obtain rfl : v = () := Subsingleton.elim v ()
    exact Relation.ReflTransGen.refl

/-- The directed path `0 → 1 → 2` is a rooted tree with root `0`. -/
example : path3.IsRootedTree 0 := by
  refine ⟨path3_isAcyclic, ?_, ?_, ?_⟩
  · decide
  · intro v hv
    fin_cases v
    · exact (hv (by decide)).elim
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
  · intro v
    fin_cases v
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by decide)
    · exact (Relation.ReflTransGen.single (by decide : path3.Adj 0 1)).tail (by decide)

/-- The directed 3-cycle is a rooted tree for no choice of root: it is not acyclic. -/
example (r : Fin 3) : ¬ cycle3.IsRootedTree r := fun h => not_isAcyclic_cycle3 h.1

/-- The diamond is not a rooted tree: vertex `3` has two parents. -/
example : ¬ diamond.IsRootedTree 0 := by
  rintro ⟨-, -, hT, -⟩
  obtain ⟨w, -, hw⟩ := hT 3 (by decide)
  have e1 := hw 1 (by decide)
  have e2 := hw 2 (by decide)
  exact absurd (e1.trans e2.symm) (by decide)

/-- The edgeless digraph on `Fin 3` is acyclic as a subgraph of the directed path. -/
example : (⊥ : Digraph (Fin 3)).IsAcyclic :=
  isAcyclic_of_le (G := path3) (fun _u _v h => h.elim) path3_isAcyclic

#print axioms Digraph.isAcyclic_iff_wellFounded
#print axioms Digraph.IsAcyclic.exists_isTopologicalOrder
#print axioms Digraph.isAcyclic_iff_exists_isTopologicalOrder
#print axioms Digraph.finite_paths
#print axioms Digraph.mem_parentsOf
#print axioms Digraph.isAcyclic_of_le
#print axioms Digraph.cycle3_not_isTopologicalOrder

end MathlibExtTest.Combinatorics.FiniteDAG
