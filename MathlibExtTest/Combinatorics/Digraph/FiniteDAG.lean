/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Digraph.FiniteDAG
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Biology.PopulationGenetics.AdmixtureGraph

/-!
# Tests for finite DAGs

The examples check the directed path and the directed 3-cycle, the empty and edgeless
digraphs, the undirected-acyclicity reuse, and that an admixture graph's parent digraph
is acyclic.
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

example : path3.IsAcyclic :=
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

/-- Integration with Atlas: the parent digraph of an admixture graph (edges parent → child) is
acyclic, via `isAcyclic_iff_wellFounded` and the structure's well-foundedness field. -/
example {W : Type*} [Finite W] (A : MathlibExt.Biology.PopulationGenetics.AdmixtureGraph W) :
    (⟨fun Y X => Y ∈ A.parents X⟩ : Digraph W).IsAcyclic :=
  isAcyclic_iff_wellFounded.mpr A.wf


#print axioms Digraph.isAcyclic_iff_wellFounded
#print axioms Digraph.IsAcyclic.exists_isTopologicalOrder
#print axioms Digraph.isAcyclic_iff_exists_isTopologicalOrder
#print axioms Digraph.finite_paths
#print axioms Digraph.cycle3_not_isTopologicalOrder

end MathlibExtTest.Combinatorics.FiniteDAG
