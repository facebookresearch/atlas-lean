/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Hamiltonian cycles from cyclic listings

This file turns a cyclic listing of all vertices into a Hamiltonian cycle.
-/

@[expose] public section

namespace SimpleGraph

/-- **A cyclic listing of the vertices gives a Hamiltonian cycle.** Let $G$ be a simple graph on a
finite vertex set $V$, and let $v_0, v_1, \dots, v_n$ be a list of vertices with $v_0 = v_n$ in
which $v_{i-1}$ and $v_i$ are adjacent in $G$ for each $1 \le i \le n$. If $v_1, \dots, v_n$ are
pairwise distinct, every vertex of $V$ is among them, and $n \ge 3$, then $G$ is Hamiltonian: it
has a cycle that visits every vertex exactly once. -/
public theorem IsHamiltonian.of_cyclic_list {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (l : List V) (hne : l ≠ [])
    (hclosed : l.head hne = l.getLast hne) (hchain : l.IsChain G.Adj)
    (hnodup : l.tail.Nodup) (hmem : ∀ v, v ∈ l.tail)
    (hthree : 3 ≤ l.length - 1) : G.IsHamiltonian := by
  let q := Walk.ofSupport l hne hchain
  let p : G.Walk (l.head hne) (l.head hne) := q.copy rfl hclosed.symm
  have hp_length : p.length = l.length - 1 := by
    simp only [p, q, Walk.length_copy, Walk.length_ofSupport]
  have hp_not_nil : ¬p.Nil := by
    rw [Walk.not_nil_iff_lt_length, hp_length]
    omega
  have hp_support : p.support = l := by
    simp only [p, q, Walk.support_copy, Walk.support_ofSupport]
  have hp_cycle : p.IsCycle := by
    rw [Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · rw [Walk.isPath_def, p.support_tail_of_not_nil hp_not_nil, hp_support]
      exact hnodup
    · omega
  intro _
  refine ⟨l.head hne, p, Walk.IsHamiltonianCycle.mk hp_cycle ?_⟩
  apply hp_cycle.isPath_tail.isHamiltonian_of_mem
  intro v
  rw [p.support_tail_of_not_nil hp_not_nil, hp_support]
  exact hmem v

end SimpleGraph
