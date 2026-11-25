/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DepthFirstSearch

/-!
# Exact transition count for depth-first search

`DepthFirstSearch.dfs_exact_steps` links the canonical DFS result to a terminal
trace with exactly one transition for each scheduled root, discovered vertex,
and scanned adjacency entry. Repeated roots and adjacency entries are counted.
This is a transition-count theorem, not a CPU-time or hashing-cost theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Cslib.Algorithms.Lean.DepthFirstSearch

universe u

private lemma step_work_conservation
    {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V)
    (a b : Internal.Machine V)
    (h : Internal.Step adj roots a b) :
    a.work.length + b.preorderRev.length +
        (b.preorderRev.map fun v => (adj.adjacency v).length).sum =
      b.work.length + a.preorderRev.length +
        (a.preorderRev.map fun v => (adj.adjacency v).length).sum + 1 := by
  cases h <;> simp_all [Internal.enterFrames] <;> omega

private lemma steps_work_conservation
    {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V)
    (a b : Internal.Machine V) (n : Nat)
    (h : Relation.RelatesInSteps (Internal.Step adj roots) a b n) :
    a.work.length + b.preorderRev.length +
        (b.preorderRev.map fun v => (adj.adjacency v).length).sum =
      b.work.length + a.preorderRev.length +
        (a.preorderRev.map fun v => (adj.adjacency v).length).sum + n := by
  induction h with
  | refl => simp
  | tail b c n _ hstep ih =>
    have hs := step_work_conservation adj roots b c hstep
    omega

private lemma completed_steps_count
    {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) (final : Internal.Machine V) (n : Nat)
    (h : Relation.RelatesInSteps (Internal.Step adj roots) (Internal.initial roots) final n)
    (hfinal : final.work = []) :
    n = roots.length + final.preorderRev.length +
      (final.preorderRev.map fun v => (adj.adjacency v).length).sum := by
  have hcount := steps_work_conservation adj roots (Internal.initial roots) final n h
  simpa [Internal.initial, Internal.enterFrames, hfinal] using hcount.symm

private lemma dfsAll_preorder_perm_vertices
    {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) : (dfsAll adj).preorder.Perm adj.vertices := by
  apply (List.perm_ext_iff_of_nodup (preorder_nodup adj adj.vertices)
    adj.vertices_nodup).mpr
  intro vertex
  exact ⟨fun _ => adj.vertices_complete vertex, fun _ => mem_dfsAll_preorder adj vertex⟩

/-- **Exact transition count of depth-first search.** Let $G$ be a finite directed graph with
ordered adjacency lists $N(v)$, whose entries may repeat, and let $R$ be a list of roots, possibly
with repetitions. Run the depth-first search machine from $R$ (each transition drops a pending
vertex that is already visited, discovers a new vertex, or finishes a vertex). Let
$v_1, \dots, v_k$ be the preorder of the depth-first search of $G$ from $R$. Then there is a
terminal machine state, with no work left, whose recorded output is the depth-first traversal of
$G$ from $R$ and which is reached from the initial state in exactly
$|R| + k + \sum_{i=1}^{k} |N(v_i)|$ transitions, where $|R|$ is the length of $R$ and $|N(v)|$
is the length of the adjacency list of $v$. -/
public theorem dfs_exact_steps
    {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) (roots : List V) :
    ∃ final : Internal.Machine V, final.work = [] ∧
      Internal.finish final = dfs adj roots ∧
      Relation.RelatesInSteps (Internal.Step adj roots) (Internal.initial roots) final
        (roots.length + (dfs adj roots).preorder.length +
          ((dfs adj roots).preorder.map fun v => (adj.adjacency v).length).sum) := by
  obtain ⟨final, hsteps, hfinal, hfinish⟩ := dfs_is_left_first adj roots
  obtain ⟨n, hn⟩ := hsteps.relatesInSteps
  have hc := completed_steps_count adj roots final n hn hfinal
  have hindex : n = roots.length + (dfs adj roots).preorder.length +
      ((dfs adj roots).preorder.map fun v => (adj.adjacency v).length).sum := by
    rw [← hfinish]
    simpa [Internal.finish] using hc
  rw [hindex] at hn
  exact ⟨final, hfinal, hfinish, hn⟩

/-- **Exact transition count of whole-graph depth-first search.** Let $G$ be a finite directed
graph whose vertices are listed without repetition as $v_1, \dots, v_n$, with ordered adjacency
lists $N(v)$ whose entries may repeat. Run the depth-first search machine with roots
$v_1, \dots, v_n$ in this order (each transition drops a pending vertex that is already visited,
discovers a new vertex, or finishes a vertex). Then there is a terminal machine state, with no
work left, whose recorded output is the whole-graph depth-first traversal of $G$ and which is
reached from the initial state in exactly $2n + \sum_{i=1}^{n} |N(v_i)|$ transitions, where
$|N(v)|$ is the length of the adjacency list of $v$, counting repeated entries and self-loops. -/
public theorem dfsAll_exact_steps
    {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (adj : DirectedAdjacency V) :
    ∃ final : Internal.Machine V, final.work = [] ∧
      Internal.finish final = dfsAll adj ∧
      Relation.RelatesInSteps (Internal.Step adj adj.vertices)
        (Internal.initial adj.vertices) final
        (2 * adj.vertices.length + (adj.vertices.map fun v => (adj.adjacency v).length).sum) := by
  obtain ⟨final, hfinal, hfinish, hsteps⟩ := dfs_exact_steps adj adj.vertices
  have hperm := dfsAll_preorder_perm_vertices adj
  have hcount : adj.vertices.length + (dfs adj adj.vertices).preorder.length +
      ((dfs adj adj.vertices).preorder.map fun v => (adj.adjacency v).length).sum =
      2 * adj.vertices.length + (adj.vertices.map fun v => (adj.adjacency v).length).sum := by
    change adj.vertices.length + (dfsAll adj).preorder.length +
      ((dfsAll adj).preorder.map fun v => (adj.adjacency v).length).sum = _
    rw [hperm.length_eq, (hperm.map fun v => (adj.adjacency v).length).sum_eq]
    omega
  rw [hcount] at hsteps
  exact ⟨final, hfinal, hfinish, hsteps⟩

end Cslib.Algorithms.Lean.DepthFirstSearch
