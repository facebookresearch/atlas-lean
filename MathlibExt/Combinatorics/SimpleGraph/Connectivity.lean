/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

@[expose] public section

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

open Finset List

/-- **Internally disjoint walks.** Two walks $p$ and $q$ in a simple graph $G$ are internally
disjoint if no vertex is an interior vertex of both, where the interior vertices of a walk are
the entries of its vertex sequence other than the first and the last. -/
def InternallyDisjoint {u v x y : V} (p : G.Walk u v) (q : G.Walk x y) : Prop :=
  Disjoint p.support.tail.dropLast q.support.tail.dropLast

/-- **Infinitely connected graphs.** A simple graph $G$ is infinitely connected if it has at
least two vertices and, for any two distinct vertices $u$ and $v$, there is an infinite set of
paths from $u$ to $v$ in $G$ that are pairwise internally disjoint.

In particular, a graph with at most one vertex is not infinitely connected. -/
def InfinitelyConnected (G : SimpleGraph V) : Prop := Nontrivial V ∧
  Pairwise fun u v ↦ ∃ P : Set (G.Walk u v),
    P.Infinite ∧ (∀ p ∈ P, p.IsPath) ∧ P.Pairwise InternallyDisjoint

/-!
### Deciding reachability by breadth-first search

This section provides efficient decidability instances for reachability and (pre)connectedness of
finite graphs through a breadth-first search (BFS) algorithm.

The algorithm is as follows: we maintain a finset of visited vertices which we grow with all its
neighbors at each round of breadth-first search at, stopping as soon as a round adds no new vertex:
a search costs `O((diam G + 1) * (card V) ^ 2)` adjacency tests.

Vertices `u` and `v` are then reachable if `v` lies in the BFS-constructed finset of vertices
reachable from `u`, and a graph is (pre)connected iff it's non-empty and (/empty or) every vertex is
lies in the reachability finset of an arbitrarily-chosen vertex.
-/

section BFS
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} {s t : Finset V} {u v w : V}

variable (G s) in
/-- **One round of breadth-first search.** For a simple graph $G$ on a finite vertex set and a
set $s$ of vertices, this is the set of vertices that lie in $s$ or are adjacent to some vertex
of $s$, that is, $s$ together with all neighbours of its vertices. -/
def bfsStep : Finset V := {w | w ∈ s ∨ ∃ v ∈ s, G.Adj v w}

@[simp, grind =]
lemma mem_bfsStep : w ∈ G.bfsStep s ↔ w ∈ s ∨ ∃ v ∈ s, G.Adj v w := by simp [bfsStep]

lemma subset_bfsStep : s ⊆ G.bfsStep s := fun _ hw ↦ G.mem_bfsStep.2 <| .inl hw

@[gcongr] lemma bfsStep_mono (hst : s ⊆ t) : G.bfsStep s ⊆ G.bfsStep t := by grind

@[gcongr]
lemma iterate_bfsStep_mono (hst : s ⊆ t) : G.bfsStep^[n] s ⊆ G.bfsStep^[n] t := by
  induction n generalizing s t with
  | zero => exact hst
  | succ n ih => simpa only [Function.iterate_succ_apply] using ih (G.bfsStep_mono hst)

lemma subset_iterate_bfsStep : s ⊆ G.bfsStep^[n] s := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => grw [Function.iterate_succ_apply', ← ih, ← G.subset_bfsStep]

lemma iterate_bfsStep_subset_of_le (hmn : m ≤ n) : G.bfsStep^[m] s ⊆ G.bfsStep^[n] s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Function.iterate_add_apply]
  exact G.iterate_bfsStep_mono G.subset_iterate_bfsStep

lemma mem_iterate_bfsStep_of_walk (p : G.Walk u v) : v ∈ G.bfsStep^[p.length] {u} := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.length_cons, Function.iterate_succ_apply]
    exact G.iterate_bfsStep_mono (by simp [h]) ih

lemma reachable_of_mem_iterate_bfsStep (hv : v ∈ G.bfsStep^[n] {u}) : G.Reachable u v := by
  induction n generalizing v with
  | zero =>
    rw [Function.iterate_zero_apply, Finset.mem_singleton] at hv
    exact hv ▸ Reachable.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply', mem_bfsStep] at hv
    obtain hv | ⟨w, hw, hwv⟩ := hv
    · exact ih hv
    · exact (ih hw).trans hwv.reachable

/-- **Breadth-first search with a round limit.** For a simple graph $G$ on a finite vertex set,
a natural number $n$ and a set $s$ of vertices, this applies rounds of breadth-first search to
$s$ (each round adds all neighbours of the current vertices), stopping after $n$ rounds or as
soon as a round adds no new vertex, whichever comes first, and returns the resulting set. -/
def bfsIterate : ℕ → Finset V → Finset V
  | 0, s => s
  | n + 1, s => if (G.bfsStep s).card ≤ s.card then s else bfsIterate n (G.bfsStep s)

lemma bfsIterate_eq_iterate_bfsStep (n : ℕ) (s : Finset V) :
    G.bfsIterate n s = G.bfsStep^[n] s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [bfsIterate]
    split_ifs with h
    · have hs : G.bfsStep s = s := (Finset.eq_of_subset_of_card_le G.subset_bfsStep h).symm
      exact (Function.iterate_fixed hs _).symm
    · rw [ih, ← Function.iterate_succ_apply]

/-- **Vertices reachable from a vertex.** For a simple graph $G$ on a finite vertex set $V$ and
a vertex $u$, this is the set obtained from $\{u\}$ by breadth-first search with at most $|V|$
rounds, stopping early as soon as a round adds no new vertex.

It consists exactly of the vertices reachable from $u$ in $G$. -/
def reachableFinset (u : V) : Finset V := G.bfsIterate (Fintype.card V) {u}

@[simp]
lemma mem_reachableFinset : v ∈ G.reachableFinset u ↔ G.Reachable u v := by
  rw [reachableFinset, bfsIterate_eq_iterate_bfsStep]
  refine ⟨G.reachable_of_mem_iterate_bfsStep, fun h ↦ h.elim_path fun p ↦ ?_⟩
  exact G.iterate_bfsStep_subset_of_le p.2.length_lt.le (G.mem_iterate_bfsStep_of_walk p.1)

lemma preconnected_iff_forall_mem_reachableFinset (u : V) :
    G.Preconnected ↔ ∀ v, v ∈ G.reachableFinset u := by
  simp only [mem_reachableFinset]
  exact ⟨fun h v ↦ h u v, fun h x y ↦ (h x).symm.trans (h y)⟩

lemma connected_iff_forall_mem_reachableFinset (u : V) :
    G.Connected ↔ ∀ v, v ∈ G.reachableFinset u := by
  rw [connected_iff, G.preconnected_iff_forall_mem_reachableFinset u, and_iff_left ⟨u⟩]

end BFS
end SimpleGraph
