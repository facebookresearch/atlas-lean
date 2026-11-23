/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Dedup

@[expose] public section

namespace Cslib.Planning.MotionPlanning.SamplingPlanners

/-!
# Deterministic sampling-based motion planners (definitions layer)

This file formalizes the algorithmic content of sampling-based motion
planners as deterministic functions: the simplified probabilistic roadmap
(sPRM), the rapidly-exploring random tree (RRT), and the optimal variants
PRM* and RRT*.

Karaman and Frazzoli ("Sampling-based algorithms for optimal motion planning",
International Journal of Robotics Research, 2011, Section 3) describe sPRM and
RRT as operating over random samples. Here the sample list is taken as an
explicit argument instead; fixing the samples is the standard way to formalize
the algorithmic content of these planners deterministically. PRM* and RRT* are
likewise formalized as deterministic functions over an explicit sample list:
the finite-sample form of the Karaman-Frazzoli algorithms, with no
asymptotic-optimality claim.

All four planners share one oracle bundle (`Oracles`): a point-collision test
`free`, a local planner `link` between configurations, a cost proxy `cost`
valued in the rationals so that examples compute by `decide`, and a connection
radius `radius`.

* sPRM: the vertices are the collision-free samples with duplicates removed.
  The edges connect each unordered pair of distinct vertices once, requiring
  the cost bound in both directions and `link` success in both directions.
  Both directions are required (rather than one), which keeps the edge
  relation symmetric by construction.
* RRT: a fold over the sample list. For each collision-free sample, the
  nearest current tree vertex (the first cost minimizer in list order, computed
  by `nearest`) is linked to the sample when the local planner succeeds.
  Samples already present in the tree are skipped by an explicit `s ∉ verts`
  check. This keeps the vertex list duplicate free and the edge set a tree.
* PRM*: like sPRM, except the connection radius is given by `radiusOf`
  applied to the vertex count instead of the fixed `radius`. Pairs connect
  when the cost bound holds in both directions and `link` succeeds in both
  directions.
* RRT*: a fold over the sample list threading vertices, parent edges, and a
  cost-to-come table. Each free new sample chooses the parent minimizing
  cost-to-come plus edge cost among vertices within `radius` (the first
  minimizer in list order), then nearby vertices are rewired through the new
  sample when that is strictly cheaper (one pass, no cascade).

Non-goals: nearest-neighbour data structures, probabilistic completeness, and
asymptotic optimality are out of scope.
-/

/-- Oracle bundle shared by all four planners. -/
structure Oracles (C : Type) where
  /-- Point-collision oracle: true when the configuration is collision free. -/
  free : C → Bool
  /-- Local planner: attempts to connect the first configuration to the second. -/
  link : C → C → Bool
  /-- Cost proxy between configurations, valued in `Rat` so examples compute. -/
  cost : C → C → Rat
  /-- Connection radius for the roadmap. -/
  radius : Rat

/-- sPRM vertices: the collision-free samples with duplicates removed. -/
def sprmVertices {C : Type} [DecidableEq C] (O : Oracles C) (samples : List C) :
    List C :=
  (samples.filter O.free).dedup

/-- Membership in the sPRM vertices: a sample that is collision free. -/
theorem sprmVertices_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) (v : C) :
    v ∈ sprmVertices O samples ↔ v ∈ samples ∧ O.free v = true := by
  unfold sprmVertices
  simp only [List.mem_dedup, List.mem_filter]

/-- Every sPRM vertex is collision free. -/
theorem sprmVertices_all_free {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) (v : C) (hv : v ∈ sprmVertices O samples) :
    O.free v = true :=
  ((sprmVertices_mem O samples v).mp hv).2

/-- sPRM vertices have no duplicates. -/
theorem sprmVertices_nodup {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) : (sprmVertices O samples).Nodup := by
  unfold sprmVertices
  exact List.nodup_dedup _

/-- Propositional sPRM edge predicate. Both the cost bound and the local
planner are required in both directions, so the predicate is symmetric in its
arguments by construction. -/
abbrev IsSprmEdge {C : Type} (O : Oracles C) (u v : C) : Prop :=
  u ≠ v ∧ O.cost u v ≤ O.radius ∧ O.cost v u ≤ O.radius ∧
    O.link u v = true ∧ O.link v u = true

/-- Boolean sPRM edge test. -/
def edgeCond {C : Type} [DecidableEq C] (O : Oracles C) (u v : C) : Bool :=
  decide (IsSprmEdge O u v)

/-- The Boolean edge test agrees with the propositional predicate. -/
theorem edgeCond_eq_true {C : Type} [DecidableEq C] (O : Oracles C) (u v : C) :
    edgeCond O u v = true ↔ IsSprmEdge O u v := by
  unfold edgeCond
  rw [decide_eq_true_eq]

/-- The edge predicate is symmetric. -/
theorem IsSprmEdge_symm {C : Type} (O : Oracles C) (u v : C)
    (h : IsSprmEdge O u v) : IsSprmEdge O v u := by
  unfold IsSprmEdge at h ⊢
  obtain ⟨hne, hc1, hc2, hl1, hl2⟩ := h
  exact ⟨Ne.symm hne, hc2, hc1, hl2, hl1⟩

/-- Edges from `u` to the vertices in `vs` that pass the edge test. -/
def pairsWith {C : Type} [DecidableEq C] (O : Oracles C) (u : C) (vs : List C) :
    List (C × C) :=
  (vs.filter (fun v => edgeCond O u v)).map (fun v => (u, v))

/-- Membership in `pairsWith` gives the edge predicate. -/
theorem mem_pairsWith {C : Type} [DecidableEq C] (O : Oracles C) (u : C)
    (vs : List C) (a b : C) (h : (a, b) ∈ pairsWith O u vs) :
    a = u ∧ b ∈ vs ∧ IsSprmEdge O a b := by
  unfold pairsWith at h
  simp only [List.mem_map, List.mem_filter] at h
  obtain ⟨v, ⟨hvmem, hcond⟩, hpair⟩ := h
  have h1 : u = a := congrArg Prod.fst hpair
  have h2 : v = b := congrArg Prod.snd hpair
  refine ⟨h1.symm, ?_, ?_⟩
  · rw [← h2]
    exact hvmem
  · have he := (edgeCond_eq_true O u v).mp hcond
    rw [h1, h2] at he
    exact he

/-- All unordered vertex pairs, each once, filtered by the edge test. -/
def allPairs {C : Type} [DecidableEq C] (O : Oracles C) : List C → List (C × C)
  | [] => []
  | u :: vs => pairsWith O u vs ++ allPairs O vs

theorem allPairs_nil {C : Type} [DecidableEq C] (O : Oracles C) :
    allPairs O ([] : List C) = [] := rfl

theorem allPairs_cons {C : Type} [DecidableEq C] (O : Oracles C) (u : C)
    (vs : List C) :
    allPairs O (u :: vs) = pairsWith O u vs ++ allPairs O vs := rfl

/-- Membership in `allPairs` gives vertices and the edge predicate. -/
theorem mem_allPairs {C : Type} [DecidableEq C] (O : Oracles C) (vs : List C) :
    ∀ (a b : C), (a, b) ∈ allPairs O vs →
      a ∈ vs ∧ b ∈ vs ∧ IsSprmEdge O a b := by
  induction vs with
  | nil =>
      intro a b h
      rw [allPairs_nil] at h
      simp at h
  | cons u vs ih =>
      intro a b h
      rw [allPairs_cons, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨rfl, hbmem, hedge⟩ := mem_pairsWith O u vs a b h
        refine ⟨?_, ?_, hedge⟩
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ hbmem
      · have h' := ih a b h
        obtain ⟨hamem, hbmem, hedge⟩ := h'
        refine ⟨?_, ?_, hedge⟩
        · exact List.mem_cons_of_mem _ hamem
        · exact List.mem_cons_of_mem _ hbmem

/-- sPRM edges: each unordered pair of distinct vertices once, when the cost
bound holds and the local planner succeeds in both directions. -/
def sprmEdges {C : Type} [DecidableEq C] (O : Oracles C) (samples : List C) :
    List (C × C) :=
  allPairs O (sprmVertices O samples)

/-- Edges attach to vertices and satisfy the edge predicate. -/
theorem sprmEdges_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) (u v : C) (h : (u, v) ∈ sprmEdges O samples) :
    u ∈ sprmVertices O samples ∧ v ∈ sprmVertices O samples ∧
      IsSprmEdge O u v :=
  mem_allPairs O (sprmVertices O samples) u v h

/-- sPRM edges are symmetric: the swapped pair satisfies the edge predicate. -/
theorem sprmEdges_symmetric {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) (u v : C) (h : (u, v) ∈ sprmEdges O samples) :
    IsSprmEdge O v u :=
  IsSprmEdge_symm O u v (sprmEdges_mem O samples u v h).2.2

/-- The undirected sPRM edge set: each edge plus its reversal. -/
def sprmEdgesUndirected {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) : List (C × C) :=
  sprmEdges O samples ++ (sprmEdges O samples).map Prod.swap

/-- The reversal of an edge lies in the undirected edge set. -/
theorem mem_sprmEdgesUndirected_swap {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) (u v : C) (h : (u, v) ∈ sprmEdges O samples) :
    (v, u) ∈ sprmEdgesUndirected O samples := by
  unfold sprmEdgesUndirected
  simp only [List.mem_append]
  refine Or.inr ?_
  rw [List.mem_map]
  exact ⟨(u, v), h, rfl⟩

/-- PRM* vertices: the same collision-free deduplicated samples as sPRM. The
vertex set does not depend on the radius schedule. -/
def prmStarVertices {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) : List C :=
  sprmVertices O samples

/-- PRM* and sPRM share the same vertex set. -/
theorem prmStarVertices_eq {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) : prmStarVertices O samples = sprmVertices O samples :=
  rfl

/-- Membership in the PRM* vertices: a sample that is collision free. -/
theorem prmStarVertices_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) (v : C) :
    v ∈ prmStarVertices O samples ↔ v ∈ samples ∧ O.free v = true :=
  sprmVertices_mem O samples v

/-- Propositional PRM* edge predicate at `n` vertices: like `IsSprmEdge` with
the connection radius `radiusOf n`. -/
abbrev IsPrmStarEdge {C : Type} (O : Oracles C) (radiusOf : Nat → Rat) (n : Nat)
    (u v : C) : Prop :=
  IsSprmEdge { O with radius := radiusOf n } u v

/-- PRM* edges: each unordered pair of distinct vertices once, connecting when
the cost bound at `radiusOf` (vertex count) holds in both directions and the
local planner succeeds in both directions. -/
def prmStarEdges {C : Type} [DecidableEq C] (O : Oracles C)
    (radiusOf : Nat → Rat) (samples : List C) : List (C × C) :=
  allPairs { O with radius := radiusOf (prmStarVertices O samples).length }
    (prmStarVertices O samples)

/-- Edges attach to vertices and satisfy the PRM* edge predicate. -/
theorem prmStarEdges_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (radiusOf : Nat → Rat) (samples : List C) (u v : C)
    (h : (u, v) ∈ prmStarEdges O radiusOf samples) :
    u ∈ prmStarVertices O samples ∧ v ∈ prmStarVertices O samples ∧
      IsPrmStarEdge O radiusOf (prmStarVertices O samples).length u v :=
  mem_allPairs _ _ u v h

/-- With a constant radius schedule, PRM* reduces to sPRM. -/
theorem prmStarEdges_const_radius {C : Type} [DecidableEq C] (O : Oracles C)
    (samples : List C) :
    prmStarEdges O (fun _ => O.radius) samples = sprmEdges O samples := rfl

/-- Nearest current vertex to `s` by cost: the first minimizer in list order,
computed by a left fold that keeps the first vertex attaining the minimum.
`dflt` is returned for the empty list. -/
def nearest {C : Type} (O : Oracles C) (verts : List C) (dflt : C) (s : C) : C :=
  match verts with
  | [] => dflt
  | v :: vs =>
      vs.foldl (fun best w => if O.cost w s < O.cost best s then w else best) v

/-- RRT growth folded over the samples by structural recursion. For each sample
`s` that is collision free, links the nearest current vertex to `s` when the
local planner succeeds. Samples already in the tree are skipped. -/
def rrtAux {C : Type} [DecidableEq C] (O : Oracles C) (start : C) :
    List C → List C → List (C × C) → List C × List (C × C)
  | [], verts, edges => (verts, edges)
  | s :: ss, verts, edges =>
      if O.free s = true ∧ O.link (nearest O verts start s) s = true ∧ s ∉ verts then
        rrtAux O start ss (s :: verts) ((nearest O verts start s, s) :: edges)
      else
        rrtAux O start ss verts edges

theorem rrtAux_nil {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (verts : List C) (edges : List (C × C)) :
    rrtAux O start [] verts edges = (verts, edges) := rfl

theorem rrtAux_cons {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (s : C) (ss : List C) (verts : List C) (edges : List (C × C)) :
    rrtAux O start (s :: ss) verts edges =
      (if O.free s = true ∧ O.link (nearest O verts start s) s = true ∧ s ∉ verts then
        rrtAux O start ss (s :: verts) ((nearest O verts start s, s) :: edges)
      else
        rrtAux O start ss verts edges) := rfl

/-- Fold invariant: edge targets stay in the vertex list and the tree property
(duplicate-free edge targets) is preserved. -/
theorem rrtAux_invar {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (ss : List C) :
    ∀ (verts : List C) (edges : List (C × C)),
      (∀ e ∈ edges, e.2 ∈ verts) →
      (edges.map Prod.snd).Nodup →
      (∀ e ∈ (rrtAux O start ss verts edges).2,
        e.2 ∈ (rrtAux O start ss verts edges).1) ∧
        (((rrtAux O start ss verts edges).2.map Prod.snd).Nodup) := by
  induction ss with
  | nil =>
      intro verts edges hmem hnd
      rw [rrtAux_nil]
      exact ⟨hmem, hnd⟩
  | cons s ss ih =>
      intro verts edges hmem hnd
      rw [rrtAux_cons]
      by_cases hcond :
        O.free s = true ∧ O.link (nearest O verts start s) s = true ∧ s ∉ verts
      · rw [ite_eq_left hcond]
        obtain ⟨-, -, hnotmem⟩ := hcond
        apply ih
        · intro e he
          simp only [List.mem_cons] at he ⊢
          rcases he with rfl | he
          · exact Or.inl rfl
          · exact Or.inr (hmem e he)
        · simp only [List.map_cons]
          rw [List.nodup_cons]
          refine ⟨?_, hnd⟩
          intro hcon
          rw [List.mem_map] at hcon
          obtain ⟨e, he, heq⟩ := hcon
          have hve := hmem e he
          rw [heq] at hve
          exact hnotmem hve
      · rw [ite_eq_right hcond]
        exact ih _ _ hmem hnd

/-- Fold invariant: vertices come from the start configuration or the samples
seen so far. -/
theorem rrtAux_subset {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (ss : List C) (seen : List C) :
    ∀ (verts : List C) (edges : List (C × C)),
      (∀ v ∈ verts, v = start ∨ v ∈ seen) →
      ∀ v ∈ (rrtAux O start ss verts edges).1,
        v = start ∨ v ∈ seen ∨ v ∈ ss := by
  induction ss generalizing seen with
  | nil =>
      intro verts edges h v hv
      rw [rrtAux_nil] at hv
      have hv' : v ∈ verts := hv
      rcases h v hv' with rfl | h'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h')
  | cons s ss ih =>
      intro verts edges h v hv
      rw [rrtAux_cons] at hv
      by_cases hcond :
        O.free s = true ∧ O.link (nearest O verts start s) s = true ∧ s ∉ verts
      · rw [ite_eq_left hcond] at hv
        have hstep : ∀ w ∈ s :: verts, w = start ∨ w ∈ s :: seen := by
          intro w hw
          simp only [List.mem_cons] at hw ⊢
          rcases hw with rfl | hw
          · exact Or.inr (Or.inl rfl)
          · rcases h w hw with rfl | hw'
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hw')
        have hmem := ih (s :: seen) (s :: verts) _ hstep v hv
        simp only [List.mem_cons] at hmem ⊢
        rcases hmem with rfl | (rfl | h') | h'
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr h'))
      · rw [ite_eq_right hcond] at hv
        have hmem := ih seen verts edges h v hv
        simp only [List.mem_cons] at ⊢
        rcases hmem with rfl | h' | h'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr h'))

/-- Fold invariant: at most one edge is added per sample. -/
theorem rrtAux_length {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (ss : List C) :
    ∀ (verts : List C) (edges : List (C × C)),
      (rrtAux O start ss verts edges).2.length ≤ ss.length + edges.length := by
  induction ss with
  | nil =>
      intro verts edges
      rw [rrtAux_nil]
      show edges.length ≤ [].length + edges.length
      omega
  | cons s ss ih =>
      intro verts edges
      rw [rrtAux_cons]
      by_cases hcond :
        O.free s = true ∧ O.link (nearest O verts start s) s = true ∧ s ∉ verts
      · rw [ite_eq_left hcond]
        have h := ih (s :: verts) ((nearest O verts start s, s) :: edges)
        simp only [List.length_cons] at h ⊢
        omega
      · rw [ite_eq_right hcond]
        have h := ih verts edges
        simp only [List.length_cons] at h ⊢
        omega

/-- Fold invariant: every vertex other than the start is the target of some
edge. -/
theorem rrtAux_edge_of_mem {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (ss : List C) :
    ∀ (verts : List C) (edges : List (C × C)),
      (∀ v ∈ verts, v = start ∨ v ∈ edges.map Prod.snd) →
      ∀ v ∈ (rrtAux O start ss verts edges).1,
        v = start ∨ v ∈ (rrtAux O start ss verts edges).2.map Prod.snd := by
  induction ss with
  | nil =>
      intro verts edges h v hv
      rw [rrtAux_nil] at hv
      exact h v hv
  | cons s ss ih =>
      intro verts edges h v hv
      rw [rrtAux_cons] at hv ⊢
      by_cases hcond :
        O.free s = true ∧ O.link (nearest O verts start s) s = true ∧ s ∉ verts
      · rw [ite_eq_left hcond] at hv ⊢
        have hstep : ∀ w ∈ s :: verts,
            w = start ∨
              w ∈ ((nearest O verts start s, s) :: edges).map Prod.snd := by
          intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact Or.inr List.mem_cons_self
          · rcases h w hw with rfl | hw'
            · exact Or.inl rfl
            · exact Or.inr (List.mem_cons_of_mem _ hw')
        exact ih _ _ hstep v hv
      · rw [ite_eq_right hcond] at hv ⊢
        exact ih _ _ h v hv

/-- RRT: grow a tree from `start` by folding over `samples`. Returns the vertex
list and the edge list. -/
def rrt {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) : List C × List (C × C) :=
  rrtAux O start samples [start] []

/-- RRT vertices lie in `start :: samples`. -/
theorem rrt_verts_subset {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) (v : C) (hv : v ∈ (rrt O start samples).1) :
    v ∈ start :: samples := by
  have h0 : ∀ w ∈ ([start] : List C), w = start ∨ w ∈ ([] : List C) := by
    intro w hw
    simp at hw
    exact Or.inl hw
  have hv' : v ∈ (rrtAux O start samples [start] []).1 := hv
  have h1 := rrtAux_subset O start samples [] [start] [] h0 v hv'
  simpa using h1

/-- RRT invariant at the top level: edges attach to vertices and form a tree. -/
theorem rrt_invar {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) :
    (∀ e ∈ (rrt O start samples).2, e.2 ∈ (rrt O start samples).1) ∧
      (((rrt O start samples).2.map Prod.snd).Nodup) := by
  have hmem : ∀ e ∈ ([] : List (C × C)), e.2 ∈ [start] := by
    intro e he
    simp at he
  have hnd : (([] : List (C × C)).map Prod.snd).Nodup := by
    simp only [List.map_nil]
    exact List.nodup_nil
  have h := rrtAux_invar O start samples [start] [] hmem hnd
  exact h

/-- Tree property: edge targets are duplicate free, so every vertex has at most
one incoming edge (existence of the incoming edge is `rrt_edge_of_mem`). -/
theorem rrt_tree {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) : ((rrt O start samples).2.map Prod.snd).Nodup :=
  (rrt_invar O start samples).2

/-- Every RRT vertex other than the start is the target of some edge. -/
theorem rrt_edge_of_mem {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) (v : C) (hv : v ∈ (rrt O start samples).1)
    (hne : v ≠ start) : v ∈ (rrt O start samples).2.map Prod.snd := by
  have h0 : ∀ w ∈ ([start] : List C),
      w = start ∨ w ∈ ([] : List (C × C)).map Prod.snd := by
    intro w hw
    simp at hw
    exact Or.inl hw
  have h1 := rrtAux_edge_of_mem O start samples [start] [] h0 v hv
  rcases h1 with rfl | h1
  · exact absurd rfl hne
  · exact h1

/-- Every RRT edge target is an RRT vertex. -/
theorem rrt_edge_snd_mem {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) (e : C × C) (he : e ∈ (rrt O start samples).2) :
    e.2 ∈ (rrt O start samples).1 :=
  (rrt_invar O start samples).1 e he

/-- RRT edge count is bounded by the sample count. -/
theorem rrt_edges_length {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) : (rrt O start samples).2.length ≤ samples.length := by
  have h := rrtAux_length O start samples [start] []
  simp at h
  unfold rrt
  exact h

/-- Cost-to-come lookup in an association list, `(0, 1)` when absent. RRT*
keeps an entry for every tree vertex, so the default is unreachable on states
produced by `rrtStarAux`. -/
def costToCome {C : Type} [DecidableEq C] :
    List (C × (Int × Nat)) → C → Int × Nat
  | [], _ => (0, 1)
  | (v, c) :: rest, w => if v = w then c else costToCome rest w

/-- Pushing an entry for another vertex does not change lookup. -/
theorem costToCome_cons_ne {C : Type} [DecidableEq C]
    (costs : List (C × (Int × Nat)))
    (v w : C) (c : Int × Nat) (hne : v ≠ w) :
    costToCome ((v, c) :: costs) w = costToCome costs w := by
  simp only [costToCome, ite_eq_right hne]

/- Costs are unnormalized numerator/denominator pairs: kernel `decide`
evaluation gets stuck on `Rat` addition (fraction normalization), so RRT*
keeps the numerator and denominator separate with manual cross-multiplied
arithmetic instead of `Rat` operations. -/

/-- Add a `Rat` edge cost to an unnormalized cost-to-come pair. -/
def ccAdd (p : Int × Nat) (r : Rat) : Int × Nat :=
  (p.1 * (r.den : Int) + r.num * (p.2 : Int), p.2 * r.den)

/-- Strict comparison of unnormalized cost-to-come pairs by cross
multiplication. -/
abbrev ccLt (p q : Int × Nat) : Prop :=
  p.1 * (q.2 : Int) < q.1 * (p.2 : Int)

/-- Candidate parents of `s`: current vertices within `O.radius` whose local
planner reaches `s`. -/
def candidates {C : Type} [DecidableEq C] (O : Oracles C) (verts : List C)
    (s : C) : List C :=
  verts.filter (fun v => decide (O.cost v s ≤ O.radius ∧ O.link v s = true))

/-- Choose the parent of `s`: the candidate minimizing cost-to-come plus edge
cost, breaking ties by first occurrence in list order (the same convention as
`nearest`). `none` when there is no candidate. -/
def chooseParent {C : Type} [DecidableEq C] (O : Oracles C)
    (costs : List (C × (Int × Nat))) (verts : List C) (s : C) : Option C :=
  match candidates O verts s with
  | [] => none
  | v :: vs =>
      some (vs.foldl
        (fun best w =>
          if ccLt (ccAdd (costToCome costs w) (O.cost w s))
              (ccAdd (costToCome costs best) (O.cost best s)) then w else best)
        v)

/-- Rewire pass over `ws` (the tree vertices in list order) after adding `s`
under parent `p`: a vertex `w` gets parent edge `(s, w)` and updated cost when
it is within radius, the local planner links `s` to `w`, and routing through
`s` is strictly cheaper. The start vertex is never rewired, so its cost stays
`(0, 1)`. Single pass, no cascade: cost updates do not trigger further passes. -/
def rewireAux {C : Type} [DecidableEq C] (O : Oracles C) (start s p : C) :
    List C → List (C × C) → List (C × (Int × Nat)) →
      List (C × C) × List (C × (Int × Nat))
  | [], edges, costs => (edges, costs)
  | w :: ws, edges, costs =>
      if w ≠ p ∧ w ≠ s ∧ w ≠ start ∧ O.cost s w ≤ O.radius ∧
          O.link s w = true ∧
          ccLt (ccAdd (costToCome costs s) (O.cost s w))
            (costToCome costs w) then
        rewireAux O start s p ws
          (edges.map (fun e => if e.2 = w then (s, w) else e))
          ((w, ccAdd (costToCome costs s) (O.cost s w)) :: costs)
      else
        rewireAux O start s p ws edges costs

theorem rewireAux_nil {C : Type} [DecidableEq C] (O : Oracles C)
    (start s p : C) (edges : List (C × C)) (costs : List (C × (Int × Nat))) :
    rewireAux O start s p [] edges costs = (edges, costs) := rfl

theorem rewireAux_cons {C : Type} [DecidableEq C] (O : Oracles C)
    (start s p : C) (w : C) (ws : List C) (edges : List (C × C))
    (costs : List (C × (Int × Nat))) :
    rewireAux O start s p (w :: ws) edges costs =
      (if w ≠ p ∧ w ≠ s ∧ w ≠ start ∧ O.cost s w ≤ O.radius ∧
          O.link s w = true ∧
          ccLt (ccAdd (costToCome costs s) (O.cost s w))
            (costToCome costs w) then
        rewireAux O start s p ws
          (edges.map (fun e => if e.2 = w then (s, w) else e))
          ((w, ccAdd (costToCome costs s) (O.cost s w)) :: costs)
      else
        rewireAux O start s p ws edges costs) := rfl

/-- Replacing a parent edge leaves the target list unchanged. -/
theorem map_replace_snd_eq {C : Type} [DecidableEq C] (edges : List (C × C))
    (s w : C) :
    ((edges.map (fun e => if e.2 = w then (s, w) else e)).map Prod.snd) =
      edges.map Prod.snd := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
      by_cases h : e.2 = w
      · simp only [List.map_cons, ite_eq_left h, ih]
        rw [h]
      · simp only [List.map_cons, ite_eq_right h, ih]

/-- Rewire invariant: edge targets stay in the vertex list and the tree property
(duplicate-free edge targets) is preserved, since rewiring only replaces
parent edges. -/
theorem rewireAux_invar {C : Type} [DecidableEq C] (O : Oracles C)
    (start s p : C) (ws : List C) :
    ∀ (edges : List (C × C)) (costs : List (C × (Int × Nat)))
      (verts : List C),
      (∀ w ∈ ws, w ∈ verts) →
      (∀ e ∈ edges, e.2 ∈ verts) →
      (edges.map Prod.snd).Nodup →
      (∀ e ∈ (rewireAux O start s p ws edges costs).1, e.2 ∈ verts) ∧
        (((rewireAux O start s p ws edges costs).1.map Prod.snd).Nodup) := by
  induction ws with
  | nil =>
      intro edges costs verts _ hmem hnd
      rw [rewireAux_nil]
      exact ⟨hmem, hnd⟩
  | cons w ws ih =>
      intro edges costs verts hsub hmem hnd
      rw [rewireAux_cons]
      by_cases hcond : w ≠ p ∧ w ≠ s ∧ w ≠ start ∧ O.cost s w ≤ O.radius ∧
        O.link s w = true ∧
        ccLt (ccAdd (costToCome costs s) (O.cost s w)) (costToCome costs w)
      · rw [ite_eq_left hcond]
        have hwv : w ∈ verts := hsub w List.mem_cons_self
        have hsub' : ∀ w' ∈ ws, w' ∈ verts :=
          fun w' hw' => hsub w' (List.mem_cons_of_mem w hw')
        have hmem' : ∀ e' ∈ edges.map (fun e => if e.2 = w then (s, w) else e),
            e'.2 ∈ verts := by
          intro e' he'
          rw [List.mem_map] at he'
          obtain ⟨e, he, rfl⟩ := he'
          by_cases h : e.2 = w
          · rw [ite_eq_left h]
            exact hwv
          · rw [ite_eq_right h]
            exact hmem e he
        have hnd' : ((edges.map
            (fun e => if e.2 = w then (s, w) else e)).map Prod.snd).Nodup := by
          rw [map_replace_snd_eq]
          exact hnd
        exact ih _ _ _ hsub' hmem' hnd'
      · rw [ite_eq_right hcond]
        have hsub' : ∀ w' ∈ ws, w' ∈ verts :=
          fun w' hw' => hsub w' (List.mem_cons_of_mem w hw')
        exact ih _ _ _ hsub' hmem hnd

/-- Rewire never changes the start vertex cost: every inserted key differs from
`start`. -/
theorem rewireAux_cost_start {C : Type} [DecidableEq C] (O : Oracles C)
    (start s p : C) (ws : List C) :
    ∀ (edges : List (C × C)) (costs : List (C × (Int × Nat))),
      costToCome costs start = (0, 1) →
      costToCome (rewireAux O start s p ws edges costs).2 start = (0, 1) := by
  induction ws with
  | nil =>
      intro edges costs h
      rw [rewireAux_nil]
      exact h
  | cons w ws ih =>
      intro edges costs h
      rw [rewireAux_cons]
      by_cases hcond : w ≠ p ∧ w ≠ s ∧ w ≠ start ∧ O.cost s w ≤ O.radius ∧
        O.link s w = true ∧
        ccLt (ccAdd (costToCome costs s) (O.cost s w)) (costToCome costs w)
      · rw [ite_eq_left hcond]
        obtain ⟨-, -, hne, -, -, -⟩ := hcond
        have h' : costToCome
            ((w, ccAdd (costToCome costs s) (O.cost s w)) :: costs) start
            = (0, 1) := by
          rw [costToCome_cons_ne _ _ _ _ hne]
          exact h
        exact ih _ _ h'
      · rw [ite_eq_right hcond]
        exact ih _ _ h

/-- Extend the tree with the free fresh sample `s` under parent `p`: add vertex
`s` with parent edge `(p, s)` and cost, then run the rewire pass. -/
def extendStar {C : Type} [DecidableEq C] (O : Oracles C) (start s p : C)
    (verts : List C) (edges : List (C × C)) (costs : List (C × (Int × Nat))) :
    List C × List (C × C) × List (C × (Int × Nat)) :=
  let cs := ccAdd (costToCome costs p) (O.cost p s)
  let rw := rewireAux O start s p verts ((p, s) :: edges) ((s, cs) :: costs)
  (s :: verts, rw.1, rw.2)

/-- Extension preserves attachment and the tree property. -/
theorem extendStar_invar {C : Type} [DecidableEq C] (O : Oracles C)
    (start s p : C) (verts : List C) (edges : List (C × C))
    (costs : List (C × (Int × Nat))) (hs : s ∉ verts)
    (hmem : ∀ e ∈ edges, e.2 ∈ verts)
    (hnd : (edges.map Prod.snd).Nodup) :
    (∀ e ∈ (extendStar O start s p verts edges costs).2.1, e.2 ∈ s :: verts) ∧
      (((extendStar O start s p verts edges costs).2.1.map Prod.snd).Nodup) := by
  have hsub : ∀ w ∈ verts, w ∈ s :: verts :=
    fun w hw => List.mem_cons_of_mem s hw
  have hmem' : ∀ e ∈ (p, s) :: edges, e.2 ∈ s :: verts := by
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem s (hmem e he)
  have hnd' : (((p, s) :: edges).map Prod.snd).Nodup := by
    simp only [List.map_cons]
    rw [List.nodup_cons]
    refine ⟨?_, hnd⟩
    intro hcon
    rw [List.mem_map] at hcon
    obtain ⟨e, he, heq⟩ := hcon
    have hve := hmem e he
    rw [heq] at hve
    exact hs hve
  exact rewireAux_invar O start s p verts _ _ _ hsub hmem' hnd'

/-- Extension keeps the start vertex cost at `(0, 1)`. -/
theorem extendStar_cost_start {C : Type} [DecidableEq C] (O : Oracles C)
    (start s p : C) (verts : List C) (edges : List (C × C))
    (costs : List (C × (Int × Nat))) (hmem : start ∈ verts) (hs : s ∉ verts)
    (h0 : costToCome costs start = (0, 1)) :
    costToCome (extendStar O start s p verts edges costs).2.2 start
      = (0, 1) := by
  have hne : s ≠ start := by
    intro h
    rw [h] at hs
    exact hs hmem
  have h' : costToCome
      ((s, ccAdd (costToCome costs p) (O.cost p s)) :: costs) start
      = (0, 1) := by
    rw [costToCome_cons_ne _ _ _ _ hne]
    exact h0
  exact rewireAux_cost_start O start s p verts _ _ h'

/-- RRT* growth folded over the samples by structural recursion. For each
collision-free sample `s` not already in the tree, `chooseParent` picks the
parent minimizing cost-to-come plus edge cost; `extendStar` adds `s` and runs
the rewire pass. Samples already in the tree are skipped. -/
def rrtStarAux {C : Type} [DecidableEq C] (O : Oracles C) (start : C) :
    List C → List C → List (C × C) → List (C × (Int × Nat)) →
      List C × List (C × C) × List (C × (Int × Nat))
  | [], verts, edges, costs => (verts, edges, costs)
  | s :: ss, verts, edges, costs =>
      if O.free s = true ∧ s ∉ verts then
        match chooseParent O costs verts s with
        | none => rrtStarAux O start ss verts edges costs
        | some p =>
            let st := extendStar O start s p verts edges costs
            rrtStarAux O start ss st.1 st.2.1 st.2.2
      else
        rrtStarAux O start ss verts edges costs

theorem rrtStarAux_nil {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (verts : List C) (edges : List (C × C)) (costs : List (C × (Int × Nat))) :
    rrtStarAux O start [] verts edges costs = (verts, edges, costs) := rfl

theorem rrtStarAux_cons {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (s : C) (ss : List C) (verts : List C) (edges : List (C × C))
    (costs : List (C × (Int × Nat))) :
    rrtStarAux O start (s :: ss) verts edges costs =
      (if O.free s = true ∧ s ∉ verts then
        match chooseParent O costs verts s with
        | none => rrtStarAux O start ss verts edges costs
        | some p =>
            let st := extendStar O start s p verts edges costs
            rrtStarAux O start ss st.1 st.2.1 st.2.2
      else
        rrtStarAux O start ss verts edges costs) := rfl

/-- Fold invariant: edge targets stay in the vertex list and the tree property
(duplicate-free edge targets) is preserved. -/
theorem rrtStarAux_invar {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (ss : List C) :
    ∀ (verts : List C) (edges : List (C × C)) (costs : List (C × (Int × Nat))),
      (∀ e ∈ edges, e.2 ∈ verts) →
      (edges.map Prod.snd).Nodup →
      (∀ e ∈ (rrtStarAux O start ss verts edges costs).2.1,
        e.2 ∈ (rrtStarAux O start ss verts edges costs).1) ∧
        (((rrtStarAux O start ss verts edges costs).2.1.map Prod.snd).Nodup) := by
  induction ss with
  | nil =>
      intro verts edges costs hmem hnd
      rw [rrtStarAux_nil]
      exact ⟨hmem, hnd⟩
  | cons s ss ih =>
      intro verts edges costs hmem hnd
      rw [rrtStarAux_cons]
      by_cases hcond : O.free s = true ∧ s ∉ verts
      · rw [ite_eq_left hcond]
        cases hcp : chooseParent O costs verts s with
        | none =>
            show (∀ e ∈ (rrtStarAux O start ss verts edges costs).2.1,
              e.2 ∈ (rrtStarAux O start ss verts edges costs).1) ∧ _
            exact ih _ _ _ hmem hnd
        | some p =>
            show (∀ e ∈ (rrtStarAux O start ss
              (extendStar O start s p verts edges costs).1 _ _).2.1, _) ∧ _
            have hext :=
              extendStar_invar O start s p verts edges costs hcond.2 hmem hnd
            exact ih (extendStar O start s p verts edges costs).1
              (extendStar O start s p verts edges costs).2.1
              (extendStar O start s p verts edges costs).2.2 hext.1 hext.2
      · rw [ite_eq_right hcond]
        exact ih _ _ _ hmem hnd

/-- Fold invariant: vertices come from the start configuration or the samples
seen so far. -/
theorem rrtStarAux_subset {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (ss : List C) (seen : List C) :
    ∀ (verts : List C) (edges : List (C × C)) (costs : List (C × (Int × Nat))),
      (∀ v ∈ verts, v = start ∨ v ∈ seen) →
      ∀ v ∈ (rrtStarAux O start ss verts edges costs).1,
        v = start ∨ v ∈ seen ∨ v ∈ ss := by
  induction ss generalizing seen with
  | nil =>
      intro verts edges costs h v hv
      rw [rrtStarAux_nil] at hv
      have hv' : v ∈ verts := hv
      rcases h v hv' with rfl | h'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl h')
  | cons s ss ih =>
      intro verts edges costs h v hv
      rw [rrtStarAux_cons] at hv
      by_cases hcond : O.free s = true ∧ s ∉ verts
      · rw [ite_eq_left hcond] at hv
        cases hcp : chooseParent O costs verts s with
        | none =>
            rw [hcp] at hv
            have hv' : v ∈ (rrtStarAux O start ss verts edges costs).1 := hv
            have hmem := ih seen verts edges costs h v hv'
            simp only [List.mem_cons] at ⊢
            rcases hmem with rfl | h' | h'
            · exact Or.inl rfl
            · exact Or.inr (Or.inl h')
            · exact Or.inr (Or.inr (Or.inr h'))
        | some p =>
            rw [hcp] at hv
            have hv' : v ∈ (rrtStarAux O start ss
              (extendStar O start s p verts edges costs).1 _ _).1 := hv
            have hstep : ∀ w ∈ s :: verts, w = start ∨ w ∈ s :: seen := by
              intro w hw
              simp only [List.mem_cons] at hw ⊢
              rcases hw with rfl | hw
              · exact Or.inr (Or.inl rfl)
              · rcases h w hw with rfl | hw'
                · exact Or.inl rfl
                · exact Or.inr (Or.inr hw')
            have hstep' : ∀ w ∈ (extendStar O start s p verts edges costs).1,
                w = start ∨ w ∈ s :: seen := hstep
            have hmem := ih (s :: seen) _ _ _ hstep' v hv'
            simp only [List.mem_cons] at hmem ⊢
            rcases hmem with rfl | (rfl | h') | h'
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inl h')
            · exact Or.inr (Or.inr (Or.inr h'))
      · rw [ite_eq_right hcond] at hv
        have hmem := ih seen verts edges costs h v hv
        simp only [List.mem_cons] at ⊢
        rcases hmem with rfl | h' | h'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inr h'))

/-- Fold invariant: the start configuration stays in the vertex list. -/
theorem rrtStarAux_start_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (ss : List C) :
    ∀ (verts : List C) (edges : List (C × C)) (costs : List (C × (Int × Nat))),
      start ∈ verts → start ∈ (rrtStarAux O start ss verts edges costs).1 := by
  induction ss with
  | nil =>
      intro verts edges costs h
      rw [rrtStarAux_nil]
      exact h
  | cons s ss ih =>
      intro verts edges costs h
      rw [rrtStarAux_cons]
      by_cases hcond : O.free s = true ∧ s ∉ verts
      · rw [ite_eq_left hcond]
        cases hcp : chooseParent O costs verts s with
        | none =>
            show start ∈ (rrtStarAux O start ss verts edges costs).1
            exact ih _ _ _ h
        | some p =>
            show start ∈ (rrtStarAux O start ss
              (extendStar O start s p verts edges costs).1 _ _).1
            exact ih _ _ _ (List.mem_cons_of_mem _ h)
      · rw [ite_eq_right hcond]
        exact ih _ _ _ h

/-- Fold invariant: the start vertex keeps cost-to-come `(0, 1)`. -/
theorem rrtStarAux_cost_start {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (ss : List C) :
    ∀ (verts : List C) (edges : List (C × C)) (costs : List (C × (Int × Nat))),
      start ∈ verts → costToCome costs start = (0, 1) →
      costToCome (rrtStarAux O start ss verts edges costs).2.2 start
        = (0, 1) := by
  induction ss with
  | nil =>
      intro verts edges costs _ h0
      rw [rrtStarAux_nil]
      exact h0
  | cons s ss ih =>
      intro verts edges costs hmem h0
      rw [rrtStarAux_cons]
      by_cases hcond : O.free s = true ∧ s ∉ verts
      · rw [ite_eq_left hcond]
        cases hcp : chooseParent O costs verts s with
        | none =>
            show costToCome (rrtStarAux O start ss verts edges costs).2.2 start
              = (0, 1)
            exact ih _ _ _ hmem h0
        | some p =>
            show costToCome (rrtStarAux O start ss
              (extendStar O start s p verts edges costs).1 _ _).2.2 start
              = (0, 1)
            have hext := extendStar_cost_start O start s p verts edges costs
              hmem hcond.2 h0
            exact ih _ _ _ (List.mem_cons_of_mem _ hmem) hext
      · rw [ite_eq_right hcond]
        exact ih _ _ _ hmem h0

/-- RRT*: grow a tree from `start` by folding over `samples`, choosing each new
sample's parent by cost-to-come plus edge cost and rewiring nearby vertices.
Returns the vertex list, the edge list, and the cost-to-come table. -/
def rrtStar {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) : List C × List (C × C) × List (C × (Int × Nat)) :=
  rrtStarAux O start samples [start] [] [(start, (0, 1))]

/-- RRT* vertices lie in `start :: samples`. -/
theorem rrtStar_verts_subset {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (v : C)
    (hv : v ∈ (rrtStar O start samples).1) : v ∈ start :: samples := by
  have h0 : ∀ w ∈ ([start] : List C), w = start ∨ w ∈ ([] : List C) := by
    intro w hw
    simp at hw
    exact Or.inl hw
  have hv' : v ∈ (rrtStarAux O start samples [start] [] [(start, (0, 1))]).1 :=
    hv
  have h1 :=
    rrtStarAux_subset O start samples [] [start] [] [(start, (0, 1))] h0 v hv'
  simpa using h1

/-- RRT* keeps the tree property: edge targets are duplicate free, so every
vertex has at most one incoming edge. Rewiring only replaces parent edges, so
targets are preserved. -/
theorem rrtStar_tree {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) :
    (((rrtStar O start samples).2.1.map Prod.snd).Nodup) := by
  have hmem : ∀ e ∈ ([] : List (C × C)), e.2 ∈ [start] := by
    intro e he
    simp at he
  have hnd : (([] : List (C × C)).map Prod.snd).Nodup := by
    simp only [List.map_nil]
    exact List.nodup_nil
  exact (rrtStarAux_invar O start samples [start] [] [(start, (0, 1))] hmem hnd).2

/-- The start vertex keeps cost-to-come `(0, 1)`: it is never added as a sample
and never rewired. -/
theorem rrtStar_cost_start {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) :
    costToCome (rrtStar O start samples).2.2 start = (0, 1) := by
  have hmem : start ∈ ([start] : List C) := List.mem_cons_self
  have h0 : costToCome ([(start, (0, 1))] : List (C × (Int × Nat))) start
      = (0, 1) := by
    simp [costToCome]
  exact rrtStarAux_cost_start O start samples [start] [] [(start, (0, 1))] hmem
    h0

end Cslib.Planning.MotionPlanning.SamplingPlanners
