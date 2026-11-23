/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Dedup
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

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
  /-- Costs are nonnegative. -/
  cost_nonneg : ∀ a b, 0 ≤ cost a b
  /-- Self-cost is zero. -/
  cost_self : ∀ a, cost a a = 0
  /-- Costs between distinct configurations are positive. -/
  cost_pos : ∀ a b, a ≠ b → 0 < cost a b

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
/- # Redesigned RRT* region (cost-pair API through `rrtStar`)

Costs are unnormalized numerator/denominator pairs: kernel `decide`
evaluation gets stuck on `Rat` addition (fraction normalization), so RRT*
keeps the numerator and denominator separate with manual cross-multiplied
arithmetic instead of `Rat` operations. The cost table is recomputed from
scratch by Bellman-Ford relaxation after every edge change, so stored costs
are never stale.
-/

/-- Add a `Rat` edge cost to an unnormalized cost-to-come pair. -/
def ccAdd (p : Int × Nat) (r : Rat) : Int × Nat :=
  (p.1 * (r.den : Int) + r.num * (p.2 : Int), p.2 * r.den)

/-- Strict comparison of unnormalized cost-to-come pairs by cross
multiplication. -/
abbrev ccLt (p q : Int × Nat) : Prop :=
  p.1 * (q.2 : Int) < q.1 * (p.2 : Int)

/-- Non-strict comparison of unnormalized cost-to-come pairs by cross
multiplication. -/
abbrev ccLe (p q : Int × Nat) : Prop :=
  p.1 * (q.2 : Int) ≤ q.1 * (p.2 : Int)

/-- Rational value of an unnormalized cost pair. -/
def pairVal (p : Int × Nat) : ℚ :=
  (p.1 : ℚ) / (p.2 : ℚ)

/-- The initial pair reads back as zero. -/
theorem pairVal_init : pairVal (0, 1) = 0 := by
  simp [pairVal]

/-- Every rational has nonzero denominator. -/
theorem rat_den_ne_zero (r : Rat) : r.den ≠ 0 :=
  Rat.den_nz r

/-- Casted denominators are nonzero. -/
theorem rat_den_cast_ne_zero (r : Rat) : ((r.den : Nat) : ℚ) ≠ 0 := by
  exact_mod_cast rat_den_ne_zero r

/-- `ccAdd` is correct for rational values. -/
theorem pairVal_ccAdd (p : Int × Nat) (r : Rat) (hp : (p.2 : ℚ) ≠ 0) :
    pairVal (ccAdd p r) = pairVal p + r := by
  have hd : ((r.den : Nat) : ℚ) ≠ 0 := rat_den_cast_ne_zero r
  set n := r.num with hn
  set d := r.den with hdd
  have hr : r = (n : ℚ) / (d : ℚ) := by
    rw [hn, hdd]
    exact (Rat.num_div_den r).symm
  have hpd : (p.2 : ℚ) * (d : ℚ) ≠ 0 := mul_ne_zero hp hd
  unfold pairVal ccAdd
  rw [← hn, ← hdd, hr]
  push_cast
  field_simp [hp, hd, hpd]

/-- Strict pair order reflects to strict rational order. -/
theorem ccLt_pairVal {p q : Int × Nat} (hp : 0 < (p.2 : ℚ))
    (hq : 0 < (q.2 : ℚ)) (h : ccLt p q) : pairVal p < pairVal q := by
  unfold pairVal at ⊢
  unfold ccLt at h
  rw [div_lt_div_iff₀ hp hq]
  exact_mod_cast h

/-- Non-strict pair order reflects to non-strict rational order. -/
theorem ccLe_pairVal {p q : Int × Nat} (hp : 0 < (p.2 : ℚ))
    (hq : 0 < (q.2 : ℚ)) (h : ccLe p q) : pairVal p ≤ pairVal q := by
  unfold pairVal at ⊢
  unfold ccLe at h
  rw [div_le_div_iff₀ hp hq]
  exact_mod_cast h

/-- Non-strict rational order reflects back to pair order. -/
theorem pairVal_le_ccLe {p q : Int × Nat} (hp : 0 < (p.2 : ℚ))
    (hq : 0 < (q.2 : ℚ)) (h : pairVal p ≤ pairVal q) : ccLe p q := by
  unfold pairVal at h
  unfold ccLe at ⊢
  rw [div_le_div_iff₀ hp hq] at h
  exact_mod_cast h

/-- Mutual pair order is rational equality. -/
theorem ccLe_antisymm_pairVal {p q : Int × Nat} (hp : 0 < (p.2 : ℚ))
    (hq : 0 < (q.2 : ℚ)) (h1 : ccLe p q) (h2 : ccLe q p) :
    pairVal p = pairVal q :=
  le_antisymm (ccLe_pairVal hp hq h1) (ccLe_pairVal hq hp h2)

/-- Rational equality is mutual pair order. -/
theorem pairVal_eq_ccLe {p q : Int × Nat} (hp : 0 < (p.2 : ℚ))
    (hq : 0 < (q.2 : ℚ)) (h : pairVal p = pairVal q) :
    ccLe p q ∧ ccLe q p :=
  ⟨pairVal_le_ccLe hp hq (le_of_eq h), pairVal_le_ccLe hq hp (le_of_eq h.symm)⟩

/-- Reading back a just-consed entry. -/
theorem costToCome_cons_eq {C : Type} [DecidableEq C]
    (costs : List (C × (Int × Nat))) (v : C) (c : Int × Nat) :
    costToCome ((v, c) :: costs) v = c := by
  simp [costToCome]

/-- A costed vertex's read is an actual table entry. -/
theorem costToCome_mem_entry {C : Type} [DecidableEq C]
    (costs : List (C × (Int × Nat))) (v : C)
    (hmem : v ∈ costs.map Prod.fst) :
    ∃ c, (v, c) ∈ costs ∧ costToCome costs v = c := by
  induction costs with
  | nil =>
      simp at hmem
  | cons kv rest ih =>
      obtain ⟨u, c⟩ := kv
      simp only [List.map_cons] at hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨c, List.mem_cons_self, costToCome_cons_eq rest v c⟩
      · obtain ⟨c', hmem', heq⟩ := ih hmem
        by_cases huv : u = v
        · subst huv
          exact ⟨c, List.mem_cons_self, costToCome_cons_eq _ _ _⟩
        · exact ⟨c', List.mem_cons_of_mem _ hmem',
            by simp only [costToCome, ite_eq_right huv]; exact heq⟩

/-- Table denominators stay positive. -/
def DenomsPos {C : Type} (costs : List (C × (Int × Nat))) : Prop :=
  ∀ kv ∈ costs, 0 < kv.2.2

/-- The initial table has positive denominators. -/
theorem denomsPos_init {C : Type} (start : C) :
    DenomsPos ([(start, (0, 1))] : List (C × (Int × Nat))) := by
  intro kv hmem
  simp only [List.mem_singleton] at hmem
  rw [hmem]
  exact one_pos

/-- Consing a positive-denominator entry preserves positivity. -/
theorem denomsPos_cons {C : Type} (costs : List (C × (Int × Nat)))
    (kv : C × (Int × Nat)) (hpos : 0 < kv.2.2)
    (h : DenomsPos costs) : DenomsPos (kv :: costs) := by
  intro kv' hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · exact hpos
  · exact h kv' hmem

/-- A costed vertex's read has positive denominator. -/
theorem denomsPos_costToCome {C : Type} [DecidableEq C]
    (costs : List (C × (Int × Nat))) (v : C)
    (hpos : DenomsPos costs) (hmem : v ∈ costs.map Prod.fst) :
    0 < (costToCome costs v).2 := by
  obtain ⟨c, hmemc, heq⟩ := costToCome_mem_entry costs v hmem
  rw [heq]
  exact hpos (v, c) hmemc

/-- `ccAdd` denominators are positive for positive inputs. -/
theorem ccAdd_den_pos (p : Int × Nat) (r : Rat) (hp : 0 < p.2)
    (hr : 0 < r.den) : 0 < (ccAdd p r).2 :=
  mul_pos hp hr

/-- One Jacobi relaxation step: read the source cost from the pass-start
table `base`, and keep the `ccLe`-minimum in the accumulator `acc`. -/
def relaxEdgeFrom {C : Type} [DecidableEq C] (O : Oracles C)
    (base acc : List (C × (Int × Nat))) (e : C × C) : List (C × (Int × Nat)) :=
  if e.1 ∈ base.map Prod.fst then
    if e.2 ∈ acc.map Prod.fst then
      if ccLt (ccAdd (costToCome base e.1) (O.cost e.1 e.2))
          (costToCome acc e.2) then
        (e.2, ccAdd (costToCome base e.1) (O.cost e.1 e.2)) :: acc
      else acc
    else (e.2, ccAdd (costToCome base e.1) (O.cost e.1 e.2)) :: acc
  else acc

theorem relaxEdgeFrom_of_notmem {C : Type} [DecidableEq C] (O : Oracles C)
    (base acc : List (C × (Int × Nat))) (e : C × C)
    (h : e.1 ∉ base.map Prod.fst) :
    relaxEdgeFrom O base acc e = acc := by
  unfold relaxEdgeFrom
  rw [ite_eq_right h]

theorem relaxEdgeFrom_of_mem_notmem {C : Type} [DecidableEq C] (O : Oracles C)
    (base acc : List (C × (Int × Nat))) (e : C × C)
    (hu : e.1 ∈ base.map Prod.fst) (hv : e.2 ∉ acc.map Prod.fst) :
    relaxEdgeFrom O base acc e =
      (e.2, ccAdd (costToCome base e.1) (O.cost e.1 e.2)) :: acc := by
  unfold relaxEdgeFrom
  rw [ite_eq_left hu, ite_eq_right hv]

theorem relaxEdgeFrom_of_mem_mem_lt {C : Type} [DecidableEq C] (O : Oracles C)
    (base acc : List (C × (Int × Nat))) (e : C × C)
    (hu : e.1 ∈ base.map Prod.fst) (hv : e.2 ∈ acc.map Prod.fst)
    (hlt : ccLt (ccAdd (costToCome base e.1) (O.cost e.1 e.2))
      (costToCome acc e.2)) :
    relaxEdgeFrom O base acc e =
      (e.2, ccAdd (costToCome base e.1) (O.cost e.1 e.2)) :: acc := by
  unfold relaxEdgeFrom
  rw [ite_eq_left hu, ite_eq_left hv, ite_eq_left hlt]

theorem relaxEdgeFrom_of_mem_mem_nlt {C : Type} [DecidableEq C] (O : Oracles C)
    (base acc : List (C × (Int × Nat))) (e : C × C)
    (hu : e.1 ∈ base.map Prod.fst) (hv : e.2 ∈ acc.map Prod.fst)
    (hnlt : ¬ ccLt (ccAdd (costToCome base e.1) (O.cost e.1 e.2))
      (costToCome acc e.2)) :
    relaxEdgeFrom O base acc e = acc := by
  unfold relaxEdgeFrom
  rw [ite_eq_left hu, ite_eq_left hv, ite_eq_right hnlt]

/-- Relaxation never drops costed vertices. -/
theorem relaxEdgeFrom_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (base acc : List (C × (Int × Nat))) (e : C × C) (x : C)
    (hmem : x ∈ acc.map Prod.fst) :
    x ∈ (relaxEdgeFrom O base acc e).map Prod.fst := by
  by_cases hu : e.1 ∈ base.map Prod.fst
  · by_cases hv : e.2 ∈ acc.map Prod.fst
    · by_cases hlt : ccLt (ccAdd (costToCome base e.1) (O.cost e.1 e.2))
        (costToCome acc e.2)
      · rw [relaxEdgeFrom_of_mem_mem_lt O base acc e hu hv hlt]
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr hmem
      · rw [relaxEdgeFrom_of_mem_mem_nlt O base acc e hu hv hlt]
        exact hmem
    · rw [relaxEdgeFrom_of_mem_notmem O base acc e hu hv]
      simp only [List.map_cons, List.mem_cons]
      exact Or.inr hmem
  · rw [relaxEdgeFrom_of_notmem O base acc e hu]
    exact hmem

/-- Relaxation preserves positive denominators. -/
theorem relaxEdgeFrom_denoms {C : Type} [DecidableEq C] (O : Oracles C)
    (base acc : List (C × (Int × Nat))) (e : C × C)
    (hbase : DenomsPos base) (hacc : DenomsPos acc) :
    DenomsPos (relaxEdgeFrom O base acc e) := by
  by_cases hu : e.1 ∈ base.map Prod.fst
  · obtain ⟨cu, hmemu, heq⟩ := costToCome_mem_entry base e.1 hu
    have hcu : 0 < cu.2 := hbase (e.1, cu) hmemu
    have hden : 0 < (O.cost e.1 e.2).den :=
      Nat.pos_of_ne_zero (rat_den_ne_zero _)
    have hnew : 0 < (ccAdd cu (O.cost e.1 e.2)).2 := mul_pos hcu hden
    rw [← heq] at hnew
    by_cases hv : e.2 ∈ acc.map Prod.fst
    · by_cases hlt : ccLt (ccAdd (costToCome base e.1) (O.cost e.1 e.2))
        (costToCome acc e.2)
      · rw [relaxEdgeFrom_of_mem_mem_lt O base acc e hu hv hlt]
        exact denomsPos_cons acc _ hnew hacc
      · rw [relaxEdgeFrom_of_mem_mem_nlt O base acc e hu hv hlt]
        exact hacc
    · rw [relaxEdgeFrom_of_mem_notmem O base acc e hu hv]
      exact denomsPos_cons acc _ hnew hacc
  · rw [relaxEdgeFrom_of_notmem O base acc e hu]
    exact hacc

/-- Relaxation never increases a costed vertex's rational value. -/
theorem relaxEdgeFrom_pairVal_le {C : Type} [DecidableEq C] (O : Oracles C)
    (base acc : List (C × (Int × Nat))) (e : C × C)
    (hbase : DenomsPos base) (hacc : DenomsPos acc) (x : C)
    (hx : x ∈ acc.map Prod.fst) :
    pairVal (costToCome (relaxEdgeFrom O base acc e) x) ≤
      pairVal (costToCome acc x) := by
  by_cases hu : e.1 ∈ base.map Prod.fst
  · have hsrcN : 0 < (costToCome base e.1).2 :=
      denomsPos_costToCome base e.1 hbase hu
    have hdenN : 0 < (O.cost e.1 e.2).den :=
      Nat.pos_of_ne_zero (rat_den_ne_zero _)
    have hcandQ : 0 < ((ccAdd (costToCome base e.1) (O.cost e.1 e.2)).2 : ℚ) := by
      exact_mod_cast ccAdd_den_pos _ _ hsrcN hdenN
    by_cases hv : e.2 ∈ acc.map Prod.fst
    · have holdQ : 0 < ((costToCome acc e.2).2 : ℚ) := by
        exact_mod_cast denomsPos_costToCome acc e.2 hacc hv
      by_cases hlt : ccLt (ccAdd (costToCome base e.1) (O.cost e.1 e.2))
        (costToCome acc e.2)
      · rw [relaxEdgeFrom_of_mem_mem_lt O base acc e hu hv hlt]
        by_cases hxe : x = e.2
        · subst hxe
          have hread : costToCome
              ((e.2, ccAdd (costToCome base e.1) (O.cost e.1 e.2)) :: acc) e.2 =
              ccAdd (costToCome base e.1) (O.cost e.1 e.2) :=
            costToCome_cons_eq acc e.2 _
          rw [hread]
          exact le_of_lt (ccLt_pairVal hcandQ holdQ hlt)
        · have hne : e.2 ≠ x := fun h => hxe h.symm
          simp [costToCome, ite_eq_right hne]
      · rw [relaxEdgeFrom_of_mem_mem_nlt O base acc e hu hv hlt]
    · rw [relaxEdgeFrom_of_mem_notmem O base acc e hu hv]
      by_cases hxe : x = e.2
      · subst hxe
        exact absurd hx hv
      · have hne : e.2 ≠ x := fun h => hxe h.symm
        simp [costToCome, ite_eq_right hne]
  · rw [relaxEdgeFrom_of_notmem O base acc e hu]

/-- Entries after relaxation are old entries or the just-consed candidate. -/
theorem relaxEdgeFrom_entry {C : Type} [DecidableEq C] (O : Oracles C)
    (base acc : List (C × (Int × Nat))) (e : C × C) (kv : C × (Int × Nat))
    (hmem : kv ∈ relaxEdgeFrom O base acc e) :
    kv ∈ acc ∨
      (e.1 ∈ base.map Prod.fst ∧
        kv = (e.2, ccAdd (costToCome base e.1) (O.cost e.1 e.2))) := by
  by_cases hu : e.1 ∈ base.map Prod.fst
  · by_cases hv : e.2 ∈ acc.map Prod.fst
    · by_cases hlt : ccLt (ccAdd (costToCome base e.1) (O.cost e.1 e.2))
        (costToCome acc e.2)
      · rw [relaxEdgeFrom_of_mem_mem_lt O base acc e hu hv hlt] at hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact Or.inr ⟨hu, rfl⟩
        · exact Or.inl hmem
      · rw [relaxEdgeFrom_of_mem_mem_nlt O base acc e hu hv hlt] at hmem
        exact Or.inl hmem
    · rw [relaxEdgeFrom_of_mem_notmem O base acc e hu hv] at hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inr ⟨hu, rfl⟩
      · exact Or.inl hmem
  · rw [relaxEdgeFrom_of_notmem O base acc e hu] at hmem
    exact Or.inl hmem

/-- One full relaxation pass over all edges. -/
def relaxPass {C : Type} [DecidableEq C] (O : Oracles C) (edges : List (C × C))
    (base : List (C × (Int × Nat))) : List (C × (Int × Nat)) :=
  edges.foldl (relaxEdgeFrom O base) base

/-- A pass never drops costed vertices. -/
theorem foldl_relax_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (base : List (C × (Int × Nat))) (l : List (C × C))
    (acc : List (C × (Int × Nat))) (x : C) :
    x ∈ acc.map Prod.fst →
      x ∈ (l.foldl (relaxEdgeFrom O base) acc).map Prod.fst := by
  induction l generalizing acc with
  | nil =>
      intro hmem
      rw [List.foldl_nil]
      exact hmem
  | cons e es ih =>
      intro hmem
      rw [List.foldl_cons]
      exact ih _ (relaxEdgeFrom_mem O base acc e x hmem)

/-- A pass preserves positive denominators. -/
theorem foldl_relax_denoms {C : Type} [DecidableEq C] (O : Oracles C)
    (base : List (C × (Int × Nat))) (l : List (C × C))
    (hbase : DenomsPos base) (acc : List (C × (Int × Nat))) :
    DenomsPos acc → DenomsPos (l.foldl (relaxEdgeFrom O base) acc) := by
  induction l generalizing acc with
  | nil =>
      intro hacc
      rw [List.foldl_nil]
      exact hacc
  | cons e es ih =>
      intro hacc
      rw [List.foldl_cons]
      exact ih _ (relaxEdgeFrom_denoms O base acc e hbase hacc)

/-- A pass never increases a costed vertex's rational value. -/
theorem foldl_relax_pairVal_le {C : Type} [DecidableEq C] (O : Oracles C)
    (base : List (C × (Int × Nat))) (l : List (C × C))
    (hbase : DenomsPos base) (acc : List (C × (Int × Nat))) (x : C) :
    DenomsPos acc → x ∈ acc.map Prod.fst →
      pairVal (costToCome (l.foldl (relaxEdgeFrom O base) acc) x) ≤
        pairVal (costToCome acc x) := by
  induction l generalizing acc with
  | nil =>
      intro hacc hx
      rw [List.foldl_nil]
  | cons e es ih =>
      intro hacc hx
      rw [List.foldl_cons]
      have hmem' : x ∈ (relaxEdgeFrom O base acc e).map Prod.fst :=
        relaxEdgeFrom_mem O base acc e x hx
      have hacc' : DenomsPos (relaxEdgeFrom O base acc e) :=
        relaxEdgeFrom_denoms O base acc e hbase hacc
      have hstep : pairVal (costToCome (relaxEdgeFrom O base acc e) x) ≤
          pairVal (costToCome acc x) :=
        relaxEdgeFrom_pairVal_le O base acc e hbase hacc x hx
      exact le_trans (ih _ hacc' hmem') hstep

/-- Entries after a pass are old entries or fresh candidates from some edge. -/
theorem foldl_relax_entry {C : Type} [DecidableEq C] (O : Oracles C)
    (base : List (C × (Int × Nat))) (l : List (C × C))
    (acc : List (C × (Int × Nat))) (kv : C × (Int × Nat)) :
    kv ∈ l.foldl (relaxEdgeFrom O base) acc →
      kv ∈ acc ∨
        ∃ e ∈ l, e.1 ∈ base.map Prod.fst ∧
          kv = (e.2, ccAdd (costToCome base e.1) (O.cost e.1 e.2)) := by
  induction l generalizing acc with
  | nil =>
      intro hmem
      rw [List.foldl_nil] at hmem
      exact Or.inl hmem
  | cons e es ih =>
      intro hmem
      rw [List.foldl_cons] at hmem
      rcases ih _ hmem with hmem | ⟨e', hmem', hu, heq⟩
      · rcases relaxEdgeFrom_entry O base acc e kv hmem with hmem | ⟨hu, heq⟩
        · exact Or.inl hmem
        · exact Or.inr ⟨e, List.mem_cons_self, hu, heq⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem e hmem', hu, heq⟩

/-- Iterated relaxation passes. -/
def relaxPasses {C : Type} [DecidableEq C] (O : Oracles C) (edges : List (C × C)) :
    ℕ → List (C × (Int × Nat)) → List (C × (Int × Nat))
  | 0, costs => costs
  | n + 1, costs => relaxPass O edges (relaxPasses O edges n costs)

theorem relaxPasses_zero {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (costs : List (C × (Int × Nat))) :
    relaxPasses O edges 0 costs = costs := rfl

theorem relaxPasses_succ {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (n : ℕ) (costs : List (C × (Int × Nat))) :
    relaxPasses O edges (n + 1) costs =
      relaxPass O edges (relaxPasses O edges n costs) := rfl

/-- A pass from a table keeps its costed vertices. -/
theorem relaxPass_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (base : List (C × (Int × Nat))) (x : C)
    (hmem : x ∈ base.map Prod.fst) :
    x ∈ (relaxPass O edges base).map Prod.fst := by
  unfold relaxPass
  exact foldl_relax_mem O base edges base x hmem

/-- A pass from a table keeps denominators positive. -/
theorem relaxPass_denoms {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (base : List (C × (Int × Nat)))
    (h : DenomsPos base) : DenomsPos (relaxPass O edges base) := by
  unfold relaxPass
  exact foldl_relax_denoms O base edges h base h

/-- A pass from a table never increases rational values. -/
theorem relaxPass_pairVal_le {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (base : List (C × (Int × Nat)))
    (h : DenomsPos base) (x : C) (hx : x ∈ base.map Prod.fst) :
    pairVal (costToCome (relaxPass O edges base) x) ≤
      pairVal (costToCome base x) := by
  unfold relaxPass
  exact foldl_relax_pairVal_le O base edges h base x h hx

/-- One more pass keeps costed vertices. -/
theorem relaxPasses_mem_succ {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (n : ℕ) (costs : List (C × (Int × Nat))) (x : C)
    (hmem : x ∈ (relaxPasses O edges n costs).map Prod.fst) :
    x ∈ (relaxPasses O edges (n + 1) costs).map Prod.fst := by
  rw [relaxPasses_succ]
  exact relaxPass_mem O edges _ x hmem

/-- Costed vertices stay costed across passes. -/
theorem relaxPasses_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (n m : ℕ) (costs : List (C × (Int × Nat))) (x : C)
    (hnm : n ≤ m) (hmem : x ∈ (relaxPasses O edges n costs).map Prod.fst) :
    x ∈ (relaxPasses O edges m costs).map Prod.fst := by
  induction hnm with
  | refl => exact hmem
  | step h ih => exact relaxPasses_mem_succ O edges _ _ _ ih

/-- Denominators stay positive across passes. -/
theorem relaxPasses_denoms {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (n : ℕ) (costs : List (C × (Int × Nat)))
    (h : DenomsPos costs) : DenomsPos (relaxPasses O edges n costs) := by
  induction n with
  | zero =>
      rw [relaxPasses_zero]
      exact h
  | succ n ih =>
      rw [relaxPasses_succ]
      exact relaxPass_denoms O edges _ ih

/-- Rational values only decrease across passes. -/
theorem relaxPasses_pairVal_le {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (n m : ℕ) (costs : List (C × (Int × Nat))) (x : C)
    (hden : DenomsPos costs) (hnm : n ≤ m)
    (hx : x ∈ (relaxPasses O edges n costs).map Prod.fst) :
    pairVal (costToCome (relaxPasses O edges m costs) x) ≤
      pairVal (costToCome (relaxPasses O edges n costs) x) := by
  induction hnm with
  | refl => exact le_refl _
  | step h ih =>
      have hxmid := relaxPasses_mem O edges _ _ _ _ h hx
      rw [relaxPasses_succ]
      exact le_trans
        (relaxPass_pairVal_le O edges _ (relaxPasses_denoms O edges _ costs hden) _ hxmid)
        ih

/-- Bellman-Ford cost table: start at `(0, 1)`, relax every edge for
`verts.length` passes. -/
def recomputeCosts {C : Type} [DecidableEq C] (O : Oracles C) (verts : List C)
    (edges : List (C × C)) (start : C) : List (C × (Int × Nat)) :=
  relaxPasses O edges verts.length [(start, (0, 1))]

/-- Recomputed tables have positive denominators. -/
theorem recomputeCosts_denoms {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C) :
    DenomsPos (recomputeCosts O verts edges start) :=
  relaxPasses_denoms O edges verts.length _ (denomsPos_init start)

/-- The start vertex is always costed. -/
theorem recomputeCosts_start_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C) :
    start ∈ (recomputeCosts O verts edges start).map Prod.fst := by
  unfold recomputeCosts
  have h0 : start ∈ ([(start, (0, 1))] : List (C × (Int × Nat))).map Prod.fst := by
    simp
  have hle : 0 ≤ verts.length := Nat.zero_le _
  exact relaxPasses_mem O edges 0 verts.length _ start hle (by
    rw [relaxPasses_zero]
    exact h0)

/-- Recomputing over no edges leaves the initial table alone. -/
theorem recomputeCosts_nil_edges {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (start : C) :
    recomputeCosts O verts [] start = [(start, (0, 1))] := by
  unfold recomputeCosts
  induction verts.length with
  | zero => exact relaxPasses_zero O [] _
  | succ m ih =>
      rw [relaxPasses_succ, ih]
      unfold relaxPass
      rw [List.foldl_nil]

/-- A fold that only targets non-start vertices keeps the start cost. -/
theorem foldl_relax_cost_start {C : Type} [DecidableEq C] (O : Oracles C)
    (base : List (C × (Int × Nat))) (l : List (C × C)) (start : C)
    (acc : List (C × (Int × Nat))) :
    (∀ e ∈ l, e.2 ≠ start) → costToCome acc start = (0, 1) →
      costToCome (l.foldl (relaxEdgeFrom O base) acc) start = (0, 1) := by
  induction l generalizing acc with
  | nil =>
      intro _ hacc
      rw [List.foldl_nil]
      exact hacc
  | cons e es ih =>
      intro hstart hacc
      rw [List.foldl_cons]
      have hne : e.2 ≠ start := hstart e List.mem_cons_self
      have hstart' : ∀ e' ∈ es, e'.2 ≠ start :=
        fun e' h => hstart e' (List.mem_cons_of_mem e h)
      have hacc' : costToCome (relaxEdgeFrom O base acc e) start = (0, 1) := by
        by_cases hu : e.1 ∈ base.map Prod.fst
        · by_cases hv : e.2 ∈ acc.map Prod.fst
          · by_cases hlt : ccLt (ccAdd (costToCome base e.1) (O.cost e.1 e.2))
              (costToCome acc e.2)
            · rw [relaxEdgeFrom_of_mem_mem_lt O base acc e hu hv hlt]
              simp only [costToCome, ite_eq_right hne]
              exact hacc
            · rw [relaxEdgeFrom_of_mem_mem_nlt O base acc e hu hv hlt]
              exact hacc
          · rw [relaxEdgeFrom_of_mem_notmem O base acc e hu hv]
            simp only [costToCome, ite_eq_right hne]
            exact hacc
        · rw [relaxEdgeFrom_of_notmem O base acc e hu]
          exact hacc
      exact ih _ hstart' hacc'

/-- Passes that only target non-start vertices keep the start cost. -/
theorem relaxPasses_cost_start {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (n : ℕ) (costs : List (C × (Int × Nat))) (start : C) :
    (∀ e ∈ edges, e.2 ≠ start) → costToCome costs start = (0, 1) →
      costToCome (relaxPasses O edges n costs) start = (0, 1) := by
  induction n with
  | zero =>
      intro _ hcosts
      rw [relaxPasses_zero]
      exact hcosts
  | succ n ih =>
      intro hstart hcosts
      rw [relaxPasses_succ]
      unfold relaxPass
      exact foldl_relax_cost_start O _ edges start _ hstart (ih hstart hcosts)

/-- Fresh tables read `(0, 1)` at the start vertex. -/
theorem recomputeCosts_cost_start {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (hstart : ∀ e ∈ edges, e.2 ≠ start) :
    costToCome (recomputeCosts O verts edges start) start = (0, 1) := by
  unfold recomputeCosts
  apply relaxPasses_cost_start O edges _ _ start hstart
  exact costToCome_cons_eq [] start (0, 1)

/-- Directed paths over an edge list, counted by edges. -/
inductive PPath {C : Type} (edges : List (C × C)) : C → C → ℕ → Type where
  | refl (v : C) : PPath edges v v 0
  | step {u w v : C} {k : ℕ} (p : PPath edges u w k) (hmem : (w, v) ∈ edges) :
      PPath edges u v (k + 1)

/-- Rational cost of a path: the sum of its edge costs. -/
def pcost {C : Type} (O : Oracles C) {edges : List (C × C)} {u v : C} {k : ℕ}
    (p : PPath edges u v k) : ℚ :=
  match p with
  | PPath.refl _ => 0
  | @PPath.step _ _ _ w v _ p' _ => pcost O p' + O.cost w v
theorem pcost_refl {C : Type} (O : Oracles C) (edges : List (C × C)) (v : C) :
    pcost O (PPath.refl (edges := edges) v) = 0 := rfl

theorem pcost_step {C : Type} (O : Oracles C) {edges : List (C × C)}
    {u w v : C} {k : Nat} (p : PPath edges u w k) (hmem : (w, v) ∈ edges) :
    pcost O (PPath.step p hmem) = pcost O p + O.cost w v := rfl

/-- Path costs are nonnegative. -/
theorem pcost_nonneg {C : Type} (O : Oracles C) {edges : List (C × C)}
    {u v : C} {k : Nat} (p : PPath edges u v k) : 0 ≤ pcost O p := by
  induction p with
  | refl =>
      simp [pcost_refl]
  | step p' hmem ih =>
      rw [pcost_step]
      exact add_nonneg ih (O.cost_nonneg _ _)

/-- Paths compose (length hidden). -/
theorem PPath.append {C : Type} {edges : List (C × C)} {u w v : C} {j k : Nat}
    (p : PPath edges u w j) (q : PPath edges w v k) :
    ∃ m, Nonempty (PPath edges u v m) := by
  induction q generalizing p with
  | refl =>
      exact ⟨j, ⟨p⟩⟩
  | step q' hmem ih =>
      obtain ⟨m, ⟨r⟩⟩ := ih p
      exact ⟨m + 1, ⟨PPath.step r hmem⟩⟩

/-- A positive-length path ends with a step. -/
theorem PPath.exists_step_of_pos {C : Type} {edges : List (C × C)} {u v : C}
    {k : Nat} (p : PPath edges u v k) (hpos : 0 < k) :
    ∃ (w : C) (k' : Nat) (p' : PPath edges u w k') (hmem : (w, v) ∈ edges),
      k = k' + 1 := by
  cases p with
  | refl => exact absurd hpos (lt_irrefl 0)
  | step p' hmem => exact ⟨_, _, p', hmem, rfl⟩

/-- Vertices of a path in order. -/
noncomputable def PPath.verts {C : Type} {edges : List (C × C)} {u v : C} {k : Nat}
    (p : PPath edges u v k) : List C :=
  PPath.rec (motive := fun _ _ _ => List C) [u]
    (fun {_w v} {_k} _ _ ih => ih ++ [v]) p

theorem PPath.verts_refl {C : Type} {edges : List (C × C)} (v : C) :
    (PPath.refl (edges := edges) v).verts = [v] := rfl

theorem PPath.verts_step {C : Type} {edges : List (C × C)} {u w v : C} {k : Nat}
    (p : PPath edges u w k) (hmem : (w, v) ∈ edges) :
    (PPath.step p hmem).verts = p.verts ++ [v] := rfl

/-- A `k`-edge path has `k + 1` vertices. -/
theorem PPath.verts_length {C : Type} {edges : List (C × C)} {u v : C} {k : Nat}
    (p : PPath edges u v k) : p.verts.length = k + 1 := by
  induction p with
  | refl =>
      simp [PPath.verts_refl]
  | step p' hmem ih =>
      simp [PPath.verts_step, List.length_append, ih]

/-- Path vertices lie in the vertex list. -/
theorem PPath.verts_mem {C : Type} {edges : List (C × C)} {u v : C} {k : Nat}
    (verts : List C) (p : PPath edges u v k) :
    u ∈ verts → (∀ e ∈ edges, e.2 ∈ verts) → ∀ x ∈ p.verts, x ∈ verts := by
  induction p with
  | refl =>
      intro hu _ x hx
      rw [PPath.verts_refl] at hx
      simp only [List.mem_singleton] at hx
      rw [hx]
      exact hu
  | step p' hmem ih =>
      intro hu htgt x hx
      rw [PPath.verts_step] at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact ih hu htgt x hx
      · exact htgt _ hmem

/-- Paths transfer along edge-list inclusion. -/
noncomputable def PPath.transfer {C : Type} {edges edges' : List (C × C)}
    {u v : C} {k : Nat}
    (hsub : ∀ e ∈ edges, e ∈ edges') (p : PPath edges u v k) :
    PPath edges' u v k := by
  induction p with
  | refl => exact PPath.refl _
  | step p' hmem ih => exact PPath.step ih (hsub _ hmem)

/-- Nonempty paths over self-loop-free edges cost something positive. -/
theorem pcost_pos {C : Type} (O : Oracles C) {edges : List (C × C)}
    {u v : C} {k : Nat} (hnoself : ∀ e ∈ edges, e.1 ≠ e.2)
    (p : PPath edges u v k) (hpos : 0 < k) : 0 < pcost O p := by
  cases p with
  | refl => exact absurd hpos (lt_irrefl 0)
  | step p' hmem =>
      rw [pcost_step]
      have hne : _ ≠ _ := hnoself _ hmem
      have hlast : 0 < O.cost _ _ := O.cost_pos _ _ hne
      have hnonneg : 0 ≤ pcost O p' := pcost_nonneg O p'
      linarith

/-- A list containing an element is nonempty. -/
theorem length_pos_of_mem_lists {C : Type} (verts : List C) (v : C)
    (hmem : v ∈ verts) : 0 < verts.length := by
  cases verts with
  | nil => simp at hmem
  | cons _ _ => exact Nat.succ_pos _

/-- A duplicate-free sublist is no longer than its (duplicate-free) superlist. -/
theorem nodup_subset_length_le {C : Type} (l verts : List C) (hnd : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ verts) (hndv : verts.Nodup) :
    l.length ≤ verts.length := by
  classical
  have h1 : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnd
  have h2 : l.toFinset ⊆ verts.toFinset := by
    intro x hx
    simp only [List.mem_toFinset] at hx ⊢
    exact hsub x hx
  have h3 := Finset.card_le_card h2
  have h4 : verts.toFinset.card = verts.length :=
    List.toFinset_card_of_nodup hndv
  omega

/-- Membership splits a list around the member. -/
theorem exists_append_of_mem {α : Type} (l : List α) (a : α)
    (hmem : a ∈ l) : ∃ l1 l2, l = l1 ++ a :: l2 := by
  induction l with
  | nil => simp at hmem
  | cons b bs ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨[], bs, rfl⟩
      · obtain ⟨l1, l2, rfl⟩ := ih hmem
        exact ⟨b :: l1, l2, rfl⟩

/-- Within a pass, relaxing a present edge costs its target below the
candidate value. -/
theorem foldl_relax_edge_le {C : Type} [DecidableEq C] (O : Oracles C)
    (base : List (C × (Int × Nat))) (l : List (C × C)) (e : C × C)
    (hmem : e ∈ l) (hbase : DenomsPos base)
    (hu : e.1 ∈ base.map Prod.fst) :
    e.2 ∈ (l.foldl (relaxEdgeFrom O base) base).map Prod.fst ∧
    pairVal (costToCome (l.foldl (relaxEdgeFrom O base) base) e.2) ≤
      pairVal (ccAdd (costToCome base e.1) (O.cost e.1 e.2)) := by
  obtain ⟨l1, l2, rfl⟩ := exists_append_of_mem l e hmem
  rw [List.foldl_append, List.foldl_cons]
  set acc_mid := l1.foldl (relaxEdgeFrom O base) base with hmid
  have hacc_den : DenomsPos acc_mid := by
    rw [hmid]
    exact foldl_relax_denoms O base l1 hbase base hbase
  have hsrcN : 0 < (costToCome base e.1).2 :=
    denomsPos_costToCome base e.1 hbase hu
  have hdenN : 0 < (O.cost e.1 e.2).den :=
    Nat.pos_of_ne_zero (rat_den_ne_zero _)
  have hcandQ : 0 < ((ccAdd (costToCome base e.1) (O.cost e.1 e.2)).2 : Rat) := by
    exact_mod_cast ccAdd_den_pos _ _ hsrcN hdenN
  have hafter_mem : e.2 ∈ (relaxEdgeFrom O base acc_mid e).map Prod.fst := by
    by_cases hv : e.2 ∈ acc_mid.map Prod.fst
    · exact relaxEdgeFrom_mem O base acc_mid e e.2 hv
    · rw [relaxEdgeFrom_of_mem_notmem O base acc_mid e hu hv]
      simp
  have hafter_le : pairVal (costToCome (relaxEdgeFrom O base acc_mid e) e.2) ≤
      pairVal (ccAdd (costToCome base e.1) (O.cost e.1 e.2)) := by
    by_cases hv : e.2 ∈ acc_mid.map Prod.fst
    · have holdQ : 0 < ((costToCome acc_mid e.2).2 : Rat) := by
        exact_mod_cast denomsPos_costToCome acc_mid e.2 hacc_den hv
      by_cases hlt : ccLt (ccAdd (costToCome base e.1) (O.cost e.1 e.2))
        (costToCome acc_mid e.2)
      · rw [relaxEdgeFrom_of_mem_mem_lt O base acc_mid e hu hv hlt]
        have hread : costToCome
            ((e.2, ccAdd (costToCome base e.1) (O.cost e.1 e.2)) :: acc_mid) e.2 =
            ccAdd (costToCome base e.1) (O.cost e.1 e.2) :=
          costToCome_cons_eq acc_mid e.2 _
        rw [hread]
      · rw [relaxEdgeFrom_of_mem_mem_nlt O base acc_mid e hu hv hlt]
        have hle : ccLe (costToCome acc_mid e.2)
            (ccAdd (costToCome base e.1) (O.cost e.1 e.2)) := by
          unfold ccLe at ⊢
          unfold ccLt at hlt
          exact le_of_not_gt hlt
        exact ccLe_pairVal holdQ hcandQ hle
    · rw [relaxEdgeFrom_of_mem_notmem O base acc_mid e hu hv]
      have hread : costToCome
          ((e.2, ccAdd (costToCome base e.1) (O.cost e.1 e.2)) :: acc_mid) e.2 =
          ccAdd (costToCome base e.1) (O.cost e.1 e.2) :=
        costToCome_cons_eq acc_mid e.2 _
      rw [hread]
  constructor
  · exact foldl_relax_mem O base l2 _ e.2 hafter_mem
  · have hacc_after_den : DenomsPos (relaxEdgeFrom O base acc_mid e) :=
      relaxEdgeFrom_denoms O base acc_mid e hbase hacc_den
    exact le_trans
      (foldl_relax_pairVal_le O base l2 hbase _ e.2 hacc_after_den hafter_mem)
      hafter_le

/-- Path lemma (upper bound): after at least as many passes as a path has
edges, the endpoint is costed and reads no more than the path cost. -/
theorem bellmanFord_upper {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (start v : C) (k : Nat) (p : PPath edges start v k)
    (n : Nat) (hkn : k ≤ n) :
    v ∈ (relaxPasses O edges n [(start, (0, 1))]).map Prod.fst ∧
    pairVal (costToCome (relaxPasses O edges n [(start, (0, 1))]) v) ≤
      pcost O p := by
  revert n hkn
  induction p with
  | refl =>
      intro n hkn
      rw [pcost_refl]
      constructor
      · have h0 : start ∈
            ([(start, (0, 1))] : List (C × (Int × Nat))).map Prod.fst := by
          simp
        have h0' : start ∈
            (relaxPasses O edges 0 [(start, (0, 1))]).map Prod.fst := by
          rw [relaxPasses_zero]
          exact h0
        exact relaxPasses_mem O edges 0 n _ start (Nat.zero_le n) h0'
      · have h0 : start ∈
            ([(start, (0, 1))] : List (C × (Int × Nat))).map Prod.fst := by
          simp
        have h0' : start ∈
            (relaxPasses O edges 0 [(start, (0, 1))]).map Prod.fst := by
          rw [relaxPasses_zero]
          exact h0
        have hdec := relaxPasses_pairVal_le O edges 0 n _ start
          (denomsPos_init start) (Nat.zero_le n) h0'
        rw [relaxPasses_zero] at hdec
        have hread : costToCome
            ([(start, (0, 1))] : List (C × (Int × Nat))) start = (0, 1) :=
          costToCome_cons_eq _ _ _
        rw [hread, pairVal_init] at hdec
        exact hdec
  | step p' hmem ih =>
      rename_i w v' k'
      intro n hkn
      obtain ⟨hwcost, hwle⟩ := ih _ (le_refl _)
      have hbase_den : DenomsPos (relaxPasses O edges k' [(start, (0, 1))]) :=
        relaxPasses_denoms O edges k' _ (denomsPos_init start)
      have hedge := foldl_relax_edge_le O _ edges _ hmem hbase_den hwcost
      have hedge1 : v' ∈ (relaxPass O edges
          (relaxPasses O edges k' [(start, (0, 1))])).map Prod.fst := hedge.1
      rw [← relaxPasses_succ] at hedge1
      have hedge2 : pairVal (costToCome (relaxPass O edges
          (relaxPasses O edges k' [(start, (0, 1))])) v') ≤ _ := hedge.2
      rw [← relaxPasses_succ] at hedge2
      have hvj := relaxPasses_mem O edges _ n _ _ hkn hedge1
      have hdec := relaxPasses_pairVal_le O edges _ n _ _
        (denomsPos_init _) hkn hedge1
      have hcw : 0 < ((costToCome
          (relaxPasses O edges k' [(start, (0, 1))]) w).2 : Rat) := by
        exact_mod_cast denomsPos_costToCome _ _
          (relaxPasses_denoms O edges _ _ (denomsPos_init _)) hwcost
      have hcand : pairVal (ccAdd (costToCome
          (relaxPasses O edges k' [(start, (0, 1))]) w) (O.cost w v')) =
          pairVal (costToCome
            (relaxPasses O edges k' [(start, (0, 1))]) w) + O.cost w v' :=
        pairVal_ccAdd _ _ (ne_of_gt hcw)
      rw [pcost_step]
      exact ⟨hvj, le_trans (le_trans hdec hedge2)
        (by rw [hcand]; exact add_le_add_left hwle _)⟩

/-- Path lemma (lower bound): every table entry attains some short path cost. -/
theorem relaxPasses_entry_path {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (start : C) (n : Nat) (v : C) (c : Int × Nat)
    (hmem : (v, c) ∈ relaxPasses O edges n [(start, (0, 1))]) :
    ∃ (k : Nat) (p : PPath edges start v k), k ≤ n ∧ pairVal c = pcost O p := by
  revert v c hmem
  induction n with
  | zero =>
      intro v c hmem
      rw [relaxPasses_zero] at hmem
      simp only [List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨h1, h2⟩ := hmem
      subst v
      subst c
      exact ⟨0, PPath.refl start, Nat.zero_le 0, by rw [pairVal_init, pcost_refl]⟩
  | succ n ih =>
      intro v c hmem
      rw [relaxPasses_succ] at hmem
      unfold relaxPass at hmem
      rcases foldl_relax_entry O _ edges _ _ hmem with hmem | ⟨e, he, hu, heq⟩
      · obtain ⟨k', p', hk'n, hpcost⟩ := ih _ _ hmem
        exact ⟨k', p', Nat.le_succ_of_le hk'n, hpcost⟩
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨cu, hmemu, heqcu⟩ := costToCome_mem_entry _ e.1 hu
        obtain ⟨k', p', hk'n, hpcost⟩ := ih e.1 cu hmemu
        have he' : (e.1, e.2) ∈ edges := he
        refine ⟨k' + 1, PPath.step p' he', Nat.succ_le_succ hk'n, ?_⟩
        rw [heqcu, pcost_step]
        have hden : DenomsPos (relaxPasses O edges n [(start, (0, 1))]) :=
          relaxPasses_denoms O edges n _ (denomsPos_init start)
        have hpos : 0 < cu.2 := hden (e.1, cu) hmemu
        have hne : (cu.2 : Rat) ≠ 0 := by exact_mod_cast ne_of_gt hpos
        rw [pairVal_ccAdd _ _ hne, hpcost]

/-- Dropping the last element keeps a list duplicate-free. -/
theorem nodup_of_append_singleton {α : Type} (l : List α) (a : α)
    (h : (l ++ [a]).Nodup) : l.Nodup := by
  revert h
  induction l with
  | nil => exact fun _ => List.nodup_nil
  | cons b bs ih =>
      intro h
      change (b :: (bs ++ [a])).Nodup at h
      simp only [List.nodup_cons] at h ⊢
      obtain ⟨hnmem, hnd⟩ := h
      refine ⟨fun hcon => hnmem (List.mem_append.mpr (Or.inl hcon)), ih hnd⟩

/-- Appending a fresh element keeps a list duplicate-free. -/
theorem nodup_append_singleton {α : Type} (l : List α) (a : α)
    (hnd : l.Nodup) (h : a ∉ l) : (l ++ [a]).Nodup := by
  revert hnd h
  induction l with
  | nil => intro _ _; exact List.nodup_singleton _
  | cons b bs ih =>
      intro hnd h
      change (b :: (bs ++ [a])).Nodup
      simp only [List.nodup_cons] at hnd ⊢
      obtain ⟨hnmem, hnd'⟩ := hnd
      simp only [List.mem_cons, not_or] at h
      obtain ⟨hne, hnin⟩ := h
      refine ⟨?_, ih hnd' hnin⟩
      intro hcon
      simp only [List.mem_append, List.mem_singleton] at hcon
      rcases hcon with hcon | hcon
      · exact hnmem hcon
      · exact hne hcon.symm

/-- Truncating a simple path at a visited vertex keeps it simple and cheap. -/
theorem PPath.truncate {C : Type} (O : Oracles C) {edges : List (C × C)}
    {u w : C} {k : Nat} (p : PPath edges u w k) :
    p.verts.Nodup → ∀ (v : C), v ∈ p.verts →
      ∃ (k' : Nat) (p' : PPath edges u v k'),
        p'.verts.Nodup ∧ pcost O p' ≤ pcost O p := by
  induction p with
  | refl =>
      intro hsimple v hmem
      simp only [PPath.verts_refl, List.mem_singleton] at hmem
      subst hmem
      exact ⟨0, PPath.refl _, by simp [PPath.verts_refl], le_refl _⟩
  | step p' hmem ih =>
      rename_i w0 v0 k0
      intro hsimple v hmemv
      rw [PPath.verts_step] at hmemv
      simp only [List.mem_append, List.mem_singleton] at hmemv
      rcases hmemv with hmemv | rfl
      · have hnod : p'.verts.Nodup := by
          rw [PPath.verts_step] at hsimple
          exact nodup_of_append_singleton _ _ hsimple
        obtain ⟨k', q, hnd, hle⟩ := ih hnod v hmemv
        refine ⟨k', q, hnd, le_trans hle ?_⟩
        rw [pcost_step]
        have hnn : 0 ≤ O.cost w0 v0 := O.cost_nonneg w0 v0
        linarith
      · exact ⟨_, PPath.step p' hmem, hsimple, le_refl _⟩

/-- Every path has a simple path below it in cost. -/
theorem PPath.exists_simple_le {C : Type} (O : Oracles C) {edges : List (C × C)}
    {u v : C} {k : Nat} (p : PPath edges u v k) :
    ∃ (k' : Nat) (p' : PPath edges u v k'),
      p'.verts.Nodup ∧ pcost O p' ≤ pcost O p := by
  induction p with
  | refl =>
      exact ⟨0, PPath.refl _, by simp [PPath.verts_refl], le_refl _⟩
  | step p hmem ih =>
      rename_i w v' k0
      obtain ⟨k', q', hnd, hle⟩ := ih
      by_cases hv : v' ∈ q'.verts
      · obtain ⟨k'', q'', hnd'', hle''⟩ := q'.truncate O hnd v' hv
        refine ⟨k'', q'', hnd'', le_trans hle'' ?_⟩
        rw [pcost_step]
        have hnn : 0 ≤ O.cost w v' := O.cost_nonneg w v'
        linarith
      · have hnd' : (PPath.step q' hmem).verts.Nodup := by
          rw [PPath.verts_step]
          exact nodup_append_singleton _ _ hnd hv
        refine ⟨_, PPath.step q' hmem, hnd', ?_⟩
        rw [pcost_step, pcost_step]
        exact add_le_add_left hle _

/-- Simple paths are short. -/
theorem PPath.simple_length_le {C : Type} {edges : List (C × C)} {u v : C}
    {k : ℕ} (verts : List C) (hu : u ∈ verts)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts) (hndv : verts.Nodup)
    (p : PPath edges u v k) (hsimple : p.verts.Nodup) :
    k + 1 ≤ verts.length := by
  have hlen : p.verts.length = k + 1 := PPath.verts_length p
  have hsub : ∀ x ∈ p.verts, x ∈ verts := PPath.verts_mem verts p hu htgt
  have hle := nodup_subset_length_le p.verts verts hsimple hsub hndv
  omega

/-- Edges with the same target coincide when targets are duplicate-free. -/
theorem nodupTargets_unique {C : Type} [DecidableEq C] (edges : List (C × C))
    (hnd : (edges.map Prod.snd).Nodup) (e1 : C × C) (h1 : e1 ∈ edges)
    (e2 : C × C) (h2 : e2 ∈ edges) (heq : e1.2 = e2.2) : e1 = e2 := by
  revert hnd h1 h2
  induction edges with
  | nil =>
      intro hnd h1 h2
      simp at h1
  | cons e es ih =>
      intro hnd h1 h2
      simp only [List.map_cons, List.nodup_cons] at hnd
      simp only [List.mem_cons] at h1 h2
      rcases h1 with rfl | h1
      · rcases h2 with rfl | h2
        · rfl
        · have hcon : e1.2 ∈ es.map Prod.snd := by
            rw [heq]
            exact List.mem_map.mpr ⟨_, h2, rfl⟩
          exact absurd hcon hnd.1
      · rcases h2 with rfl | h2
        · have hcon : e2.2 ∈ es.map Prod.snd := by
            rw [← heq]
            exact List.mem_map.mpr ⟨_, h1, rfl⟩
          exact absurd hcon hnd.1
        · exact ih hnd.2 h1 h2

/-- An edge from a costed vertex costs its target. -/
theorem costed_of_edge_of_costed {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts) (e : C × C) (hmem : e ∈ edges)
    (hu : e.1 ∈ (recomputeCosts O verts edges start).map Prod.fst) :
    e.2 ∈ (recomputeCosts O verts edges start).map Prod.fst := by
  unfold recomputeCosts at hu ⊢
  obtain ⟨cu, hmemu, _⟩ := costToCome_mem_entry _ e.1 hu
  obtain ⟨_, p, _, _⟩ :=
    relaxPasses_entry_path O edges start verts.length e.1 cu hmemu
  obtain ⟨ks, ps, hnds, _⟩ := PPath.exists_simple_le O p
  have hlen : ks + 1 ≤ verts.length :=
    PPath.simple_length_le verts hstart htgt hnd ps hnds
  have hmem' : (e.1, e.2) ∈ edges := hmem
  have hup := bellmanFord_upper O edges start e.2 (ks + 1)
    (PPath.step ps hmem') verts.length hlen
  exact hup.1

/-- Bellman inequality, rational form: every edge can only improve its target. -/
theorem recomputeCosts_bellman_val {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts) (e : C × C) (hmem : e ∈ edges)
    (hu : e.1 ∈ (recomputeCosts O verts edges start).map Prod.fst) :
    pairVal (costToCome (recomputeCosts O verts edges start) e.2) ≤
      pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) e.1)
        (O.cost e.1 e.2)) := by
  have hv : e.2 ∈ (recomputeCosts O verts edges start).map Prod.fst :=
    costed_of_edge_of_costed O verts edges start hstart hnd htgt e hmem hu
  unfold recomputeCosts at hu hv ⊢
  obtain ⟨cu, hmemu, heqcu⟩ := costToCome_mem_entry _ e.1 hu
  obtain ⟨_, p, _, hpcost⟩ :=
    relaxPasses_entry_path O edges start verts.length e.1 cu hmemu
  obtain ⟨ks, ps, hnds, hles⟩ := PPath.exists_simple_le O p
  have hlen : ks + 1 ≤ verts.length :=
    PPath.simple_length_le verts hstart htgt hnd ps hnds
  have hmem' : (e.1, e.2) ∈ edges := hmem
  have hup := bellmanFord_upper O edges start e.2 (ks + 1)
    (PPath.step ps hmem') verts.length hlen
  have hup2 := hup.2
  rw [pcost_step] at hup2
  have hdenm : DenomsPos (relaxPasses O edges verts.length [(start, (0, 1))]) :=
    relaxPasses_denoms O edges verts.length _ (denomsPos_init start)
  have hpos : 0 < (costToCome
      (relaxPasses O edges verts.length [(start, (0, 1))]) e.1).2 :=
    denomsPos_costToCome _ e.1 hdenm hu
  have hne : ((costToCome
      (relaxPasses O edges verts.length [(start, (0, 1))]) e.1).2 : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos
  have hcand : pairVal (ccAdd (costToCome
        (relaxPasses O edges verts.length [(start, (0, 1))]) e.1)
      (O.cost e.1 e.2)) =
      pairVal (costToCome
        (relaxPasses O edges verts.length [(start, (0, 1))]) e.1) +
        O.cost e.1 e.2 :=
    pairVal_ccAdd _ _ hne
  rw [hcand, heqcu, hpcost]
  exact le_trans hup2 (add_le_add_left hles _)

/-- Bellman inequality in the pair order. -/
theorem recomputeCosts_bellman {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts) (e : C × C) (hmem : e ∈ edges)
    (hu : e.1 ∈ (recomputeCosts O verts edges start).map Prod.fst) :
    ccLe (costToCome (recomputeCosts O verts edges start) e.2)
      (ccAdd (costToCome (recomputeCosts O verts edges start) e.1)
        (O.cost e.1 e.2)) := by
  have hv : e.2 ∈ (recomputeCosts O verts edges start).map Prod.fst :=
    costed_of_edge_of_costed O verts edges start hstart hnd htgt e hmem hu
  have hval := recomputeCosts_bellman_val O verts edges start hstart hnd htgt e
    hmem hu
  have hden := recomputeCosts_denoms O verts edges start
  have hp : 0 < ((costToCome (recomputeCosts O verts edges start) e.2).2 : ℚ) := by
    exact_mod_cast denomsPos_costToCome _ e.2 hden hv
  have hq : 0 < ((ccAdd (costToCome (recomputeCosts O verts edges start) e.1)
      (O.cost e.1 e.2)).2 : ℚ) := by
    exact_mod_cast ccAdd_den_pos _ _
      (denomsPos_costToCome _ e.1 hden hu)
      (Nat.pos_of_ne_zero (rat_den_ne_zero _))
  exact pairVal_le_ccLe hp hq hval

/-- Tightness: a costed non-start vertex has an incoming edge attaining
equality of rational values. -/
theorem recomputeCosts_tight {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts) (v : C)
    (hv : v ∈ (recomputeCosts O verts edges start).map Prod.fst)
    (hne : v ≠ start) :
    ∃ u, (u, v) ∈ edges ∧ u ∈ (recomputeCosts O verts edges start).map Prod.fst ∧
      pairVal (costToCome (recomputeCosts O verts edges start) v) =
        pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) u)
          (O.cost u v)) := by
  unfold recomputeCosts at hv ⊢
  obtain ⟨c, hmemc, heqc⟩ := costToCome_mem_entry _ v hv
  obtain ⟨_, p, _, hpcost⟩ :=
    relaxPasses_entry_path O edges start verts.length v c hmemc
  obtain ⟨ks, ps, hnds, hles⟩ := PPath.exists_simple_le O p
  have hlenS : ks + 1 ≤ verts.length :=
    PPath.simple_length_le verts hstart htgt hnd ps hnds
  cases ps
  case refl => exact absurd rfl hne
  case step mid k ps' hmem' =>
    have hup_u := bellmanFord_upper O edges start mid k ps' verts.length
      (by omega)
    have hu' : mid ∈ (recomputeCosts O verts edges start).map Prod.fst := hup_u.1
    have hbell := recomputeCosts_bellman_val O verts edges start hstart hnd
      htgt (mid, v) hmem' hu'
    have hbellm := hbell
    have hdenm : DenomsPos (relaxPasses O edges verts.length [(start, (0, 1))]) :=
      relaxPasses_denoms O edges verts.length [(start, (0, 1))] (denomsPos_init start)
    have hposw : 0 < ((costToCome
        (relaxPasses O edges verts.length [(start, (0, 1))]) mid).2 : ℚ) := by
      exact_mod_cast denomsPos_costToCome _ mid hdenm hup_u.1
    have hcand : pairVal (ccAdd (costToCome
        (relaxPasses O edges verts.length [(start, (0, 1))]) mid) (O.cost mid v)) =
        pairVal (costToCome
          (relaxPasses O edges verts.length [(start, (0, 1))]) mid) + O.cost mid v :=
      pairVal_ccAdd _ _ (ne_of_gt hposw)
    rw [pcost_step] at hles
    have heqcV : pairVal (costToCome
        (relaxPasses O edges verts.length [(start, (0, 1))]) v) = pairVal c := by
      rw [heqc]
    refine ⟨mid, hmem', hu', le_antisymm hbellm ?_⟩
    linarith [hcand, hles, hpcost, heqcV, hup_u.2]

/-- Tightness in the pair order: mutual `ccLe`. -/
theorem recomputeCosts_tight_ccLe {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts) (v : C)
    (hv : v ∈ (recomputeCosts O verts edges start).map Prod.fst)
    (hne : v ≠ start) :
    ∃ u, (u, v) ∈ edges ∧
      ccLe (costToCome (recomputeCosts O verts edges start) v)
        (ccAdd (costToCome (recomputeCosts O verts edges start) u)
          (O.cost u v)) ∧
      ccLe (ccAdd (costToCome (recomputeCosts O verts edges start) u)
          (O.cost u v))
        (costToCome (recomputeCosts O verts edges start) v) := by
  obtain ⟨u, hmem, hucost, heq⟩ :=
    recomputeCosts_tight O verts edges start hstart hnd htgt v hv hne
  have hden := recomputeCosts_denoms O verts edges start
  have hp : 0 < ((costToCome (recomputeCosts O verts edges start) v).2 : ℚ) := by
    exact_mod_cast denomsPos_costToCome _ v hden hv
  have hq : 0 < ((ccAdd (costToCome (recomputeCosts O verts edges start) u)
      (O.cost u v)).2 : ℚ) := by
    exact_mod_cast ccAdd_den_pos _ _
      (denomsPos_costToCome _ u hden hucost)
      (Nat.pos_of_ne_zero (rat_den_ne_zero _))
  exact ⟨u, hmem, pairVal_eq_ccLe hp hq heq⟩

/-- A maintained parent edge strictly increases rational cost-to-come. -/
theorem parent_edge_cost_lt {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (costs : List (C × (Int × Nat)))
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts)
    (hnodup : (edges.map Prod.snd).Nodup)
    (hnoself : ∀ e ∈ edges, e.1 ≠ e.2)
    (hfresh : costs = recomputeCosts O verts edges start)
    (u v : C) (hmem : (u, v) ∈ edges) (hne : v ≠ start)
    (hu : u ∈ costs.map Prod.fst) (hv : v ∈ costs.map Prod.fst) :
    pairVal (costToCome costs u) < pairVal (costToCome costs v) := by
  subst hfresh
  obtain ⟨u', hmem', _, heq⟩ :=
    recomputeCosts_tight O verts edges start hstart hnd htgt v hv hne
  have hpair : (u, v) = (u', v) :=
    nodupTargets_unique edges hnodup _ hmem _ hmem' rfl
  have huu : u = u' := congrArg Prod.fst hpair
  subst huu
  have hden := recomputeCosts_denoms O verts edges start
  have hpos : 0 < ((costToCome (recomputeCosts O verts edges start) u).2 : ℚ) := by
    exact_mod_cast denomsPos_costToCome _ u hden hu
  have hcand : pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) u)
      (O.cost u v)) =
      pairVal (costToCome (recomputeCosts O verts edges start) u) + O.cost u v :=
    pairVal_ccAdd _ _ (ne_of_gt hpos)
  have hpos' : 0 < O.cost u v := O.cost_pos u v (hnoself _ hmem)
  linarith [heq, hcand, hpos']

/-- First edge in list order targeting `v` whose endpoints satisfy tight
equality: the deterministic tight-parent pick. -/
def firstTightParent {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (costs : List (C × (Int × Nat))) (v : C) :
    Option C :=
  match edges with
  | [] => none
  | e :: es =>
      if e.2 = v ∧
          pairVal (costToCome costs e.2) =
            pairVal (ccAdd (costToCome costs e.1) (O.cost e.1 e.2)) then
        some e.1
      else firstTightParent O es costs v

theorem firstTightParent_nil {C : Type} [DecidableEq C] (O : Oracles C)
    (costs : List (C × (Int × Nat))) (v : C) :
    firstTightParent O [] costs v = none := rfl

theorem firstTightParent_cons {C : Type} [DecidableEq C] (O : Oracles C)
    (e : C × C) (es : List (C × C)) (costs : List (C × (Int × Nat))) (v : C) :
    firstTightParent O (e :: es) costs v =
      (if e.2 = v ∧
          pairVal (costToCome costs e.2) =
            pairVal (ccAdd (costToCome costs e.1) (O.cost e.1 e.2)) then
        some e.1
      else firstTightParent O es costs v) := rfl

/-- The first tight edge in list order is the maintained parent edge. -/
theorem firstTightParent_eq_parent {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (costs : List (C × (Int × Nat))) (p v : C) :
    (edges.map Prod.snd).Nodup → (p, v) ∈ edges →
      pairVal (costToCome costs v) =
        pairVal (ccAdd (costToCome costs p) (O.cost p v)) →
      firstTightParent O edges costs v = some p := by
  induction edges with
  | nil =>
      intro _ hmem _
      simp at hmem
  | cons e es ih =>
      intro hnodup hmem htight
      simp only [List.mem_cons] at hmem
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rw [firstTightParent_cons]
      rcases hmem with rfl | hmem
      · rw [if_pos ⟨rfl, htight⟩]
      · have hne : e.2 ≠ v := by
          intro hcon
          have hndfull : ((e :: es).map Prod.snd).Nodup :=
            List.nodup_cons.mpr hnodup
          have heq : e = (p, v) :=
            nodupTargets_unique (e :: es) hndfull e List.mem_cons_self (p, v)
              (List.mem_cons_of_mem e hmem) hcon
          have hcon2 : e.2 ∈ es.map Prod.snd := by
            rw [heq]
            exact List.mem_map.mpr ⟨(p, v), hmem, rfl⟩
          exact hnodup.1 hcon2
        rw [if_neg (fun h => hne h.1)]
        exact ih hnodup.2 hmem htight

/-- A parent chain over `edges`: consecutive vertices linked by parent edges. -/
def IsParentChain {C : Type} (edges : List (C × C)) : List C → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => (u, v) ∈ edges ∧ IsParentChain edges (v :: rest)

/-- Every later member of a parent chain costs strictly more than the head. -/
theorem chain_all_gt {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (costs : List (C × (Int × Nat)))
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts)
    (hnodup : (edges.map Prod.snd).Nodup)
    (hnoself : ∀ e ∈ edges, e.1 ≠ e.2)
    (hnotgt : ∀ e ∈ edges, e.2 ≠ start)
    (hfresh : costs = recomputeCosts O verts edges start)
    (u : C) (rest : List C) :
    IsParentChain edges (u :: rest) → (∀ x ∈ u :: rest, x ∈ costs.map Prod.fst) →
      ∀ y ∈ rest, pairVal (costToCome costs u) < pairVal (costToCome costs y) := by
  induction rest generalizing u with
  | nil =>
      intro _ _ y hy
      simp at hy
  | cons w rest' ih =>
      intro hchain hcost y hy
      simp only [IsParentChain] at hchain
      obtain ⟨huw, hchain'⟩ := hchain
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact parent_edge_cost_lt O verts edges start costs hstart hnd htgt
          hnodup hnoself hfresh u y huw (hnotgt _ huw)
          (hcost u List.mem_cons_self)
          (hcost y (List.mem_cons_of_mem u List.mem_cons_self))
      · have h1 : pairVal (costToCome costs u) < pairVal (costToCome costs w) :=
          parent_edge_cost_lt O verts edges start costs hstart hnd htgt
            hnodup hnoself hfresh u w huw (hnotgt _ huw)
            (hcost u List.mem_cons_self)
            (hcost w (List.mem_cons_of_mem u List.mem_cons_self))
        have hcost' : ∀ x ∈ w :: rest', x ∈ costs.map Prod.fst := by
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hcost x (List.mem_cons_of_mem u List.mem_cons_self)
          · exact hcost x (List.mem_cons_of_mem u (List.mem_cons_of_mem w hx))
        have h2 : pairVal (costToCome costs w) < pairVal (costToCome costs y) :=
          ih w hchain' hcost' y hy
        exact lt_trans h1 h2

/-- Parent chains over fresh tables visit no vertex twice. -/
theorem parentChain_nodup {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (costs : List (C × (Int × Nat)))
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts)
    (hnodup : (edges.map Prod.snd).Nodup)
    (hnoself : ∀ e ∈ edges, e.1 ≠ e.2)
    (hnotgt : ∀ e ∈ edges, e.2 ≠ start)
    (hfresh : costs = recomputeCosts O verts edges start)
    (l : List C) :
    IsParentChain edges l → (∀ x ∈ l, x ∈ costs.map Prod.fst) → l.Nodup := by
  induction l with
  | nil =>
      intro _ _
      exact List.nodup_nil
  | cons u rest ih =>
      intro hchain hcost
      simp only [List.nodup_cons]
      constructor
      · intro hcon
        have hlt := chain_all_gt O verts edges start costs hstart hnd htgt
          hnodup hnoself hnotgt hfresh u rest hchain hcost u hcon
        exact (lt_self_iff_false _).mp hlt
      · cases rest with
        | nil => exact List.nodup_nil
        | cons w rest' =>
            have hchain' : IsParentChain edges (w :: rest') := by
              simp only [IsParentChain] at hchain
              exact hchain.2
            have hcost' : ∀ x ∈ w :: rest', x ∈ costs.map Prod.fst := by
              intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact hcost x (List.mem_cons_of_mem u List.mem_cons_self)
              · exact hcost x (List.mem_cons_of_mem u (List.mem_cons_of_mem w hx))
            exact ih hchain' hcost'
-- RRT* tail: candidates through rrtStar.
-- Append inside the SamplingPlanners namespace, after the cost machinery.
--
-- Design (intentional deviations from an earlier draft):
-- * Costs are recomputed ONCE per tree change. `extendStar` finishes by
--   setting `costs := recomputeCosts O verts' edges' start`. At step
--   boundaries `costs` IS the recomputed table, so `chooseParent` never reads
--   stale descendant costs. During one rewire pass, comparisons read the
--   pass-start table (single-pass rewiring as in RRT* pseudocode).
-- * `candidates` is a single filter over `verts`. `chooseParent` computes it
--   internally and returns the first minimizer, or `none` when empty.
-- * `radiusOf : ℕ → ℚ` is threaded through `candidates`, `chooseParent`,
--   `rewireAux`, `extendStar`, `rrtStarAux` and `rrtStar`. It is evaluated at
--   the current vertex count: `verts.length` before adding (candidates) and
--   `(s :: verts).length` after adding (rewire). See each docstring.
-- * Rewiring replaces a vertex's parent edge via `replaceParent` on edge
--   lists. Self-loops are impossible (`s ∉ verts`, `w ≠ s`).
--
-- Signature changes vs the old region (all reported):
-- * `candidates` gains `radiusOf` and `start` (start seeds `nearest`).
-- * `chooseParent` takes `verts`/`radiusOf`/`start` and computes `candidates`
--   internally (old form took a precomputed candidate list).
-- * `rewireAux` gains `radiusOf`, an explicit count `n`, `start`, `s` and `p`.
-- * `extendStar`, `rrtStarAux`, `rrtStar` gain `radiusOf` (and `start`).
-- * `StarInvar` is new (structure bundle, see below).
-- * Helpers `mem_candidates`, `foldl_mem`, `findParent`, `parentChain`,
--   `nodup_length_le`, `chain_ppath_cons`, `reachable_of_invar` are new.
-- No declarations are dropped; `firstTightParent` (prefix) is not used here.
--
-- Stub forms relied on (names only; bodies are the integrator's):
-- `Oracles` fields, `Int × Nat`/`pairVal`/`ccAdd`/`ccLt`/`ccLe`,
-- `costToCome`, `nearest`, `DenomsPos`/`Costed`, `recomputeCosts` and its
-- `*_denoms`, `*_cost_start`, `*_tight`, `parent_edge_cost_lt` lemmas,
-- `PPath` (`refl`/`step`) with `PPath.append`, `nodupTargets_unique`,
-- `IsParentChain` with `parentChain_nodup`.

/-- Candidate parents for `s`: linked vertices within `radiusOf` at the
    current count (`verts.length`, before adding), plus the nearest vertex
    as fallback (in its list position). -/
def candidates {S : Type} [DecidableEq S] (O : Oracles S) (verts : List S)
    (radiusOf : ℕ → ℚ) (start s : S) : List S :=
  verts.filter (fun v =>
    O.link v s &&
      (decide (O.cost v s ≤ radiusOf verts.length) ||
        decide (v = nearest O verts start s)))

/-- Membership characterization for `candidates`. -/
theorem mem_candidates {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (radiusOf : ℕ → ℚ) (start s v : S) :
    v ∈ candidates O verts radiusOf start s ↔
      v ∈ verts ∧ O.link v s = true ∧
        (O.cost v s ≤ radiusOf verts.length ∨
          v = nearest O verts start s) := by
  simp only [candidates, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]

theorem candidates_subset_verts {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (radiusOf : ℕ → ℚ) (start s v : S)
    (h : v ∈ candidates O verts radiusOf start s) : v ∈ verts :=
  ((mem_candidates O verts radiusOf start s v).mp h).1

/-- The nearest vertex is a candidate iff it links to `s`.
    `hmem` holds when `verts` is nonempty by `nearest`'s head-seeded fold;
    the caller supplies it to avoid depending on unstated prefix lemmas. -/
theorem nearest_mem_candidates_iff {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (radiusOf : ℕ → ℚ) (start s : S)
    (hmem : nearest O verts start s ∈ verts) :
    nearest O verts start s ∈ candidates O verts radiusOf start s ↔
      O.link (nearest O verts start s) s = true := by
  rw [mem_candidates]
  constructor
  · rintro ⟨_, hlink, _⟩
    exact hlink
  · intro hlink
    exact ⟨hmem, hlink, Or.inr rfl⟩

/-- First minimizer of `ccAdd (costToCome costs ·) (O.cost · s)` over the
    candidates, by a head-seeded fold; `none` iff candidates are empty.
    Strict `ccLt` keeps the earliest vertex on ties. -/
def chooseParent {S : Type} [DecidableEq S] (O : Oracles S) (verts : List S)
    (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ) (start s : S) :
    Option S :=
  match candidates O verts radiusOf start s with
  | [] => none
  | h :: t =>
      some (t.foldl
        (fun best v =>
          if ccLt (ccAdd (costToCome costs v) (O.cost v s))
            (ccAdd (costToCome costs best) (O.cost best s)) then v
          else best) h)

/-- A fold that always keeps one of its two inputs stays in the list. -/
theorem foldl_mem {S : Type} (f : S → S → S)
    (h : ∀ a b, f a b = a ∨ f a b = b) (init : S) (l : List S) :
    l.foldl f init ∈ init :: l := by
  induction l generalizing init with
  | nil =>
      simp
  | cons v vs ih =>
      simp only [List.foldl_cons]
      have h1 := h init v
      cases h1 with
      | inl heq =>
          rw [heq]
          have hmem := ih (init := init)
          simp only [List.mem_cons] at hmem ⊢
          tauto
      | inr heq =>
          rw [heq]
          have hmem := ih (init := v)
          simp only [List.mem_cons] at hmem ⊢
          tauto

theorem chooseParent_eq_none_iff {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ)
    (start s : S) :
    chooseParent O verts costs radiusOf start s = none ↔
      candidates O verts radiusOf start s = [] := by
  cases hc : candidates O verts radiusOf start s with
  | nil => simp [chooseParent, hc]
  | cons h t => simp [chooseParent, hc]

theorem chooseParent_mem {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ)
    (start s p : S) (h : chooseParent O verts costs radiusOf start s = some p) :
    p ∈ candidates O verts radiusOf start s := by
  cases hc : candidates O verts radiusOf start s with
  | nil =>
      simp only [chooseParent, hc] at h
      contradiction
  | cons hd tl =>
      simp only [chooseParent, hc] at h
      have hmem : tl.foldl
          (fun best v =>
            if ccLt (ccAdd (costToCome costs v) (O.cost v s))
              (ccAdd (costToCome costs best) (O.cost best s)) then v
            else best) hd ∈ hd :: tl := by
        apply foldl_mem
        intro a b
        by_cases hcLt : ccLt (ccAdd (costToCome costs b) (O.cost b s))
          (ccAdd (costToCome costs a) (O.cost a s))
        · simp [hcLt]
        · simp [hcLt]
      cases h
      exact hmem

/-- Replace every edge targeting `w` with `(s, w)`. Under `Nodup` targets at
    most one edge changes. -/
def replaceParent {S : Type} [DecidableEq S] (edges : List (S × S)) (s w : S) :
    List (S × S) :=
  edges.map (fun e => if e.2 = w then (s, w) else e)


/-- First parent of `v` in `edges`, if any. -/
def findParent {S : Type} [DecidableEq S] (edges : List (S × S)) (v : S) :
    Option S :=
  match edges with
  | [] => none
  | e :: es => if e.2 = v then some e.1 else findParent es v

theorem findParent_some_mem {S : Type} [DecidableEq S] (edges : List (S × S))
    (v u : S) (h : findParent edges v = some u) : (u, v) ∈ edges := by
  induction edges with
  | nil =>
      simp [findParent] at h
  | cons e es ih =>
      simp only [findParent] at h
      by_cases he : e.2 = v
      · simp [he] at h
        obtain rfl := h
        have heq : e = (e.1, v) := by
          obtain ⟨a, b⟩ := e
          dsimp only at he ⊢
          rw [he]
        rw [heq]
        exact List.mem_cons_self
      · simp [he] at h
        exact List.mem_cons_of_mem e (ih h)

theorem findParent_none_notmem {S : Type} [DecidableEq S] (edges : List (S × S))
    (v u : S) (h : findParent edges v = none) : (u, v) ∉ edges := by
  induction edges with
  | nil =>
      simp
  | cons e es ih =>
      simp only [findParent] at h
      by_cases he : e.2 = v
      · simp [he] at h
      · simp only [he, ite_false] at h
        simp only [List.mem_cons]
        rintro (rfl | hmem)
        · exact he rfl
        · exact ih h hmem

/-- Parent chain from `v` with `fuel` steps, child-first (`[v, .., start]`). -/
def parentChain {S : Type} [DecidableEq S] (edges : List (S × S)) (start v : S) :
    ℕ → List S
  | 0 => [v]
  | n + 1 =>
      if v = start then [v]
      else match findParent edges v with
        | none => [v]
        | some u => v :: parentChain edges start u n

theorem parentChain_mem_verts {S : Type} [DecidableEq S] (edges : List (S × S))
    (verts : List S) (start v : S) (fuel : ℕ)
    (hend : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (hv : v ∈ verts) : ∀ x ∈ parentChain edges start v fuel, x ∈ verts := by
  induction fuel generalizing v with
  | zero =>
      simp only [parentChain]
      intro x hx
      simp only [List.mem_singleton] at hx
      rw [hx]
      exact hv
  | succ n ih =>
      simp only [parentChain]
      by_cases hvs : v = start
      · simp only [ite_eq_left hvs]
        intro x hx
        simp only [List.mem_singleton] at hx
        rw [hx]
        exact hv
      · simp only [hvs, ite_false]
        cases hfp : findParent edges v with
        | none =>
            dsimp only
            intro x hx
            simp only [List.mem_singleton] at hx
            rw [hx]
            exact hv
        | some u =>
            dsimp only
            have hu_mem : (u, v) ∈ edges := findParent_some_mem edges v u hfp
            have hu_verts := (hend (u, v) hu_mem).1
            intro x hx
            simp only [List.mem_cons] at hx
            cases hx with
            | inl heq =>
                rw [heq]
                exact hv
            | inr hmem => exact ih (v := u) hu_verts x hmem


def rewireAux {S : Type} [DecidableEq S] (O : Oracles S)
    (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ) (n : ℕ) (forbid : List S) (start s p : S) :
    List S → List (S × S) → List (S × S)
  | [], edges => edges
  | w :: ws, edges =>
      if w ≠ start ∧ w ≠ s ∧ w ≠ p ∧ w ∉ forbid ∧ O.cost s w ≤ radiusOf n ∧
        O.link s w = true ∧
        ccLt (ccAdd (costToCome costs s) (O.cost s w)) (costToCome costs w)
      then rewireAux O (relaxPasses O (replaceParent edges s w) n [(start, (0, 1))])
        radiusOf n forbid start s p ws (replaceParent edges s w)
      else rewireAux O costs radiusOf n forbid start s p ws edges

theorem rewireAux_nil {S : Type} [DecidableEq S] (O : Oracles S)
    (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ) (n : ℕ) (forbid : List S) (start s p : S)
    (edges : List (S × S)) :
    rewireAux O costs radiusOf n forbid start s p [] edges = edges :=
  rfl

theorem rewireAux_cons {S : Type} [DecidableEq S] (O : Oracles S)
    (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ) (n : ℕ) (forbid : List S) (start s p : S)
    (w : S) (ws : List S) (edges : List (S × S)) :
    rewireAux O costs radiusOf n forbid start s p (w :: ws) edges =
      (if w ≠ start ∧ w ≠ s ∧ w ≠ p ∧ w ∉ forbid ∧ O.cost s w ≤ radiusOf n ∧
        O.link s w = true ∧
        ccLt (ccAdd (costToCome costs s) (O.cost s w)) (costToCome costs w)
      then rewireAux O (relaxPasses O (replaceParent edges s w) n [(start, (0, 1))])
        radiusOf n forbid start s p ws (replaceParent edges s w)
      else rewireAux O costs radiusOf n forbid start s p ws edges) :=
  rfl

/-- Replacing parents preserves the target list. -/
theorem map_replace_snd_eq {S : Type} [DecidableEq S] (edges : List (S × S))
    (s w : S) :
    (edges.map (fun e => if e.2 = w then (s, w) else e)).map Prod.snd =
      edges.map Prod.snd := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons]
      by_cases h : e.2 = w
      · simp [h, ih]
      · simp [h, ih]

theorem replaceParent_snd_eq {S : Type} [DecidableEq S] (edges : List (S × S))
    (s w : S) :
    (replaceParent edges s w).map Prod.snd = edges.map Prod.snd := by
  simp only [replaceParent]
  exact map_replace_snd_eq edges s w

theorem mem_replaceParent {S : Type} [DecidableEq S] (edges : List (S × S))
    (s w u v : S) :
    (u, v) ∈ replaceParent edges s w ↔
      ((u, v) ∈ edges ∧ v ≠ w) ∨
        (u = s ∧ v = w ∧ ∃ u', (u', w) ∈ edges) := by
  simp only [replaceParent, List.mem_map]
  constructor
  · rintro ⟨e, he_mem, he_eq⟩
    obtain ⟨a, b⟩ := e
    dsimp only at he_eq he_mem
    by_cases h : b = w
    · simp only [h, ite_true] at he_eq
      obtain ⟨rfl, rfl⟩ := he_eq
      right
      refine ⟨rfl, rfl, a, ?_⟩
      simpa [h] using he_mem
    · simp only [h, ite_false] at he_eq
      obtain ⟨rfl, rfl⟩ := he_eq
      left
      exact ⟨he_mem, h⟩
  · rintro (⟨hmem, hne⟩ | ⟨hu, hv, u', hmem⟩)
    · refine ⟨(u, v), hmem, ?_⟩
      show (if v = w then (s, w) else (u, v)) = (u, v)
      simp [hne]
    · rw [hu, hv]
      refine ⟨(u', w), hmem, ?_⟩
      show (if w = w then (s, w) else (u', w)) = (s, w)
      simp

theorem replaceParent_mem_of_ne {S : Type} [DecidableEq S]
    (edges : List (S × S)) (s w u v : S)
    (hmem : (u, v) ∈ edges) (hne : v ≠ w) :
    (u, v) ∈ replaceParent edges s w :=
  (mem_replaceParent edges s w u v).mpr (Or.inl ⟨hmem, hne⟩)

theorem replaceParent_mem_parent {S : Type} [DecidableEq S]
    (edges : List (S × S)) (s w : S) (u' : S)
    (hmem : (u', w) ∈ edges) : (s, w) ∈ replaceParent edges s w :=
  (mem_replaceParent edges s w s w).mpr
    (Or.inr ⟨rfl, rfl, u', hmem⟩)

theorem replaceParent_endpoints {S : Type} [DecidableEq S]
    (edges : List (S × S)) (verts : List S) (s w : S)
    (hs : s ∈ verts) (hw : w ∈ verts)
    (h : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts) :
    ∀ e ∈ replaceParent edges s w, e.1 ∈ verts ∧ e.2 ∈ verts := by
  intro e he
  obtain ⟨a, b⟩ := e
  rw [mem_replaceParent] at he
  cases he with
  | inl hmem => exact h (a, b) hmem.1
  | inr hmem =>
      obtain ⟨rfl, rfl, _, _⟩ := hmem
      exact ⟨hs, hw⟩

theorem replaceParent_nodup {S : Type} [DecidableEq S] (edges : List (S × S))
    (s w : S) (h : (edges.map Prod.snd).Nodup) :
    ((replaceParent edges s w).map Prod.snd).Nodup := by
  rw [replaceParent_snd_eq]
  exact h

theorem replaceParent_no_self {S : Type} [DecidableEq S] (edges : List (S × S))
    (s w : S) (hns : s ≠ w) (h : ∀ e ∈ edges, e.1 ≠ e.2) :
    ∀ e ∈ replaceParent edges s w, e.1 ≠ e.2 := by
  intro e he
  obtain ⟨a, b⟩ := e
  rw [mem_replaceParent] at he
  cases he with
  | inl hmem => exact h (a, b) hmem.1
  | inr hmem =>
      obtain ⟨rfl, rfl, _, _⟩ := hmem
      exact hns

theorem replaceParent_ne_start {S : Type} [DecidableEq S] (edges : List (S × S))
    (s w start : S) (h : ∀ e ∈ edges, e.2 ≠ start) :
    ∀ e ∈ replaceParent edges s w, e.2 ≠ start := by
  intro e he
  obtain ⟨a, b⟩ := e
  rw [mem_replaceParent] at he
  cases he with
  | inl hmem => exact h (a, b) hmem.1
  | inr hmem =>
      obtain ⟨_, rfl, u', hmem⟩ := hmem
      exact h (u', _) hmem

theorem replaceParent_has_parent {S : Type} [DecidableEq S]
    (edges : List (S × S)) (verts : List S) (s w start : S)
    (hw : w ∈ verts) (hws : w ≠ start)
    (h : ∀ v ∈ verts, v ≠ start → ∃ u, (u, v) ∈ edges) :
    ∀ v ∈ verts, v ≠ start → ∃ u, (u, v) ∈ replaceParent edges s w := by
  intro v hv hne
  by_cases hvw : v = w
  · subst v
    obtain ⟨u', hu'⟩ := h w hw hws
    exact ⟨s, replaceParent_mem_parent edges s w u' hu'⟩
  · obtain ⟨u, hu⟩ := h v hv hne
    exact ⟨u, replaceParent_mem_of_ne edges s w u v hu hvw⟩

/-- Rewiring preserves the tree edge invariants (endpoints, `Nodup` targets,
    no self-loops, targets below `start`, every vertex keeps a parent). -/
theorem rewireAux_invar {S : Type} [DecidableEq S] (O : Oracles S)
    (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ) (n : ℕ) (forbid : List S) (start s p : S)
    (verts : List S) (ws : List S) (edges : List (S × S))
    (hs : s ∈ verts) (hp : p ∈ verts)
    (hws : ∀ w ∈ ws, w ∈ verts)
    (h_end : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (h_nodup : (edges.map Prod.snd).Nodup)
    (h_noself : ∀ e ∈ edges, e.1 ≠ e.2)
    (h_nestart : ∀ e ∈ edges, e.2 ≠ start)
    (h_parent : ∀ v ∈ verts, v ≠ start → ∃ u, (u, v) ∈ edges)
    (hs_ne : s ≠ start) :
    (∀ e ∈ rewireAux O costs radiusOf n forbid start s p ws edges,
        e.1 ∈ verts ∧ e.2 ∈ verts) ∧
      ((rewireAux O costs radiusOf n forbid start s p ws edges).map Prod.snd).Nodup ∧
      (∀ e ∈ rewireAux O costs radiusOf n forbid start s p ws edges, e.1 ≠ e.2) ∧
      (∀ e ∈ rewireAux O costs radiusOf n forbid start s p ws edges, e.2 ≠ start) ∧
      (∀ v ∈ verts, v ≠ start →
        ∃ u, (u, v) ∈ rewireAux O costs radiusOf n forbid start s p ws edges) := by
  induction ws generalizing edges costs h_end h_nodup h_noself h_nestart h_parent
    with
  | nil =>
      simp only [rewireAux_nil]
      exact ⟨h_end, h_nodup, h_noself, h_nestart, h_parent⟩
  | cons w ws ih =>
      by_cases hcond : w ≠ start ∧ w ≠ s ∧ w ≠ p ∧ w ∉ forbid ∧ O.cost s w ≤ radiusOf n ∧
          O.link s w = true ∧
          ccLt (ccAdd (costToCome costs s) (O.cost s w)) (costToCome costs w)
      · rw [rewireAux_cons, ite_eq_left hcond]
        obtain ⟨hw_start, hw_s, _, _, _, _, _⟩ := hcond
        have hw_mem : w ∈ verts := hws w List.mem_cons_self
        have hws' : ∀ v ∈ ws, v ∈ verts := fun v hv =>
          hws v (List.mem_cons_of_mem w hv)
        have h_end' := replaceParent_endpoints edges verts s w hs hw_mem h_end
        have h_nodup' := replaceParent_nodup edges s w h_nodup
        have h_noself' :=
          replaceParent_no_self edges s w (Ne.symm hw_s) h_noself
        have h_nestart' := replaceParent_ne_start edges s w start h_nestart
        have h_parent' :=
          replaceParent_has_parent edges verts s w start hw_mem hw_start h_parent
        exact ih (edges := replaceParent edges s w)
          (costs := relaxPasses O (replaceParent edges s w) n [(start, (0, 1))])
          (hws := hws')
          (h_end := h_end') (h_nodup := h_nodup') (h_noself := h_noself')
          (h_nestart := h_nestart') (h_parent := h_parent')
      · rw [rewireAux_cons, ite_eq_right hcond]
        have hws' : ∀ v ∈ ws, v ∈ verts := fun v hv =>
          hws v (List.mem_cons_of_mem w hv)
        exact ih (edges := edges) (costs := costs) (hws := hws') (h_end := h_end)
          (h_nodup := h_nodup) (h_noself := h_noself)
          (h_nestart := h_nestart) (h_parent := h_parent)

/-- Recomputed costs after rewiring still start at `(0, 1)`. -/
theorem rewireAux_cost_start {S : Type} [DecidableEq S] (O : Oracles S)
    (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ) (n : ℕ) (forbid : List S) (start s p : S)
    (verts' : List S) (ws : List S) (edges : List (S × S))
    (hstart : ∀ e ∈ (rewireAux O costs radiusOf n forbid start s p ws edges), e.2 ≠ start) :
    costToCome
        (recomputeCosts O verts'
          (rewireAux O costs radiusOf n forbid start s p ws edges) start)
        start = (0, 1) :=
  recomputeCosts_cost_start O verts' _ start hstart

theorem ppath_mono {S : Type} (edges edges' : List (S × S))
    (hsub : ∀ e ∈ edges, e ∈ edges')
    (a b : S) (k : Nat) (p : PPath edges a b k) :
    Nonempty (PPath edges' a b k) := by
  induction p with
  | refl => exact ⟨.refl _⟩
  | step p' hmem ih =>
      obtain ⟨q'⟩ := ih
      exact ⟨.step q' (hsub _ hmem)⟩

theorem ppath_mono_cons {S : Type} (edges : List (S × S)) (e : S × S)
    (a b : S) (k : Nat) (p : PPath edges a b k) :
    Nonempty (PPath (e :: edges) a b k) := by
  apply ppath_mono edges (e :: edges) _ a b k p
  intro x hx
  exact List.mem_cons_of_mem e hx

theorem ppath_replaceParent_of_notmem {S : Type} [DecidableEq S]
    (edges : List (S × S)) (s w a b : S) (k : Nat)
    (P : PPath edges a b k) (hw : w ∉ P.verts) :
    ∃ Q : PPath (replaceParent edges s w) a b k, Q.verts = P.verts := by
  induction P with
  | refl =>
      exact ⟨.refl _, rfl⟩
  | step p' hmem ih =>
      rename_i mid fin kk
      rw [PPath.verts_step] at hw
      have hqw : w ∉ p'.verts := fun hmem => hw (by simp [hmem])
      have hcw : fin ≠ w := fun heq => hw (by simp [heq])
      obtain ⟨Q', hQ'⟩ := ih hqw
      have hmem' : (mid, fin) ∈ replaceParent edges s w :=
        replaceParent_mem_of_ne edges s w _ _ hmem hcw
      refine ⟨.step Q' hmem', ?_⟩
      rw [PPath.verts_step, PPath.verts_step, hQ']

theorem ppath_replaceParent {S : Type} [DecidableEq S]
    (edges : List (S × S)) (s w start : S) (k0 : Nat)
    (hs : PPath (replaceParent edges s w) start s k0)
    (b : S) (k : Nat) (P : PPath edges start b k) :
    ∃ k', Nonempty (PPath (replaceParent edges s w) start b k') := by
  induction P with
  | refl => exact ⟨0, ⟨.refl _⟩⟩
  | step p' hmem ih =>
      rename_i mid fin kk
      obtain ⟨k1, ⟨Q'⟩⟩ := ih
      by_cases hcw : fin = w
      · subst hcw
        have hsw : (s, fin) ∈ replaceParent edges s fin :=
          replaceParent_mem_parent edges s fin _ hmem
        have hsingle : PPath (replaceParent edges s fin) s fin 1 :=
          .step (.refl s) hsw
        exact hs.append hsingle
      · have hmem' : (mid, fin) ∈ replaceParent edges s w :=
          replaceParent_mem_of_ne edges s w _ _ hmem hcw
        exact ⟨k1 + 1, ⟨.step Q' hmem'⟩⟩

theorem ppath_rewireAux_all {S : Type} [DecidableEq S] (O : Oracles S)
    (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ) (n : ℕ) (forbid : List S)
    (start s p : S) (ws : List S) (edges0 : List (S × S))
    (k0 : Nat) (hs0 : PPath edges0 start s k0)
    (hverts : ∀ x ∈ hs0.verts, x = s ∨ x ∈ forbid) :
    ∀ (v : S) (k : Nat), PPath edges0 start v k →
      ∃ k', Nonempty (PPath (rewireAux O costs radiusOf n forbid start s p ws edges0) start v k') := by
  induction ws generalizing edges0 k0 hs0 costs with
  | nil =>
      intro v k P
      exact ⟨k, ⟨P⟩⟩
  | cons w ws' ih =>
      intro v k P
      by_cases hcond : w ≠ start ∧ w ≠ s ∧ w ≠ p ∧ w ∉ forbid ∧ O.cost s w ≤ radiusOf n ∧
          O.link s w = true ∧
          ccLt (ccAdd (costToCome costs s) (O.cost s w)) (costToCome costs w)
      · rw [rewireAux_cons, ite_eq_left hcond]
        obtain ⟨_, hw_s, _, hw_forbid, _, _, _⟩ := hcond
        have hw_notmem : w ∉ hs0.verts := by
          intro hmem
          obtain (heq | hmem') := hverts w hmem
          · exact hw_s heq
          · exact hw_forbid hmem'
        obtain ⟨hs1, hverts_eq⟩ := ppath_replaceParent_of_notmem edges0 s w start s k0 hs0 hw_notmem
        have hverts1 : ∀ x ∈ hs1.verts, x = s ∨ x ∈ forbid := by
          rw [hverts_eq]
          exact hverts
        obtain ⟨k1, ⟨P1⟩⟩ := ppath_replaceParent edges0 s w start k0 hs1 v k P
        exact ih (edges0 := replaceParent edges0 s w) (k0 := k0) (hs0 := hs1)
          (costs := relaxPasses O (replaceParent edges0 s w) n [(start, (0, 1))])
          hverts1 v k1 P1
      · rw [rewireAux_cons, ite_eq_right hcond]
        exact ih (edges0 := edges0) (k0 := k0) (hs0 := hs0) (costs := costs) hverts v k P

structure StarInvar {S : Type} [DecidableEq S] (O : Oracles S) (verts : List S)
    (edges : List (S × S)) (costs : List (S × Int × Nat)) (start : S) : Prop where
  start_mem : start ∈ verts
  verts_nodup : verts.Nodup
  edges_endpoints : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts
  targets_nodup : (edges.map Prod.snd).Nodup
  no_self : ∀ e ∈ edges, e.1 ≠ e.2
  target_ne_start : ∀ e ∈ edges, e.2 ≠ start
  has_parent : ∀ v ∈ verts, v ≠ start → ∃ u, (u, v) ∈ edges
  reachable : ∀ v ∈ verts, ∃ k, Nonempty (PPath edges start v k)
  costs_eq : costs = recomputeCosts O verts edges start

/-- A `Nodup` list contained in another is no longer (via finsets). -/
theorem nodup_length_le {S : Type} [DecidableEq S] (l verts : List S)
    (h1 : l.Nodup) (h2 : ∀ x ∈ l, x ∈ verts) : l.length ≤ verts.length := by
  have hsub : l.toFinset ⊆ verts.toFinset := by
    intro x hx
    simp only [List.mem_toFinset] at hx ⊢
    exact h2 x hx
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup h1] at hcard
  have hle := List.toFinset_card_le (l := verts)
  omega


/-- From the head of a parent chain, every member is reachable. -/
theorem chain_ppath_cons {S : Type} (edges : List (S × S)) (a : S)
    (l : List S) (h : IsParentChain edges (a :: l)) (v : S)
    (hv : v ∈ a :: l) : ∃ k, Nonempty (PPath edges a v k) := by
  induction l generalizing a v with
  | nil =>
      simp only [List.mem_singleton] at hv
      subst hv
      exact ⟨0, ⟨PPath.refl _⟩⟩
  | cons b rest ih =>
      simp only [IsParentChain] at h
      obtain ⟨hedge, hchain⟩ := h
      rw [List.mem_cons] at hv
      cases hv with
      | inl heq =>
          subst heq
          exact ⟨0, ⟨PPath.refl _⟩⟩
      | inr hmem =>
          obtain ⟨k, ⟨hp⟩⟩ := ih (a := b) (v := v) hchain hmem
          have hab : PPath edges a b (0 + 1) := PPath.step (PPath.refl a) hedge
          obtain ⟨m, ⟨hpath⟩⟩ := PPath.append hab hp
          exact ⟨m, ⟨hpath⟩⟩

/-- Appending a child to a chain ending in its parent keeps it a chain. -/
theorem isChain_append_singleton {S : Type} (edges : List (S × S))
    (l : List S) (u v : S) (hchain : IsParentChain edges l) (l' : List S)
    (hl : l = l' ++ [u]) (hmem : (u, v) ∈ edges) :
    IsParentChain edges (l ++ [v]) := by
  induction l' generalizing u l with
  | nil =>
      simp only [List.nil_append] at hl
      subst hl
      refine ⟨hmem, trivial⟩
  | cons a rest ih =>
      simp only [List.cons_append] at hl
      subst hl
      cases rest with
      | nil =>
          simp only [List.nil_append] at hchain ⊢
          obtain ⟨h1, _⟩ := hchain
          refine ⟨h1, hmem, trivial⟩
      | cons b rest2 =>
          simp only [List.cons_append] at hchain ⊢
          obtain ⟨h1, hchain2⟩ := hchain
          refine ⟨h1, ?_⟩
          have htail : IsParentChain edges
              ((b :: rest2 ++ [u]) ++ [v]) :=
            ih (u := u) (l := b :: rest2 ++ [u]) hchain2 rfl hmem
          simpa [List.cons_append, List.append_assoc] using htail

/-- Every parent chain starts with its seed. -/
theorem parentChain_eq_cons {S : Type} [DecidableEq S] (edges : List (S × S))
    (start u : S) (n : ℕ) :
    ∃ rest, parentChain edges start u n = u :: rest := by
  cases n with
  | zero => exact ⟨[], rfl⟩
  | succ n =>
      simp only [parentChain]
      by_cases hus : u = start
      · simp only [ite_eq_left hus]
        exact ⟨[], rfl⟩
      · simp only [hus, ite_false]
        cases hfp : findParent edges u with
        | none =>
            exact ⟨[], rfl⟩
        | some w =>
            exact ⟨_, rfl⟩

/-- Reversed parent chains are `IsParentChain`. -/
theorem parentChain_rev_isChain {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) (fuel : ℕ) :
    IsParentChain edges (parentChain edges start v fuel).reverse := by
  induction fuel generalizing v with
  | zero =>
      simp only [parentChain]
      simp
      trivial
  | succ n ih =>
      simp only [parentChain]
      by_cases hvs : v = start
      · simp [hvs]
        trivial
      · simp only [hvs, ite_false]
        cases hfp : findParent edges v with
        | none =>
            simp
            trivial
        | some u =>
            simp only [List.reverse_cons]
            have hmem : (u, v) ∈ edges :=
              findParent_some_mem edges v u hfp
            have htail := ih (v := u)
            obtain ⟨rest, hrest⟩ := parentChain_eq_cons edges start u n
            have hrev : (parentChain edges start u n).reverse =
                rest.reverse ++ [u] := by
              rw [hrest]
              simp
            rw [hrev] at htail ⊢
            exact isChain_append_singleton _ _ u v htail _ rfl hmem
/-- A parent chain missing `start` must have run out of fuel. -/
theorem parentChain_length_of_missing {S : Type} [DecidableEq S]
    (edges : List (S × S)) (verts : List S) (start v : S) (fuel : ℕ)
    (hend : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (hv : v ∈ verts)
    (h_parent : ∀ v ∈ verts, v ≠ start → ∃ u, (u, v) ∈ edges)
    (hmiss : start ∉ parentChain edges start v fuel) :
    (parentChain edges start v fuel).length = fuel + 1 := by
  induction fuel generalizing v with
  | zero =>
      simp [parentChain]
  | succ n ih =>
      simp only [parentChain] at hmiss ⊢
      by_cases hvs : v = start
      · subst hvs
        simp at hmiss
      · simp only [hvs, ite_false] at hmiss ⊢
        cases hfp : findParent edges v with
        | none =>
            simp at hmiss ⊢
            exfalso
            have hnone := findParent_none_notmem edges v
            obtain ⟨u, hu⟩ := h_parent v hv hvs
            exact hnone u hfp hu
        | some u =>
            rw [hfp] at hmiss
            dsimp only at hmiss ⊢
            simp only [List.length_cons] at ⊢
            have hu_mem : (u, v) ∈ edges :=
              findParent_some_mem edges v u hfp
            have hu_verts := (hend (u, v) hu_mem).1
            have hmiss' : start ∉ parentChain edges start u n := by
              intro hcon
              exact hmiss (List.mem_cons_of_mem v hcon)
            have hlen := ih (v := u) hu_verts hmiss'
            omega
/-- With `verts.length` fuel the parent chain reaches `start`. -/
-- GROUP 2
theorem parentChain_has_start {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (edges : List (S × S)) (costs : List (S × (Int × Nat)))
    (start v : S)
    (h_nodup : (edges.map Prod.snd).Nodup)
    (h_noself : ∀ e ∈ edges, e.1 ≠ e.2)
    (h_parent : ∀ v ∈ verts, v ≠ start → ∃ u, (u, v) ∈ edges)
    (h_end : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (h_costs : costs = recomputeCosts O verts edges start)
    (h_start : start ∈ verts)
    (h_verts_nodup : verts.Nodup)
    (h_notgt : ∀ e ∈ edges, e.2 ≠ start)
    (hcosted : ∀ x ∈ parentChain edges start v verts.length,
      x ∈ costs.map Prod.fst)
    (hv : v ∈ verts) :
    start ∈ parentChain edges start v verts.length := by
  by_contra hmiss
  have hmem_verts := parentChain_mem_verts edges verts start v verts.length
    h_end hv
  have hchain := parentChain_rev_isChain edges start v verts.length
  have hrev_mem : ∀ x ∈ (parentChain edges start v verts.length).reverse,
      x ∈ verts := by
    intro x hx
    simp only [List.mem_reverse] at hx
    exact hmem_verts x hx
  have hcosted_rev : ∀ x ∈ (parentChain edges start v verts.length).reverse,
      x ∈ costs.map Prod.fst := by
    intro x hx
    simp only [List.mem_reverse] at hx
    exact hcosted x hx
  have hnodup := parentChain_nodup O verts edges start costs
    h_start h_verts_nodup (fun e he => (h_end e he).2)
    h_nodup h_noself h_notgt h_costs
    ((parentChain edges start v verts.length).reverse)
    hchain hcosted_rev
  have hle := nodup_length_le _ verts hnodup hrev_mem
  rw [List.length_reverse] at hle
  have hlen := parentChain_length_of_missing edges verts start v verts.length
    h_end hv h_parent hmiss
  omega

/-- A chain containing `start` yields a path to its seed. -/
theorem parentChain_ppath {S : Type} [DecidableEq S] (edges : List (S × S))
    (start v : S) (fuel : ℕ)
    (hmem : start ∈ parentChain edges start v fuel) :
    ∃ k, Nonempty (PPath edges start v k) := by
  induction fuel generalizing v with
  | zero =>
      simp only [parentChain, List.mem_singleton] at hmem
      subst hmem
      exact ⟨0, ⟨PPath.refl _⟩⟩
  | succ n ih =>
      simp only [parentChain] at hmem
      by_cases hvs : v = start
      · subst hvs
        exact ⟨0, ⟨PPath.refl _⟩⟩
      · simp only [hvs, ite_false] at hmem
        cases hfp : findParent edges v with
        | none =>
            rw [hfp] at hmem
            dsimp only at hmem
            simp only [List.mem_singleton] at hmem
            subst hmem
            exact False.elim (hvs rfl)
        | some u =>
            rw [hfp] at hmem
            dsimp only at hmem
            simp only [List.mem_cons] at hmem
            cases hmem with
            | inl heq =>
                subst heq
                exact False.elim (hvs rfl)
            | inr htail =>
                obtain ⟨k, ⟨hp⟩⟩ := ih (v := u) htail
                have hedge : (u, v) ∈ edges :=
                  findParent_some_mem edges v u hfp
                refine ⟨k + 1, ⟨?_⟩⟩
                constructor <;> (first | exact hp | exact hedge)

/-- Every vertex is reachable from `start` in a tree with recomputed costs:
    follow `findParent` with `verts.length` fuel; the reversed chain is
    `IsParentChain` hence `Nodup`, so it cannot outgrow `verts` and must hit
    `start`; the chain then yields the path. -/
theorem reachable_of_invar {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (edges : List (S × S))
    (costs : List (S × (Int × Nat))) (start : S)
    (h_nodup : (edges.map Prod.snd).Nodup)
    (h_noself : ∀ e ∈ edges, e.1 ≠ e.2)
    (h_parent : ∀ v ∈ verts, v ≠ start → ∃ u, (u, v) ∈ edges)
    (h_end : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (h_verts_nodup : verts.Nodup)
    (h_costs : costs = recomputeCosts O verts edges start)
    (h_start : start ∈ verts)
    (h_notgt : ∀ e ∈ edges, e.2 ≠ start)
    (h_all_costed : ∀ v ∈ verts, v ∈ costs.map Prod.fst) :
    ∀ v ∈ verts, ∃ k, Nonempty (PPath edges start v k) := by
  intro v hv
  have hcosted : ∀ x ∈ parentChain edges start v verts.length,
      x ∈ costs.map Prod.fst := by
    intro x hx
    exact h_all_costed x
      (parentChain_mem_verts edges verts start v verts.length h_end hv x hx)
  have hstart := parentChain_has_start O verts edges costs start v
    h_nodup h_noself h_parent h_end h_costs
    h_start h_verts_nodup h_notgt hcosted hv
  exact parentChain_ppath edges start v verts.length hstart


/-- Vertices of an extended path: the new head or an old vertex. -/
theorem PPath.verts_append {S : Type} [DecidableEq S] {edges : List (S × S)}
    {start u v : S} {k : ℕ} (h : PPath edges start u k)
    (hmem : (u, v) ∈ edges) :
    ∀ x ∈ (PPath.step h hmem).verts, x = v ∨ x ∈ h.verts := by
  rw [PPath.verts_step]
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  exact hx.symm


/-- The chain from `start` is a singleton. -/
theorem parentChain_self {S : Type} [DecidableEq S] (edges : List (S × S))
    (start : S) (fuel : ℕ) :
    parentChain edges start start fuel = [start] := by
  cases fuel with
  | zero => rfl
  | succ n => simp [parentChain]


/-- A chain containing `start` yields a path staying inside the chain. -/
theorem parentChain_ppath_verts {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) (fuel : ℕ)
    (hmem : start ∈ parentChain edges start v fuel) :
    ∃ (k : ℕ) (p : PPath edges start v k),
      ∀ x ∈ p.verts, x ∈ parentChain edges start v fuel := by
  induction fuel generalizing v with
  | zero =>
      simp only [parentChain] at hmem
      have heq := List.mem_singleton.mp hmem
      rw [← heq]
      refine ⟨0, PPath.refl start, ?_⟩
      simp only [PPath.verts_refl, parentChain]
      intro x hx
      exact hx
  | succ n ih =>
      simp only [parentChain] at hmem
      by_cases hvs : v = start
      · rw [hvs]
        refine ⟨0, PPath.refl start, ?_⟩
        simp only [PPath.verts_refl]
        intro x hx
        simp only [List.mem_singleton] at hx
        rw [hx]
        rw [parentChain_self]
        exact List.mem_cons_self
      · simp only [hvs, ite_false] at hmem
        have hcases : findParent edges v = none ∨
            ∃ u, findParent edges v = some u := by
          cases h' : findParent edges v with
          | none => exact Or.inl rfl
          | some u => exact Or.inr ⟨u, rfl⟩
        cases hcases with
        | inl hfp =>
            rw [hfp] at hmem
            dsimp only at hmem
            have heq := List.mem_singleton.mp hmem
            exact absurd heq (Ne.symm hvs)
        | inr hex =>
            obtain ⟨u, hfp⟩ := hex
            rw [hfp] at hmem
            dsimp only at hmem
            simp only [List.mem_cons] at hmem
            have hmem' : start ∈ parentChain edges start u n := by
              cases hmem with
              | inl heq => exact absurd heq (Ne.symm hvs)
              | inr hm => exact hm
            obtain ⟨k', p', hsub⟩ := ih (v := u) (hmem := hmem')
            have hedge : (u, v) ∈ edges :=
              findParent_some_mem edges v u hfp
            refine ⟨k' + 1, PPath.step p' hedge, ?_⟩
            have hchain : parentChain edges start v (n + 1) =
                v :: parentChain edges start u n := by
              simp only [parentChain, hvs, ite_false, hfp]
            rw [hchain, PPath.verts_step]
            intro x hx
            simp only [List.mem_append, List.mem_singleton] at hx
            simp only [List.mem_cons]
            cases hx with
            | inl hm => exact Or.inr (hsub x hm)
            | inr heq => exact Or.inl heq

theorem parentChain_cons_eq {S : Type} [DecidableEq S] (edges : List (S × S))
    (verts : List S) (start : S) (e : S × S) (v : S) (fuel : ℕ)
    (hend : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (hv : v ∈ verts) (hne : e.2 ∉ verts) :
    parentChain (e :: edges) start v fuel = parentChain edges start v fuel := by
  induction fuel generalizing v with
  | zero => rfl
  | succ n ih =>
      simp only [parentChain]
      by_cases hvs : v = start
      · rw [ite_eq_left hvs, ite_eq_left hvs]
      · simp only [hvs, ite_false]
        have hnev : e.2 ≠ v := by
          intro heq
          apply hne
          rw [heq]
          exact hv
        have hfp : findParent (e :: edges) v = findParent edges v := by
          simp only [findParent, hnev, ite_false]
        rw [hfp]
        cases hfp' : findParent edges v with
        | none => rfl
        | some u =>
            dsimp only [hfp']
            have hu_mem : (u, v) ∈ edges :=
              findParent_some_mem edges v u hfp'
            have hu_verts := (hend (u, v) hu_mem).1
            exact congrArg (v :: ·) (ih (v := u) hu_verts)

/-- Extend the tree by one sample: if `s` is free and has a parent `p`,
    add `s` and `(p, s)`, rewire over the old vertices at count
    `(s :: verts).length` while refusing `p`'s ancestor chain, then
    recompute costs once. -/
def extendStar {S : Type} [DecidableEq S] (O : Oracles S) (verts : List S)
    (edges : List (S × S)) (costs : List (S × (Int × Nat))) (radiusOf : ℕ → ℚ)
    (start s : S) : List S × List (S × S) × List (S × (Int × Nat)) :=
  if O.free s = true then
    match chooseParent O verts costs radiusOf start s with
    | none => (verts, edges, costs)
    | some p =>
        let verts' := s :: verts
        let edges0 := (p, s) :: edges
        let forbid := parentChain edges0 start p verts.length
        let edges' :=
          rewireAux O (recomputeCosts O verts' edges0 start) radiusOf verts'.length
            forbid start s p verts edges0
        let costs' := recomputeCosts O verts' edges' start
        (verts', edges', costs')
  else (verts, edges, costs)

theorem extendStar_invar {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (edges : List (S × S)) (costs : List (S × (Int × Nat)))
    (radiusOf : ℕ → ℚ) (start s : S)
    (h : StarInvar O verts edges costs start) (hs : s ∉ verts) :
    StarInvar O (extendStar O verts edges costs radiusOf start s).1
      (extendStar O verts edges costs radiusOf start s).2.1
      (extendStar O verts edges costs radiusOf start s).2.2 start := by
  unfold extendStar
  by_cases hfree : O.free s = true
  · rw [ite_eq_left hfree]
    cases hcp : chooseParent O verts costs radiusOf start s with
    | none =>
        exact h
    | some p =>
        have hpmem : p ∈ candidates O verts radiusOf start s :=
          chooseParent_mem O verts costs radiusOf start s p hcp
        have hmem := (mem_candidates O verts radiusOf start s p).mp hpmem
        obtain ⟨hp_verts, _, _⟩ := hmem
        have hs_ne : s ≠ start := fun heq => hs (heq.symm ▸ h.start_mem)
        have hp_ne_s : p ≠ s := fun heq => hs (heq ▸ hp_verts)
        have hs_new : s ∈ s :: verts := List.mem_cons_self
        have hp_new : p ∈ s :: verts := List.mem_cons_of_mem s hp_verts
        have hws : ∀ w ∈ verts, w ∈ s :: verts := fun w hw =>
          List.mem_cons_of_mem s hw
        have h_end0 : ∀ e ∈ (p, s) :: edges,
            e.1 ∈ s :: verts ∧ e.2 ∈ s :: verts := by
          intro e he
          simp only [List.mem_cons] at he
          cases he with
          | inl heq =>
              subst heq
              exact ⟨hp_new, hs_new⟩
          | inr hmem =>
              have hend := h.edges_endpoints e hmem
              exact ⟨List.mem_cons_of_mem s hend.1,
                List.mem_cons_of_mem s hend.2⟩
        have h_nodup0 : (((p, s) :: edges).map Prod.snd).Nodup := by
          have hs_nmem : s ∉ edges.map Prod.snd := by
            intro hcontra
            obtain ⟨e, he_mem, he_eq⟩ := List.mem_map.mp hcontra
            have hend := (h.edges_endpoints e he_mem).2
            rw [he_eq] at hend
            exact hs hend
          show (s :: edges.map Prod.snd).Nodup
          rw [List.nodup_cons]
          exact ⟨hs_nmem, h.targets_nodup⟩
        have h_noself0 : ∀ e ∈ (p, s) :: edges, e.1 ≠ e.2 := by
          intro e he
          simp only [List.mem_cons] at he
          cases he with
          | inl heq =>
              subst heq
              exact hp_ne_s
          | inr hmem => exact h.no_self e hmem
        have h_nestart0 : ∀ e ∈ (p, s) :: edges, e.2 ≠ start := by
          intro e he
          simp only [List.mem_cons] at he
          cases he with
          | inl heq =>
              subst heq
              exact hs_ne
          | inr hmem => exact h.target_ne_start e hmem
        have h_parent0 : ∀ v ∈ s :: verts, v ≠ start →
            ∃ u, (u, v) ∈ (p, s) :: edges := by
          intro v hv hne
          simp only [List.mem_cons] at hv
          cases hv with
          | inl heq =>
              subst heq
              exact ⟨p, List.mem_cons_self⟩
          | inr hmem =>
              obtain ⟨u, hu⟩ := h.has_parent v hmem hne
              exact ⟨u, List.mem_cons_of_mem (p, s) hu⟩
        have hrew := rewireAux_invar O
          (recomputeCosts O (s :: verts) ((p, s) :: edges) start)
          radiusOf ((s :: verts).length)
          (parentChain ((p, s) :: edges) start p verts.length)
          start s p
          (s :: verts) verts ((p, s) :: edges)
          hs_new hp_new hws h_end0 h_nodup0 h_noself0 h_nestart0 h_parent0 hs_ne
        obtain ⟨h_end', h_nodup', h_noself', h_nestart', h_parent'⟩ := hrew
        have h_verts_nodup : (s :: verts).Nodup :=
          List.nodup_cons.mpr ⟨hs, h.verts_nodup⟩
        have h_all_costed : ∀ v ∈ verts, v ∈ costs.map Prod.fst := by
          intro v hv
          obtain ⟨k, ⟨hp⟩⟩ := h.reachable v hv
          obtain ⟨k', hp', hnodup, _hle⟩ := PPath.exists_simple_le O hp
          have htgt : ∀ e ∈ edges, e.2 ∈ verts := fun e he =>
            (h.edges_endpoints e he).2
          have hlen := PPath.simple_length_le verts h.start_mem htgt
            h.verts_nodup hp' hnodup
          have hkn : k' ≤ verts.length := by omega
          have hcost :=
            bellmanFord_upper O edges start v k' hp' verts.length hkn
          rw [h.costs_eq]
          simpa [recomputeCosts] using hcost.1
        have hchain_mem : ∀ x ∈ parentChain edges start p verts.length, x ∈ verts :=
          parentChain_mem_verts edges verts start p verts.length h.edges_endpoints hp_verts
        have hcosted : ∀ x ∈ parentChain edges start p verts.length,
            x ∈ costs.map Prod.fst :=
          fun x hx => h_all_costed x (hchain_mem x hx)
        have hp_start_old : start ∈ parentChain edges start p verts.length :=
          parentChain_has_start O verts edges costs start p
            h.targets_nodup h.no_self h.has_parent h.edges_endpoints h.costs_eq
            h.start_mem h.verts_nodup h.target_ne_start hcosted hp_verts
        have hchains : parentChain ((p, s) :: edges) start p verts.length =
            parentChain edges start p verts.length :=
          parentChain_cons_eq edges verts start (p, s) p verts.length
            h.edges_endpoints hp_verts hs
        have hp_start0 :
            start ∈ parentChain ((p, s) :: edges) start p verts.length := by
          rw [hchains]
          exact hp_start_old
        obtain ⟨k1, Pc, hPcsub⟩ :=
          parentChain_ppath_verts ((p, s) :: edges) start p verts.length
            hp_start0
        have hps_mem : (p, s) ∈ (p, s) :: edges := List.mem_cons_self
        have hhs0 : ∀ x ∈ (PPath.step Pc hps_mem).verts,
            x = s ∨ x ∈ parentChain ((p, s) :: edges) start p verts.length := by
          intro x hx
          have happ := PPath.verts_append Pc hps_mem x hx
          cases happ with
          | inl heq => exact Or.inl heq
          | inr hmem => exact Or.inr (hPcsub x hmem)
        have hreach : ∀ v ∈ s :: verts, ∃ (k : ℕ), Nonempty
            (PPath (rewireAux O
              (recomputeCosts O (s :: verts) ((p, s) :: edges) start)
              radiusOf ((s :: verts).length)
              (parentChain ((p, s) :: edges) start p verts.length) start s p
              verts
              ((p, s) :: edges)) start v k) := by
          intro v hv
          simp only [List.mem_cons] at hv
          cases hv with
          | inl heq =>
              subst v
              exact ppath_rewireAux_all O
                (recomputeCosts O (s :: verts) ((p, s) :: edges) start)
                radiusOf ((s :: verts).length)
                (parentChain ((p, s) :: edges) start p verts.length)
                start s p
                verts
                ((p, s) :: edges) (k1 + 1) (PPath.step Pc hps_mem) hhs0 s
                (k1 + 1) (PPath.step Pc hps_mem)
          | inr hmem =>
              obtain ⟨k, ⟨hp⟩⟩ := h.reachable v hmem
              have hp0 : Nonempty (PPath ((p, s) :: edges) start v k) :=
                ppath_mono edges ((p, s) :: edges)
                  (fun e he => List.mem_cons_of_mem (p, s) he) start v k hp
              obtain ⟨hp0'⟩ := hp0
              exact ppath_rewireAux_all O
                (recomputeCosts O (s :: verts) ((p, s) :: edges) start)
                radiusOf ((s :: verts).length)
                (parentChain ((p, s) :: edges) start p verts.length)
                start s p
                verts
                ((p, s) :: edges) (k1 + 1) (PPath.step Pc hps_mem) hhs0 v k
                hp0'
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact List.mem_cons_of_mem s h.start_mem
        · exact h_verts_nodup
        · exact h_end'
        · exact h_nodup'
        · exact h_noself'
        · exact h_nestart'
        · exact h_parent'
        · exact hreach
        · rfl
  · rw [ite_eq_right hfree]
    dsimp only
    exact h

theorem extendStar_cost_start {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (edges : List (S × S)) (costs : List (S × (Int × Nat)))
    (radiusOf : ℕ → ℚ) (start s : S)
    (h : StarInvar O verts edges costs start) (hs : s ∉ verts) :
    costToCome (extendStar O verts edges costs radiusOf start s).2.2 start =
      (0, 1) := by
  have hinv := extendStar_invar O verts edges costs radiusOf start s h hs
  rw [hinv.costs_eq]
  exact recomputeCosts_cost_start O _ _ start hinv.target_ne_start

/-- Main loop: extend by each sample in turn, skipping samples already in the
    tree (which would break `Nodup`). Samples come last. -/
def rrtStarAux {S : Type} [DecidableEq S] (O : Oracles S) (radiusOf : ℕ → ℚ)
    (start : S) (verts : List S) (edges : List (S × S))
    (costs : List (S × (Int × Nat))) : List S → List S × List (S × S) ×
      List (S × (Int × Nat))
  | [] => (verts, edges, costs)
  | s :: ss =>
      if s ∈ verts then rrtStarAux O radiusOf start verts edges costs ss
      else
        let (verts', edges', costs') :=
          extendStar O verts edges costs radiusOf start s
        rrtStarAux O radiusOf start verts' edges' costs' ss

theorem rrtStarAux_nil {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (verts : List S) (edges : List (S × S))
    (costs : List (S × (Int × Nat))) :
    rrtStarAux O radiusOf start verts edges costs [] = (verts, edges, costs) :=
  rfl

theorem rrtStarAux_cons {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (verts : List S) (edges : List (S × S))
    (costs : List (S × (Int × Nat))) (s : S) (ss : List S) :
    rrtStarAux O radiusOf start verts edges costs (s :: ss) =
      (if s ∈ verts then rrtStarAux O radiusOf start verts edges costs ss
      else
        let (verts', edges', costs') :=
          extendStar O verts edges costs radiusOf start s
        rrtStarAux O radiusOf start verts' edges' costs' ss) :=
  rfl

theorem rrtStarAux_invar {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (verts : List S)
    (edges : List (S × S)) (costs : List (S × (Int × Nat)))
    (h : StarInvar O verts edges costs start) :
    StarInvar O (rrtStarAux O radiusOf start verts edges costs samples).1
      (rrtStarAux O radiusOf start verts edges costs samples).2.1
      (rrtStarAux O radiusOf start verts edges costs samples).2.2 start := by
  induction samples generalizing verts edges costs with
  | nil =>
      simpa [rrtStarAux_nil] using h
  | cons s ss ih =>
      rw [rrtStarAux_cons]
      by_cases hmem : s ∈ verts
      · rw [ite_eq_left hmem]
        exact ih (verts := verts) (edges := edges) (costs := costs) h
      · rw [ite_eq_right hmem]
        dsimp only
        have h' := extendStar_invar O verts edges costs radiusOf start s h hmem
        exact ih _ _ _ h'

/-- Output vertices come from the input tree or the samples. -/
theorem rrtStarAux_subset {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (verts : List S)
    (edges : List (S × S)) (costs : List (S × (Int × Nat))) (v : S)
    (hmem : v ∈ (rrtStarAux O radiusOf start verts edges costs samples).1) :
    v ∈ verts ∨ v ∈ samples := by
  induction samples generalizing verts edges costs with
  | nil =>
      simp only [rrtStarAux_nil] at hmem
      exact Or.inl hmem
  | cons s ss ih =>
      rw [rrtStarAux_cons] at hmem
      by_cases hvs : s ∈ verts
      · rw [ite_eq_left hvs] at hmem
        have hor := ih (verts := verts) (edges := edges) (costs := costs) hmem
        cases hor with
        | inl hv => exact Or.inl hv
        | inr hs =>
            exact Or.inr (List.mem_cons_of_mem s hs)
      · rw [ite_eq_right hvs] at hmem
        dsimp only at hmem
        have hor := ih
          (verts := (extendStar O verts edges costs radiusOf start s).1)
          (edges := (extendStar O verts edges costs radiusOf start s).2.1)
          (costs := (extendStar O verts edges costs radiusOf start s).2.2)
          hmem
        cases hor with
        | inl hv =>
            unfold extendStar at hv
            by_cases hfree : O.free s = true
            · rw [ite_eq_left hfree] at hv
              cases hcp : chooseParent O verts costs radiusOf start s with
              | none =>
                  simp only [hcp] at hv
                  exact Or.inl hv
              | some p =>
                  simp only [hcp] at hv
                  simp only [List.mem_cons] at hv
                  cases hv with
                  | inl heq =>
                      subst heq
                      exact Or.inr (List.mem_cons_self)
                  | inr hv2 => exact Or.inl hv2
            · rw [ite_eq_right hfree] at hv
              dsimp only at hv
              exact Or.inl hv
        | inr hs =>
            exact Or.inr (List.mem_cons_of_mem s hs)

theorem rrtStarAux_start_mem {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (verts : List S)
    (edges : List (S × S)) (costs : List (S × (Int × Nat)))
    (h : StarInvar O verts edges costs start) :
    start ∈ (rrtStarAux O radiusOf start verts edges costs samples).1 :=
  (rrtStarAux_invar O radiusOf start samples verts edges costs h).start_mem

theorem rrtStarAux_cost_start {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (verts : List S)
    (edges : List (S × S)) (costs : List (S × (Int × Nat)))
    (h : StarInvar O verts edges costs start) :
    costToCome
        (rrtStarAux O radiusOf start verts edges costs samples).2.2 start =
      (0, 1) := by
  have hinv := rrtStarAux_invar O radiusOf start samples verts edges costs h
  rw [hinv.costs_eq]
  exact recomputeCosts_cost_start O _ _ start hinv.target_ne_start

/-- RRT*: run the loop from the singleton tree. -/
def rrtStar {S : Type} [DecidableEq S] (O : Oracles S) (radiusOf : ℕ → ℚ)
    (start : S) (samples : List S) :
    List S × List (S × S) × List (S × (Int × Nat)) :=
  rrtStarAux O radiusOf start [start] [] (recomputeCosts O [start] [] start)
    samples

/-- The singleton tree satisfies the invariant. -/
theorem rrtStar_init {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) :
    StarInvar O [start] [] (recomputeCosts O [start] [] start) start := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.mem_cons_self
  · exact List.nodup_singleton start
  · simp
  · exact List.nodup_nil
  · simp
  · simp
  · intro v hv hne
    simp only [List.mem_singleton] at hv
    subst hv
    exact False.elim (hne rfl)
  · intro v hv
    simp only [List.mem_singleton] at hv
    subst hv
    exact ⟨0, ⟨PPath.refl _⟩⟩
  · rfl

/-- Every invariant vertex is costed after recomputation (via a short path). -/
theorem all_costed_of_invar {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (edges : List (S × S)) (costs : List (S × (Int × Nat)))
    (start : S) (h : StarInvar O verts edges costs start) (v : S)
    (hv : v ∈ verts) : v ∈ (recomputeCosts O verts edges start).map Prod.fst := by
  obtain ⟨k, ⟨hp⟩⟩ := h.reachable v hv
  obtain ⟨k', p', hnodup, _⟩ := PPath.exists_simple_le O hp
  have hu : start ∈ verts := h.start_mem
  have htgt : ∀ e ∈ edges, e.2 ∈ verts := fun e he => (h.edges_endpoints e he).2
  have hndv : verts.Nodup := h.verts_nodup
  have hlen : k' + 1 ≤ verts.length :=
    PPath.simple_length_le verts hu htgt hndv p' hnodup
  have hk_le : k' ≤ verts.length := by omega
  have hbf := bellmanFord_upper O edges start v k' p' verts.length hk_le
  simpa [recomputeCosts] using hbf.1

/-- Output vertices are `start` or samples. -/
theorem rrtStar_verts_subset {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (v : S)
    (hmem : v ∈ (rrtStar O radiusOf start samples).1) :
    v = start ∨ v ∈ samples := by
  have hmem2 : v ∈ (rrtStarAux O radiusOf start [start] []
      (recomputeCosts O [start] [] start) samples).1 := by
    simpa [rrtStar] using hmem
  have hor := rrtStarAux_subset O radiusOf start samples [start] [] _ v hmem2
  cases hor with
  | inl hv =>
      simp only [List.mem_singleton] at hv
      exact Or.inl hv
  | inr hs => exact Or.inr hs

/-- Output edges have `Nodup` targets (they form a tree). -/
theorem rrtStar_tree {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) :
    (((rrtStar O radiusOf start samples).2.1).map Prod.snd).Nodup := by
  have hinit := rrtStar_init O radiusOf start
  have hinv := rrtStarAux_invar O radiusOf start samples [start] []
    (recomputeCosts O [start] [] start) hinit
  simpa [rrtStar] using hinv.targets_nodup

theorem rrtStar_cost_start {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) :
    costToCome (rrtStar O radiusOf start samples).2.2 start = (0, 1) := by
  have hinit := rrtStar_init O radiusOf start
  have hinv := rrtStarAux_invar O radiusOf start samples [start] []
    (recomputeCosts O [start] [] start) hinit
  have hinv' : StarInvar O (rrtStar O radiusOf start samples).1
      (rrtStar O radiusOf start samples).2.1
      (rrtStar O radiusOf start samples).2.2 start := by
    simpa [rrtStar] using hinv
  rw [hinv'.costs_eq]
  exact recomputeCosts_cost_start O _ _ start hinv'.target_ne_start

/-- Every maintained parent edge attains `pairVal` equality. -/
theorem rrtStar_parent_tight {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (p v : S)
    (hmem : (p, v) ∈ (rrtStar O radiusOf start samples).2.1) :
    pairVal (ccAdd (costToCome (rrtStar O radiusOf start samples).2.2 p)
        (O.cost p v)) =
      pairVal (costToCome (rrtStar O radiusOf start samples).2.2 v) := by
  have hinit := rrtStar_init O radiusOf start
  have hinv := rrtStarAux_invar O radiusOf start samples [start] []
    (recomputeCosts O [start] [] start) hinit
  have hinv' : StarInvar O (rrtStar O radiusOf start samples).1
      (rrtStar O radiusOf start samples).2.1
      (rrtStar O radiusOf start samples).2.2 start := by
    simpa [rrtStar] using hinv
  have hne : v ≠ start := hinv'.target_ne_start (p, v) hmem
  have hv_verts : v ∈ (rrtStar O radiusOf start samples).1 :=
    (hinv'.edges_endpoints (p, v) hmem).2
  have hcosted : v ∈ (recomputeCosts O (rrtStar O radiusOf start samples).1
      (rrtStar O radiusOf start samples).2.1 start).map Prod.fst :=
    all_costed_of_invar O _ _ _ start hinv' v hv_verts
  have hhtgt : ∀ e ∈ (rrtStar O radiusOf start samples).2.1,
      e.2 ∈ (rrtStar O radiusOf start samples).1 :=
    fun e he => (hinv'.edges_endpoints e he).2
  rw [hinv'.costs_eq]
  obtain ⟨u, hu_mem, _, hu_tight⟩ :=
    recomputeCosts_tight O _ _ start hinv'.start_mem hinv'.verts_nodup hhtgt v
      hcosted hne
  have hedge_eq : (u, v) = (p, v) :=
    nodupTargets_unique _ hinv'.targets_nodup (u, v) hu_mem (p, v) hmem rfl
  have huniq : u = p := congrArg Prod.fst hedge_eq
  subst huniq
  exact hu_tight.symm

/-- Parent costs are strictly below child costs. -/
theorem rrtStar_parent_cost_lt {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (p v : S)
    (hmem : (p, v) ∈ (rrtStar O radiusOf start samples).2.1) :
    pairVal (costToCome (rrtStar O radiusOf start samples).2.2 p) <
      pairVal (costToCome (rrtStar O radiusOf start samples).2.2 v) := by
  have hinit := rrtStar_init O radiusOf start
  have hinv := rrtStarAux_invar O radiusOf start samples [start] []
    (recomputeCosts O [start] [] start) hinit
  have hinv' : StarInvar O (rrtStar O radiusOf start samples).1
      (rrtStar O radiusOf start samples).2.1
      (rrtStar O radiusOf start samples).2.2 start := by
    simpa [rrtStar] using hinv
  have hne : v ≠ start := hinv'.target_ne_start (p, v) hmem
  have hv_verts : v ∈ (rrtStar O radiusOf start samples).1 :=
    (hinv'.edges_endpoints (p, v) hmem).2
  have hu_verts : p ∈ (rrtStar O radiusOf start samples).1 :=
    (hinv'.edges_endpoints (p, v) hmem).1
  have hv_costed : v ∈ (recomputeCosts O (rrtStar O radiusOf start samples).1
      (rrtStar O radiusOf start samples).2.1 start).map Prod.fst :=
    all_costed_of_invar O _ _ _ start hinv' v hv_verts
  have hu_costed : p ∈ (recomputeCosts O (rrtStar O radiusOf start samples).1
      (rrtStar O radiusOf start samples).2.1 start).map Prod.fst :=
    all_costed_of_invar O _ _ _ start hinv' p hu_verts
  have hv : v ∈ (rrtStar O radiusOf start samples).2.2.map Prod.fst := by
    rw [hinv'.costs_eq]
    exact hv_costed
  have hu : p ∈ (rrtStar O radiusOf start samples).2.2.map Prod.fst := by
    rw [hinv'.costs_eq]
    exact hu_costed
  have hhtgt : ∀ e ∈ (rrtStar O radiusOf start samples).2.1,
      e.2 ∈ (rrtStar O radiusOf start samples).1 :=
    fun e he => (hinv'.edges_endpoints e he).2
  exact parent_edge_cost_lt O _ _ start _ hinv'.start_mem hinv'.verts_nodup
    hhtgt hinv'.targets_nodup hinv'.no_self hinv'.costs_eq p v hmem hne hu hv

/-- Parent chains over the output are `Nodup` (the tree is acyclic). -/
theorem rrtStar_acyclic {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (l : List S)
    (hchain : IsParentChain (rrtStar O radiusOf start samples).2.1 l)
    (hverts : ∀ v ∈ l, v ∈ (rrtStar O radiusOf start samples).1) :
    l.Nodup := by
  have hinit := rrtStar_init O radiusOf start
  have hinv := rrtStarAux_invar O radiusOf start samples [start] []
    (recomputeCosts O [start] [] start) hinit
  have hinv' : StarInvar O (rrtStar O radiusOf start samples).1
      (rrtStar O radiusOf start samples).2.1
      (rrtStar O radiusOf start samples).2.2 start := by
    simpa [rrtStar] using hinv
  have hcosted : ∀ x ∈ l,
      x ∈ (rrtStar O radiusOf start samples).2.2.map Prod.fst := by
    intro x hx
    rw [hinv'.costs_eq]
    exact all_costed_of_invar O _ _ _ start hinv' x (hverts x hx)
  exact parentChain_nodup O _ _ start _ hinv'.start_mem hinv'.verts_nodup
    (fun e he => (hinv'.edges_endpoints e he).2) hinv'.targets_nodup
    hinv'.no_self hinv'.target_ne_start hinv'.costs_eq l hchain hcosted

/-- Two-element parent chains have distinct ends.
    The general `head? ≠ getLast?` form needs index reasoning over `getLast?`
    (more than one lemma past `rrtStar_acyclic`), so this is the `Nodup`-direct
    form. -/
theorem rrtStar_chain_ends_ne {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (a b : S)
    (hchain : IsParentChain (rrtStar O radiusOf start samples).2.1 [a, b])
    (ha : a ∈ (rrtStar O radiusOf start samples).1)
    (hb : b ∈ (rrtStar O radiusOf start samples).1) : a ≠ b := by
  have hverts : ∀ v ∈ [a, b], v ∈ (rrtStar O radiusOf start samples).1 := by
    intro v hv
    rw [List.mem_cons] at hv
    cases hv with
    | inl heq =>
        subst heq
        exact ha
    | inr hmem =>
        simp only [List.mem_singleton] at hmem
        subst hmem
        exact hb
  have hnodup := rrtStar_acyclic O radiusOf start samples [a, b] hchain hverts
  simp only [List.nodup_cons, List.mem_singleton] at hnodup
  exact hnodup.1

end Cslib.Planning.MotionPlanning.SamplingPlanners
