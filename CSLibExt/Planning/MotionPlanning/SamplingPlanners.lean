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
asymptotic-optimality claim. This formalization uses the single rational
`cost` both as the proximity measure (nearest-vertex selection, near-vertex
sets, radius tests, and roadmap adjacency bounds) and as the objective cost
accumulated in cost-to-come; its laws assume neither symmetry nor the
triangle inequality. This is the cost-induced-proximity specialization of
the Karaman-Frazzoli algorithms (in their Euclidean path-length setting the
two roles coincide), not the general metric-plus-cost form. Steering is an
unconstrained oracle with no steering bound modelled. With an asymmetric
cost, parent candidates test the directed cost from candidate to steered
point while rewiring tests the directed cost from the new vertex to the old
vertex.

All four planners share one oracle bundle (`Oracles`): a point-collision test
`free`, a local planner `link` between configurations, a steering function
`steer` from a vertex toward a sample, a cost proxy `cost`, valued in the
rationals so that examples compute by `decide`, serving both as the proximity
measure and as the objective cost, and a connection radius `radius`.

* sPRM: the vertices are the initial configuration together with the
  collision-free samples, duplicates removed. The edge list carries both
  directed arcs of each qualifying unordered pair, requiring the cost bound
  in both directions and `link` success in both directions.
* RRT: a fold over the sample list. For each sample `s`, let `u` be the
  nearest current tree vertex (the first cost minimizer in list order,
  computed by `nearest`) and `x := O.steer u s` the steered configuration;
  `x` is inserted with edge `(u, x)` when the raw sample `s` is free, `x`
  is free, the local planner links `u` to `x`, and `x` is fresh. A sample
  that is not collision free is skipped without steering influence,
  matching the source algorithms, which draw every sample from the
  collision-free space; a sample whose steered point already lies in the
  tree inserts nothing. The output keeps both edge
  endpoints in the vertex list, vertices and edge targets duplicate free,
  no edge into the start, one more vertex than edges, every vertex
  reachable from the start, and parent chains with vertices in the RRT vertex list duplicate free
  (`rrt_reachable`, `rrt_acyclic`).
* PRM*: like sPRM, except the connection radius is given by `radiusOf`
  applied to the number of collision-free samples instead of the fixed
  `radius`. The vertices are the initial configuration together with the
  collision-free samples, duplicates removed, and the edge list carries
  both directed arcs of each qualifying unordered pair.
* RRT*: a fold over the sample list threading vertices, parent edges, and a
  cost-to-come table. Every collision-free sample `s` is steered from its
  nearest vertex `u` (`x := O.steer u s`) and the extension is skipped when
  `s` is not collision free or when `x` fails the free/link/fresh/has-parent
  gate; a sample that is not collision free is skipped without steering
  influence, matching the source algorithms, which draw every sample from
  the collision-free space. The parent search is seeded
  with the nearest vertex `u` when it is a candidate (otherwise the first
  candidate) and replaces the incumbent only on a strictly smaller
  cost-to-come plus edge cost among vertices that link to `x` and are
  `radiusOf`-near it, so ties keep the incumbent and `u` wins ties against
  other candidates, since `u` itself is a candidate whenever it links to
  `x`, even outside the radius (the `v = near` disjunct in `candidates`);
  then nearby vertices that `x` links to are rewired through `x` when that
  is strictly cheaper (sequential per-flip recompute, no cascade), and costs
  are fully recomputed.

Non-goals: nearest-neighbour data structures, probabilistic completeness, and
asymptotic optimality are out of scope.
-/

/-- Oracle bundle shared by all four planners. -/
structure Oracles (C : Type) where
  /-- Point-collision oracle: true when the configuration is collision free. -/
  free : C → Bool
  /-- Local planner: attempts to connect the first configuration to the second. -/
  link : C → C → Bool
  /-- Steering function: `steer u s` is the configuration reached from `u`
      toward sample `s` (identity steering `steer u s = s` is the
      unbounded-step case). -/
  steer : C → C → C
  /-- Cost proxy between configurations, valued in `Rat` so examples compute.
      It serves both as the proximity measure and as the objective cost
      accumulated in cost-to-come. -/
  cost : C → C → Rat
  /-- Connection radius for the roadmap. -/
  radius : Rat
  /-- Costs are nonnegative. -/
  cost_nonneg : ∀ a b, 0 ≤ cost a b
  /-- Self-cost is zero. -/
  cost_self : ∀ a, cost a a = 0
  /-- Costs between distinct configurations are positive. -/
  cost_pos : ∀ a b, a ≠ b → 0 < cost a b

/-- sPRM vertices: the initial configuration together with the collision-free
samples, duplicates removed. -/
def sprmVertices {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) : List C :=
  (start :: (samples.filter O.free)).dedup

/-- Membership in the sPRM vertices: the initial configuration or a
collision-free sample. -/
theorem sprmVertices_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (v : C) :
    v ∈ sprmVertices O start samples ↔
      v = start ∨ (v ∈ samples ∧ O.free v = true) := by
  unfold sprmVertices
  simp only [List.mem_dedup, List.mem_cons, List.mem_filter]

/-- The initial configuration is an sPRM vertex. -/
theorem sprmVertices_start_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) : start ∈ sprmVertices O start samples := by
  rw [sprmVertices_mem]
  exact Or.inl rfl

/-- Every sPRM vertex is collision free, when the initial configuration is. -/
theorem sprmVertices_all_free {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (hstart : O.free start = true) (v : C)
    (hv : v ∈ sprmVertices O start samples) : O.free v = true := by
  rw [sprmVertices_mem] at hv
  rcases hv with rfl | ⟨_, hfree⟩
  · exact hstart
  · exact hfree

/-- sPRM vertices have no duplicates. -/
theorem sprmVertices_nodup {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) : (sprmVertices O start samples).Nodup := by
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

/-- Both directed arcs of each edge: the list plus its reversals. -/
def withReversals {C : Type} (edges : List (C × C)) : List (C × C) :=
  edges ++ edges.map Prod.swap

/-- Membership in `withReversals`: the arc or its reversal is in the input. -/
theorem mem_withReversals {C : Type} (edges : List (C × C)) (u v : C) :
    (u, v) ∈ withReversals edges ↔ (u, v) ∈ edges ∨ (v, u) ∈ edges := by
  unfold withReversals
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨p, hmem, hpair⟩)
    · exact Or.inl h
    · obtain ⟨a, b⟩ := p
      rw [Prod.swap_prod_mk] at hpair
      rw [Prod.mk.injEq] at hpair
      obtain ⟨rfl, rfl⟩ := hpair
      exact Or.inr hmem
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨(v, u), h, rfl⟩

/-- Reversals are closed under swapping. -/
theorem swap_mem_withReversals {C : Type} (edges : List (C × C)) (u v : C)
    (h : (u, v) ∈ withReversals edges) : (v, u) ∈ withReversals edges := by
  rw [mem_withReversals] at h ⊢
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- sPRM edges: both directed arcs of each qualifying unordered pair, when the
cost bound holds and the local planner succeeds in both directions. -/
def sprmEdges {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) : List (C × C) :=
  withReversals (allPairs O (sprmVertices O start samples))

/-- Edges attach to vertices and satisfy the edge predicate. -/
theorem sprmEdges_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (u v : C)
    (h : (u, v) ∈ sprmEdges O start samples) :
    u ∈ sprmVertices O start samples ∧ v ∈ sprmVertices O start samples ∧
      IsSprmEdge O u v := by
  unfold sprmEdges at h
  rw [mem_withReversals] at h
  rcases h with h | h
  · exact mem_allPairs O (sprmVertices O start samples) u v h
  · obtain ⟨h1, h2, h3⟩ := mem_allPairs O (sprmVertices O start samples) v u h
    exact ⟨h2, h1, IsSprmEdge_symm O v u h3⟩

/-- sPRM edges are symmetric: the swapped pair satisfies the edge predicate. -/
theorem sprmEdges_symmetric {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (u v : C)
    (h : (u, v) ∈ sprmEdges O start samples) : IsSprmEdge O v u :=
  IsSprmEdge_symm O u v (sprmEdges_mem O start samples u v h).2.2

/-- The reversal of an edge lies in the edge list. -/
theorem sprmEdges_swap_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (u v : C)
    (h : (u, v) ∈ sprmEdges O start samples) :
    (v, u) ∈ sprmEdges O start samples := by
  unfold sprmEdges at h ⊢
  exact swap_mem_withReversals _ u v h

/-- PRM* vertices: the initial configuration together with the collision-free
samples, duplicates removed, as in sPRM. The vertex set does not depend on the
radius schedule. -/
def prmStarVertices {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) : List C :=
  sprmVertices O start samples

/-- PRM* and sPRM share the same vertex set. -/
theorem prmStarVertices_eq {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) :
    prmStarVertices O start samples = sprmVertices O start samples :=
  rfl

/-- Membership in the PRM* vertices: the initial configuration or a
collision-free sample. -/
theorem prmStarVertices_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (v : C) :
    v ∈ prmStarVertices O start samples ↔
      v = start ∨ (v ∈ samples ∧ O.free v = true) :=
  sprmVertices_mem O start samples v

/-- Propositional PRM* edge predicate at `n` collision-free samples: like
`IsSprmEdge` with the connection radius `radiusOf n`. -/
abbrev IsPrmStarEdge {C : Type} (O : Oracles C) (radiusOf : Nat → Rat) (n : Nat)
    (u v : C) : Prop :=
  IsSprmEdge { O with radius := radiusOf n } u v

/-- PRM* edges: both directed arcs of each qualifying unordered pair,
connecting when the cost bound at `radiusOf` (collision-free sample count)
holds in both directions and the local planner succeeds in both
directions. -/
def prmStarEdges {C : Type} [DecidableEq C] (O : Oracles C)
    (radiusOf : Nat → Rat) (start : C) (samples : List C) : List (C × C) :=
  withReversals (allPairs
    { O with radius := radiusOf (samples.filter O.free).length }
    (prmStarVertices O start samples))

/-- Edges attach to vertices and satisfy the PRM* edge predicate. -/
theorem prmStarEdges_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (radiusOf : Nat → Rat) (start : C) (samples : List C) (u v : C)
    (h : (u, v) ∈ prmStarEdges O radiusOf start samples) :
    u ∈ prmStarVertices O start samples ∧ v ∈ prmStarVertices O start samples ∧
      IsPrmStarEdge O radiusOf (samples.filter O.free).length u v := by
  unfold prmStarEdges at h
  rw [mem_withReversals] at h
  rcases h with h | h
  · exact mem_allPairs _ _ u v h
  · obtain ⟨h1, h2, h3⟩ := mem_allPairs _ _ v u h
    refine ⟨h2, h1, ?_⟩
    exact IsSprmEdge_symm _ v u h3

/-- The reversal of a PRM* edge lies in the edge list. -/
theorem prmStarEdges_swap_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (radiusOf : Nat → Rat) (start : C) (samples : List C) (u v : C)
    (h : (u, v) ∈ prmStarEdges O radiusOf start samples) :
    (v, u) ∈ prmStarEdges O radiusOf start samples := by
  unfold prmStarEdges at h ⊢
  exact swap_mem_withReversals _ u v h

/-- With radius schedule `fun _ => O.radius`, PRM* reduces to sPRM. -/
theorem prmStarEdges_const_radius {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) :
    prmStarEdges O (fun _ => O.radius) start samples =
      sprmEdges O start samples := rfl

/-- Nearest current vertex to `s` by cost: the first minimizer in list order,
computed by a left fold that keeps the first vertex attaining the minimum.
`dflt` is returned for the empty list. -/
def nearest {C : Type} (O : Oracles C) (verts : List C) (dflt : C) (s : C) : C :=
  match verts with
  | [] => dflt
  | v :: vs =>
      vs.foldl (fun best w => if O.cost w s < O.cost best s then w else best) v

private theorem nearest_foldl_mem {C : Type} (O : Oracles C) (s : C)
    (verts : List C) (l : List C) (best : C)
    (hbest : best ∈ verts) (hl : ∀ w ∈ l, w ∈ verts) :
    l.foldl (fun best w => if O.cost w s < O.cost best s then w else best) best ∈ verts := by
  induction l generalizing best with
  | nil => simpa
  | cons w ws ih =>
      simp only [List.foldl_cons]
      apply ih
      · by_cases h : O.cost w s < O.cost best s
        · simp only [h, ↓reduceIte]
          exact hl w List.mem_cons_self
        · simp only [h, ↓reduceIte]
          exact hbest
      · intro w' hw'
        exact hl w' (List.mem_cons_of_mem w hw')

/-- The nearest vertex is drawn from the vertex list when it is nonempty. -/
theorem nearest_mem {C : Type} (O : Oracles C) {verts : List C}
    (hne : verts ≠ []) (dflt s : C) : nearest O verts dflt s ∈ verts := by
  match _h : verts with
  | [] => exact absurd rfl hne
  | v :: vs =>
      unfold nearest
      apply nearest_foldl_mem
      · exact List.mem_cons_self
      · intro w hw
        exact List.mem_cons_of_mem v hw

/-- RRT growth folded over the samples by structural recursion. For each sample
`s`, samples that are not collision free are skipped (the source algorithms
sample only collision-free configurations); otherwise steer from the nearest
current vertex toward `s` and link to the steered configuration when it is
collision free and the local planner succeeds. Steered configurations already
in the tree are skipped. -/
def rrtAux {C : Type} [DecidableEq C] (O : Oracles C) (start : C) :
    List C → List C → List (C × C) → List C × List (C × C)
  | [], verts, edges => (verts, edges)
  | s :: ss, verts, edges =>
      let u := nearest O verts start s
      let x := O.steer u s
      if O.free s = true ∧ O.free x = true ∧ O.link u x = true ∧ x ∉ verts then
        rrtAux O start ss (x :: verts) ((u, x) :: edges)
      else
        rrtAux O start ss verts edges

theorem rrtAux_nil {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (verts : List C) (edges : List (C × C)) :
    rrtAux O start [] verts edges = (verts, edges) := rfl

theorem rrtAux_cons {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (s : C) (ss : List C) (verts : List C) (edges : List (C × C)) :
    rrtAux O start (s :: ss) verts edges =
      (if O.free s = true ∧ O.free (O.steer (nearest O verts start s) s) = true ∧
          O.link (nearest O verts start s) (O.steer (nearest O verts start s) s) = true ∧
          O.steer (nearest O verts start s) s ∉ verts then
        rrtAux O start ss (O.steer (nearest O verts start s) s :: verts)
          ((nearest O verts start s, O.steer (nearest O verts start s) s) :: edges)
      else
        rrtAux O start ss verts edges) := rfl

/-- Fold invariant: the vertex list keeps `start` and stays duplicate free,
every edge joins two vertices, edge targets stay duplicate free with no
self loops and no edge into `start`, and vertices outnumber edges by one. -/
theorem rrtAux_invar {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (ss : List C) :
    ∀ (verts : List C) (edges : List (C × C)),
      start ∈ verts →
      verts.Nodup →
      (∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts) →
      (edges.map Prod.snd).Nodup →
      (∀ e ∈ edges, e.1 ≠ e.2) →
      (∀ e ∈ edges, e.2 ≠ start) →
      edges.length + 1 = verts.length →
      start ∈ (rrtAux O start ss verts edges).1 ∧
        ((rrtAux O start ss verts edges).1).Nodup ∧
        (∀ e ∈ (rrtAux O start ss verts edges).2,
          e.1 ∈ (rrtAux O start ss verts edges).1 ∧
            e.2 ∈ (rrtAux O start ss verts edges).1) ∧
        (((rrtAux O start ss verts edges).2.map Prod.snd).Nodup) ∧
        (∀ e ∈ (rrtAux O start ss verts edges).2, e.1 ≠ e.2) ∧
        (∀ e ∈ (rrtAux O start ss verts edges).2, e.2 ≠ start) ∧
        (rrtAux O start ss verts edges).2.length + 1 =
          (rrtAux O start ss verts edges).1.length := by
  induction ss with
  | nil =>
      intro verts edges hstart hnd hend htgtnd hnoself hnotgt hlen
      rw [rrtAux_nil]
      exact ⟨hstart, hnd, hend, htgtnd, hnoself, hnotgt, hlen⟩
  | cons s ss ih =>
      intro verts edges hstart hnd hend htgtnd hnoself hnotgt hlen
      rw [rrtAux_cons]
      by_cases hcond :
        O.free s = true ∧ O.free (O.steer (nearest O verts start s) s) = true ∧
          O.link (nearest O verts start s) (O.steer (nearest O verts start s) s) = true ∧
          O.steer (nearest O verts start s) s ∉ verts
      · rw [ite_eq_left hcond]
        obtain ⟨-, -, -, hnotmem⟩ := hcond
        have hne : verts ≠ [] := List.ne_nil_of_mem hstart
        have hu : nearest O verts start s ∈ verts := nearest_mem O hne start s
        have hstart' : start ∈ O.steer (nearest O verts start s) s :: verts :=
          List.mem_cons_of_mem _ hstart
        have hnd' : (O.steer (nearest O verts start s) s :: verts).Nodup :=
          List.nodup_cons.mpr ⟨hnotmem, hnd⟩
        have hend' : ∀ e ∈ (nearest O verts start s,
            O.steer (nearest O verts start s) s) :: edges,
            e.1 ∈ O.steer (nearest O verts start s) s :: verts ∧
              e.2 ∈ O.steer (nearest O verts start s) s :: verts := by
          intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact ⟨List.mem_cons_of_mem _ hu, List.mem_cons_self⟩
          · obtain ⟨h1, h2⟩ := hend e he
            exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
        have hmap : O.steer (nearest O verts start s) s ∉ edges.map Prod.snd := by
          intro hcon
          rw [List.mem_map] at hcon
          obtain ⟨e, he, heq⟩ := hcon
          have hve := (hend e he).2
          rw [heq] at hve
          exact hnotmem hve
        have htgtnd' : (((nearest O verts start s,
            O.steer (nearest O verts start s) s) :: edges).map Prod.snd).Nodup := by
          simp only [List.map_cons]
          exact List.nodup_cons.mpr ⟨hmap, htgtnd⟩
        have hne_ux : nearest O verts start s ≠ O.steer (nearest O verts start s) s := by
          intro hcon
          rw [hcon] at hu
          exact hnotmem hu
        have hnoself' : ∀ e ∈ (nearest O verts start s,
            O.steer (nearest O verts start s) s) :: edges, e.1 ≠ e.2 := by
          intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact hne_ux
          · exact hnoself e he
        have hxs : O.steer (nearest O verts start s) s ≠ start := by
          intro hcon
          apply hnotmem
          rw [hcon]
          exact hstart
        have hnotgt' : ∀ e ∈ (nearest O verts start s,
            O.steer (nearest O verts start s) s) :: edges, e.2 ≠ start := by
          intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact hxs
          · exact hnotgt e he
        have hlen' : ((nearest O verts start s,
            O.steer (nearest O verts start s) s) :: edges).length + 1 =
            (O.steer (nearest O verts start s) s :: verts).length := by
          simp only [List.length_cons]
          omega
        exact ih _ _ hstart' hnd' hend' htgtnd' hnoself' hnotgt' hlen'
      · rw [ite_eq_right hcond]
        exact ih _ _ hstart hnd hend htgtnd hnoself hnotgt hlen

/-- Fold invariant: every output vertex is the start configuration, one of the
input vertices `seen`, or `O.steer u s` for some remaining sample `s ∈ ss`
and some configuration `u`. -/
theorem rrtAux_subset {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (ss : List C) (seen : List C) :
    ∀ (verts : List C) (edges : List (C × C)),
      (∀ v ∈ verts, v = start ∨ v ∈ seen) →
      ∀ v ∈ (rrtAux O start ss verts edges).1,
        v = start ∨ v ∈ seen ∨ ∃ s ∈ ss, ∃ u, v = O.steer u s := by
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
        O.free s = true ∧ O.free (O.steer (nearest O verts start s) s) = true ∧
          O.link (nearest O verts start s) (O.steer (nearest O verts start s) s) = true ∧
          O.steer (nearest O verts start s) s ∉ verts
      · rw [ite_eq_left hcond] at hv
        have hstep : ∀ w ∈ O.steer (nearest O verts start s) s :: verts,
            w = start ∨ w ∈ O.steer (nearest O verts start s) s :: seen := by
          intro w hw
          simp only [List.mem_cons] at hw ⊢
          rcases hw with rfl | hw
          · exact Or.inr (Or.inl rfl)
          · rcases h w hw with rfl | hw'
            · exact Or.inl rfl
            · exact Or.inr (Or.inr hw')
        have hmem := ih (O.steer (nearest O verts start s) s :: seen)
          (O.steer (nearest O verts start s) s :: verts) _ hstep v hv
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | (rfl | h') | ⟨s', hs'mem, u, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨s, List.mem_cons_self,
            nearest O verts start s, rfl⟩)
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr ⟨s', List.mem_cons_of_mem s hs'mem, u, rfl⟩)
      · rw [ite_eq_right hcond] at hv
        have hmem := ih seen verts edges h v hv
        rcases hmem with rfl | h' | ⟨s', hs'mem, u, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr ⟨s', List.mem_cons_of_mem s hs'mem, u, rfl⟩)

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
        O.free s = true ∧ O.free (O.steer (nearest O verts start s) s) = true ∧
          O.link (nearest O verts start s) (O.steer (nearest O verts start s) s) = true ∧
          O.steer (nearest O verts start s) s ∉ verts
      · rw [ite_eq_left hcond]
        have h := ih (O.steer (nearest O verts start s) s :: verts)
          ((nearest O verts start s, O.steer (nearest O verts start s) s) :: edges)
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
        O.free s = true ∧ O.free (O.steer (nearest O verts start s) s) = true ∧
          O.link (nearest O verts start s) (O.steer (nearest O verts start s) s) = true ∧
          O.steer (nearest O verts start s) s ∉ verts
      · rw [ite_eq_left hcond] at hv ⊢
        have hstep : ∀ w ∈ O.steer (nearest O verts start s) s :: verts,
            w = start ∨
              w ∈ ((nearest O verts start s,
                O.steer (nearest O verts start s) s) :: edges).map Prod.snd := by
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

/-- Every RRT vertex is the start configuration or is steered from some
configuration toward some sample. -/
theorem rrt_verts_subset {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) (v : C) (hv : v ∈ (rrt O start samples).1) :
    v = start ∨ ∃ s ∈ samples, ∃ u, v = O.steer u s := by
  have h0 : ∀ w ∈ ([start] : List C), w = start ∨ w ∈ ([] : List C) := by
    intro w hw
    simp at hw
    exact Or.inl hw
  have hv' : v ∈ (rrtAux O start samples [start] []).1 := hv
  have h1 := rrtAux_subset O start samples [] [start] [] h0 v hv'
  simpa using h1

/-- RRT invariant at the top level: the vertex list contains `start` and is
duplicate free, every edge joins two vertices, edge targets are duplicate
free with no self loops and no edge into `start`, and vertices outnumber
edges by one. Reachability is `rrt_reachable` and acyclicity is `rrt_acyclic`. -/
theorem rrt_invar {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) :
    start ∈ (rrt O start samples).1 ∧
      ((rrt O start samples).1).Nodup ∧
      (∀ e ∈ (rrt O start samples).2,
        e.1 ∈ (rrt O start samples).1 ∧ e.2 ∈ (rrt O start samples).1) ∧
      (((rrt O start samples).2.map Prod.snd).Nodup) ∧
      (∀ e ∈ (rrt O start samples).2, e.1 ≠ e.2) ∧
      (∀ e ∈ (rrt O start samples).2, e.2 ≠ start) ∧
      (rrt O start samples).2.length + 1 = (rrt O start samples).1.length := by
  have hstart0 : start ∈ ([start] : List C) := List.mem_cons_self
  have hnd0 : ([start] : List C).Nodup := by simp
  have hend0 : ∀ e ∈ ([] : List (C × C)), e.1 ∈ [start] ∧ e.2 ∈ [start] := by
    intro e he
    simp at he
  have htgt0 : (([] : List (C × C)).map Prod.snd).Nodup := by
    simp only [List.map_nil]
    exact List.nodup_nil
  have hself0 : ∀ e ∈ ([] : List (C × C)), e.1 ≠ e.2 := by
    intro e he
    simp at he
  have hnotgt0 : ∀ e ∈ ([] : List (C × C)), e.2 ≠ start := by
    intro e he
    simp at he
  have hlen0 : ([] : List (C × C)).length + 1 = ([start] : List C).length := rfl
  have h := rrtAux_invar O start samples [start] [] hstart0 hnd0 hend0 htgt0
    hself0 hnotgt0 hlen0
  exact h

/-- The start configuration is an RRT vertex. -/
theorem rrt_start_mem {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) : start ∈ (rrt O start samples).1 :=
  (rrt_invar O start samples).1

/-- RRT vertices are duplicate free. -/
theorem rrt_verts_nodup {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) : ((rrt O start samples).1).Nodup :=
  (rrt_invar O start samples).2.1

/-- Every RRT edge joins two RRT vertices. -/
theorem rrt_edge_endpoints {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (e : C × C)
    (he : e ∈ (rrt O start samples).2) :
    e.1 ∈ (rrt O start samples).1 ∧ e.2 ∈ (rrt O start samples).1 := by
  obtain ⟨_, _, hend, _, _, _, _⟩ := rrt_invar O start samples
  exact hend e he

/-- Every RRT edge source is an RRT vertex. -/
theorem rrt_edge_fst_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (e : C × C)
    (he : e ∈ (rrt O start samples).2) : e.1 ∈ (rrt O start samples).1 :=
  (rrt_edge_endpoints O start samples e he).1

/-- Target uniqueness: edge targets are duplicate free, so every vertex has at
most one incoming edge (existence for vertices other than the start is `rrt_edge_of_mem`). -/
theorem rrt_targets_nodup {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) :
    ((rrt O start samples).2.map Prod.snd).Nodup := by
  obtain ⟨_, _, _, htgt, _, _, _⟩ := rrt_invar O start samples
  exact htgt

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
  (rrt_edge_endpoints O start samples e he).2

/-- No RRT edge is a self loop. -/
theorem rrt_edge_fst_ne_snd {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (e : C × C)
    (he : e ∈ (rrt O start samples).2) : e.1 ≠ e.2 := by
  obtain ⟨_, _, _, _, hnoself, _, _⟩ := rrt_invar O start samples
  exact hnoself e he

/-- No RRT edge targets the start configuration. -/
theorem rrt_edge_snd_ne_start {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (e : C × C)
    (he : e ∈ (rrt O start samples).2) : e.2 ≠ start := by
  obtain ⟨_, _, _, _, _, hnotgt, _⟩ := rrt_invar O start samples
  exact hnotgt e he

/-- RRT vertices outnumber edges by one. -/
theorem rrt_edges_length_eq {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) :
    (rrt O start samples).2.length + 1 = (rrt O start samples).1.length := by
  obtain ⟨_, _, _, _, _, _, hlen⟩ := rrt_invar O start samples
  exact hlen

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
scratch by a single breadth-first traversal after each extension and its rewiring pass (each
vertex is costed once from its parent), so stored costs are never stale.
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

/-- Add two unnormalized cost pairs by cross multiplication. -/
def ccAddPair (p q : Int × Nat) : Int × Nat :=
  (p.1 * (q.2 : Int) + q.1 * (p.2 : Int), p.2 * q.2)

/-- Unnormalized pair for the rational difference `pairVal p - pairVal q`. -/
def pairDelta (p q : Int × Nat) : Int × Nat :=
  (p.1 * (q.2 : Int) - q.1 * (p.2 : Int), p.2 * q.2)

theorem pairVal_ccAddPair (p q : Int × Nat) (hp : (p.2 : ℚ) ≠ 0)
    (hq : (q.2 : ℚ) ≠ 0) :
    pairVal (ccAddPair p q) = pairVal p + pairVal q := by
  have hpd : (p.2 : ℚ) * (q.2 : ℚ) ≠ 0 := mul_ne_zero hp hq
  unfold pairVal ccAddPair
  push_cast
  field_simp [hp, hq, hpd]

theorem pairVal_pairDelta (p q : Int × Nat) (hp : (p.2 : ℚ) ≠ 0)
    (hq : (q.2 : ℚ) ≠ 0) :
    pairVal (pairDelta p q) = pairVal p - pairVal q := by
  have hpd : (p.2 : ℚ) * (q.2 : ℚ) ≠ 0 := mul_ne_zero hp hq
  unfold pairVal pairDelta
  push_cast
  field_simp [hp, hq, hpd]

theorem ccAddPair_den_pos (p q : Int × Nat) (hp : 0 < p.2) (hq : 0 < q.2) :
    0 < (ccAddPair p q).2 := by
  unfold ccAddPair
  simp only
  exact Nat.mul_pos hp hq

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


/-- Breadth-first cost table auxiliary: traverse from a queue of
`(vertex, cost pair)` entries, accumulating each vertex once. Children are
generated by scanning `edges` once per added vertex. -/
def treeCostsAux {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) :
    Nat → List (C × (Int × Nat)) → List (C × (Int × Nat)) →
      List (C × (Int × Nat))
  | 0, _, acc => acc
  | _, [], acc => acc
  | fuel + 1, (u, cu) :: queue, acc =>
      if _ : u ∈ acc.map Prod.fst then
        treeCostsAux O edges fuel queue acc
      else
        let acc' := (u, cu) :: acc
        let children := edges.filterMap (fun e =>
          if e.1 = u then
            if e.2 ∈ acc'.map Prod.fst then none
            else some (e.2, ccAdd cu (O.cost u e.2))
          else none)
        treeCostsAux O edges fuel (queue ++ children) acc'

/-- Breadth-first cost table: start at `(0, 1)`, traverse once from `start`.
The vertex-list argument is kept for signature stability and is not read:
the table holds exactly the vertices reachable from `start` along `edges`,
each with the cost of the path that first discovered it. On a tree edge
list (unique targets, no edge into `start`) that path is the unique tree
path; on a general graph the stored cost need not be the cheapest. -/
def recomputeCosts {C : Type} [DecidableEq C] (O : Oracles C) (_verts : List C)
    (edges : List (C × C)) (start : C) : List (C × (Int × Nat)) :=
  treeCostsAux O edges (edges.length + 1) [(start, (0, 1))] []


theorem treeCostsAux_zero {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (queue : List (C × (Int × Nat)))
    (acc : List (C × (Int × Nat))) :
    treeCostsAux O edges 0 queue acc = acc := rfl

theorem treeCostsAux_nil {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (fuel : Nat)
    (acc : List (C × (Int × Nat))) :
    treeCostsAux O edges (fuel + 1) [] acc = acc := rfl

theorem treeCostsAux_cons_dup {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (fuel : Nat) (u : C) (cu : Int × Nat)
    (queue : List (C × (Int × Nat))) (acc : List (C × (Int × Nat)))
    (h : u ∈ acc.map Prod.fst) :
    treeCostsAux O edges (fuel + 1) ((u, cu) :: queue) acc =
      treeCostsAux O edges fuel queue acc := by
  simp [treeCostsAux, h]

theorem treeCostsAux_cons_new {C : Type} [DecidableEq C] (O : Oracles C)
    (edges : List (C × C)) (fuel : Nat) (u : C) (cu : Int × Nat)
    (queue : List (C × (Int × Nat))) (acc : List (C × (Int × Nat)))
    (h : u ∉ acc.map Prod.fst) :
    treeCostsAux O edges (fuel + 1) ((u, cu) :: queue) acc =
      treeCostsAux O edges fuel (queue ++ edges.filterMap (fun e =>
        if e.1 = u then
          if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
          else some (e.2, ccAdd cu (O.cost u e.2))
        else none)) ((u, cu) :: acc) := by
  simp [treeCostsAux, h]

-- Helpers

private theorem treeCostsAux_acc_mem {C : Type} [DecidableEq C]
    (O : Oracles C) (edges : List (C × C)) (fuel : Nat)
    (queue : List (C × (Int × Nat))) (acc : List (C × (Int × Nat)))
    (kv : C × (Int × Nat)) (hmem : kv ∈ acc) :
    kv ∈ treeCostsAux O edges fuel queue acc := by
  induction fuel generalizing queue acc with
  | zero =>
      rw [treeCostsAux_zero]
      exact hmem
  | succ fuel ih =>
      cases queue with
      | nil =>
          rw [treeCostsAux_nil]
          exact hmem
      | cons head tail =>
          obtain ⟨u, cu⟩ := head
          by_cases h : u ∈ acc.map Prod.fst
          · rw [treeCostsAux_cons_dup O edges fuel u cu tail acc h]
            exact ih tail acc hmem
          · rw [treeCostsAux_cons_new O edges fuel u cu tail acc h]
            apply ih
            exact List.mem_cons_of_mem (u, cu) hmem

private theorem treeCostsAux_keys_subset {C : Type} [DecidableEq C]
    (O : Oracles C) (edges : List (C × C)) (fuel : Nat)
    (queue : List (C × (Int × Nat))) (acc : List (C × (Int × Nat)))
    (v : C) (hmem : v ∈ acc.map Prod.fst) :
    v ∈ (treeCostsAux O edges fuel queue acc).map Prod.fst := by
  obtain ⟨c, hmemc, _⟩ := costToCome_mem_entry acc v hmem
  have hmem' := treeCostsAux_acc_mem O edges fuel queue acc (v, c) hmemc
  exact List.mem_map_of_mem hmem'

private theorem rat_den_pos_aux {C : Type} [DecidableEq C]
    (O : Oracles C) (a b : C) : 0 < (O.cost a b).den := by
  have h := rat_den_ne_zero (O.cost a b)
  omega

private theorem treeCostsAux_denoms {C : Type} [DecidableEq C]
    (O : Oracles C) (edges : List (C × C)) (fuel : Nat)
    (queue : List (C × (Int × Nat))) (acc : List (C × (Int × Nat)))
    (hq : DenomsPos queue) (ha : DenomsPos acc) :
    DenomsPos (treeCostsAux O edges fuel queue acc) := by
  induction fuel generalizing queue acc with
  | zero =>
      rw [treeCostsAux_zero]
      exact ha
  | succ fuel ih =>
      cases queue with
      | nil =>
          rw [treeCostsAux_nil]
          exact ha
      | cons head tail =>
          obtain ⟨u, cu⟩ := head
          have hcu : 0 < cu.2 := by
            apply hq (u, cu) List.mem_cons_self
          have htail : DenomsPos tail := by
            intro kv hmem
            exact hq kv (List.mem_cons_of_mem (u, cu) hmem)
          by_cases h : u ∈ acc.map Prod.fst
          · rw [treeCostsAux_cons_dup O edges fuel u cu tail acc h]
            exact ih tail acc htail ha
          · rw [treeCostsAux_cons_new O edges fuel u cu tail acc h]
            have ha' : DenomsPos ((u, cu) :: acc) :=
              denomsPos_cons acc (u, cu) hcu ha
            have hchild : DenomsPos (edges.filterMap (fun e =>
                if e.1 = u then
                  if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                  else some (e.2, ccAdd cu (O.cost u e.2))
                else none)) := by
              intro kv hmem
              rw [List.mem_filterMap] at hmem
              obtain ⟨e, _, heq⟩ := hmem
              by_cases he1 : e.1 = u
              · simp only [he1, ite_true] at heq
                by_cases he2 : e.2 ∈ ((u, cu) :: acc).map Prod.fst
                · simp only [he2, ite_true] at heq
                  simp at heq
                · simp only [he2, ite_false] at heq
                  simp at heq
                  subst heq
                  exact ccAdd_den_pos cu (O.cost u e.2) hcu
                    (rat_den_pos_aux O u e.2)
              · simp only [he1, ite_false] at heq
                simp at heq
            have hq' : DenomsPos (tail ++ edges.filterMap (fun e =>
                if e.1 = u then
                  if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                  else some (e.2, ccAdd cu (O.cost u e.2))
                else none)) := by
              intro kv hmem
              rw [List.mem_append] at hmem
              cases hmem with
              | inl h => exact htail kv h
              | inr h => exact hchild kv h
            exact ih _ _ hq' ha'

private theorem treeCostsAux_cost_mem {C : Type} [DecidableEq C]
    (O : Oracles C) (edges : List (C × C)) (fuel : Nat)
    (queue : List (C × (Int × Nat))) (acc : List (C × (Int × Nat)))
    (w : C) (hmem : w ∈ acc.map Prod.fst) :
    costToCome (treeCostsAux O edges fuel queue acc) w =
      costToCome acc w := by
  induction fuel generalizing queue acc with
  | zero =>
      rw [treeCostsAux_zero]
  | succ fuel ih =>
      cases queue with
      | nil =>
          rw [treeCostsAux_nil]
      | cons head tail =>
          obtain ⟨u, cu⟩ := head
          by_cases h : u ∈ acc.map Prod.fst
          · rw [treeCostsAux_cons_dup O edges fuel u cu tail acc h]
            exact ih tail acc hmem
          · rw [treeCostsAux_cons_new O edges fuel u cu tail acc h]
            have hne : u ≠ w := by
              intro heq
              subst heq
              exact h hmem
            have hmem' : w ∈ ((u, cu) :: acc).map Prod.fst := by
              simp only [List.map_cons, List.mem_cons]
              exact Or.inr hmem
            have hstep : costToCome ((u, cu) :: acc) w = costToCome acc w :=
              costToCome_cons_ne acc u w cu hne
            rw [ih _ _ hmem']
            exact hstep

/-- Recomputed tables have positive denominators. -/
theorem recomputeCosts_denoms {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C) :
    DenomsPos (recomputeCosts O verts edges start) := by
  unfold recomputeCosts
  apply treeCostsAux_denoms
  · exact denomsPos_init start
  · intro kv hmem
    simp at hmem

/-- The start vertex is always costed. -/
theorem recomputeCosts_start_mem {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C) :
    start ∈ (recomputeCosts O verts edges start).map Prod.fst := by
  unfold recomputeCosts
  have hnil : start ∉ ([] : List (C × (Int × Nat))).map Prod.fst := by simp
  rw [treeCostsAux_cons_new O edges edges.length start (0, 1) [] [] hnil]
  apply treeCostsAux_keys_subset
  simp

/-- Recomputing over no edges leaves the initial table alone. -/
theorem recomputeCosts_nil_edges {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (start : C) :
    recomputeCosts O verts [] start = [(start, (0, 1))] := by
  unfold recomputeCosts
  simp only [List.length_nil, Nat.zero_add]
  have hnil : start ∉ ([] : List (C × (Int × Nat))).map Prod.fst := by simp
  rw [treeCostsAux_cons_new O [] 0 start (0, 1) [] [] hnil]
  rw [treeCostsAux_zero]

/-- Fresh tables read `(0, 1)` at the start vertex. -/
theorem recomputeCosts_cost_start {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (hstart : ∀ e ∈ edges, e.2 ≠ start) :
    costToCome (recomputeCosts O verts edges start) start = (0, 1) := by
  have _ := hstart
  unfold recomputeCosts
  have hnil : start ∉ ([] : List (C × (Int × Nat))).map Prod.fst := by simp
  rw [treeCostsAux_cons_new O edges edges.length start (0, 1) [] [] hnil]
  have hmem : start ∈ ((start, (0, 1)) :: ([] : List (C × (Int × Nat)))).map Prod.fst := by
    simp
  have hbase : costToCome ((start, (0, 1)) :: ([] : List (C × (Int × Nat)))) start = (0, 1) :=
    costToCome_cons_eq [] start (0, 1)
  have hpres := treeCostsAux_cost_mem O edges edges.length
    ([] ++ edges.filterMap (fun e =>
      if e.1 = start then
        if e.2 ∈ ((start, (0, 1)) :: ([] : List (C × (Int × Nat)))).map Prod.fst then none
        else some (e.2, ccAdd (0, 1) (O.cost start e.2))
      else none)) ((start, (0, 1)) :: []) start hmem
  rw [hpres]
  exact hbase

private theorem treeCostsAux_tight {C : Type} [DecidableEq C]
    (O : Oracles C) (edges : List (C × C)) (start : C) (fuel : Nat)
    (queue : List (C × (Int × Nat))) (acc : List (C × (Int × Nat)))
    (hnodup : (acc.map Prod.fst).Nodup)
    (hacc : ∀ kv ∈ acc, (kv.1 = start ∧ kv.2 = (0, 1)) ∨
      ∃ u, (u, kv.1) ∈ edges ∧ u ∈ acc.map Prod.fst ∧ u ≠ kv.1 ∧
        kv.2 = ccAdd (costToCome acc u) (O.cost u kv.1))
    (hqueue : ∀ kv ∈ queue, (kv.1 = start ∧ kv.2 = (0, 1)) ∨
      ∃ u, (u, kv.1) ∈ edges ∧ u ∈ acc.map Prod.fst ∧ u ≠ kv.1 ∧
        kv.2 = ccAdd (costToCome acc u) (O.cost u kv.1)) :
    ∀ kv ∈ treeCostsAux O edges fuel queue acc, (kv.1 = start ∧ kv.2 = (0, 1)) ∨
      ∃ u, (u, kv.1) ∈ edges ∧
        u ∈ (treeCostsAux O edges fuel queue acc).map Prod.fst ∧
        u ≠ kv.1 ∧
        kv.2 = ccAdd (costToCome (treeCostsAux O edges fuel queue acc) u)
          (O.cost u kv.1) := by
  induction fuel generalizing queue acc with
  | zero =>
      rw [treeCostsAux_zero]
      exact hacc
  | succ fuel ih =>
      cases queue with
      | nil =>
          rw [treeCostsAux_nil]
          exact hacc
      | cons head tail =>
          obtain ⟨u, cu⟩ := head
          by_cases h : u ∈ acc.map Prod.fst
          · rw [treeCostsAux_cons_dup O edges fuel u cu tail acc h]
            apply ih
            · exact hnodup
            · exact hacc
            · intro kv hmem
              exact hqueue kv (List.mem_cons_of_mem (u, cu) hmem)
          · rw [treeCostsAux_cons_new O edges fuel u cu tail acc h]
            have hnodup' : (((u, cu) :: acc).map Prod.fst).Nodup := by
              simp only [List.map_cons]
              exact List.nodup_cons.mpr ⟨h, hnodup⟩
            have hacc' : ∀ kv ∈ (u, cu) :: acc, (kv.1 = start ∧ kv.2 = (0, 1)) ∨
                ∃ p, (p, kv.1) ∈ edges ∧ p ∈ ((u, cu) :: acc).map Prod.fst ∧
                  p ≠ kv.1 ∧
                  kv.2 = ccAdd (costToCome ((u, cu) :: acc) p) (O.cost p kv.1) := by
              intro kv hmem
              simp only [List.mem_cons] at hmem
              cases hmem with
              | inl heq =>
                  subst heq
                  have hhead := hqueue (u, cu) List.mem_cons_self
                  cases hhead with
                  | inl hstart => exact Or.inl hstart
                  | inr hwit =>
                      obtain ⟨p, hp_edge, hp_mem, hp_ne, hp_eq⟩ := hwit
                      have hp_mem' : p ∈ ((u, cu) :: acc).map Prod.fst := by
                        simp only [List.map_cons, List.mem_cons]
                        exact Or.inr hp_mem
                      have hne : u ≠ p := by
                        intro heq
                        apply h
                        rw [heq]
                        exact hp_mem
                      have hcost : costToCome ((u, cu) :: acc) p =
                          costToCome acc p :=
                        costToCome_cons_ne acc u p cu hne
                      exact Or.inr ⟨p, hp_edge, hp_mem', hp_ne, by
                        rw [hcost]
                        exact hp_eq⟩
              | inr hmem_acc =>
                  have hold := hacc kv hmem_acc
                  cases hold with
                  | inl hstart => exact Or.inl hstart
                  | inr hwit =>
                      obtain ⟨p, hp_edge, hp_mem, hp_ne, hp_eq⟩ := hwit
                      have hp_mem' : p ∈ ((u, cu) :: acc).map Prod.fst := by
                        simp only [List.map_cons, List.mem_cons]
                        exact Or.inr hp_mem
                      have hne : u ≠ p := by
                        intro heq
                        apply h
                        rw [heq]
                        exact hp_mem
                      have hcost : costToCome ((u, cu) :: acc) p =
                          costToCome acc p :=
                        costToCome_cons_ne acc u p cu hne
                      exact Or.inr ⟨p, hp_edge, hp_mem', hp_ne, by
                        rw [hcost]
                        exact hp_eq⟩
            have hqueue' : ∀ kv ∈ tail ++ edges.filterMap (fun e =>
                if e.1 = u then
                  if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                  else some (e.2, ccAdd cu (O.cost u e.2))
                else none),
                (kv.1 = start ∧ kv.2 = (0, 1)) ∨
                ∃ p, (p, kv.1) ∈ edges ∧ p ∈ ((u, cu) :: acc).map Prod.fst ∧
                  p ≠ kv.1 ∧
                  kv.2 = ccAdd (costToCome ((u, cu) :: acc) p) (O.cost p kv.1) := by
              intro kv hmem
              rw [List.mem_append] at hmem
              cases hmem with
              | inl htail =>
                  have hold := hqueue kv (List.mem_cons_of_mem (u, cu) htail)
                  cases hold with
                  | inl hstart => exact Or.inl hstart
                  | inr hwit =>
                      obtain ⟨p, hp_edge, hp_mem, hp_ne, hp_eq⟩ := hwit
                      have hp_mem' : p ∈ ((u, cu) :: acc).map Prod.fst := by
                        simp only [List.map_cons, List.mem_cons]
                        exact Or.inr hp_mem
                      have hne : u ≠ p := by
                        intro heq
                        apply h
                        rw [heq]
                        exact hp_mem
                      have hcost : costToCome ((u, cu) :: acc) p =
                          costToCome acc p :=
                        costToCome_cons_ne acc u p cu hne
                      exact Or.inr ⟨p, hp_edge, hp_mem', hp_ne, by
                        rw [hcost]
                        exact hp_eq⟩
              | inr hchild =>
                  rw [List.mem_filterMap] at hchild
                  obtain ⟨e, he_mem, he_eq⟩ := hchild
                  by_cases he1 : e.1 = u
                  · simp only [he1, ite_true] at he_eq
                    by_cases he2 : e.2 ∈ ((u, cu) :: acc).map Prod.fst
                    · simp only [he2, ite_true] at he_eq
                      simp at he_eq
                    · simp only [he2, ite_false] at he_eq
                      simp at he_eq
                      subst he_eq
                      have hu_mem : u ∈ ((u, cu) :: acc).map Prod.fst := by simp
                      have hne_uv : u ≠ e.2 := by
                        intro heq
                        apply he2
                        rw [← heq]
                        exact hu_mem
                      have heq_edge : (u, e.2) = e := by
                        cases e with
                        | mk a b =>
                            simp only at he1 ⊢
                            rw [he1]
                      have hmem_edge : (u, e.2) ∈ edges := by
                        rw [heq_edge]
                        exact he_mem
                      have hcu : costToCome ((u, cu) :: acc) u = cu :=
                        costToCome_cons_eq acc u cu
                      exact Or.inr ⟨u, hmem_edge, hu_mem, hne_uv, by rw [hcu]⟩
                  · simp only [he1, ite_false] at he_eq
                    simp at he_eq
            exact ih _ _ hnodup' hacc' hqueue'

private def unseenEdges {C : Type} [DecidableEq C] :
    List (C × C) → List C → Nat
  | [], _ => 0
  | e :: es, seen => if e.1 ∈ seen then unseenEdges es seen else 1 + unseenEdges es seen

private theorem unseenEdges_nil {C : Type} [DecidableEq C]
    (seen : List C) : unseenEdges ([] : List (C × C)) seen = 0 := rfl

private theorem unseenEdges_cons {C : Type} [DecidableEq C]
    (e : C × C) (es : List (C × C)) (seen : List C) :
    unseenEdges (e :: es) seen =
      (if e.1 ∈ seen then unseenEdges es seen else 1 + unseenEdges es seen) := rfl

private theorem unseenEdges_empty_seen {C : Type} [DecidableEq C]
    (edges : List (C × C)) : unseenEdges edges [] = edges.length := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
      rw [unseenEdges_cons]
      have hnil : e.1 ∉ ([] : List C) := by simp
      rw [ite_eq_right hnil, ih, List.length_cons]
      omega

private theorem children_unseen_le {C : Type} [DecidableEq C]
    (O : Oracles C) (edges : List (C × C)) (u : C) (cu : Int × Nat)
    (acc : List (C × (Int × Nat))) (h : u ∉ acc.map Prod.fst) :
    (edges.filterMap (fun e =>
      if e.1 = u then
        if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
        else some (e.2, ccAdd cu (O.cost u e.2))
      else none)).length +
    unseenEdges edges (((u, cu) :: acc).map Prod.fst) ≤
    unseenEdges edges (acc.map Prod.fst) := by
  induction edges with
  | nil =>
      simp only [List.filterMap_nil, List.length_nil, unseenEdges_nil, Nat.zero_add,
        Nat.le_refl]
  | cons e es ih =>
      rw [List.filterMap_cons, unseenEdges_cons, unseenEdges_cons]
      by_cases he1 : e.1 = u
      · have hmem_acc : e.1 ∉ acc.map Prod.fst := by
          rw [he1]
          exact h
        have hmem_acc' : e.1 ∈ ((u, cu) :: acc).map Prod.fst := by
          simp [he1]
        rw [ite_eq_left hmem_acc', ite_eq_right hmem_acc]
        by_cases he2 : e.2 ∈ ((u, cu) :: acc).map Prod.fst
        · have hf : (fun e =>
              if e.1 = u then
                if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                else some (e.2, ccAdd cu (O.cost u e.2))
              else none) e = none := by
            show (if e.1 = u then
              (if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                else some (e.2, ccAdd cu (O.cost u e.2))) else none) = none
            rw [ite_eq_left he1, ite_eq_left he2]
          simp only [hf] at ⊢
          omega
        · have hf : (fun e =>
              if e.1 = u then
                if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                else some (e.2, ccAdd cu (O.cost u e.2))
              else none) e = some (e.2, ccAdd cu (O.cost u e.2)) := by
            show (if e.1 = u then
              (if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                else some (e.2, ccAdd cu (O.cost u e.2))) else none) =
              some (e.2, ccAdd cu (O.cost u e.2))
            rw [ite_eq_left he1, ite_eq_right he2]
          simp only [hf, List.length_cons] at ⊢
          omega
      · have hf : (fun e =>
            if e.1 = u then
              if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
              else some (e.2, ccAdd cu (O.cost u e.2))
            else none) e = none := by
          show (if e.1 = u then
            (if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
              else some (e.2, ccAdd cu (O.cost u e.2))) else none) = none
          rw [ite_eq_right he1]
        simp only [hf] at ⊢
        by_cases hmem : e.1 ∈ acc.map Prod.fst
        · have hmem' : e.1 ∈ ((u, cu) :: acc).map Prod.fst := by
            simp only [List.map_cons, List.mem_cons]
            exact Or.inr hmem
          rw [ite_eq_left hmem, ite_eq_left hmem']
          exact ih
        · have hmem_n : e.1 ∉ acc.map Prod.fst := hmem
          have hmem_n' : e.1 ∉ ((u, cu) :: acc).map Prod.fst := by
            simp only [List.map_cons, List.mem_cons, not_or]
            exact ⟨he1, hmem_n⟩
          rw [ite_eq_right hmem_n, ite_eq_right hmem_n']
          omega

private theorem treeCostsAux_closed {C : Type} [DecidableEq C]
    (O : Oracles C) (edges : List (C × C)) (fuel : Nat)
    (queue : List (C × (Int × Nat))) (acc : List (C × (Int × Nat)))
    (hclosed_from : ∀ w ∈ acc.map Prod.fst, ∀ e ∈ edges, e.1 = w →
      e.2 ∈ acc.map Prod.fst ∨ e.2 ∈ queue.map Prod.fst)
    (hfuel : queue.length + unseenEdges edges (acc.map Prod.fst) ≤ fuel) :
    ∀ w ∈ (treeCostsAux O edges fuel queue acc).map Prod.fst,
      ∀ e ∈ edges, e.1 = w →
        e.2 ∈ (treeCostsAux O edges fuel queue acc).map Prod.fst := by
  induction fuel generalizing queue acc with
  | zero =>
      rw [treeCostsAux_zero]
      intro w hmem e he hsrc
      have hdisj := hclosed_from w hmem e he hsrc
      cases hdisj with
      | inl h => exact h
      | inr h =>
          have hlen : queue.length = 0 := by omega
          cases queue with
          | nil =>
              simp at h
          | cons head tail =>
              simp only [List.length_cons] at hlen
              have : False := by omega
              exact False.elim this
  | succ fuel ih =>
      cases queue with
      | nil =>
          rw [treeCostsAux_nil]
          intro w hmem e he hsrc
          have hdisj := hclosed_from w hmem e he hsrc
          cases hdisj with
          | inl h => exact h
          | inr h =>
              simp at h
      | cons head tail =>
          obtain ⟨u, cu⟩ := head
          by_cases h : u ∈ acc.map Prod.fst
          · rw [treeCostsAux_cons_dup O edges fuel u cu tail acc h]
            apply ih
            · intro w hmem e he hsrc
              have hdisj := hclosed_from w hmem e he hsrc
              cases hdisj with
              | inl hacc => exact Or.inl hacc
              | inr hqueue =>
                  simp only [List.map_cons, List.mem_cons] at hqueue
                  cases hqueue with
                  | inl heq =>
                      subst heq
                      exact Or.inl h
                  | inr htail =>
                      exact Or.inr htail
            · simp only [List.length_cons] at hfuel ⊢
              omega
          · rw [treeCostsAux_cons_new O edges fuel u cu tail acc h]
            have hfuel' : (tail ++ edges.filterMap (fun e =>
                if e.1 = u then
                  if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                  else some (e.2, ccAdd cu (O.cost u e.2))
                else none)).length +
                unseenEdges edges (((u, cu) :: acc).map Prod.fst) ≤ fuel := by
              rw [List.length_append]
              simp only [List.length_cons] at hfuel
              have hle := children_unseen_le O edges u cu acc h
              omega
            have hclosed_from' : ∀ w ∈ (((u, cu) :: acc).map Prod.fst),
                ∀ e ∈ edges, e.1 = w →
                  e.2 ∈ (((u, cu) :: acc).map Prod.fst) ∨
                  e.2 ∈ (tail ++ edges.filterMap (fun e =>
                    if e.1 = u then
                      if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                      else some (e.2, ccAdd cu (O.cost u e.2))
                    else none)).map Prod.fst := by
              intro w hmem e he hsrc
              simp only [List.map_cons, List.mem_cons] at hmem
              cases hmem with
              | inl heq =>
                  rw [heq] at hsrc
                  by_cases he2 : e.2 ∈ ((u, cu) :: acc).map Prod.fst
                  · exact Or.inl he2
                  · have he1 : e.1 = u := hsrc
                    have hf : (fun e =>
                        if e.1 = u then
                          if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                          else some (e.2, ccAdd cu (O.cost u e.2))
                        else none) e =
                        some (e.2, ccAdd cu (O.cost u e.2)) := by
                      show (if e.1 = u then
                        (if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                          else some (e.2, ccAdd cu (O.cost u e.2))) else none) =
                        some (e.2, ccAdd cu (O.cost u e.2))
                      rw [ite_eq_left he1, ite_eq_right he2]
                    have hchild : (e.2, ccAdd cu (O.cost u e.2)) ∈
                        edges.filterMap (fun e =>
                          if e.1 = u then
                            if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                            else some (e.2, ccAdd cu (O.cost u e.2))
                          else none) :=
                      List.mem_filterMap.mpr ⟨e, he, hf⟩
                    have hmem_child : e.2 ∈ (edges.filterMap (fun e =>
                        if e.1 = u then
                          if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                          else some (e.2, ccAdd cu (O.cost u e.2))
                        else none)).map Prod.fst :=
                      List.mem_map_of_mem hchild
                    have hmap : (tail ++ edges.filterMap (fun e =>
                        if e.1 = u then
                          if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                          else some (e.2, ccAdd cu (O.cost u e.2))
                        else none)).map Prod.fst =
                        tail.map Prod.fst ++ (edges.filterMap (fun e =>
                          if e.1 = u then
                            if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                            else some (e.2, ccAdd cu (O.cost u e.2))
                          else none)).map Prod.fst :=
                      List.map_append
                    rw [hmap, List.mem_append]
                    exact Or.inr (Or.inr hmem_child)
              | inr hmem_acc =>
                  have hdisj := hclosed_from w hmem_acc e he hsrc
                  cases hdisj with
                  | inl hacc =>
                      have hmem_acc' : e.2 ∈ ((u, cu) :: acc).map Prod.fst := by
                        simp only [List.map_cons, List.mem_cons]
                        exact Or.inr hacc
                      exact Or.inl hmem_acc'
                  | inr hqueue =>
                      simp only [List.map_cons, List.mem_cons] at hqueue
                      cases hqueue with
                      | inl heq =>
                          have hu_mem : u ∈ ((u, cu) :: acc).map Prod.fst := by simp
                          have hmem_e2 : e.2 ∈ ((u, cu) :: acc).map Prod.fst := by
                            rw [heq]
                            exact hu_mem
                          exact Or.inl hmem_e2
                      | inr htail =>
                          have hmap : (tail ++ edges.filterMap (fun e =>
                              if e.1 = u then
                                if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                                else some (e.2, ccAdd cu (O.cost u e.2))
                              else none)).map Prod.fst =
                              tail.map Prod.fst ++ (edges.filterMap (fun e =>
                                if e.1 = u then
                                  if e.2 ∈ ((u, cu) :: acc).map Prod.fst then none
                                  else some (e.2, ccAdd cu (O.cost u e.2))
                                else none)).map Prod.fst :=
                            List.map_append
                          rw [hmap, List.mem_append]
                          exact Or.inr (Or.inl htail)
            exact ih _ _ hclosed_from' hfuel'

theorem recomputeCosts_closed {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (u : C) (hmem : u ∈ (recomputeCosts O verts edges start).map Prod.fst)
    (e : C × C) (he : e ∈ edges) (hsrc : e.1 = u) :
    e.2 ∈ (recomputeCosts O verts edges start).map Prod.fst := by
  unfold recomputeCosts at hmem ⊢
  have hclosed_from : ∀ w ∈ ([] : List (C × (Int × Nat))).map Prod.fst,
      ∀ e ∈ edges, e.1 = w →
        e.2 ∈ ([] : List (C × (Int × Nat))).map Prod.fst ∨
        e.2 ∈ ([(start, (0, 1))] : List (C × (Int × Nat))).map Prod.fst := by
    intro w hmem
    simp at hmem
  have hfuel : ([(start, (0, 1))] : List (C × (Int × Nat))).length +
      unseenEdges edges (([] : List (C × (Int × Nat))).map Prod.fst) ≤
      edges.length + 1 := by
    simp [unseenEdges_empty_seen]
    omega
  exact treeCostsAux_closed O edges (edges.length + 1) [(start, (0, 1))] []
    hclosed_from hfuel u hmem e he hsrc

theorem recomputeCosts_tight_pair {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (v : C) (c : Int × Nat)
    (hmem : (v, c) ∈ recomputeCosts O verts edges start) :
    (v = start ∧ c = (0, 1)) ∨
      ∃ u, (u, v) ∈ edges ∧ u ∈ (recomputeCosts O verts edges start).map Prod.fst ∧
        u ≠ v ∧ c = ccAdd (costToCome (recomputeCosts O verts edges start) u) (O.cost u v) := by
  unfold recomputeCosts at hmem ⊢
  have hnodup : (([] : List (C × (Int × Nat))).map Prod.fst).Nodup := by simp
  have hacc : ∀ kv ∈ ([] : List (C × (Int × Nat))),
      (kv.1 = start ∧ kv.2 = (0, 1)) ∨
      ∃ u, (u, kv.1) ∈ edges ∧ u ∈ ([] : List (C × (Int × Nat))).map Prod.fst ∧
        u ≠ kv.1 ∧ kv.2 = ccAdd (costToCome [] u) (O.cost u kv.1) := by
    intro kv hmem
    simp at hmem
  have hqueue : ∀ kv ∈ [(start, (0, 1))] ,
      (kv.1 = start ∧ kv.2 = (0, 1)) ∨
      ∃ u, (u, kv.1) ∈ edges ∧ u ∈ ([] : List (C × (Int × Nat))).map Prod.fst ∧
        u ≠ kv.1 ∧ kv.2 = ccAdd (costToCome [] u) (O.cost u kv.1) := by
    intro kv hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    exact Or.inl ⟨rfl, rfl⟩
  have hall := treeCostsAux_tight O edges start (edges.length + 1)
    [(start, (0, 1))] [] hnodup hacc hqueue (v, c) hmem
  simp only at hall
  exact hall

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
theorem recomputeCosts_mem_of_path {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start v : C)
    (k : Nat) (p : PPath edges start v k) :
    v ∈ (recomputeCosts O verts edges start).map Prod.fst := by
  induction p with
  | refl => exact recomputeCosts_start_mem O verts edges start
  | @step u v k q h ih =>
      exact recomputeCosts_closed O verts edges start u ih (u, v) h rfl

theorem costed_of_edge_of_costed {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts) (e : C × C) (hmem : e ∈ edges)
    (hu : e.1 ∈ (recomputeCosts O verts edges start).map Prod.fst) :
    e.2 ∈ (recomputeCosts O verts edges start).map Prod.fst := by
  exact recomputeCosts_closed O verts edges start e.1 hu e hmem rfl

/-- Bellman inequality, rational form, on a tree edge list (unique targets,
no edge into `start`): every edge can only improve its target. -/
theorem recomputeCosts_bellman_val {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts)
    (htnd : (edges.map Prod.snd).Nodup) (hnotgt : ∀ e ∈ edges, e.2 ≠ start)
    (e : C × C) (hmem : e ∈ edges)
    (hu : e.1 ∈ (recomputeCosts O verts edges start).map Prod.fst) :
    pairVal (costToCome (recomputeCosts O verts edges start) e.2) ≤
      pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) e.1)
        (O.cost e.1 e.2)) := by
  have hv : e.2 ∈ (recomputeCosts O verts edges start).map Prod.fst :=
    costed_of_edge_of_costed O verts edges start hstart hnd htgt e hmem hu
  obtain ⟨c, hmemc, heqc⟩ := costToCome_mem_entry _ e.2 hv
  have hpair := recomputeCosts_tight_pair O verts edges start e.2 c hmemc
  rcases hpair with ⟨heq, -⟩ | ⟨u, hmemu, hucost, -, hceq⟩
  · exact absurd heq (hnotgt e hmem)
  · have hmem' : (e.1, e.2) ∈ edges := hmem
    have hpair_eq : (u, e.2) = (e.1, e.2) :=
      nodupTargets_unique edges htnd (u, e.2) hmemu (e.1, e.2) hmem' rfl
    have huv : u = e.1 := congrArg Prod.fst hpair_eq
    have hden := recomputeCosts_denoms O verts edges start
    have hposu : 0 < ((costToCome (recomputeCosts O verts edges start) u).2 : ℚ) := by
      exact_mod_cast denomsPos_costToCome _ u hden hucost
    have hpos1 : 0 < ((costToCome (recomputeCosts O verts edges start) e.1).2 : ℚ) := by
      exact_mod_cast denomsPos_costToCome _ e.1 hden hu
    have hexpand_lhs : pairVal (costToCome (recomputeCosts O verts edges start) e.2) =
        pairVal (costToCome (recomputeCosts O verts edges start) u) + O.cost u e.2 := by
      rw [heqc, hceq]
      exact pairVal_ccAdd _ _ (ne_of_gt hposu)
    have hexpand_rhs : pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) e.1)
        (O.cost e.1 e.2)) =
        pairVal (costToCome (recomputeCosts O verts edges start) e.1) + O.cost e.1 e.2 :=
      pairVal_ccAdd _ _ (ne_of_gt hpos1)
    rw [hexpand_lhs, hexpand_rhs, huv]

/-- Bellman inequality in the pair order, on a tree edge list (unique
targets, no edge into `start`). -/
theorem recomputeCosts_bellman {C : Type} [DecidableEq C] (O : Oracles C)
    (verts : List C) (edges : List (C × C)) (start : C)
    (hstart : start ∈ verts) (hnd : verts.Nodup)
    (htgt : ∀ e ∈ edges, e.2 ∈ verts)
    (htnd : (edges.map Prod.snd).Nodup) (hnotgt : ∀ e ∈ edges, e.2 ≠ start)
    (e : C × C) (hmem : e ∈ edges)
    (hu : e.1 ∈ (recomputeCosts O verts edges start).map Prod.fst) :
    ccLe (costToCome (recomputeCosts O verts edges start) e.2)
      (ccAdd (costToCome (recomputeCosts O verts edges start) e.1)
        (O.cost e.1 e.2)) := by
  have hv : e.2 ∈ (recomputeCosts O verts edges start).map Prod.fst :=
    costed_of_edge_of_costed O verts edges start hstart hnd htgt e hmem hu
  have hval := recomputeCosts_bellman_val O verts edges start hstart hnd htgt htnd
    hnotgt e hmem hu
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
  obtain ⟨c, hmemc, heqc⟩ := costToCome_mem_entry _ v hv
  have hpair := recomputeCosts_tight_pair O verts edges start v c hmemc
  rcases hpair with ⟨heq, -⟩ | ⟨u, hmemu, hucost, -, hceq⟩
  · exact absurd heq hne
  · refine ⟨u, hmemu, hucost, ?_⟩
    have hden := recomputeCosts_denoms O verts edges start
    have hpos : 0 < ((costToCome (recomputeCosts O verts edges start) u).2 : ℚ) := by
      exact_mod_cast denomsPos_costToCome _ u hden hucost
    have hexpand : pairVal (costToCome (recomputeCosts O verts edges start) v) =
        pairVal (costToCome (recomputeCosts O verts edges start) u) + O.cost u v := by
      rw [heqc, hceq]
      exact pairVal_ccAdd _ _ (ne_of_gt hpos)
    have hexpand_rhs : pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) u)
        (O.cost u v)) =
        pairVal (costToCome (recomputeCosts O verts edges start) u) + O.cost u v :=
      pairVal_ccAdd _ _ (ne_of_gt hpos)
    rw [hexpand, hexpand_rhs]

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
-- Design (intentional deviations from an earlier draft):
-- * Costs are recomputed at each `extendStar` step, twice: the post-insertion
--   guard table handed to `rewireAux` and the final table over the new edges;
--   inside `rewireAux` the guard table is maintained by subtree shifts after
--   each flip (sequential per-flip shift, not a recomputation or a pass-start
--   snapshot). At step boundaries `costs` is exactly the recomputed table, so
--   `chooseParent` never reads stale descendant costs.
-- * Steering and the nearest-edge gate: `extendStar` steers the raw sample
--   `s` from its nearest vertex `u` to `x := O.steer u s` and proceeds only
--   when `x` is free, the nearest edge `u ~ x` links, and `x` is fresh.
-- * `candidates` is a single filter over `verts`. `chooseParent` computes it
--   internally and returns the nearest-seeded minimizer, or `none` when empty.
-- * `radiusOf : ℕ → ℚ` is threaded through `candidates`, `chooseParent`,
--   `rewireAux`, `extendStar`, `rrtStarAux` and `rrtStar`. It is evaluated
--   once at the pre-insertion vertex count `verts.length`, shared by parent
--   selection (candidates) and rewiring. See each docstring.
-- * Rewiring replaces a vertex's parent edge via `replaceParent` on edge
--   lists. Self-loops are impossible (`x ∉ verts`, `w ≠ x`).
-- * Helpers `mem_candidates`, `foldl_mem`, `findParent`, `parentChain`,
--   `nodup_length_le`, `chain_ppath_cons`, `reachable_of_invar` are new.
-- No declarations are dropped; `firstTightParent` (prefix) is not used here.

/-- Candidate parents for `s`: linked vertices within `radiusOf` at the
    current count (`verts.length`, before adding), plus the fallback vertex
    `near` when it links (in its list position). `near` is the fallback
    candidate (the vertex nearest the raw sample, supplied by the caller). -/
def candidates {S : Type} [DecidableEq S] (O : Oracles S) (verts : List S)
    (radiusOf : ℕ → ℚ) (near s : S) : List S :=
  verts.filter (fun v =>
    O.link v s &&
      (decide (O.cost v s ≤ radiusOf verts.length) ||
        decide (v = near)))

/-- Membership characterization for `candidates`. -/
theorem mem_candidates {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (radiusOf : ℕ → ℚ) (near s v : S) :
    v ∈ candidates O verts radiusOf near s ↔
      v ∈ verts ∧ O.link v s = true ∧
        (O.cost v s ≤ radiusOf verts.length ∨
          v = near) := by
  simp only [candidates, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]

theorem candidates_subset_verts {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (radiusOf : ℕ → ℚ) (near s v : S)
    (h : v ∈ candidates O verts radiusOf near s) : v ∈ verts :=
  ((mem_candidates O verts radiusOf near s v).mp h).1

/-- The fallback vertex is a candidate iff it links to `s`, given membership
    supplied by the caller. -/
theorem near_mem_candidates_iff {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (radiusOf : ℕ → ℚ) (near s : S)
    (hmem : near ∈ verts) :
    near ∈ candidates O verts radiusOf near s ↔
      O.link near s = true := by
  rw [mem_candidates]
  constructor
  · rintro ⟨_, hlink, _⟩
    exact hlink
  · intro hlink
    exact ⟨hmem, hlink, Or.inr rfl⟩

/-- Minimizer of `ccAdd (costToCome costs ·) (O.cost · s)` over the
    candidates, by a fold seeded at `near` when `near` is a candidate
    (otherwise at the head); `none` iff candidates are empty.
    Strict `ccLt` improvement is required to replace the current best,
    so ties against `near` keep `near`. -/
def chooseParent {S : Type} [DecidableEq S] (O : Oracles S) (verts : List S)
    (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ) (near s : S) :
    Option S :=
  match candidates O verts radiusOf near s with
  | [] => none
  | h :: t =>
      some ((h :: t).foldl
        (fun best v =>
          if ccLt (ccAdd (costToCome costs v) (O.cost v s))
            (ccAdd (costToCome costs best) (O.cost best s)) then v
          else best) (if near ∈ h :: t then near else h))

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
    (near s : S) :
    chooseParent O verts costs radiusOf near s = none ↔
      candidates O verts radiusOf near s = [] := by
  cases hc : candidates O verts radiusOf near s with
  | nil => simp [chooseParent, hc]
  | cons h t => simp [chooseParent, hc]

theorem chooseParent_mem {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ)
    (near s p : S) (h : chooseParent O verts costs radiusOf near s = some p) :
    p ∈ candidates O verts radiusOf near s := by
  cases hc : candidates O verts radiusOf near s with
  | nil =>
      simp only [chooseParent, hc] at h
      contradiction
  | cons hd tl =>
      simp only [chooseParent, hc] at h
      cases h
      have hseed : (if near ∈ hd :: tl then near else hd) ∈ hd :: tl := by
        by_cases hnear : near ∈ hd :: tl
        · simp [hnear]
        · simp [hnear]
      have hmem : (hd :: tl).foldl
          (fun best v =>
            if ccLt (ccAdd (costToCome costs v) (O.cost v s))
              (ccAdd (costToCome costs best) (O.cost best s)) then v
            else best) (if near ∈ hd :: tl then near else hd) ∈
          (if near ∈ hd :: tl then near else hd) :: (hd :: tl) := by
        apply foldl_mem
        intro a b
        by_cases hcLt : ccLt (ccAdd (costToCome costs b) (O.cost b s))
          (ccAdd (costToCome costs a) (O.cost a s))
        · simp [hcLt]
        · simp [hcLt]
      have hmem_or := List.mem_cons.mp hmem
      cases hmem_or with
      | inl heq =>
          rw [heq]
          exact hseed
      | inr hmem_tl =>
          exact hmem_tl

/-- If the fallback vertex links, parent search succeeds. -/
theorem chooseParent_isSome_of_gate {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ)
    (near s : S) (hmem : near ∈ verts) (hlink : O.link near s = true) :
    (chooseParent O verts costs radiusOf near s).isSome := by
  have hcand : near ∈ candidates O verts radiusOf near s :=
    (near_mem_candidates_iff O verts radiusOf near s hmem).mpr hlink
  have hne : candidates O verts radiusOf near s ≠ [] := by
    intro hemp
    rw [hemp] at hcand
    simp at hcand
  have hnn : chooseParent O verts costs radiusOf near s ≠ none := by
    intro hnone
    rw [chooseParent_eq_none_iff] at hnone
    exact hne hnone
  cases ho : chooseParent O verts costs radiusOf near s with
  | none => exact absurd ho hnn
  | some p => rfl

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


/-- Last of verts is the target. -/
private theorem PPath.verts_getLast_some {C : Type} {edges : List (C × C)} {u v : C} {k : Nat}
    (p : PPath edges u v k) : p.verts.getLast? = some v := by
  induction p with
  | refl =>
      simp [PPath.verts_refl]
  | step p' hmem ih =>
      rw [PPath.verts_step, List.getLast?_concat]

/-- Source lies in verts. -/
private theorem PPath.mem_source {C : Type} {edges : List (C × C)} {u v : C} {k : Nat}
    (p : PPath edges u v k) : u ∈ p.verts := by
  induction p with
  | refl =>
      simp [PPath.verts_refl]
  | step p' hmem ih =>
      rw [PPath.verts_step]
      exact List.mem_append_left _ ih

/-- Two edges with the same target in a target-nodup list are equal. -/
private theorem pair_eq_of_snd_mem_of_nodup {C : Type} {edges : List (C × C)}
    (hnd : (edges.map Prod.snd).Nodup) {e1 e2 : C × C}
    (h1 : e1 ∈ edges) (h2 : e2 ∈ edges) (hsnd : e1.2 = e2.2) : e1 = e2 := by
  induction edges generalizing e1 e2 with
  | nil => simp at h1
  | cons hd tl ih =>
      simp only [List.map_cons] at hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hnmem, hnd_tl⟩ := hnd
      simp only [List.mem_cons] at h1 h2
      rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
      · rfl
      · exfalso
        apply hnmem
        rw [hsnd]
        exact List.mem_map_of_mem h2
      · exfalso
        apply hnmem
        rw [← hsnd]
        exact List.mem_map_of_mem h1
      · exact ih hnd_tl h1 h2 hsnd

/-- Predecessors with the same target coincide. -/
private theorem pred_eq_of_mem_of_nodup {C : Type} {edges : List (C × C)}
    (hnd : (edges.map Prod.snd).Nodup) {w w' v : C}
    (h1 : (w, v) ∈ edges) (h2 : (w', v) ∈ edges) : w = w' := by
  have hpair : (w, v) = (w', v) :=
    pair_eq_of_snd_mem_of_nodup hnd h1 h2 rfl
  simpa using congrArg Prod.fst hpair

/-- Tail vertex is fresh in a simple path. -/
private theorem not_mem_of_nodup_append_singleton {C : Type} {l : List C} {a : C}
    (h : (l ++ [a]).Nodup) : a ∉ l := by
  intro hmem
  have hdisj := (List.nodup_append.mp h).2.2
  have hne := hdisj a hmem a (by simp)
  exact hne rfl

private theorem pcost_eq_of_verts_eq_aux {C : Type} (O : Oracles C)
    {edges : List (C × C)} {u : C} {v : C} {k : Nat} (p : PPath edges u v k) :
    ∀ {j : Nat} (q : PPath edges u v j),
      p.verts = q.verts → pcost O p = pcost O q := by
  induction p with
  | refl =>
      intro j q h
      cases q with
      | refl =>
          rfl
      | step q' hmem' =>
          exfalso
          simp [PPath.verts_refl, PPath.verts_step] at h
          have hlen := congrArg List.length h
          simp [q'.verts_length] at hlen
  | step p' hmem ih =>
      intro j q h
      cases q with
      | refl =>
          exfalso
          simp [PPath.verts_refl, PPath.verts_step] at h
          have hlen := congrArg List.length h
          simp [p'.verts_length] at hlen
      | step q' hmem2 =>
          rw [PPath.verts_step, PPath.verts_step] at h
          have hpre : p'.verts = q'.verts := List.append_cancel_right h
          have hgl := congrArg List.getLast? hpre
          rw [p'.verts_getLast_some, q'.verts_getLast_some] at hgl
          have hww : _ = _ := Option.some_inj.mp hgl
          subst hww
          have iheq : pcost O p' = pcost O q' := ih q' hpre
          simp [pcost_step, iheq]

private theorem verts_eq_of_simple_aux {C : Type} {edges : List (C × C)} {u : C}
    (hnd : (edges.map Prod.snd).Nodup) {v : C} {k : Nat} (p : PPath edges u v k) :
    ∀ {j : Nat} (q : PPath edges u v j),
      p.verts.Nodup → q.verts.Nodup → p.verts = q.verts := by
  induction p with
  | refl =>
      intro j q hp hq
      cases q with
      | refl =>
          simp [PPath.verts_refl]
      | step q' hmem' =>
          exfalso
          rw [PPath.verts_step] at hq
          have hnem : _ ∉ q'.verts := not_mem_of_nodup_append_singleton hq
          have hmem : _ ∈ q'.verts := q'.mem_source
          exact hnem hmem
  | step p' hmem ih =>
      intro j q hp hq
      cases q with
      | refl =>
          exfalso
          rw [PPath.verts_step] at hp
          have hnem : _ ∉ p'.verts := not_mem_of_nodup_append_singleton hp
          have hmemsrc : _ ∈ p'.verts := p'.mem_source
          exact hnem hmemsrc
      | step q' hmem2 =>
          have hww : _ = _ := pred_eq_of_mem_of_nodup hnd hmem hmem2
          subst hww
          rw [PPath.verts_step] at hp hq
          have hp' : p'.verts.Nodup := List.Nodup.of_append_left hp
          have hq' : q'.verts.Nodup := List.Nodup.of_append_left hq
          have heq : p'.verts = q'.verts := ih q' hp' hq'
          simp [PPath.verts_step, heq]

/-- Path cost depends only on the vertex sequence. -/
theorem pcost_eq_of_verts_eq {C : Type} (O : Oracles C) {edges : List (C × C)}
    {u v : C} {k j : ℕ} (p : PPath edges u v k) (q : PPath edges u v j)
    (h : p.verts = q.verts) : pcost O p = pcost O q := by
  exact pcost_eq_of_verts_eq_aux O p q h

/-- In a target-nodup edge list, two simple paths with the same endpoints
    have the same vertex sequence. -/
theorem PPath.verts_eq_of_simple {C : Type} {edges : List (C × C)} {u v : C}
    {k j : ℕ} (hnd : (edges.map Prod.snd).Nodup)
    (p : PPath edges u v k) (q : PPath edges u v j)
    (hp : p.verts.Nodup) (hq : q.verts.Nodup) : p.verts = q.verts := by
  exact verts_eq_of_simple_aux hnd p q hp hq

/-- Simple paths with the same endpoints in a tree cost the same. -/
theorem pcost_eq_of_simple {C : Type} (O : Oracles C) {edges : List (C × C)}
    {u v : C} {k j : ℕ} (hnd : (edges.map Prod.snd).Nodup)
    (p : PPath edges u v k) (q : PPath edges u v j)
    (hp : p.verts.Nodup) (hq : q.verts.Nodup) : pcost O p = pcost O q := by
  exact pcost_eq_of_verts_eq O p q (PPath.verts_eq_of_simple hnd p q hp hq)

private theorem start_mem_verts_aux {S : Type} {edges : List (S × S)} {start v : S} {k : Nat}
    (p : PPath edges start v k) : start ∈ p.verts := by
  induction p with
  | refl => simp [PPath.verts_refl]
  | @step u v k q h ih =>
      rw [PPath.verts_step]
      exact List.mem_append.mpr (Or.inl ih)

private theorem recomputeCosts_cost_start_uncond_aux {C : Type} [DecidableEq C]
    (O : Oracles C) (verts : List C) (edges : List (C × C)) (start : C) :
    costToCome (recomputeCosts O verts edges start) start = (0, 1) := by
  unfold recomputeCosts
  rw [treeCostsAux_cons_new]
  · refine (treeCostsAux_cost_mem _ _ _ _ _ _ (by simp)).trans ?_
    first | exact costToCome_cons_eq | simp [costToCome_cons_eq]
  simp

theorem pairVal_costToCome_recomputeCosts {S : Type} [DecidableEq S]
    (O : Oracles S) (verts : List S) (edges : List (S × S)) (start v : S)
    (h_end : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (hnd : (edges.map Prod.snd).Nodup)
    (hvnd : verts.Nodup) (hstart : start ∈ verts) (hv : v ∈ verts)
    (k : ℕ) (p : PPath edges start v k) (hsimple : p.verts.Nodup) :
    pairVal (costToCome (recomputeCosts O verts edges start) v) = pcost O p := by
  induction p with
  | refl =>
      have hcost := recomputeCosts_cost_start_uncond_aux O verts edges start
      simp [hcost, pairVal_init, pcost_refl]
  | @step u v k q h ih =>
      have hu_mem : u ∈ verts := (h_end _ h).1
      rw [PPath.verts_step] at hsimple
      have hq_nodup : q.verts.Nodup := List.Nodup.of_append_left hsimple
      have ih_eq := ih hu_mem hq_nodup
      have v_mem := recomputeCosts_mem_of_path O verts edges start v _ (q.step h)
      have hv_notmem : v ∉ q.verts := by
        intro hmem
        have hdisj := (List.nodup_append.mp hsimple).2.2
        have hvv : v ≠ v := hdisj v hmem v (by simp)
        exact hvv rfl
      have hstart_mem : start ∈ q.verts := start_mem_verts_aux q
      have v_ne_start : v ≠ start := by
        intro heq
        subst heq
        exact hv_notmem hstart_mem
      obtain ⟨c, hmem_entry, heq_entry⟩ := costToCome_mem_entry _ v v_mem
      have htight := recomputeCosts_tight_pair O verts edges start v c hmem_entry
      rcases htight with ⟨heq_start, hc0⟩ | ⟨u_tight, h_edge_tight, h_mem_tight, h_ne_tight, h_eq_tight⟩
      · exact absurd heq_start v_ne_start
      · have hpair_eq : (u_tight, v) = (u, v) :=
          nodupTargets_unique edges hnd (u_tight, v) h_edge_tight (u, v) h rfl
        have heq_parent : u_tight = u := congrArg Prod.fst hpair_eq
        rw [heq_parent] at h_eq_tight
        have h_eq : costToCome (recomputeCosts O verts edges start) v =
            ccAdd (costToCome (recomputeCosts O verts edges start) u) (O.cost u v) :=
          heq_entry.trans h_eq_tight
        have hdenoms := recomputeCosts_denoms O verts edges start
        have hu_costed : u ∈ (recomputeCosts O verts edges start).map Prod.fst := by
          rw [←heq_parent]
          exact h_mem_tight
        have hu_pos : 0 < ((costToCome (recomputeCosts O verts edges start) u).2 : ℚ) := by
          exact_mod_cast denomsPos_costToCome _ u hdenoms hu_costed
        have hadd : pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) u) (O.cost u v)) =
            pairVal (costToCome (recomputeCosts O verts edges start) u) + O.cost u v :=
          pairVal_ccAdd _ _ (ne_of_gt hu_pos)
        rw [h_eq, hadd, ih_eq, pcost_step]


private theorem findParent_cons_eq_aux {S : Type} [DecidableEq S]
    (e : S × S) (rest : List (S × S)) (x : S) (h : e.2 = x) :
    findParent (e :: rest) x = some e.1 := by
  simp [findParent, h]

private theorem findParent_cons_ne_aux {S : Type} [DecidableEq S]
    (e : S × S) (rest : List (S × S)) (x : S) (h : ¬ e.2 = x) :
    findParent (e :: rest) x = findParent rest x := by
  simp [findParent, h]

private theorem findParent_some_of_mem_aux {S : Type} [DecidableEq S]
    (edges : List (S × S)) (u x : S)
    (hmem : (u, x) ∈ edges) (hnd : (edges.map Prod.snd).Nodup) :
    findParent edges x = some u := by
  induction edges with
  | nil =>
    simp at hmem
  | cons e rest ih =>
    simp only [List.map] at hnd
    rw [List.nodup_cons] at hnd
    obtain ⟨hnotin, hndTail⟩ := hnd
    simp at hmem
    cases hmem with
    | inl heq =>
      have heq2 : e.2 = x := by
        have h := congrArg Prod.snd heq
        simp at h
        exact h.symm
      have heq1 : e.1 = u := by
        have h := congrArg Prod.fst heq
        simp at h
        exact h.symm
      rw [findParent_cons_eq_aux _ _ _ heq2, heq1]
    | inr htail =>
      have hne : ¬ e.2 = x := by
        intro heq
        rw [heq] at hnotin
        have hmemMap : x ∈ rest.map Prod.snd := by
          rw [List.mem_map]
          exact ⟨(u, x), htail, rfl⟩
        exact hnotin hmemMap
      rw [findParent_cons_ne_aux _ _ _ hne]
      exact ih htail hndTail

private theorem parentChain_zero_aux {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) :
    parentChain edges start v 0 = [v] := rfl

private theorem parentChain_succ_of_eq_aux {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) (n : Nat) (h : v = start) :
    parentChain edges start v (n + 1) = [v] := by
  simp [parentChain, h]

private theorem parentChain_succ_of_ne_none_aux {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) (n : Nat)
    (hne : ¬ v = start) (hfind : findParent edges v = none) :
    parentChain edges start v (n + 1) = [v] := by
  simp [parentChain, hne, hfind]

private theorem parentChain_succ_of_ne_some_aux {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v u : S) (n : Nat)
    (hne : ¬ v = start) (hfind : findParent edges v = some u) :
    parentChain edges start v (n + 1) = v :: parentChain edges start u n := by
  simp [parentChain, hne, hfind]

private theorem parentChain_mem_self_aux {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) (n : Nat) :
    v ∈ parentChain edges start v n := by
  cases n with
  | zero =>
    rw [parentChain_zero_aux]
    simp
  | succ n =>
    by_cases h : v = start
    · rw [parentChain_succ_of_eq_aux _ _ _ _ h]
      simp
    · match hfind : findParent edges v with
      | none =>
        rw [parentChain_succ_of_ne_none_aux _ _ _ _ h hfind]
        simp
      | some u =>
        rw [parentChain_succ_of_ne_some_aux _ _ _ _ _ h hfind]
        simp

private theorem parentChain_mono_succ_aux {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start : S) (k : Nat) :
    ∀ (v w : S), w ∈ parentChain edges start v k → w ∈ parentChain edges start v (k + 1) := by
  induction k with
  | zero =>
    intro v w hmem
    rw [parentChain_zero_aux] at hmem
    simp at hmem
    subst hmem
    apply parentChain_mem_self_aux
  | succ k ih =>
    intro v w hmem
    by_cases heq : v = start
    · rw [parentChain_succ_of_eq_aux _ _ _ _ heq] at hmem
      rw [parentChain_succ_of_eq_aux _ _ _ _ heq]
      exact hmem
    · match hfind : findParent edges v with
      | none =>
        rw [parentChain_succ_of_ne_none_aux _ _ _ _ heq hfind] at hmem
        rw [parentChain_succ_of_ne_none_aux _ _ _ _ heq hfind]
        exact hmem
      | some u =>
        rw [parentChain_succ_of_ne_some_aux _ _ _ _ _ heq hfind] at hmem
        rw [parentChain_succ_of_ne_some_aux _ _ _ _ _ heq hfind]
        simp [List.mem_cons] at hmem ⊢
        cases hmem with
        | inl heq2 => exact Or.inl heq2
        | inr htail => exact Or.inr (ih u w htail)

private theorem parentChain_mono_le_aux {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v w : S) (k n : Nat)
    (hle : k ≤ n) (hmem : w ∈ parentChain edges start v k) :
    w ∈ parentChain edges start v n := by
  induction n generalizing k with
  | zero =>
    have heq : k = 0 := Nat.le_zero.mp hle
    subst heq
    exact hmem
  | succ n ih =>
    by_cases heq : k = n + 1
    · subst heq
      exact hmem
    · have hle' : k ≤ n := by omega
      have hmid := ih k hle' hmem
      exact parentChain_mono_succ_aux edges start n v w hmid

private theorem parentChain_stable_succ_aux {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start : S) (k : Nat) :
    ∀ (v : S), start ∈ parentChain edges start v k →
      parentChain edges start v (k + 1) = parentChain edges start v k := by
  induction k with
  | zero =>
    intro v hmem
    rw [parentChain_zero_aux] at hmem
    simp at hmem
    subst hmem
    rw [parentChain_succ_of_eq_aux _ _ _ _ rfl]
    rw [parentChain_zero_aux]
  | succ k ih =>
    intro v hmem
    by_cases heq : v = start
    · rw [parentChain_succ_of_eq_aux _ _ _ _ heq]
      rw [parentChain_succ_of_eq_aux _ _ _ _ heq]
    · match hfind : findParent edges v with
      | none =>
        rw [parentChain_succ_of_ne_none_aux _ _ _ _ heq hfind]
        rw [parentChain_succ_of_ne_none_aux _ _ _ _ heq hfind]
      | some u =>
        rw [parentChain_succ_of_ne_some_aux _ _ _ _ _ heq hfind] at hmem
        rw [parentChain_succ_of_ne_some_aux _ _ _ _ _ heq hfind]
        rw [parentChain_succ_of_ne_some_aux _ _ _ _ _ heq hfind]
        simp [List.mem_cons] at hmem
        cases hmem with
        | inl heq2 =>
          subst heq2
          contradiction
        | inr htail =>
          rw [ih u htail]

private theorem parentChain_stable_le_aux {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) (k n : Nat)
    (hmem : start ∈ parentChain edges start v k) (hle : k ≤ n) :
    parentChain edges start v n = parentChain edges start v k := by
  induction n generalizing k with
  | zero =>
    have heq : k = 0 := Nat.le_zero.mp hle
    subst heq
    rfl
  | succ n ih =>
    by_cases heq : k = n + 1
    · subst heq
      rfl
    · have hle' : k ≤ n := by omega
      have heqMid := ih k hmem hle'
      have hmemMid : start ∈ parentChain edges start v n := by
        rw [heqMid]
        exact hmem
      have hstep := parentChain_stable_succ_aux edges start n v hmemMid
      rw [hstep]
      exact heqMid

private theorem ppath_start_mem_aux {S : Type} [DecidableEq S]
    {edges : List (S × S)} {start v : S} {k : Nat}
    (p : PPath edges start v k) : start ∈ p.verts := by
  induction p with
  | refl =>
    rw [PPath.verts_refl]
    simp
  | step q _ ih =>
    rw [PPath.verts_step]
    simp [List.mem_append, ih]

private theorem nodup_append_singleton_left_aux {S : Type}
    (l : List S) (a : S) (h : (l ++ [a]).Nodup) : l.Nodup := by
  induction l with
  | nil =>
    exact List.nodup_nil
  | cons hd tl ih =>
    simp only [List.cons_append, List.nodup_cons] at h ⊢
    obtain ⟨hnotin, htail⟩ := h
    have hnotin_tl : hd ∉ tl := by
      intro hmem
      apply hnotin
      rw [List.mem_append]
      exact Or.inl hmem
    exact ⟨hnotin_tl, ih htail⟩

private theorem not_mem_of_nodup_append_singleton_aux {S : Type}
    (l : List S) (a : S) (h : (l ++ [a]).Nodup) : a ∉ l := by
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>
    simp only [List.cons_append, List.nodup_cons] at h
    obtain ⟨hnotin, htail⟩ := h
    have hne : hd ≠ a := by
      intro heq
      apply hnotin
      rw [List.mem_append]
      exact Or.inr (by simp [heq])
    intro hmem
    simp [List.mem_cons] at hmem
    cases hmem with
    | inl heq =>
      exact hne heq.symm
    | inr hmem_tl =>
      exact (ih htail) hmem_tl

private theorem ppath_verts_reverse_eq_parentChain_aux {S : Type} [DecidableEq S]
    {edges : List (S × S)} {start : S} {v : S} {k : Nat}
    (p : PPath edges start v k)
    (hnd : (edges.map Prod.snd).Nodup) (hp : p.verts.Nodup) :
    p.verts.reverse = parentChain edges start v k := by
  induction p with
  | refl =>
    rw [PPath.verts_refl, List.reverse_singleton, parentChain_zero_aux]
  | step q hmem ih =>
    rename_i u w kk
    rw [PPath.verts_step] at hp
    have hq : q.verts.Nodup := nodup_append_singleton_left_aux _ _ hp
    have ih' := ih hq
    have hne : w ≠ start := by
      intro heq
      subst heq
      have hstart := ppath_start_mem_aux q
      have hnot := not_mem_of_nodup_append_singleton_aux _ _ hp
      exact hnot hstart
    have hfind : findParent edges w = some u := findParent_some_of_mem_aux edges u w hmem hnd
    rw [PPath.verts_step]
    rw [List.reverse_append, List.reverse_singleton]
    simp only [List.singleton_append]
    rw [parentChain_succ_of_ne_some_aux _ _ _ _ _ hne hfind]
    rw [ih']

theorem mem_parentChain_iff_mem_verts {S : Type} [DecidableEq S]
    (edges : List (S × S)) (verts : List S) (start v w : S)
    (hnd : (edges.map Prod.snd).Nodup) (hvnd : verts.Nodup)
    (h_end : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (hstart : start ∈ verts) (hv : v ∈ verts)
    (k : ℕ) (p : PPath edges start v k) (hp : p.verts.Nodup) :
    w ∈ p.verts ↔ w ∈ parentChain edges start v verts.length := by
  have hle1 : k + 1 ≤ verts.length :=
    PPath.simple_length_le verts hstart (fun e he => (h_end e he).2) hvnd p hp
  have hle : k ≤ verts.length := Nat.le_of_succ_le hle1
  have hrev := ppath_verts_reverse_eq_parentChain_aux p hnd hp
  have hstart_mem := ppath_start_mem_aux p
  have hstart_chain : start ∈ parentChain edges start v k := by
    rw [← hrev]
    exact List.mem_reverse.mpr hstart_mem
  have hstable := parentChain_stable_le_aux edges start v k verts.length hstart_chain hle
  constructor
  · intro hmem
    have hmem_rev : w ∈ p.verts.reverse := List.mem_reverse.mpr hmem
    rw [hrev] at hmem_rev
    exact parentChain_mono_le_aux edges start v w k verts.length hle hmem_rev
  · intro hmemL
    rw [hstable] at hmemL
    rw [← hrev] at hmemL
    exact List.mem_reverse.mp hmemL

private theorem ppath_split {S : Type} [DecidableEq S] (O : Oracles S)
    {edges : List (S × S)} {start v w : S} {k : ℕ}
    (p : PPath edges start v k) (hp : p.verts.Nodup) (hw : w ∈ p.verts) :
    ∃ (i j : ℕ) (pfx : PPath edges start w i) (sfx : PPath edges w v j),
      pfx.verts.Nodup ∧ sfx.verts.Nodup ∧
      (∀ x ∈ sfx.verts, x ∈ p.verts) ∧
      pcost O p = pcost O pfx + pcost O sfx := by
  revert hp hw
  induction p with
  | refl =>
      intro hp hw
      rw [PPath.verts_refl] at hp hw
      have hww : w = start := List.mem_singleton.mp hw
      subst hww
      refine ⟨0, 0, PPath.refl _, PPath.refl _, ?_, ?_, ?_, ?_⟩
      · rw [PPath.verts_refl]
        exact List.nodup_singleton _
      · rw [PPath.verts_refl]
        exact List.nodup_singleton _
      · rw [PPath.verts_refl]
        intro x hx
        exact hx
      · simp [pcost_refl]
  | step p' hmem ih =>
      rename_i hinst mid tgt len
      intro hp hw
      rw [PPath.verts_step] at hp hw
      by_cases heq : tgt = w
      · subst heq
        refine ⟨_, 0, PPath.step p' hmem, PPath.refl _, ?_, ?_, ?_, ?_⟩
        · rw [PPath.verts_step]
          exact hp
        · rw [PPath.verts_refl]
          exact List.nodup_singleton _
        · intro x hx
          rw [PPath.verts_refl] at hx
          rw [List.mem_singleton] at hx
          subst hx
          rw [PPath.verts_step]
          exact hw
        · rw [pcost_refl, add_zero]
      · have hwq : w ∈ p'.verts := by
          have hdisj := List.mem_append.mp hw
          cases hdisj with
          | inl hleft => exact hleft
          | inr hright =>
              have heq2 : w = tgt := List.mem_singleton.mp hright
              exact absurd heq2.symm heq
        have hpq : p'.verts.Nodup := (List.nodup_append.mp hp).1
        have hcnotin : tgt ∉ p'.verts := by
          have hdisj := (List.nodup_append.mp hp).2.2
          intro hmem2
          have hcself : tgt ∈ [tgt] := List.mem_singleton.mpr rfl
          exact hdisj tgt hmem2 tgt hcself rfl
        obtain ⟨i, j', pfx, sfx', hpfx, hsfx', hsub', hcost'⟩ := ih hpq hwq
        have hcnotin2 : tgt ∉ sfx'.verts := by
          intro hmem2
          exact hcnotin (hsub' tgt hmem2)
        have hnod : (sfx'.verts ++ [tgt]).Nodup :=
          nodup_append_singleton _ _ hsfx' hcnotin2
        refine ⟨_, _, pfx, PPath.step sfx' hmem, hpfx, ?_, ?_, ?_⟩
        · rw [PPath.verts_step]
          exact hnod
        · rw [PPath.verts_step, PPath.verts_step]
          intro x hx
          have hdisj := List.mem_append.mp hx
          cases hdisj with
          | inl hleft =>
              have hmemq := hsub' x hleft
              exact List.mem_append.mpr (Or.inl hmemq)
          | inr hright =>
              exact List.mem_append.mpr (Or.inr hright)
        · rw [pcost_step, pcost_step, hcost', add_assoc]

theorem ppath_split_pcost {S : Type} [DecidableEq S] (O : Oracles S)
    {edges : List (S × S)} {start v w : S} {k jw : ℕ}
    (hnd : (edges.map Prod.snd).Nodup)
    (p : PPath edges start v k) (hp : p.verts.Nodup) (hw : w ∈ p.verts)
    (pw : PPath edges start w jw) (hpw : pw.verts.Nodup) :
    ∃ (j : ℕ) (p2 : PPath edges w v j),
      p2.verts.Nodup ∧ (∀ x ∈ p2.verts, x ∈ p.verts) ∧
      pcost O p = pcost O pw + pcost O p2 := by
  obtain ⟨i, j, pfx, p2, hpfx, hnod, hsub, hcost⟩ := ppath_split O p hp hw
  have heq : pcost O pfx = pcost O pw := pcost_eq_of_simple O hnd pfx pw hpfx hpw
  exact ⟨j, p2, hnod, hsub, by rw [hcost, heq]⟩

/-- Shift the entries of `costs` whose vertex lies in the subtree rooted at
    `w` (membership read off `parentChain`) by the rational delta `d`. -/
def shiftCosts {S : Type} [DecidableEq S] (edges : List (S × S)) (start w : S)
    (n : ℕ) (d : Rat) (costs : List (S × Int × Nat)) : List (S × Int × Nat) :=
  costs.map (fun e =>
    if w ∈ parentChain edges start e.1 n then (e.1, ccAdd e.2 d) else e)

theorem shiftCosts_cons {S : Type} [DecidableEq S] (edges : List (S × S))
    (start w : S) (n : ℕ) (d : Rat) (a : S) (b : Int × Nat)
    (tl : List (S × Int × Nat)) :
    shiftCosts edges start w n d ((a, b) :: tl) =
      (if w ∈ parentChain edges start a n then (a, ccAdd b d) else (a, b)) ::
        shiftCosts edges start w n d tl := rfl

theorem shiftCosts_cons_of_mem {S : Type} [DecidableEq S] (edges : List (S × S))
    (start w : S) (n : ℕ) (d : Rat) (a : S) (b : Int × Nat)
    (tl : List (S × Int × Nat)) (hmem : w ∈ parentChain edges start a n) :
    shiftCosts edges start w n d ((a, b) :: tl) =
      (a, ccAdd b d) :: shiftCosts edges start w n d tl := by
  rw [shiftCosts_cons, ite_eq_left hmem]

theorem shiftCosts_cons_of_notmem {S : Type} [DecidableEq S] (edges : List (S × S))
    (start w : S) (n : ℕ) (d : Rat) (a : S) (b : Int × Nat)
    (tl : List (S × Int × Nat)) (hmem : w ∉ parentChain edges start a n) :
    shiftCosts edges start w n d ((a, b) :: tl) =
      (a, b) :: shiftCosts edges start w n d tl := by
  rw [shiftCosts_cons, ite_eq_right hmem]

theorem costToCome_shiftCosts_of_mem {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start w v : S) (n : ℕ) (d : Rat)
    (costs : List (S × Int × Nat)) (hcosted : v ∈ costs.map Prod.fst)
    (hmem : w ∈ parentChain edges start v n) :
    costToCome (shiftCosts edges start w n d costs) v = ccAdd (costToCome costs v) d
  := by
  induction costs with
  | nil =>
    simp at hcosted
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    have hcc : ∀ (x y : S) (c : Int × Nat) (r : List (S × (Int × Nat))),
        costToCome ((x, c) :: r) y = (if x = y then c else costToCome r y) :=
      fun x y c r => rfl
    by_cases hav : a = v
    · rw [← hav] at hmem
      rw [shiftCosts_cons_of_mem _ _ _ _ _ _ _ _ hmem, hcc, hcc, ite_eq_left hav, ite_eq_left hav]
    · have hne : v ≠ a := fun h => hav h.symm
      have hcosted_tl : v ∈ tl.map Prod.fst := by
        have h := hcosted
        simp only [List.map_cons, List.mem_cons] at h
        exact h.resolve_left hne
      by_cases hchain : w ∈ parentChain edges start a n
      · rw [shiftCosts_cons_of_mem _ _ _ _ _ _ _ _ hchain, hcc, hcc, ite_eq_right hav, ite_eq_right hav]
        exact ih hcosted_tl
      · rw [shiftCosts_cons_of_notmem _ _ _ _ _ _ _ _ hchain, hcc, hcc, ite_eq_right hav,
          ite_eq_right hav]
        exact ih hcosted_tl

theorem costToCome_shiftCosts_of_notmem {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start w v : S) (n : ℕ) (d : Rat)
    (costs : List (S × Int × Nat))
    (hmem : w ∉ parentChain edges start v n) :
    costToCome (shiftCosts edges start w n d costs) v = costToCome costs v
  := by
  induction costs with
  | nil =>
    rfl
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    have hcc : ∀ (x y : S) (c : Int × Nat) (r : List (S × (Int × Nat))),
        costToCome ((x, c) :: r) y = (if x = y then c else costToCome r y) :=
      fun x y c r => rfl
    by_cases hav : a = v
    · rw [← hav] at hmem
      rw [shiftCosts_cons_of_notmem _ _ _ _ _ _ _ _ hmem, hcc, hcc, ite_eq_left hav, ite_eq_left hav]
    · by_cases hchain : w ∈ parentChain edges start a n
      · rw [shiftCosts_cons_of_mem _ _ _ _ _ _ _ _ hchain, hcc, hcc, ite_eq_right hav, ite_eq_right hav]
        exact ih
      · rw [shiftCosts_cons_of_notmem _ _ _ _ _ _ _ _ hchain, hcc, hcc, ite_eq_right hav,
          ite_eq_right hav]
        exact ih

theorem shiftCosts_keys {S : Type} [DecidableEq S] (edges : List (S × S))
    (start w : S) (n : ℕ) (d : Rat) (costs : List (S × Int × Nat)) :
    (shiftCosts edges start w n d costs).map Prod.fst = costs.map Prod.fst
  := by
  induction costs with
  | nil =>
    rfl
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    rw [shiftCosts_cons]
    simp only [List.map_cons]
    by_cases h : w ∈ parentChain edges start a n
    · rw [ite_eq_left h, ih]
    · rw [ite_eq_right h, ih]

theorem pairVal_costToCome_shiftCosts {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start w v : S) (n : ℕ) (d : Rat)
    (costs : List (S × Int × Nat)) (hcosted : v ∈ costs.map Prod.fst)
    (hden : ((costToCome costs v).2 : ℚ) ≠ 0)
    (hmem : w ∈ parentChain edges start v n) :
    pairVal (costToCome (shiftCosts edges start w n d costs) v) =
      pairVal (costToCome costs v) + (d : ℚ)
  := by
  rw [costToCome_shiftCosts_of_mem _ _ _ _ _ _ _ hcosted hmem]
  exact pairVal_ccAdd _ _ hden

/-- Shift subtree entries by an unnormalized pair delta. This is the
    executable form used by `rewireAux`: it stays in pair arithmetic, so kernel
    evaluation does not normalize rational additions. -/
def shiftCostsPair {S : Type} [DecidableEq S] (edges : List (S × S)) (start w : S)
    (n : ℕ) (d : Int × Nat) (costs : List (S × Int × Nat)) : List (S × Int × Nat) :=
  costs.map (fun e =>
    if w ∈ parentChain edges start e.1 n then (e.1, ccAddPair e.2 d) else e)

private theorem shiftCostsPair_cons {S : Type} [DecidableEq S] (edges : List (S × S))
    (start w : S) (n : ℕ) (d : Int × Nat) (a : S) (b : Int × Nat)
    (tl : List (S × Int × Nat)) :
    shiftCostsPair edges start w n d ((a, b) :: tl) =
      (if w ∈ parentChain edges start a n then (a, ccAddPair b d) else (a, b)) ::
        shiftCostsPair edges start w n d tl := rfl

private theorem shiftCostsPair_cons_of_mem {S : Type} [DecidableEq S] (edges : List (S × S))
    (start w : S) (n : ℕ) (d : Int × Nat) (a : S) (b : Int × Nat)
    (tl : List (S × Int × Nat)) (hmem : w ∈ parentChain edges start a n) :
    shiftCostsPair edges start w n d ((a, b) :: tl) =
      (a, ccAddPair b d) :: shiftCostsPair edges start w n d tl := by
  rw [shiftCostsPair_cons, ite_eq_left hmem]

private theorem shiftCostsPair_cons_of_notmem {S : Type} [DecidableEq S] (edges : List (S × S))
    (start w : S) (n : ℕ) (d : Int × Nat) (a : S) (b : Int × Nat)
    (tl : List (S × Int × Nat)) (hmem : w ∉ parentChain edges start a n) :
    shiftCostsPair edges start w n d ((a, b) :: tl) =
      (a, b) :: shiftCostsPair edges start w n d tl := by
  rw [shiftCostsPair_cons, ite_eq_right hmem]

theorem costToCome_shiftCostsPair_of_mem {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start w v : S) (n : ℕ) (d : Int × Nat)
    (costs : List (S × Int × Nat)) (hcosted : v ∈ costs.map Prod.fst)
    (hmem : w ∈ parentChain edges start v n) :
    costToCome (shiftCostsPair edges start w n d costs) v =
      ccAddPair (costToCome costs v) d
  := by
  induction costs with
  | nil =>
    simp at hcosted
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    have hcc : ∀ (x y : S) (c : Int × Nat) (r : List (S × (Int × Nat))),
        costToCome ((x, c) :: r) y = (if x = y then c else costToCome r y) :=
      fun x y c r => rfl
    by_cases hav : a = v
    · rw [← hav] at hmem
      rw [shiftCostsPair_cons_of_mem _ _ _ _ _ _ _ _ hmem, hcc, hcc, ite_eq_left hav, ite_eq_left hav]
    · have hne : v ≠ a := fun h => hav h.symm
      have hcosted_tl : v ∈ tl.map Prod.fst := by
        have h := hcosted
        simp only [List.map_cons, List.mem_cons] at h
        exact h.resolve_left hne
      by_cases hchain : w ∈ parentChain edges start a n
      · rw [shiftCostsPair_cons_of_mem _ _ _ _ _ _ _ _ hchain, hcc, hcc, ite_eq_right hav, ite_eq_right hav]
        exact ih hcosted_tl
      · rw [shiftCostsPair_cons_of_notmem _ _ _ _ _ _ _ _ hchain, hcc, hcc, ite_eq_right hav,
          ite_eq_right hav]
        exact ih hcosted_tl

theorem costToCome_shiftCostsPair_of_notmem {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start w v : S) (n : ℕ) (d : Int × Nat)
    (costs : List (S × Int × Nat))
    (hmem : w ∉ parentChain edges start v n) :
    costToCome (shiftCostsPair edges start w n d costs) v = costToCome costs v
  := by
  induction costs with
  | nil =>
    rfl
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    have hcc : ∀ (x y : S) (c : Int × Nat) (r : List (S × (Int × Nat))),
        costToCome ((x, c) :: r) y = (if x = y then c else costToCome r y) :=
      fun x y c r => rfl
    by_cases hav : a = v
    · rw [← hav] at hmem
      rw [shiftCostsPair_cons_of_notmem _ _ _ _ _ _ _ _ hmem, hcc, hcc, ite_eq_left hav, ite_eq_left hav]
    · by_cases hchain : w ∈ parentChain edges start a n
      · rw [shiftCostsPair_cons_of_mem _ _ _ _ _ _ _ _ hchain, hcc, hcc, ite_eq_right hav, ite_eq_right hav]
        exact ih
      · rw [shiftCostsPair_cons_of_notmem _ _ _ _ _ _ _ _ hchain, hcc, hcc, ite_eq_right hav,
          ite_eq_right hav]
        exact ih

theorem pairVal_costToCome_shiftCostsPair {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start w v : S) (n : ℕ) (d : Int × Nat)
    (costs : List (S × Int × Nat)) (hcosted : v ∈ costs.map Prod.fst)
    (hden : ((costToCome costs v).2 : ℚ) ≠ 0) (hd : ((d.2 : Nat) : ℚ) ≠ 0)
    (hmem : w ∈ parentChain edges start v n) :
    pairVal (costToCome (shiftCostsPair edges start w n d costs) v) =
      pairVal (costToCome costs v) + pairVal d
  := by
  rw [costToCome_shiftCostsPair_of_mem _ _ _ _ _ _ _ hcosted hmem]
  exact pairVal_ccAddPair _ _ hden hd

theorem shiftCostsPair_denoms {S : Type} [DecidableEq S] (edges : List (S × S))
    (start w : S) (n : ℕ) (d : Int × Nat) (costs : List (S × Int × Nat))
    (hd : 0 < d.2) (h : DenomsPos costs) :
    DenomsPos (shiftCostsPair edges start w n d costs) := by
  induction costs with
  | nil =>
    intro kv hmem
    simp [shiftCostsPair] at hmem
  | cons hhead tl ih =>
    obtain ⟨a, b⟩ := hhead
    have h_head : 0 < b.2 := h (a, b) (by simp)
    have h_tail : DenomsPos tl := fun kv hmem => h kv (by simp [hmem])
    have ih' := ih h_tail
    by_cases hchain : w ∈ parentChain edges start a n
    · rw [shiftCostsPair_cons_of_mem _ _ _ _ _ _ _ _ hchain]
      intro kv hmem
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
        rw [heq]
        exact ccAddPair_den_pos b d h_head hd
      | inr hmem_tl =>
        exact ih' kv hmem_tl
    · rw [shiftCostsPair_cons_of_notmem _ _ _ _ _ _ _ _ hchain]
      intro kv hmem
      simp only [List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
        rw [heq]
        exact h_head
      | inr hmem_tl =>
        exact ih' kv hmem_tl

private theorem start_mem_verts {S : Type} {edges : List (S × S)} {u v : S}
    {k : ℕ} (p : PPath edges u v k) : u ∈ p.verts := by
  induction p with
  | refl => simp [PPath.verts_refl]
  | step q _ ih => simp [PPath.verts_step, ih]

private theorem step_target_ne_of_nodup {S : Type} {edges : List (S × S)}
    {w u V : S} {k : ℕ} (q' : PPath edges w u k)
    (h : (q'.verts ++ [V]).Nodup) : V ≠ w := by
  have hw : w ∈ q'.verts := start_mem_verts q'
  obtain ⟨_, _, hdisj⟩ := List.nodup_append.mp h
  exact Ne.symm (hdisj w hw V (by simp))

private theorem replaceParent_mem_of_target_ne {S : Type} [DecidableEq S]
    {edges : List (S × S)} (s : S) {w u V : S} (hmem : (u, V) ∈ edges)
    (hne : V ≠ w) : (u, V) ∈ replaceParent edges s w := by
  simp only [replaceParent, List.mem_map]
  exact ⟨(u, V), hmem, ite_eq_right hne⟩

private theorem tail_append_singleton {S : Type} (l : List S) (V : S)
    (hne : l ≠ []) : (l ++ [V]).tail = l.tail ++ [V] := by
  cases l with
  | nil => exact absurd rfl hne
  | cons hd tl => rfl

private theorem parentChain_zero_eq {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) :
    parentChain edges start v 0 = [v] := rfl

private theorem parentChain_succ_start_eq {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) (n : ℕ) (h : v = start) :
    parentChain edges start v (n + 1) = [v] := by
  have hunfold : parentChain edges start v (n + 1) =
      (if v = start then [v] else match findParent edges v with
        | none => [v]
        | some u => v :: parentChain edges start u n) := rfl
  rw [hunfold, ite_eq_left h]

private theorem parentChain_succ_none_eq {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) (n : ℕ)
    (hne : v ≠ start) (hfp : findParent edges v = none) :
    parentChain edges start v (n + 1) = [v] := by
  have hunfold : parentChain edges start v (n + 1) =
      (if v = start then [v] else match findParent edges v with
        | none => [v]
        | some u => v :: parentChain edges start u n) := rfl
  rw [hunfold, ite_eq_right hne, hfp]

private theorem parentChain_succ_some_eq {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v u : S) (n : ℕ)
    (hne : v ≠ start) (hfp : findParent edges v = some u) :
    parentChain edges start v (n + 1) = v :: parentChain edges start u n := by
  have hunfold : parentChain edges start v (n + 1) =
      (if v = start then [v] else match findParent edges v with
        | none => [v]
        | some u => v :: parentChain edges start u n) := rfl
  rw [hunfold, ite_eq_right hne, hfp]

private theorem parentChain_suffix_and_mem {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start : S) (n : ℕ) (z x : S)
    (hx : x ∈ parentChain edges start z n)
    (hz : start ∈ parentChain edges start z n) :
    (∃ pre, parentChain edges start z n = pre ++ parentChain edges start x n)
      ∧ start ∈ parentChain edges start x n := by
  induction n generalizing z x with
  | zero =>
    rw [parentChain_zero_eq] at hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨⟨[], by simp⟩, hz⟩
  | succ n ih =>
    by_cases hzz : z = start
    · subst hzz
      rw [parentChain_succ_start_eq _ _ _ _ rfl] at hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨⟨[], by simp⟩, hz⟩
    · cases hfp : findParent edges z with
      | none =>
        rw [parentChain_succ_none_eq _ _ _ _ hzz hfp] at hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact ⟨⟨[], by simp⟩, hz⟩
      | some u =>
        have hchain : parentChain edges start z (n + 1) =
            z :: parentChain edges start u n :=
          parentChain_succ_some_eq _ _ _ _ _ hzz hfp
        rw [hchain] at hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hxmem
        · exact ⟨⟨[], by simp⟩, hz⟩
        · have hstart_u : start ∈ parentChain edges start u n := by
            have hz' : start ∈ z :: parentChain edges start u n := by
              rw [← hchain]; exact hz
            simp only [List.mem_cons] at hz'
            rcases hz' with h | h
            · exact (hzz h.symm).elim
            · exact h
          obtain ⟨⟨pre, hpre⟩, hstart_x⟩ := ih u x hxmem hstart_u
          have hstab : parentChain edges start x (n + 1) =
              parentChain edges start x n :=
            parentChain_stable_le_aux _ _ _ _ _ hstart_x (by omega)
          have hmono : start ∈ parentChain edges start x (n + 1) :=
            parentChain_mono_le_aux _ _ _ _ _ _ (by omega) hstart_x
          refine ⟨⟨z :: pre, ?_⟩, hmono⟩
          simp only [hchain, hpre, hstab, List.cons_append]

private theorem parentChain_suffix_of_mem {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start : S) (n : ℕ) (z x : S)
    (hx : x ∈ parentChain edges start z n)
    (hz : start ∈ parentChain edges start z n) :
    ∃ pre, parentChain edges start z n = pre ++ parentChain edges start x n :=
  (parentChain_suffix_and_mem _ _ _ _ _ hx hz).1

/-- A path from `w` whose steps never target `w` (as a simple path from `w`
    guarantees) keeps all its edges under `replaceParent · s w`, with the same
    vertex sequence. -/
private theorem ppath_replaceParent_of_target_ne {S : Type} [DecidableEq S]
    {edges : List (S × S)} {s w v : S} {j : ℕ} (q : PPath edges w v j)
    (hq : q.verts.Nodup) :
    ∃ q' : PPath (replaceParent edges s w) w v j, q'.verts = q.verts := by
  induction q with
  | refl =>
    exact ⟨PPath.refl _, rfl⟩
  | step q' hmem ih =>
    rw [PPath.verts_step] at hq
    obtain ⟨hqnodup, _, _⟩ := List.nodup_append.mp hq
    have hVw := step_target_ne_of_nodup q' hq
    have hmem' := replaceParent_mem_of_target_ne s hmem hVw
    obtain ⟨q'', hverts⟩ := ih hqnodup
    exact ⟨q''.step hmem', by simp [PPath.verts_step, hverts]⟩

/-- Chaining: extend a base path by a path starting at its endpoint,
    adding costs and concatenating vertex lists at the junction. -/
private theorem ppath_chain {S : Type} [DecidableEq S] (O : Oracles S)
    {edges : List (S × S)} {a w v : S} {i j : ℕ}
    (base : PPath edges a w i) (q : PPath edges w v j) :
    ∃ r : PPath edges a v (i + j),
      pcost O r = pcost O base + pcost O q ∧
      r.verts = base.verts ++ q.verts.tail := by
  induction q generalizing a i base with
  | refl =>
    exact ⟨base, by simp [pcost_refl], by simp [PPath.verts_refl]⟩
  | step q' hmem ih =>
    obtain ⟨r', hr'cost, hr'verts⟩ := ih base
    have hne : q'.verts ≠ [] := by
      intro hnil
      have hlen := PPath.verts_length q'
      rw [hnil] at hlen
      simp at hlen
    refine ⟨r'.step hmem, ?_, ?_⟩
    · simp only [pcost_step, hr'cost]
      exact add_assoc _ _ _
    · rw [PPath.verts_step, hr'verts, PPath.verts_step, tail_append_singleton _ _ hne,
        List.append_assoc]

/-- Ancestor transitivity along parent chains at a complete fuel. -/
private theorem mem_parentChain_trans {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start x y z : S) (n : ℕ)
    (hz : start ∈ parentChain edges start z n)
    (hx : x ∈ parentChain edges start z n)
    (hy : y ∈ parentChain edges start x n) :
    y ∈ parentChain edges start z n := by
  obtain ⟨pre, hpre⟩ := parentChain_suffix_of_mem _ _ _ _ _ hx hz
  rw [hpre]
  exact List.mem_append_right pre hy

private theorem mem_parentChain_self {S : Type} [DecidableEq S]
    (edges : List (S × S)) (start v : S) (n : ℕ) :
    v ∈ parentChain edges start v n := by
  cases n with
  | zero => simp [parentChain]
  | succ n =>
    simp only [parentChain]
    by_cases h : v = start
    · simp [h]
    · simp [h]
      cases hfp : findParent edges v
      · simp
      · simp

private theorem end_mem_verts {S : Type} {edges : List (S × S)} {u v : S} {k : Nat}
    (p : PPath edges u v k) : v ∈ PPath.verts p := by
  induction p with
  | refl => simp [PPath.verts]
  | step p _ ih =>
    rw [PPath.verts_step]
    simp

private theorem mem_parentChain_of_ppath_fixed {S : Type} [DecidableEq S]
    {edges : List (S × S)} {start w x : S} {j : ℕ}
    (hnd : (edges.map Prod.snd).Nodup)
    (q : PPath edges w x j) (hq : q.verts.Nodup) (m : ℕ)
    (hm : start ∈ parentChain edges start w m) (hx : x ≠ start)
    (hns : start ∉ q.verts) :
    w ∈ parentChain edges start x (j + m) := by
  revert hq hm hx hns
  induction q generalizing m with
  | refl =>
    intro hq hm hx hns
    simp only [Nat.zero_add]
    exact mem_parentChain_self edges start _ m
  | step p hmem ih =>
    intro hq hm hx hns
    rename_i u v j'
    rw [PPath.verts_step] at hq hns
    have hq' : p.verts.Nodup := (List.nodup_append.mp hq).1
    have hns' : start ∉ p.verts := by
      intro hmem2
      exact hns (List.mem_append_left _ hmem2)
    have hu : u ∈ p.verts := end_mem_verts p
    have hx' : u ≠ start := by
      intro hcon
      subst hcon
      exact hns' hu
    have ihw := ih m hq' hm hx' hns'
    have hfuel : j' + 1 + m = (j' + m).succ := by omega
    rw [hfuel]
    have hfp : findParent edges v = some u :=
      findParent_some_of_mem_aux edges u v hmem hnd
    simp only [parentChain, ite_eq_right hx, hfp, List.mem_cons]
    exact Or.inr ihw

/-- One rewire pass over all the old vertices `ws`: flip `w`'s parent to the
    new vertex `s` (the `x` passed by `extendStar`) when `w` is admissible
    (`w` differs from `start`, `s`, and `p`; `w ∉ forbid`; `w` is within
    `radiusOf n` of `s`; `s` links to `w`) and routing through `s` is strictly
    cheaper by the current guard table. The guard table is maintained after
    each flip by shifting the rewired subtree; the parent `p`, the new vertex
    `s`, and the `forbid` chain are never reparented. -/
def rewireAux {S : Type} [DecidableEq S] (O : Oracles S)
    (costs : List (S × Int × Nat)) (radiusOf : ℕ → ℚ) (n : ℕ) (forbid : List S) (start s p : S) :
    List S → List (S × S) → List (S × S)
  | [], edges => edges
  | w :: ws, edges =>
      if w ≠ start ∧ w ≠ s ∧ w ≠ p ∧ w ∉ forbid ∧ O.cost s w ≤ radiusOf n ∧
        O.link s w = true ∧
        ccLt (ccAdd (costToCome costs s) (O.cost s w)) (costToCome costs w)
      then rewireAux O (shiftCostsPair edges start w (n + 1)
        (pairDelta (ccAdd (costToCome costs s) (O.cost s w))
          (costToCome costs w)) costs)
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
      then rewireAux O (shiftCostsPair edges start w (n + 1)
        (pairDelta (ccAdd (costToCome costs s) (O.cost s w))
          (costToCome costs w)) costs)
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
          (costs := shiftCostsPair edges start w (n + 1)
            (pairDelta (ccAdd (costToCome costs s) (O.cost s w))
              (costToCome costs w)) costs)
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
          (costs := shiftCostsPair edges0 start w (n + 1)
            (pairDelta (ccAdd (costToCome costs s) (O.cost s w))
              (costToCome costs w)) costs)
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

private theorem ppath_vert_source_or_edge_target {S : Type} {edges : List (S × S)}
    {a v : S} {k : ℕ} (p : PPath edges a v k) :
    ∀ x ∈ p.verts, x = a ∨ ∃ e ∈ edges, e.2 = x := by
  induction p with
  | refl =>
      intro x hx
      rw [PPath.verts_refl] at hx
      simp at hx
      exact Or.inl hx
  | @step w v _ _ hmem ih =>
      intro x hx
      rw [PPath.verts_step] at hx
      rw [List.mem_append] at hx
      cases hx with
      | inl hx =>
          obtain rfl | ⟨e, he, heq⟩ := ih x hx
          · exact Or.inl rfl
          · exact Or.inr ⟨e, he, heq⟩
      | inr hx =>
          simp at hx
          rw [hx]
          exact Or.inr ⟨(w, v), hmem, rfl⟩

private theorem shiftCosts_start_absent_of_source {S : Type} {edges : List (S × S)}
    {start w v : S} {j : ℕ} (q : PPath edges w v j)
    (hnostart : ∀ e ∈ edges, e.2 ≠ start) (hwne : w ≠ start) :
    start ∉ q.verts := by
  intro hmem
  obtain heq | ⟨e, he, heq⟩ := ppath_vert_source_or_edge_target q start hmem
  · exact hwne heq.symm
  · exact hnostart e he heq

private theorem ppath_verts_rev_head {S : Type} {edges : List (S × S)} {a v : S}
    {k : ℕ} (p : PPath edges a v k) : p.verts.reverse.head? = some v := by
  induction p with
  | refl => simp [PPath.verts_refl]
  | step p _ ih => simp [PPath.verts_step, List.reverse_append]

private theorem shiftCosts_pcost_of_verts_eq {S : Type} (O : Oracles S)
    {e₁ e₂ : List (S × S)} {a b : S} {k j : ℕ}
    (p : PPath e₁ a b k) (q : PPath e₂ a b j)
    (h : p.verts = q.verts) : pcost O p = pcost O q := by
  induction p generalizing j with
  | refl =>
      cases q with
      | refl => rfl
      | step q' hmem =>
          exfalso
          have hlen := congrArg List.length h
          rw [PPath.verts_refl, PPath.verts_step] at hlen
          simp only [List.length_cons, List.length_nil, List.length_append] at hlen
          rw [PPath.verts_length] at hlen
          simp at hlen
  | @step w _ _ p' hmem' ih =>
      cases q with
      | refl =>
          exfalso
          have hlen := congrArg List.length h
          rw [PPath.verts_refl, PPath.verts_step] at hlen
          simp only [List.length_cons, List.length_nil, List.length_append] at hlen
          rw [PPath.verts_length] at hlen
          simp at hlen
      | step q' hmem'' =>
          simp only [PPath.verts_step] at h
          have h' : p'.verts = q'.verts := List.append_cancel_right h
          have hlast : p'.verts.reverse.head? = q'.verts.reverse.head? := by rw [h']
          simp only [ppath_verts_rev_head] at hlast
          replace hlast := Option.some_inj.mp hlast
          subst hlast
          have ih' : pcost O p' = pcost O q' := ih _ h'
          rw [pcost_step O p' hmem', pcost_step O q' hmem'', ih']

private theorem ppath_verts_cons {S : Type} {edges : List (S × S)} {a v : S} {k : ℕ}
    (p : PPath edges a v k) : ∃ t, p.verts = a :: t := by
  induction p with
  | refl => exact ⟨[], PPath.verts_refl _⟩
  | @step _ v _ _ _ ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t ++ [v], ?_⟩
      simp [PPath.verts_step, ht]

theorem shiftCosts_exact {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (edges : List (S × S)) (start s w : S)
    (h_end : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (hnd : (edges.map Prod.snd).Nodup)
    (hnoself : ∀ e ∈ edges, e.1 ≠ e.2)
    (hnostart : ∀ e ∈ edges, e.2 ≠ start)
    (hparent : ∀ x ∈ verts, x ≠ start → ∃ u, (u, x) ∈ edges)
    (hvnd : verts.Nodup) (hstart : start ∈ verts)
    (hreach : ∀ v ∈ verts, ∃ k, Nonempty (PPath edges start v k))
    (hs : s ∈ verts) (hw : w ∈ verts) (hwne : w ≠ start) (hsw : s ≠ w)
    (hnotanc : w ∉ parentChain edges start s verts.length)
    (v : S) (hv : v ∈ verts) :
    pairVal (costToCome (shiftCosts edges start w verts.length
        (pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) s)
          (O.cost s w)) -
          pairVal (costToCome (recomputeCosts O verts edges start) w))
        (recomputeCosts O verts edges start)) v) =
      pairVal (costToCome
        (recomputeCosts O verts (replaceParent edges s w) start) v) := by
  obtain ⟨kv, hne_v⟩ := hreach v hv
  obtain ⟨pv0⟩ := hne_v
  obtain ⟨kv', pv, hpv, _⟩ := PPath.exists_simple_le O pv0
  have hcosted_v :=
    recomputeCosts_mem_of_path O verts edges start v kv' pv
  have hchar_v := pairVal_costToCome_recomputeCosts O verts edges start v
    h_end hnd hvnd hstart hv kv' pv hpv
  obtain ⟨ks, hne_s⟩ := hreach s hs
  obtain ⟨ps0⟩ := hne_s
  obtain ⟨ks', ps, hps, _⟩ := PPath.exists_simple_le O ps0
  have hcosted_s :=
    recomputeCosts_mem_of_path O verts edges start s ks' ps
  have hchar_s := pairVal_costToCome_recomputeCosts O verts edges start s
    h_end hnd hvnd hstart hs ks' ps hps
  obtain ⟨kw, hne_w⟩ := hreach w hw
  obtain ⟨pw0⟩ := hne_w
  obtain ⟨kw', pw, hpw, _⟩ := PPath.exists_simple_le O pw0
  have hchar_w := pairVal_costToCome_recomputeCosts O verts edges start w
    h_end hnd hvnd hstart hw kw' pw hpw
  have hdenoms := recomputeCosts_denoms O verts edges start
  have hmem_v : v ∈ (recomputeCosts O verts edges start).map Prod.fst :=
    hcosted_v
  have hmem_s : s ∈ (recomputeCosts O verts edges start).map Prod.fst :=
    hcosted_s
  have hden_v : 0 < (costToCome (recomputeCosts O verts edges start) v).2 :=
    denomsPos_costToCome _ _ hdenoms hmem_v
  have hden_s : 0 < (costToCome (recomputeCosts O verts edges start) s).2 :=
    denomsPos_costToCome _ _ hdenoms hmem_s
  have hne_v : (((costToCome (recomputeCosts O verts edges start) v).2 : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hden_v)
  have hne_s : (((costToCome (recomputeCosts O verts edges start) s).2 : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hden_s)
  have hd : pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) s)
        (O.cost s w)) - pairVal (costToCome (recomputeCosts O verts edges start) w)
        = (pcost O ps + O.cost s w) - pcost O pw := by
    rw [pairVal_ccAdd _ _ hne_s, hchar_s, hchar_w]
  have h_end' : ∀ e ∈ replaceParent edges s w, e.1 ∈ verts ∧ e.2 ∈ verts :=
    replaceParent_endpoints edges verts s w hs hw h_end
  have hnd' : ((replaceParent edges s w).map Prod.snd).Nodup :=
    replaceParent_nodup edges s w hnd
  by_cases hwmem : w ∈ pv.verts
  · obtain ⟨i, j, pfx, sfx, hpfx_nodup, hsfx_nodup, hsfx_sub, hpcost_split⟩ :=
      ppath_split O pv hpv hwmem
    have hpcost_pfx : pcost O pfx = pcost O pw :=
      pcost_eq_of_simple O hnd pfx pw hpfx_nodup hpw
    have hpcost_pv : pcost O pv = pcost O pw + pcost O sfx := by
      rw [hpcost_split, hpcost_pfx]
    have hL1_v := mem_parentChain_iff_mem_verts edges verts start v w
      hnd hvnd h_end hstart hv kv' pv hpv
    have hchain_mem : w ∈ parentChain edges start v verts.length :=
      hL1_v.mp hwmem
    have hLHS : pairVal (costToCome (shiftCosts edges start w verts.length
            (pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) s)
              (O.cost s w)) -
              pairVal (costToCome (recomputeCosts O verts edges start) w))
            (recomputeCosts O verts edges start)) v)
          = pcost O pv + ((pcost O ps + O.cost s w) - pcost O pw) := by
      rw [pairVal_costToCome_shiftCosts edges start w v verts.length _ _ hmem_v hne_v
        hchain_mem, hchar_v, hd]
    have hL1_s := mem_parentChain_iff_mem_verts edges verts start s w
      hnd hvnd h_end hstart hs ks' ps hps
    have hw_not_ps : w ∉ ps.verts := fun hc => hnotanc (hL1_s.mp hc)
    obtain ⟨psT, hpsT_verts⟩ :=
      ppath_replaceParent_of_notmem edges s w start s ks' ps hw_not_ps
    have hsw_mem : (s, w) ∈ replaceParent edges s w := by
      obtain ⟨u, hu⟩ := hparent w hw hwne
      exact replaceParent_mem_parent edges s w u hu
    obtain ⟨sfxT, hsfxT_verts⟩ :=
      ppath_replaceParent_of_target_ne (s := s) sfx hsfx_nodup
    obtain ⟨r, hpcost_r, hverts_r⟩ :=
      ppath_chain O (PPath.step psT hsw_mem) sfxT
    have hpcost_mid :
        pcost O (PPath.step psT hsw_mem) = pcost O psT + O.cost s w :=
      pcost_step O psT hsw_mem
    have hpcost_psT : pcost O psT = pcost O ps :=
      shiftCosts_pcost_of_verts_eq O psT ps hpsT_verts
    have hpcost_sfxT : pcost O sfxT = pcost O sfx :=
      shiftCosts_pcost_of_verts_eq O sfxT sfx hsfxT_verts
    have hpcost_r_eq :
        pcost O r = (pcost O ps + O.cost s w) + pcost O sfx := by
      rw [hpcost_r, hpcost_mid, hpcost_psT, hpcost_sfxT]
    have hmid_verts : (PPath.step psT hsw_mem).verts = psT.verts ++ [w] :=
      PPath.verts_step psT hsw_mem
    have hverts_r_eq : r.verts = (ps.verts ++ [w]) ++ sfx.verts.tail := by
      rw [hverts_r, hmid_verts, hpsT_verts, hsfxT_verts]
    obtain ⟨t_sfx, ht_sfx⟩ := ppath_verts_cons sfx
    have hsfx_tail : sfx.verts.tail = t_sfx := by simp [ht_sfx]
    have hsfx_cons_nodup : (w :: t_sfx).Nodup := by
      rw [← ht_sfx]; exact hsfx_nodup
    have hw_not_t : w ∉ t_sfx := (List.nodup_cons.mp hsfx_cons_nodup).1
    have ht_nodup : t_sfx.Nodup := (List.nodup_cons.mp hsfx_cons_nodup).2
    have hstart_not_sfx : start ∉ sfx.verts :=
      shiftCosts_start_absent_of_source sfx hnostart hwne
    have hdisj_ps_t : ∀ x ∈ ps.verts, x ∉ t_sfx := by
      intro x hx_ps hx_t
      have hx_tail : x ∈ sfx.verts.tail := by rw [hsfx_tail]; exact hx_t
      have hx_sfx : x ∈ sfx.verts := List.mem_of_mem_tail hx_tail
      have hx_pv : x ∈ pv.verts := hsfx_sub x hx_sfx
      have hx_ne_w : x ≠ w := by
        intro heq
        rw [heq] at hx_ps
        exact hw_not_ps hx_ps
      have hx_ne_start : x ≠ start := by
        intro heq
        rw [heq] at hx_sfx
        exact hstart_not_sfx hx_sfx
      obtain ⟨jpre, _, pre, _, hpre_nodup, _, _, _⟩ :=
        ppath_split O sfx hsfx_nodup hx_sfx
      have hL1_w_start := mem_parentChain_iff_mem_verts edges verts start w start
        hnd hvnd h_end hstart hw kw' pw hpw
      have hm : start ∈ parentChain edges start w verts.length :=
        hL1_w_start.mp (start_mem_verts pw)
      have hns : start ∉ pre.verts :=
        shiftCosts_start_absent_of_source pre hnostart hwne
      have hw_chain_x := mem_parentChain_of_ppath_fixed hnd pre hpre_nodup
        verts.length hm hx_ne_start hns
      obtain ⟨ix, _, pfx_x, _, hpfx_x_nodup, _, _, _⟩ :=
        ppath_split O pv hpv hx_pv
      have hx_verts : x ∈ verts :=
        PPath.verts_mem verts ps hstart (fun e he => (h_end e he).2) x hx_ps
      have hL1_x := mem_parentChain_iff_mem_verts edges verts start x start
        hnd hvnd h_end hstart hx_verts ix pfx_x hpfx_x_nodup
      have hstart_chain_x : start ∈ parentChain edges start x verts.length :=
        hL1_x.mp (start_mem_verts pfx_x)
      have hstab := parentChain_stable_le_aux edges start x verts.length
        (jpre + verts.length) hstart_chain_x (Nat.le_add_left _ _)
      have hw_chain_x' : w ∈ parentChain edges start x verts.length := by
        rw [hstab] at hw_chain_x
        exact hw_chain_x
      have hL1_s_x := mem_parentChain_iff_mem_verts edges verts start s x
        hnd hvnd h_end hstart hs ks' ps hps
      have hx_chain_s : x ∈ parentChain edges start s verts.length :=
        hL1_s_x.mp hx_ps
      have hL1_s_start := mem_parentChain_iff_mem_verts edges verts start s start
        hnd hvnd h_end hstart hs ks' ps hps
      have hstart_chain_s : start ∈ parentChain edges start s verts.length :=
        hL1_s_start.mp (start_mem_verts ps)
      have hw_chain_s : w ∈ parentChain edges start s verts.length :=
        mem_parentChain_trans edges start x w s verts.length hstart_chain_s
          hx_chain_s hw_chain_x'
      exact hnotanc hw_chain_s
    have hps_w_nodup : (ps.verts ++ [w]).Nodup := by
      apply List.Nodup.append hps _ _
      · simp
      · intro x hx_mem hcontra
        simp at hcontra
        rw [hcontra] at hx_mem
        exact hw_not_ps hx_mem
    have hdisj_outer : (ps.verts ++ [w]).Disjoint t_sfx := by
      intro x hx_mem
      rw [List.mem_append] at hx_mem
      cases hx_mem with
      | inl hx_ps => exact hdisj_ps_t x hx_ps
      | inr hx_w =>
        simp at hx_w
        rw [hx_w]
        exact hw_not_t
    have hr_nodup : r.verts.Nodup := by
      rw [hverts_r_eq, hsfx_tail]
      exact List.Nodup.append hps_w_nodup ht_nodup hdisj_outer
    have hchar_r := pairVal_costToCome_recomputeCosts O verts
      (replaceParent edges s w) start v h_end' hnd' hvnd hstart hv _ r
      hr_nodup
    rw [hLHS, hchar_r, hpcost_r_eq, hpcost_pv]
    linarith
  · have hL1 := mem_parentChain_iff_mem_verts edges verts start v w
      hnd hvnd h_end hstart hv kv' pv hpv
    have hchain_notmem : w ∉ parentChain edges start v verts.length :=
      fun hc => hwmem (hL1.mpr hc)
    obtain ⟨qv, hqv_verts⟩ :=
      ppath_replaceParent_of_notmem edges s w start v kv' pv hwmem
    have hqv_nodup : qv.verts.Nodup := by rw [hqv_verts]; exact hpv
    have hchar_v' := pairVal_costToCome_recomputeCosts O verts
      (replaceParent edges s w) start v h_end' hnd' hvnd hstart hv _ qv
      hqv_nodup
    have hpcost_qv : pcost O qv = pcost O pv :=
      shiftCosts_pcost_of_verts_eq O qv pv hqv_verts
    rw [costToCome_shiftCosts_of_notmem edges start w v verts.length _ _
      hchain_notmem, hchar_v, hchar_v', hpcost_qv]

theorem shiftCosts_denoms {S : Type} [DecidableEq S] (edges : List (S × S))
    (start w : S) (n : ℕ) (d : Rat) (costs : List (S × Int × Nat))
    (h : DenomsPos costs) :
    DenomsPos (shiftCosts edges start w n d costs) := by
  intro kv hmem
  unfold shiftCosts at hmem
  obtain ⟨e, he_mem, he_eq⟩ := List.mem_map.mp hmem
  by_cases hif : w ∈ parentChain edges start e.1 n
  · simp [hif] at he_eq
    subst he_eq
    have hpos : 0 < e.2.2 := h e he_mem
    have hden : 0 < d.den := Nat.pos_of_ne_zero (rat_den_ne_zero d)
    exact ccAdd_den_pos e.2 d hpos hden
  · simp [hif] at he_eq
    subst he_eq
    exact h e he_mem

theorem shiftCosts_pairVal_eq_recomputeCosts {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (edges : List (S × S)) (start s w : S)
    (costs : List (S × Int × Nat))
    (h_end : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (hnd : (edges.map Prod.snd).Nodup)
    (hnoself : ∀ e ∈ edges, e.1 ≠ e.2)
    (hnostart : ∀ e ∈ edges, e.2 ≠ start)
    (hparent : ∀ x ∈ verts, x ≠ start → ∃ u, (u, x) ∈ edges)
    (hvnd : verts.Nodup) (hstart : start ∈ verts)
    (hreach : ∀ v ∈ verts, ∃ k, Nonempty (PPath edges start v k))
    (hs : s ∈ verts) (hw : w ∈ verts) (hwne : w ≠ start) (hsw : s ≠ w)
    (hnotanc : w ∉ parentChain edges start s verts.length)
    (hden : DenomsPos costs)
    (hcosted : ∀ v ∈ verts, v ∈ costs.map Prod.fst)
    (heq : ∀ v ∈ verts, pairVal (costToCome costs v) =
      pairVal (costToCome (recomputeCosts O verts edges start) v))
    (v : S) (hv : v ∈ verts) :
    pairVal (costToCome (shiftCosts edges start w verts.length
        (pairVal (ccAdd (costToCome costs s) (O.cost s w)) -
          pairVal (costToCome costs w)) costs) v) =
      pairVal (costToCome
        (recomputeCosts O verts (replaceParent edges s w) start) v) := by
  have hmem_recomp : ∀ u ∈ verts, u ∈ (recomputeCosts O verts edges start).map Prod.fst := by
    intro u hu
    obtain ⟨k, ⟨p⟩⟩ := hreach u hu
    obtain ⟨k', p', hnodup, _hcost⟩ := PPath.exists_simple_le O p
    have hbell := recomputeCosts_mem_of_path O verts edges start u k' p'
    unfold recomputeCosts
    exact hbell
  have hden_recomp : DenomsPos (recomputeCosts O verts edges start) :=
    recomputeCosts_denoms O verts edges start
  have hpos_costs_s : 0 < (costToCome costs s).2 :=
    denomsPos_costToCome costs s hden (hcosted s hs)
  have hne_costs_s : ((costToCome costs s).2 : ℚ) ≠ 0 :=
    by exact_mod_cast (ne_of_gt hpos_costs_s)
  have hpos_recomp_s : 0 < (costToCome (recomputeCosts O verts edges start) s).2 :=
    denomsPos_costToCome _ s hden_recomp (hmem_recomp s hs)
  have hne_recomp_s : ((costToCome (recomputeCosts O verts edges start) s).2 : ℚ) ≠ 0 :=
    by exact_mod_cast (ne_of_gt hpos_recomp_s)
  have hpos_costs_v : 0 < (costToCome costs v).2 :=
    denomsPos_costToCome costs v hden (hcosted v hv)
  have hne_costs_v : ((costToCome costs v).2 : ℚ) ≠ 0 :=
    by exact_mod_cast (ne_of_gt hpos_costs_v)
  have hpos_recomp_v : 0 < (costToCome (recomputeCosts O verts edges start) v).2 :=
    denomsPos_costToCome _ v hden_recomp (hmem_recomp v hv)
  have hne_recomp_v : ((costToCome (recomputeCosts O verts edges start) v).2 : ℚ) ≠ 0 :=
    by exact_mod_cast (ne_of_gt hpos_recomp_v)
  have hcc_costs : pairVal (ccAdd (costToCome costs s) (O.cost s w)) =
      pairVal (costToCome costs s) + (O.cost s w : ℚ) :=
    pairVal_ccAdd (costToCome costs s) (O.cost s w) hne_costs_s
  have hcc_recomp : pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) s) (O.cost s w)) =
      pairVal (costToCome (recomputeCosts O verts edges start) s) + (O.cost s w : ℚ) :=
    pairVal_ccAdd (costToCome (recomputeCosts O verts edges start) s) (O.cost s w) hne_recomp_s
  have hdelta : (pairVal (ccAdd (costToCome costs s) (O.cost s w)) -
      pairVal (costToCome costs w)) =
      (pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) s) (O.cost s w)) -
        pairVal (costToCome (recomputeCosts O verts edges start) w)) := by
    rw [hcc_costs, hcc_recomp, heq s hs, heq w hw]
  have hexact := shiftCosts_exact O verts edges start s w h_end hnd hnoself hnostart hparent hvnd hstart hreach hs hw hwne hsw hnotanc v hv
  by_cases hmem : w ∈ parentChain edges start v verts.length
  · have hshift_costs := pairVal_costToCome_shiftCosts edges start w v verts.length
      (pairVal (ccAdd (costToCome costs s) (O.cost s w)) - pairVal (costToCome costs w))
      costs (hcosted v hv) hne_costs_v hmem
    have hshift_recomp := pairVal_costToCome_shiftCosts edges start w v verts.length
      (pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) s) (O.cost s w)) -
        pairVal (costToCome (recomputeCosts O verts edges start) w))
      (recomputeCosts O verts edges start) (hmem_recomp v hv) hne_recomp_v hmem
    calc pairVal (costToCome (shiftCosts edges start w verts.length
          (pairVal (ccAdd (costToCome costs s) (O.cost s w)) -
            pairVal (costToCome costs w)) costs) v)
        = pairVal (costToCome costs v) +
          ((pairVal (ccAdd (costToCome costs s) (O.cost s w)) -
            pairVal (costToCome costs w)) : ℚ) := hshift_costs
      _ = pairVal (costToCome (recomputeCosts O verts edges start) v) +
          ((pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) s) (O.cost s w)) -
            pairVal (costToCome (recomputeCosts O verts edges start) w)) : ℚ) := by
            rw [heq v hv, hdelta]
      _ = pairVal (costToCome (shiftCosts edges start w verts.length
          (pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) s) (O.cost s w)) -
            pairVal (costToCome (recomputeCosts O verts edges start) w))
          (recomputeCosts O verts edges start)) v) := hshift_recomp.symm
      _ = pairVal (costToCome
          (recomputeCosts O verts (replaceParent edges s w) start) v) := hexact
  · have hcost_eq : costToCome (shiftCosts edges start w verts.length
        (pairVal (ccAdd (costToCome costs s) (O.cost s w)) -
          pairVal (costToCome costs w)) costs) v = costToCome costs v :=
      costToCome_shiftCosts_of_notmem edges start w v verts.length _ costs hmem
    have hrecomp_eq : costToCome (shiftCosts edges start w verts.length
        (pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) s) (O.cost s w)) -
          pairVal (costToCome (recomputeCosts O verts edges start) w))
        (recomputeCosts O verts edges start)) v =
        costToCome (recomputeCosts O verts edges start) v :=
      costToCome_shiftCosts_of_notmem edges start w v verts.length _ _ hmem
    calc pairVal (costToCome (shiftCosts edges start w verts.length
          (pairVal (ccAdd (costToCome costs s) (O.cost s w)) -
            pairVal (costToCome costs w)) costs) v)
        = pairVal (costToCome costs v) := by rw [hcost_eq]
      _ = pairVal (costToCome (recomputeCosts O verts edges start) v) := heq v hv
      _ = pairVal (costToCome (shiftCosts edges start w verts.length
          (pairVal (ccAdd (costToCome (recomputeCosts O verts edges start) s) (O.cost s w)) -
            pairVal (costToCome (recomputeCosts O verts edges start) w))
          (recomputeCosts O verts edges start)) v) := by rw [hrecomp_eq]
      _ = pairVal (costToCome
          (recomputeCosts O verts (replaceParent edges s w) start) v) := hexact

theorem shiftCostsPair_pairVal_eq_recomputeCosts {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (edges : List (S × S)) (start s w : S)
    (costs : List (S × Int × Nat))
    (h_end : ∀ e ∈ edges, e.1 ∈ verts ∧ e.2 ∈ verts)
    (hnd : (edges.map Prod.snd).Nodup)
    (hnoself : ∀ e ∈ edges, e.1 ≠ e.2)
    (hnostart : ∀ e ∈ edges, e.2 ≠ start)
    (hparent : ∀ x ∈ verts, x ≠ start → ∃ u, (u, x) ∈ edges)
    (hvnd : verts.Nodup) (hstart : start ∈ verts)
    (hreach : ∀ v ∈ verts, ∃ k, Nonempty (PPath edges start v k))
    (hs : s ∈ verts) (hw : w ∈ verts) (hwne : w ≠ start) (hsw : s ≠ w)
    (hnotanc : w ∉ parentChain edges start s verts.length)
    (hden : DenomsPos costs)
    (hcosted : ∀ v ∈ verts, v ∈ costs.map Prod.fst)
    (heq : ∀ v ∈ verts, pairVal (costToCome costs v) =
      pairVal (costToCome (recomputeCosts O verts edges start) v))
    (v : S) (hv : v ∈ verts) :
    pairVal (costToCome (shiftCostsPair edges start w verts.length
        (pairDelta (ccAdd (costToCome costs s) (O.cost s w))
          (costToCome costs w)) costs) v) =
      pairVal (costToCome
        (recomputeCosts O verts (replaceParent edges s w) start) v) := by
  have hRat := shiftCosts_pairVal_eq_recomputeCosts O verts edges start s w costs
    h_end hnd hnoself hnostart hparent hvnd hstart hreach hs hw hwne hsw hnotanc
    hden hcosted heq v hv
  have hcosted_s : s ∈ costs.map Prod.fst := hcosted s hs
  have hcosted_w : w ∈ costs.map Prod.fst := hcosted w hw
  have hcosted_v : v ∈ costs.map Prod.fst := hcosted v hv
  have hpos_s : 0 < (costToCome costs s).2 :=
    denomsPos_costToCome costs s hden hcosted_s
  have hpos_w : 0 < (costToCome costs w).2 :=
    denomsPos_costToCome costs w hden hcosted_w
  have hpos_v : 0 < (costToCome costs v).2 :=
    denomsPos_costToCome costs v hden hcosted_v
  have hden_rat : 0 < (O.cost s w).den :=
    Nat.pos_of_ne_zero (rat_den_ne_zero (O.cost s w))
  have hpos_A : 0 < (ccAdd (costToCome costs s) (O.cost s w)).2 := by
    unfold ccAdd
    simp only
    exact Nat.mul_pos hpos_s hden_rat
  have hA_ne : (((ccAdd (costToCome costs s) (O.cost s w)).2 : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos_A
  have hB_ne : (((costToCome costs w).2 : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos_w
  have hV_ne : (((costToCome costs v).2 : Nat) : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos_v
  have hPairVal : pairVal (pairDelta (ccAdd (costToCome costs s) (O.cost s w))
      (costToCome costs w)) =
      pairVal (ccAdd (costToCome costs s) (O.cost s w)) -
        pairVal (costToCome costs w) :=
    pairVal_pairDelta _ _ hA_ne hB_ne
  have hpos_dPair : 0 < (pairDelta (ccAdd (costToCome costs s) (O.cost s w))
      (costToCome costs w)).2 := by
    unfold pairDelta
    simp only
    exact Nat.mul_pos hpos_A hpos_w
  have hdPair_ne : ((((pairDelta (ccAdd (costToCome costs s) (O.cost s w))
      (costToCome costs w)).2 : Nat)) : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt hpos_dPair
  by_cases hmem : w ∈ parentChain edges start v verts.length
  · have hPair := pairVal_costToCome_shiftCostsPair edges start w v verts.length
      (pairDelta (ccAdd (costToCome costs s) (O.cost s w)) (costToCome costs w))
      costs hcosted_v hV_ne hdPair_ne hmem
    have hRatRead := pairVal_costToCome_shiftCosts edges start w v verts.length
      (pairVal (ccAdd (costToCome costs s) (O.cost s w)) -
        pairVal (costToCome costs w)) costs hcosted_v hV_ne hmem
    rw [hPairVal] at hPair
    rw [hPair]
    rw [hRatRead] at hRat
    exact hRat
  · have hPairUn : costToCome (shiftCostsPair edges start w verts.length
        (pairDelta (ccAdd (costToCome costs s) (O.cost s w))
          (costToCome costs w)) costs) v = costToCome costs v :=
      costToCome_shiftCostsPair_of_notmem _ _ _ _ _ _ _ hmem
    have hRatUn : costToCome (shiftCosts edges start w verts.length
        (pairVal (ccAdd (costToCome costs s) (O.cost s w)) -
          pairVal (costToCome costs w)) costs) v = costToCome costs v :=
      costToCome_shiftCosts_of_notmem _ _ _ _ _ _ _ hmem
    rw [hPairUn]
    rw [hRatUn] at hRat
    exact hRat

/-- Extend the tree by one steered sample: steer `s` from its nearest vertex
    `u` to `x`, and if `s` is free, `x` is free, the nearest edge links, `x`
    is fresh, and `x` has a parent `p` (parent search falls back to `u`),
    add `x` and `(p, x)`, rewire over the old vertices
    at the pre-insertion count `verts.length` while refusing `p`'s ancestor
    chain, judging flips by the post-insertion recomputed guard table
    (maintained by subtree shifts after each flip inside `rewireAux`,
    agreeing in rational value with per-flip recomputation); the final costs
    are the recomputation over the new edges. A sample that is not collision
    free is skipped unchanged; the source algorithms sample only
    collision-free configurations. -/
def extendStar {S : Type} [DecidableEq S] (O : Oracles S) (verts : List S)
    (edges : List (S × S)) (costs : List (S × (Int × Nat))) (radiusOf : ℕ → ℚ)
    (start s : S) : List S × List (S × S) × List (S × (Int × Nat)) :=
  let u := nearest O verts start s
  let x := O.steer u s
  if O.free s = true ∧ O.free x = true ∧ O.link u x = true ∧ x ∉ verts then
    match chooseParent O verts costs radiusOf u x with
    | none => (verts, edges, costs)
    | some p =>
        let verts' := x :: verts
        let edges0 := (p, x) :: edges
        let forbid := parentChain edges0 start p verts.length
        let edges' :=
          rewireAux O (recomputeCosts O verts' edges0 start) radiusOf verts.length
            forbid start x p verts edges0
        let costs' := recomputeCosts O verts' edges' start
        (verts', edges', costs')
  else (verts, edges, costs)

theorem extendStar_invar {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (edges : List (S × S)) (costs : List (S × (Int × Nat)))
    (radiusOf : ℕ → ℚ) (start s : S)
    (h : StarInvar O verts edges costs start) :
    StarInvar O (extendStar O verts edges costs radiusOf start s).1
      (extendStar O verts edges costs radiusOf start s).2.1
      (extendStar O verts edges costs radiusOf start s).2.2 start := by
  unfold extendStar
  dsimp only
  set u := nearest O verts start s with hu
  set x := O.steer u s with hx
  by_cases hgate : O.free s = true ∧ O.free x = true ∧ O.link u x = true ∧ x ∉ verts
  · rw [ite_eq_left hgate]
    cases hcp : chooseParent O verts costs radiusOf u x with
    | none =>
        exact h
    | some p =>
        have hpmem : p ∈ candidates O verts radiusOf u x :=
          chooseParent_mem O verts costs radiusOf u x p hcp
        have hmem := (mem_candidates O verts radiusOf u x p).mp hpmem
        obtain ⟨hp_verts, _, _⟩ := hmem
        have hx_fresh : x ∉ verts := hgate.2.2.2
        have hx_ne : x ≠ start := fun heq => hx_fresh (heq.symm ▸ h.start_mem)
        have hp_ne_x : p ≠ x := fun heq => hx_fresh (heq ▸ hp_verts)
        have hx_new : x ∈ x :: verts := List.mem_cons_self
        have hp_new : p ∈ x :: verts := List.mem_cons_of_mem x hp_verts
        have hws : ∀ w ∈ verts, w ∈ x :: verts := fun w hw =>
          List.mem_cons_of_mem x hw
        have h_end0 : ∀ e ∈ (p, x) :: edges,
            e.1 ∈ x :: verts ∧ e.2 ∈ x :: verts := by
          intro e he
          simp only [List.mem_cons] at he
          cases he with
          | inl heq =>
              subst heq
              exact ⟨hp_new, hx_new⟩
          | inr hmem =>
              have hend := h.edges_endpoints e hmem
              exact ⟨List.mem_cons_of_mem x hend.1,
                List.mem_cons_of_mem x hend.2⟩
        have h_nodup0 : (((p, x) :: edges).map Prod.snd).Nodup := by
          have hx_nmem : x ∉ edges.map Prod.snd := by
            intro hcontra
            obtain ⟨e, he_mem, he_eq⟩ := List.mem_map.mp hcontra
            have hend := (h.edges_endpoints e he_mem).2
            rw [he_eq] at hend
            exact hx_fresh hend
          show (x :: edges.map Prod.snd).Nodup
          rw [List.nodup_cons]
          exact ⟨hx_nmem, h.targets_nodup⟩
        have h_noself0 : ∀ e ∈ (p, x) :: edges, e.1 ≠ e.2 := by
          intro e he
          simp only [List.mem_cons] at he
          cases he with
          | inl heq =>
              subst heq
              exact hp_ne_x
          | inr hmem => exact h.no_self e hmem
        have h_nestart0 : ∀ e ∈ (p, x) :: edges, e.2 ≠ start := by
          intro e he
          simp only [List.mem_cons] at he
          cases he with
          | inl heq =>
              subst heq
              exact hx_ne
          | inr hmem => exact h.target_ne_start e hmem
        have h_parent0 : ∀ v ∈ x :: verts, v ≠ start →
            ∃ u, (u, v) ∈ (p, x) :: edges := by
          intro v hv hne
          simp only [List.mem_cons] at hv
          cases hv with
          | inl heq =>
              subst heq
              exact ⟨p, List.mem_cons_self⟩
          | inr hmem =>
              obtain ⟨u, hu⟩ := h.has_parent v hmem hne
              exact ⟨u, List.mem_cons_of_mem (p, x) hu⟩
        have hrew := rewireAux_invar O
          (recomputeCosts O (x :: verts) ((p, x) :: edges) start)
          radiusOf verts.length
          (parentChain ((p, x) :: edges) start p verts.length)
          start x p
          (x :: verts) verts ((p, x) :: edges)
          hx_new hp_new hws h_end0 h_nodup0 h_noself0 h_nestart0 h_parent0 hx_ne
        obtain ⟨h_end', h_nodup', h_noself', h_nestart', h_parent'⟩ := hrew
        have h_verts_nodup : (x :: verts).Nodup :=
          List.nodup_cons.mpr ⟨hx_fresh, h.verts_nodup⟩
        have hpx_mem : (p, x) ∈ (p, x) :: edges := List.mem_cons_self
        have hreach : ∀ v ∈ x :: verts, ∃ (k : ℕ), Nonempty
            (PPath (rewireAux O
              (recomputeCosts O (x :: verts) ((p, x) :: edges) start)
              radiusOf verts.length
              (parentChain ((p, x) :: edges) start p verts.length) start x p
              verts
              ((p, x) :: edges)) start v k) := by
          have h_all_costed : ∀ v ∈ verts, v ∈ costs.map Prod.fst := by
            intro v hv
            obtain ⟨k, ⟨hp⟩⟩ := h.reachable v hv
            obtain ⟨k', p', hnodup, _⟩ := PPath.exists_simple_le O hp
            have hu : start ∈ verts := h.start_mem
            have htgt : ∀ e ∈ edges, e.2 ∈ verts := fun e he => (h.edges_endpoints e he).2
            have hndv : verts.Nodup := h.verts_nodup
            have hbf := recomputeCosts_mem_of_path O verts edges start v k' p'
            have hmem : v ∈ (recomputeCosts O verts edges start).map Prod.fst := by
              simpa [recomputeCosts] using hbf
            rwa [← h.costs_eq] at hmem
          have hcosted : ∀ x ∈ parentChain edges start p verts.length, x ∈ costs.map Prod.fst := by
            intro x hx
            exact h_all_costed x (parentChain_mem_verts edges verts start p verts.length
              h.edges_endpoints hp_verts x hx)
          have hstart_chain : start ∈ parentChain edges start p verts.length :=
            parentChain_has_start O verts edges costs start p h.targets_nodup h.no_self h.has_parent
              h.edges_endpoints h.costs_eq h.start_mem h.verts_nodup
              h.target_ne_start hcosted hp_verts
          have hchain_eq : parentChain ((p, x) :: edges) start p verts.length =
              parentChain edges start p verts.length :=
            parentChain_cons_eq edges verts start (p, x) p verts.length
              h.edges_endpoints hp_verts hx_fresh
          have hmem_cons : start ∈ parentChain ((p, x) :: edges) start p verts.length := by
            rw [hchain_eq]
            exact hstart_chain
          obtain ⟨kp, pp, hpp_chain⟩ :=
            parentChain_ppath_verts ((p, x) :: edges) start p verts.length hmem_cons
          have hverts : ∀ y ∈ (PPath.step pp hpx_mem).verts,
              y = x ∨ y ∈ parentChain ((p, x) :: edges) start p verts.length := by
            intro y hy
            have hy' : y ∈ pp.verts ++ [x] := hy
            rw [List.mem_append] at hy'
            cases hy' with
            | inl hmem_verts =>
                exact Or.inr (hpp_chain y hmem_verts)
            | inr hmem_x =>
                simp only [List.mem_singleton] at hmem_x
                exact Or.inl hmem_x
          have hmain := ppath_rewireAux_all O
            (recomputeCosts O (x :: verts) ((p, x) :: edges) start)
            radiusOf verts.length
            (parentChain ((p, x) :: edges) start p verts.length)
            start x p verts ((p, x) :: edges) (kp + 1)
            (PPath.step pp hpx_mem) hverts
          intro v hv
          simp only [List.mem_cons] at hv
          cases hv with
          | inl heq =>
              subst heq
              obtain ⟨k', hk'⟩ := hmain x (kp + 1) (PPath.step pp hpx_mem)
              exact ⟨k', hk'⟩
          | inr hmem_v =>
              obtain ⟨k, ⟨pv⟩⟩ := h.reachable v hmem_v
              obtain ⟨pv0⟩ := ppath_mono edges ((p, x) :: edges)
                (fun e he => List.mem_cons_of_mem (p, x) he) start v k pv
              obtain ⟨k', hk'⟩ := hmain v k pv0
              exact ⟨k', hk'⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact List.mem_cons_of_mem x h.start_mem
        · exact h_verts_nodup
        · exact h_end'
        · exact h_nodup'
        · exact h_noself'
        · exact h_nestart'
        · exact h_parent'
        · exact hreach
        · rfl
  · rw [ite_eq_right hgate]
    dsimp only
    exact h

/-- The extended tree still prices `start` at `(0, 1)`. -/
theorem extendStar_cost_start {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (edges : List (S × S)) (costs : List (S × (Int × Nat)))
    (radiusOf : ℕ → ℚ) (start s : S)
    (h : StarInvar O verts edges costs start) :
    costToCome (extendStar O verts edges costs radiusOf start s).2.2 start = (0, 1) := by
  unfold extendStar
  dsimp only
  set u := nearest O verts start s with hu
  set x := O.steer u s with hx
  by_cases hgate : O.free s = true ∧ O.free x = true ∧ O.link u x = true ∧ x ∉ verts
  · rw [ite_eq_left hgate]
    cases hcp : chooseParent O verts costs radiusOf u x with
    | none =>
        dsimp only
        rw [h.costs_eq]
        exact recomputeCosts_cost_start O verts edges start h.target_ne_start
    | some p =>
        dsimp only
        have hinv := extendStar_invar O verts edges costs radiusOf start s h
        have hne := hinv.target_ne_start
        unfold extendStar at hne
        rw [ite_eq_left hgate] at hne
        rw [hcp] at hne
        dsimp only at hne
        exact rewireAux_cost_start O _ _ _ _ _ _ _ _ _ _ hne
  · rw [ite_eq_right hgate]
    dsimp only
    rw [h.costs_eq]
    exact recomputeCosts_cost_start O verts edges start h.target_ne_start

/-- The RRT* fold over the sample list, threading vertices, edges, and the
    cost table: every sample is processed by `extendStar`, whose gate
    rejects a steered point already among `verts`. -/
def rrtStarAux {S : Type} [DecidableEq S] (O : Oracles S) (radiusOf : ℕ → ℚ)
    (start : S) (verts : List S) (edges : List (S × S))
    (costs : List (S × (Int × Nat))) : List S → List S × List (S × S) ×
      List (S × (Int × Nat))
  | [] => (verts, edges, costs)
  | s :: ss =>
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
      (let (verts', edges', costs') :=
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
      dsimp only
      have h' := extendStar_invar O verts edges costs radiusOf start s h
      exact ih _ _ _ h'
/-- Output vertices come from the input tree or steered samples. -/
theorem rrtStarAux_subset {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (verts : List S)
    (edges : List (S × S)) (costs : List (S × (Int × Nat))) (v : S)
    (hmem : v ∈ (rrtStarAux O radiusOf start verts edges costs samples).1) :
    v ∈ verts ∨ ∃ s ∈ samples, ∃ u, v = O.steer u s := by
  induction samples generalizing verts edges costs with
  | nil =>
      simp only [rrtStarAux_nil] at hmem
      exact Or.inl hmem
  | cons s ss ih =>
      rw [rrtStarAux_cons] at hmem
      dsimp only at hmem
      have hor := ih
        (verts := (extendStar O verts edges costs radiusOf start s).1)
        (edges := (extendStar O verts edges costs radiusOf start s).2.1)
        (costs := (extendStar O verts edges costs radiusOf start s).2.2)
        hmem
      cases hor with
      | inl hv =>
          unfold extendStar at hv
          dsimp only at hv
          by_cases hcond : (O.free s = true ∧
            O.free (O.steer (nearest O verts start s) s) = true ∧
            O.link (nearest O verts start s)
              (O.steer (nearest O verts start s) s) = true ∧
            O.steer (nearest O verts start s) s ∉ verts)
          · rw [ite_eq_left hcond] at hv
            cases hcp : chooseParent O verts costs radiusOf
              (nearest O verts start s) (O.steer (nearest O verts start s) s) with
            | none =>
                simp only [hcp] at hv
                exact Or.inl hv
            | some p =>
                simp only [hcp] at hv
                simp only [List.mem_cons] at hv
                cases hv with
                | inl heq =>
                    exact Or.inr ⟨s, List.mem_cons_self,
                      nearest O verts start s, heq⟩
                | inr hv2 => exact Or.inl hv2
          · rw [ite_eq_right hcond] at hv
            dsimp only at hv
            exact Or.inl hv
      | inr hs =>
          obtain ⟨s', hs', u, heq⟩ := hs
          exact Or.inr ⟨s', List.mem_cons_of_mem s hs', u, heq⟩

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
  have hbf := recomputeCosts_mem_of_path O verts edges start v k' p'
  simpa [recomputeCosts] using hbf

/-- Output vertices are `start` or steered samples. -/
theorem rrtStar_verts_subset {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (v : S)
    (hmem : v ∈ (rrtStar O radiusOf start samples).1) :
    v = start ∨ ∃ s ∈ samples, ∃ u, v = O.steer u s := by
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


/-- Fold invariant: reachability from `start` is preserved by growth. -/
theorem rrtAux_reachable {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (ss : List C) :
    ∀ (verts : List C) (edges : List (C × C)),
      (∀ v ∈ verts, ∃ k, Nonempty (PPath edges start v k)) →
      ∀ v ∈ (rrtAux O start ss verts edges).1,
        ∃ k, Nonempty (PPath (rrtAux O start ss verts edges).2 start v k) := by
  induction ss with
  | nil =>
      intro verts edges hreach v hv
      rw [rrtAux_nil] at hv ⊢
      exact hreach v hv
  | cons s ss ih =>
      intro verts edges hreach v hv
      rw [rrtAux_cons] at hv ⊢
      by_cases hcond :
        O.free s = true ∧ O.free (O.steer (nearest O verts start s) s) = true ∧
          O.link (nearest O verts start s) (O.steer (nearest O verts start s) s) = true ∧
          O.steer (nearest O verts start s) s ∉ verts
      · rw [ite_eq_left hcond] at hv ⊢
        have hsub : ∀ e ∈ edges,
            e ∈ (nearest O verts start s,
              O.steer (nearest O verts start s) s) :: edges := by
          intro e he
          exact List.mem_cons_of_mem _ he
        have hstep : ∀ w ∈ O.steer (nearest O verts start s) s :: verts,
            ∃ k, Nonempty (PPath ((nearest O verts start s,
              O.steer (nearest O verts start s) s) :: edges) start w k) := by
          intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw
          · by_cases hne : verts = []
            · subst hne
              have hu_eq : nearest O ([] : List C) start s = start := rfl
              have hmem : (start,
                  O.steer (nearest O ([] : List C) start s) s) ∈
                  (nearest O ([] : List C) start s,
                    O.steer (nearest O ([] : List C) start s) s) ::
                    edges := by
                rw [hu_eq]
                exact List.mem_cons_self
              exact ⟨1, ⟨PPath.step (PPath.refl start) hmem⟩⟩
            · have hu : nearest O verts start s ∈ verts :=
                nearest_mem O hne start s
              obtain ⟨k, ⟨p⟩⟩ := hreach _ hu
              have p' : PPath ((nearest O verts start s,
                  O.steer (nearest O verts start s) s) :: edges) start
                  (nearest O verts start s) k :=
                PPath.transfer hsub p
              exact ⟨k + 1, ⟨PPath.step p' List.mem_cons_self⟩⟩
          · obtain ⟨k, ⟨p⟩⟩ := hreach w hw
            exact ⟨k, ⟨PPath.transfer hsub p⟩⟩
        exact ih _ _ hstep v hv
      · rw [ite_eq_right hcond] at hv ⊢
        exact ih _ _ hreach v hv

/-- Every RRT vertex is reachable from `start` along RRT edges. -/
theorem rrt_reachable {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) :
    ∀ v ∈ (rrt O start samples).1,
      ∃ k, Nonempty (PPath (rrt O start samples).2 start v k) := by
  have h0 : ∀ v ∈ ([start] : List C),
      ∃ k, Nonempty (PPath ([] : List (C × C)) start v k) := by
    intro v hv
    simp at hv
    subst hv
    exact ⟨0, ⟨PPath.refl _⟩⟩
  have h := rrtAux_reachable O start samples [start] [] h0
  exact h

/-- The RRT output assembles the shared star invariant with recomputed costs. -/
theorem rrt_starInvar {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) :
    StarInvar O (rrt O start samples).1 (rrt O start samples).2
      (recomputeCosts O (rrt O start samples).1 (rrt O start samples).2 start)
      start := by
  refine ⟨rrt_start_mem O start samples, rrt_verts_nodup O start samples, ?_,
    rrt_targets_nodup O start samples, ?_, ?_, ?_, ?_, rfl⟩
  · intro e he
    exact rrt_edge_endpoints O start samples e he
  · intro e he
    exact rrt_edge_fst_ne_snd O start samples e he
  · intro e he
    exact rrt_edge_snd_ne_start O start samples e he
  · intro v hv hne
    have hmem := rrt_edge_of_mem O start samples v hv hne
    rw [List.mem_map] at hmem
    obtain ⟨e, he, heq⟩ := hmem
    cases e with
    | mk u w =>
      simp only at heq
      subst heq
      exact ⟨u, he⟩
  · intro v hv
    exact rrt_reachable O start samples v hv

/-- Parent chains with vertices in the RRT vertex list visit no vertex twice. -/
theorem rrt_acyclic {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) (l : List C)
    (hchain : IsParentChain (rrt O start samples).2 l)
    (hverts : ∀ v ∈ l, v ∈ (rrt O start samples).1) : l.Nodup := by
  have hinv' : StarInvar O (rrt O start samples).1 (rrt O start samples).2
      (recomputeCosts O (rrt O start samples).1 (rrt O start samples).2 start)
      start :=
    rrt_starInvar O start samples
  have hcosted : ∀ x ∈ l,
      x ∈ (recomputeCosts O (rrt O start samples).1 (rrt O start samples).2
        start).map Prod.fst := by
    intro x hx
    exact all_costed_of_invar O _ _ _ start hinv' x (hverts x hx)
  exact parentChain_nodup O _ _ start _ hinv'.start_mem hinv'.verts_nodup
    (fun e he => (hinv'.edges_endpoints e he).2) hinv'.targets_nodup
    hinv'.no_self hinv'.target_ne_start hinv'.costs_eq l hchain hcosted

end Cslib.Planning.MotionPlanning.SamplingPlanners
