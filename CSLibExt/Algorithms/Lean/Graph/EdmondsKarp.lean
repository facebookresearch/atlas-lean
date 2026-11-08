/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Certified augmenting-path maximum flow

This module implements a finite integral maximum-flow reference algorithm on
`Fin n`. It calls the landed executable breadth-first search on the transposed
residual graph, then reconstructs a shortest path by following residual edges
whose distance to the sink decreases by one. The outer loop stops immediately
when no augmenting path remains.

Each iteration augments by the minimum residual capacity on a shortest path,
as in Edmonds and Karp, *Theoretical Improvements in Algorithmic Efficiency
for Network Flow Problems* (1972). For distinct source and sink, integrality
implies that a successful iteration raises the flow value by at least one, so
the algorithm performs at most one more search than the total capacity leaving
the source. Equal endpoints return the zero flow before fuel is computed. Its `Flow`
representation is a nested persistent closure: after `i` augmentations, one
lookup traverses up to `i` earlier closures and their paths, each of length at
most `V`. Under unit-cost natural/integer arithmetic, constant-time evaluation
of the input capacity function, and the expected hash-map cost model, a
residual adjacency-list computation costs
`O((i + 1) * V^2)`. BFS on the on-demand transposed residual graph costs
conservatively `O((i + 1) * V^4)`, while distance-descent reconstruction and
the bottleneck scan cost `O((i + 1) * V^3)`. Thus, for source capacity `C`, a
conservative implementation-level account is
`O(∑ i ∈ [0, C], (i + 1) * V^4)`, hence
`O((C + 1)^2 * V^4)`. This informal bound is not a mechanically verified cost
theorem. The implementation does not claim the textbook `O(V E^2)`
Edmonds-Karp bound.

Flows are integer-valued skew-symmetric matrices. The upper bound
`flow u v ≤ capacity u v`, together with skew symmetry and the reverse
upper bound, supplies both directed capacity bounds. Parallel arcs are
represented by adding their capacities in the matrix.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.EdmondsKarp

open DirectedAdjacency
open BreadthFirstSearch
open scoped BigOperators

/-- An integral skew-flow matrix on `Fin n`. -/
abbrev Flow (n : Nat) := Fin n → Fin n → Int

/-- Net flow leaving a vertex. -/
def flowValue {n : Nat} (source : Fin n) (flow : Flow n) : Int :=
  ∑ target, flow source target

/-- Feasibility for the skew-symmetric integral-flow representation. -/
def IsFeasible {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source sink : Fin n) (flow : Flow n) : Prop :=
  (∀ u v, flow u v = -flow v u) ∧
  (∀ u v, flow u v ≤ (capacity u v : Int)) ∧
  ∀ v, v ≠ source → v ≠ sink → flowValue v flow = 0

/-- The zero skew-flow. -/
def zeroFlow (n : Nat) : Flow n := fun _ _ => 0

/-- The zero skew-flow is feasible for every natural capacity matrix. -/
theorem zeroFlow_feasible {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source sink : Fin n) : IsFeasible capacity source sink (zeroFlow n) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [zeroFlow]
  · intro u v
    simp [zeroFlow]
  · intro v _ _
    simp [flowValue, zeroFlow]

/-- Both directed capacity bounds follow from skew symmetry. -/
theorem IsFeasible.capacity_bounds {n : Nat}
    {capacity : Fin n → Fin n → Nat} {source sink : Fin n}
    {flow : Flow n} (feasible : IsFeasible capacity source sink flow)
    (u v : Fin n) :
    -(capacity v u : Int) ≤ flow u v ∧ flow u v ≤ (capacity u v : Int) := by
  constructor
  · rw [feasible.1 u v]
    have := feasible.2.1 v u
    omega
  · exact feasible.2.1 u v

/-- The residual graph contains exactly the ordered pairs with positive residual capacity. -/
def residualGraph {n : Nat} (capacity : Fin n → Fin n → Nat)
    (flow : Flow n) : DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency u := (List.finRange n).filter fun v => decide (flow u v < capacity u v)

/-- Residual adjacency is exactly strict slack in the directed capacity bound. -/
@[simp]
theorem residualGraph_edge_iff {n : Nat}
    (capacity : Fin n → Fin n → Nat) (flow : Flow n) (u v : Fin n) :
    (residualGraph capacity flow).Edge u v ↔ flow u v < (capacity u v : Int) := by
  simp [residualGraph, DirectedAdjacency.Edge]

/-- A duplicate-free, nonempty directed path with specified endpoints. -/
def IsPath {V : Type*} (graph : DirectedAdjacency V)
    (source sink : V) (path : List V) : Prop :=
  path.IsChainFromTo graph.Edge source sink ∧ path.Nodup

private theorem find?_some_of_mem {V : Type*} (predicate : V → Bool)
    {values : List V} {value : V} (member : value ∈ values)
    (accepts : predicate value = true) :
    ∃ found, values.find? predicate = some found := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      by_cases headAccepted : predicate head = true
      · exact ⟨head, by simp [List.find?, headAccepted]⟩
      · have headRejected : predicate head = false := by
          cases result : predicate head
          · rfl
          · exact False.elim (headAccepted result)
        rcases member with rfl | member
        · contradiction
        · obtain ⟨found, foundSpec⟩ := induction member
          exact ⟨found, by simpa [List.find?, headRejected] using foundSpec⟩

private theorem shortest_chain_nodup {V : Type*}
    (graph : DirectedAdjacency V) (source sink : V) (length : Nat)
    {path : List V} (chain : path.IsChainFromTo graph.Edge source sink)
    (pathLength : path.length = length + 1)
    (minimal : ∀ shorter, graph.Walk shorter source sink → length ≤ shorter) :
    path.Nodup := by
  by_contra duplicates
  obtain ⟨shorterPath, shorterChain, shorterLength⟩ :=
    chain.exists_length_lt_of_not_nodup duplicates
  have shorterPositive := shorterChain.length_pos
  let shorter := shorterPath.length - 1
  have shorterPathLength : shorterPath.length = shorter + 1 := by
    dsimp [shorter]
    omega
  have shorterWalk : graph.Walk shorter source sink :=
    shorterChain.relatesInSteps shorterPathLength
  have := minimal shorter shorterWalk
  omega

/-- Reconstruct a path by following strictly decreasing distance labels. -/
def pathFromDistances {V : Type*} [BEq V]
    (graph : DirectedAdjacency V) (distance : V → Option Nat) (sink : V) :
    Nat → V → Option (List V)
  | 0, current => if current == sink then some [current] else none
  | remaining + 1, current =>
      match (graph.adjacency current).find? fun next => distance next == some remaining with
      | none => none
      | some next =>
          (pathFromDistances graph distance sink remaining next).map (current :: ·)

/-- Successful distance-guided reconstruction produces a path of the labelled length. -/
theorem pathFromDistances_sound {V : Type*} [BEq V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (distance : V → Option Nat) (sink : V)
    {remaining : Nat} {current : V} {path : List V}
    (result : pathFromDistances graph distance sink remaining current = some path) :
    path.IsChainFromTo graph.Edge current sink ∧ path.length = remaining + 1 := by
  induction remaining generalizing current path with
  | zero =>
      simp only [pathFromDistances] at result
      split at result
      · rename_i equal
        have current_eq_sink : current = sink := by simpa using equal
        subst sink
        simp at result
        subst path
        simp
      · contradiction
  | succ remaining induction =>
      simp only [pathFromDistances] at result
      cases nextResult : (graph.adjacency current).find?
          (fun next => distance next == some remaining) with
      | none => simp [nextResult] at result
      | some next =>
          cases pathResult : pathFromDistances graph distance sink remaining next with
          | none => simp [nextResult, pathResult] at result
          | some tail =>
              have path_eq : current :: tail = path := by
                simpa [nextResult, pathResult] using result
              subst path
              have edge : graph.Edge current next :=
                List.mem_of_find?_eq_some nextResult
              have tailSpec := induction pathResult
              exact ⟨tailSpec.1.cons edge, by simp [tailSpec.2]⟩

private theorem pathFromDistances_present {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (sink : Fin n) {current : Fin n}
    {remaining : Nat}
    (distanceSpec : (bfs graph.transpose sink).distance current = some remaining) :
    ∃ path, pathFromDistances graph (bfs graph.transpose sink).distance sink
      remaining current = some path := by
  induction remaining generalizing current with
  | zero =>
      have shortest :=
        (distance_eq_some_iff_shortest graph.transpose sink current 0).mp distanceSpec
      have current_eq_sink : current = sink := by
        exact (DirectedAdjacency.walk_zero_iff.mp shortest.1).symm
      subst current
      simp [pathFromDistances]
  | succ remaining induction =>
      have shortest :=
        (distance_eq_some_iff_shortest graph.transpose sink current (remaining + 1)).mp
          distanceSpec
      have forwardWalk : graph.Walk (remaining + 1) current sink :=
        DirectedAdjacency.walk_transpose_iff.mp shortest.1
      obtain ⟨next, edge, nextWalk⟩ :=
        DirectedAdjacency.walk_succ_iff.mp forwardWalk
      have nextDistance :
          (bfs graph.transpose sink).distance next = some remaining := by
        apply (distance_eq_some_iff_shortest graph.transpose sink next remaining).mpr
        refine ⟨DirectedAdjacency.walk_transpose_iff.mpr nextWalk, ?_⟩
        intro shorter shorterWalk
        have forwardShorter : graph.Walk shorter next sink :=
          DirectedAdjacency.walk_transpose_iff.mp shorterWalk
        have currentWalk : graph.Walk (shorter + 1) current sink :=
          DirectedAdjacency.walk_succ_iff.mpr ⟨next, edge, forwardShorter⟩
        have reverseCurrentWalk : graph.transpose.Walk (shorter + 1) sink current :=
          DirectedAdjacency.walk_transpose_iff.mpr currentWalk
        have := shortest.2 (shorter + 1) reverseCurrentWalk
        omega
      have accepted :
          ((fun vertex => (bfs graph.transpose sink).distance vertex == some remaining)
            next) = true := by
        simp [nextDistance]
      obtain ⟨found, foundResult⟩ :=
        find?_some_of_mem
          (fun vertex => (bfs graph.transpose sink).distance vertex == some remaining)
          edge accepted
      have foundDistance :
          (bfs graph.transpose sink).distance found = some remaining := by
        simpa using List.find?_some foundResult
      obtain ⟨foundPath, foundPathResult⟩ := induction foundDistance
      refine ⟨current :: foundPath, ?_⟩
      simp [pathFromDistances, foundResult, foundPathResult]

/-- A shortest residual path reconstructed from executable BFS distances. -/
def shortestPath {n : Nat} (graph : DirectedAdjacency (Fin n))
    (source sink : Fin n) : Option (List (Fin n)) :=
  let search := bfs graph.transpose sink
  match search.distance source with
  | none => none
  | some distance => pathFromDistances graph search.distance sink distance source

/-- A returned shortest path is a nodup directed path with the BFS distance. -/
theorem shortestPath_sound {n : Nat} {graph : DirectedAdjacency (Fin n)}
    {source sink : Fin n} {path : List (Fin n)}
    (result : shortestPath graph source sink = some path) :
    IsPath graph source sink path ∧
      ∃ distance, (bfs graph source).distance sink = some distance ∧
        path.length = distance + 1 := by
  simp only [shortestPath] at result
  split at result
  · contradiction
  · rename_i distance distanceSpec
    have pathSpec := pathFromDistances_sound graph _ sink result
    have reverseShortest :=
      (distance_eq_some_iff_shortest graph.transpose sink source distance).mp distanceSpec
    have shortestWalk : graph.Walk distance source sink :=
      DirectedAdjacency.walk_transpose_iff.mp reverseShortest.1
    have minimal : ∀ shorter, graph.Walk shorter source sink → distance ≤ shorter := by
      intro shorter walk
      exact reverseShortest.2 shorter (DirectedAdjacency.walk_transpose_iff.mpr walk)
    have nodup := shortest_chain_nodup graph source sink distance pathSpec.1 pathSpec.2 minimal
    refine ⟨⟨pathSpec.1, nodup⟩, distance, ?_, pathSpec.2⟩
    exact (distance_eq_some_iff_shortest graph source sink distance).mpr
      ⟨shortestWalk, minimal⟩

/-- Residual reachability is equivalent to returning a shortest path. -/
theorem shortestPath_present_iff_reachable {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (source sink : Fin n) :
    (∃ path, shortestPath graph source sink = some path) ↔ graph.Reachable source sink := by
  constructor
  · rintro ⟨path, result⟩
    obtain ⟨pathSpec, distance, distanceSpec, pathLength⟩ :=
      shortestPath_sound result
    exact (reachable_iff_exists_walk).mpr
      ⟨distance, pathSpec.1.relatesInSteps pathLength⟩
  · intro reachable
    have reverseReachable : graph.transpose.Reachable sink source :=
      DirectedAdjacency.reachable_transpose_iff.mpr reachable
    obtain ⟨distance, distanceSpec⟩ :=
      (distance_present_iff_reachable graph.transpose sink source).mpr reverseReachable
    obtain ⟨path, pathResult⟩ :=
      pathFromDistances_present graph sink distanceSpec
    simp only [shortestPath]
    rw [distanceSpec]
    exact ⟨path, pathResult⟩

/-- No returned path is equivalent to absence of residual reachability. -/
theorem shortestPath_eq_none_iff_not_reachable {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (source sink : Fin n) :
    shortestPath graph source sink = none ↔ ¬ graph.Reachable source sink := by
  rw [← shortestPath_present_iff_reachable]
  cases shortestPath graph source sink <;> simp

/-- Consecutive ordered pairs in a list. -/
def pathEdges {V : Type*} : List V → List (V × V)
  | [] | [_] => []
  | first :: second :: rest => (first, second) :: pathEdges (second :: rest)

private theorem pathEdges_cons {V : Type*} (first second : V) (rest : List V) :
    pathEdges (first :: second :: rest) =
      (first, second) :: pathEdges (second :: rest) := rfl

/-- Residual capacity of an ordered pair in the skew-flow representation. -/
def residualAmount {n : Nat} (capacity : Fin n → Fin n → Nat)
    (flow : Flow n) (source target : Fin n) : Int :=
  (capacity source target : Int) - flow source target

/-- Minimum residual capacity along a nontrivial path, and zero on shorter lists. -/
def pathBottleneck {n : Nat} (capacity : Fin n → Fin n → Nat)
    (flow : Flow n) : List (Fin n) → Int
  | [] | [_] => 0
  | first :: second :: [] => residualAmount capacity flow first second
  | first :: second :: third :: rest =>
      min (residualAmount capacity flow first second)
        (pathBottleneck capacity flow (second :: third :: rest))

/-- Skew unit-flow contribution of one oriented edge. -/
def localDelta {V : Type*} [DecidableEq V]
    (first second source target : V) : Int :=
  (if source = first ∧ target = second then 1 else 0) -
    if source = second ∧ target = first then 1 else 0

/-- Sum of skew unit-flow contributions along a path. -/
def edgeDelta {V : Type*} [DecidableEq V] : List V → V → V → Int
  | [] | [_] => fun _ _ => 0
  | first :: second :: rest => fun source target =>
      localDelta first second source target +
        edgeDelta (second :: rest) source target

/-- Add `amount` along each path edge and subtract it on reverse entries. -/
def augment {n : Nat} (flow : Flow n) (path : List (Fin n))
    (amount : Int) : Flow n :=
  fun source target => flow source target + amount * edgeDelta path source target

private theorem localDelta_swap {V : Type*} [DecidableEq V]
    (first second u v : V) :
    localDelta first second v u = -localDelta first second u v := by
  unfold localDelta
  by_cases huv : u = first ∧ v = second <;>
    by_cases hvu : u = second ∧ v = first <;>
      simp [huv, hvu, and_comm]

private theorem edgeDelta_swap {V : Type*} [DecidableEq V]
    (path : List V) (u v : V) :
    edgeDelta path v u = -edgeDelta path u v := by
  induction path with
  | nil => simp [edgeDelta]
  | cons first rest induction =>
      cases rest with
      | nil => simp [edgeDelta]
      | cons second tail =>
          simp only [edgeDelta]
          rw [localDelta_swap, induction]
          omega

private theorem mem_vertices_of_mem_pathEdges {V : Type*} {path : List V}
    {u v : V} (member : (u, v) ∈ pathEdges path) : u ∈ path ∧ v ∈ path := by
  induction path with
  | nil => simp [pathEdges] at member
  | cons first rest induction =>
      cases rest with
      | nil => simp [pathEdges] at member
      | cons second tail =>
          simp only [pathEdges, List.mem_cons, Prod.mk.injEq] at member
          rcases member with ⟨rfl, rfl⟩ | member
          · simp
          · have vertices := induction member
            exact ⟨by simp [vertices.1], by simp [vertices.2]⟩

private theorem edgeDelta_zero_of_not_mem {V : Type*} [DecidableEq V]
    {path : List V} {vertex other : V} (absent : vertex ∉ path) :
    edgeDelta path vertex other = 0 ∧ edgeDelta path other vertex = 0 := by
  induction path with
  | nil => simp [edgeDelta]
  | cons first rest induction =>
      cases rest with
      | nil => simp [edgeDelta]
      | cons second tail =>
          have absentParts : vertex ≠ first ∧ vertex ≠ second ∧ vertex ∉ tail := by
            simpa using absent
          have firstNe := absentParts.1
          have secondNe := absentParts.2.1
          have restAbsent : vertex ∉ second :: tail := by
            simpa using absentParts.2
          have tailResult := induction restAbsent
          simp [edgeDelta, localDelta, firstNe, secondNe, tailResult]

private theorem edgeDelta_eq_one_of_mem {V : Type*} [DecidableEq V]
    {path : List V} (nodup : path.Nodup) {u v : V}
    (member : (u, v) ∈ pathEdges path) : edgeDelta path u v = 1 := by
  induction path with
  | nil => simp [pathEdges] at member
  | cons first rest induction =>
      cases rest with
      | nil => simp [pathEdges] at member
      | cons second tail =>
          have nodupParts := List.nodup_cons.mp nodup
          have tailNodup := nodupParts.2
          simp only [pathEdges, List.mem_cons, Prod.mk.injEq] at member
          rcases member with headMember | member
          · have uEq : u = first := headMember.1
            have vEq : v = second := headMember.2
            subst u
            subst v
            have firstAbsent : first ∉ second :: tail := nodupParts.1
            have tailZero := edgeDelta_zero_of_not_mem (other := second) firstAbsent
            have distinct : first ≠ second := fun equal =>
              firstAbsent (by simp [equal])
            simp [edgeDelta, localDelta, distinct, tailZero.1]
          · have vertices := mem_vertices_of_mem_pathEdges member
            have firstNeU : first ≠ u := fun equal =>
              nodupParts.1 (equal ▸ vertices.1)
            have firstNeV : first ≠ v := fun equal =>
              nodupParts.1 (equal ▸ vertices.2)
            have tailResult := induction tailNodup member
            simp [edgeDelta, localDelta, Ne.symm firstNeU,
              Ne.symm firstNeV, tailResult]

private theorem edgeDelta_nonpos_of_not_mem {V : Type*} [DecidableEq V]
    {path : List V} (nodup : path.Nodup) {u v : V}
    (notMember : (u, v) ∉ pathEdges path) : edgeDelta path u v ≤ 0 := by
  induction path with
  | nil => simp [edgeDelta]
  | cons first rest induction =>
      cases rest with
      | nil => simp [edgeDelta]
      | cons second tail =>
          have nodupParts := List.nodup_cons.mp nodup
          have notHead : (u, v) ≠ (first, second) := by
            intro equal
            exact notMember (by simp [pathEdges, equal])
          have notTail : (u, v) ∉ pathEdges (second :: tail) := by
            intro member
            exact notMember (by simp [pathEdges, member])
          have tailBound := induction nodupParts.2 notTail
          by_cases reverseHead : u = second ∧ v = first
          · have uEq : u = second := reverseHead.1
            have vEq : v = first := reverseHead.2
            subst u
            subst v
            have firstAbsent : first ∉ second :: tail := nodupParts.1
            have tailZero := edgeDelta_zero_of_not_mem (other := second) firstAbsent
            have distinct : second ≠ first := fun equal =>
              firstAbsent (by simp [equal])
            simp [edgeDelta, localDelta, distinct, tailZero.2]
          · have notForward : ¬ (u = first ∧ v = second) := by
              intro forward
              exact notHead (Prod.ext forward.1 forward.2)
            simpa [edgeDelta, localDelta, notForward, reverseHead] using tailBound

private theorem edgeDelta_eq_zero_or_neg_one_of_not_mem {V : Type*}
    [DecidableEq V] {path : List V} (nodup : path.Nodup) {u v : V}
    (notMember : (u, v) ∉ pathEdges path) :
    edgeDelta path u v = 0 ∨ edgeDelta path u v = -1 := by
  by_cases reverseMember : (v, u) ∈ pathEdges path
  · right
    have reverseDelta := edgeDelta_eq_one_of_mem nodup reverseMember
    have swap := edgeDelta_swap path u v
    omega
  · left
    have forwardBound := edgeDelta_nonpos_of_not_mem nodup notMember
    have reverseBound := edgeDelta_nonpos_of_not_mem nodup reverseMember
    have swap := edgeDelta_swap path u v
    omega

private theorem edge_of_mem_pathEdges {V : Type*} {graph : DirectedAdjacency V}
    {source sink u v : V} {path : List V}
    (chain : path.IsChainFromTo graph.Edge source sink)
    (member : (u, v) ∈ pathEdges path) : graph.Edge u v := by
  induction chain using List.IsChainFromTo.head_induction_on with
  | h_refl => simp [pathEdges] at member
  | @h_head first second last rest edge chain induction =>
      cases rest with
      | nil => exact False.elim (chain.ne_nil rfl)
      | cons head tail =>
          have headEq : head = second := chain.head_eq
          subst head
          simp only [pathEdges, List.mem_cons, Prod.mk.injEq] at member
          rcases member with ⟨rfl, rfl⟩ | member
          · exact edge
          · exact induction member

private theorem localDelta_sum {n : Nat} (first second vertex : Fin n) :
    (∑ target, localDelta first second vertex target) =
      (if vertex = first then 1 else 0) - if vertex = second then 1 else 0 := by
  classical
  unfold localDelta
  simp only [Finset.sum_sub_distrib]
  by_cases firstEq : vertex = first <;> by_cases secondEq : vertex = second
  · subst first
    subst second
    simp
  · subst first
    simp [secondEq]
  · subst second
    simp [firstEq]
  · simp [firstEq, secondEq]

private theorem edgeDelta_sum {n : Nat} {path : List (Fin n)}
    {source sink : Fin n} (chain : path.IsChainFromTo
      (fun _ _ => True) source sink) (vertex : Fin n) :
    (∑ target, edgeDelta path vertex target) =
      (if vertex = source then 1 else 0) - if vertex = sink then 1 else 0 := by
  induction chain using List.IsChainFromTo.head_induction_on with
  | h_refl => simp [edgeDelta]
  | @h_head first second last rest _ chain induction =>
      cases rest with
      | nil => exact False.elim (chain.ne_nil rfl)
      | cons head tail =>
          have headEq : head = second := chain.head_eq
          subst head
          simp only [edgeDelta, Finset.sum_add_distrib, localDelta_sum, induction]
          omega

private theorem chain_true_of_chain {V : Type*} {relation : V → V → Prop}
    {path : List V} {source sink : V}
    (chain : path.IsChainFromTo relation source sink) :
    path.IsChainFromTo (fun _ _ => True) source sink := by
  exact ⟨chain.isChain.imp fun _ _ _ => trivial, chain.ne_nil,
    chain.head_eq, chain.getLast_eq⟩

private theorem pathBottleneck_le_of_mem {n : Nat}
    (capacity : Fin n → Fin n → Nat) (flow : Flow n)
    {path : List (Fin n)} {u v : Fin n}
    (member : (u, v) ∈ pathEdges path) :
    pathBottleneck capacity flow path ≤ residualAmount capacity flow u v := by
  induction path with
  | nil => simp [pathEdges] at member
  | cons first rest induction =>
      cases rest with
      | nil => simp [pathEdges] at member
      | cons second tail =>
          cases tail with
          | nil =>
              rw [pathEdges_cons, show pathEdges [second] = [] from rfl,
                List.mem_singleton] at member
              cases member
              exact Int.le_refl _
          | cons third remaining =>
              rw [pathEdges_cons, List.mem_cons] at member
              rcases member with member | member
              · cases member
                exact min_le_left _ _
              · exact le_trans (min_le_right _ _) (induction member)

private theorem pathBottleneck_nonneg_of_edges {n : Nat}
    (capacity : Fin n → Fin n → Nat) (flow : Flow n)
    (path : List (Fin n))
    (positive : ∀ u v, (u, v) ∈ pathEdges path →
      0 < residualAmount capacity flow u v) :
    0 ≤ pathBottleneck capacity flow path := by
  induction path with
  | nil => simp [pathBottleneck]
  | cons first rest induction =>
      cases rest with
      | nil => simp [pathBottleneck]
      | cons second tail =>
          cases tail with
          | nil =>
              exact le_of_lt (positive first second (by simp [pathEdges]))
          | cons third remaining =>
              apply le_min
              · exact le_of_lt (positive first second (by simp [pathEdges]))
              · apply induction
                intro u v member
                apply positive u v
                rw [pathEdges_cons, List.mem_cons]
                exact Or.inr member

private theorem pathBottleneck_pos_of_edges {n : Nat}
    (capacity : Fin n → Fin n → Nat) (flow : Flow n)
    (path : List (Fin n)) (nontrivial : pathEdges path ≠ [])
    (positive : ∀ u v, (u, v) ∈ pathEdges path →
      0 < residualAmount capacity flow u v) :
    0 < pathBottleneck capacity flow path := by
  induction path with
  | nil => contradiction
  | cons first rest induction =>
      cases rest with
      | nil => contradiction
      | cons second tail =>
          cases tail with
          | nil => exact positive first second (by simp [pathEdges])
          | cons third remaining =>
              apply lt_min
              · exact positive first second (by simp [pathEdges])
              · apply induction
                · simp [pathEdges]
                · intro u v member
                  apply positive u v
                  rw [pathEdges_cons, List.mem_cons]
                  exact Or.inr member

private theorem pathEdges_ne_nil_of_chain {V : Type*} {relation : V → V → Prop}
    {path : List V} {source sink : V}
    (chain : path.IsChainFromTo relation source sink)
    (source_ne_sink : source ≠ sink) : pathEdges path ≠ [] := by
  induction chain using List.IsChainFromTo.head_induction_on with
  | h_refl => exact False.elim (source_ne_sink rfl)
  | @h_head first second last rest _ chain induction =>
      cases rest with
      | nil => exact False.elim (chain.ne_nil rfl)
      | cons head tail => simp [pathEdges]

/-- A residual source-to-sink path has a positive integral bottleneck. -/
theorem pathBottleneck_pos {n : Nat}
    (capacity : Fin n → Fin n → Nat) (flow : Flow n)
    {source sink : Fin n} (source_ne_sink : source ≠ sink)
    {path : List (Fin n)}
    (pathSpec : IsPath (residualGraph capacity flow) source sink path) :
    0 < pathBottleneck capacity flow path := by
  apply pathBottleneck_pos_of_edges capacity flow path
    (pathEdges_ne_nil_of_chain pathSpec.1 source_ne_sink)
  intro u v member
  have residualEdge := edge_of_mem_pathEdges pathSpec.1 member
  rw [residualGraph_edge_iff] at residualEdge
  unfold residualAmount
  omega

private theorem sum_mul_left {n : Nat} (amount : Int) (term : Fin n → Int) :
    (∑ target, amount * term target) = amount * ∑ target, term target := by
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => simp
  | @insert target targets absent induction =>
      simp [absent, induction, mul_add]

/-- Augmenting within every path-edge residual bound preserves feasibility. -/
theorem augment_feasible {n : Nat}
    (capacity : Fin n → Fin n → Nat) (source sink : Fin n)
    (flow : Flow n) (feasible : IsFeasible capacity source sink flow)
    (path : List (Fin n)) (pathSpec : path.Nodup) (amount : Int)
    (amount_nonneg : 0 ≤ amount)
    (amount_le_residual : ∀ u v, (u, v) ∈ pathEdges path →
      amount ≤ residualAmount capacity flow u v)
    (chain : path.IsChainFromTo (fun _ _ => True) source sink) :
    IsFeasible capacity source sink (augment flow path amount) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    change flow u v + amount * edgeDelta path u v =
      -(flow v u + amount * edgeDelta path v u)
    rw [feasible.1 u v, edgeDelta_swap path v u]
    simp [mul_neg, neg_add_rev, add_comm]
  · intro u v
    by_cases member : (u, v) ∈ pathEdges path
    · rw [augment, edgeDelta_eq_one_of_mem pathSpec member]
      have bound := amount_le_residual u v member
      unfold residualAmount at bound
      omega
    · have deltaCases :=
        edgeDelta_eq_zero_or_neg_one_of_not_mem pathSpec member
      have capacityBound := feasible.2.1 u v
      simp only [augment]
      rcases deltaCases with deltaZero | deltaNegOne
      · rw [deltaZero]
        simp only [mul_zero, add_zero]
        exact capacityBound
      · rw [deltaNegOne]
        simp only [mul_neg, mul_one]
        omega
  · intro vertex vertex_ne_source vertex_ne_sink
    unfold flowValue augment
    rw [Finset.sum_add_distrib, sum_mul_left, edgeDelta_sum chain]
    have conservation := feasible.2.2 vertex vertex_ne_source vertex_ne_sink
    change (∑ target, flow vertex target) = 0 at conservation
    simpa [vertex_ne_source, vertex_ne_sink] using conservation

/-- Augmentation raises source flow value by exactly the supplied amount. -/
theorem flowValue_augment {n : Nat} (source sink : Fin n)
    (source_ne_sink : source ≠ sink) (flow : Flow n)
    (path : List (Fin n)) (amount : Int)
    (chain : path.IsChainFromTo (fun _ _ => True) source sink) :
    flowValue source (augment flow path amount) = flowValue source flow + amount := by
  unfold flowValue augment
  rw [Finset.sum_add_distrib, sum_mul_left, edgeDelta_sum chain]
  simp [source_ne_sink]

/-- Augmenting by a residual path's bottleneck preserves feasibility. -/
theorem augment_pathBottleneck_feasible {n : Nat}
    (capacity : Fin n → Fin n → Nat) (source sink : Fin n)
    (flow : Flow n) (feasible : IsFeasible capacity source sink flow)
    (path : List (Fin n))
    (pathSpec : IsPath (residualGraph capacity flow) source sink path) :
    IsFeasible capacity source sink
      (augment flow path (pathBottleneck capacity flow path)) := by
  apply augment_feasible capacity source sink flow feasible path pathSpec.2
  · apply pathBottleneck_nonneg_of_edges
    intro u v member
    have residualEdge := edge_of_mem_pathEdges pathSpec.1 member
    rw [residualGraph_edge_iff] at residualEdge
    unfold residualAmount
    omega
  · intro u v member
    exact pathBottleneck_le_of_mem capacity flow member
  · exact chain_true_of_chain pathSpec.1

/-- Perform one bottleneck augmentation when a residual path exists. -/
def step {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source sink : Fin n) (flow : Flow n) : Flow n :=
  match shortestPath (residualGraph capacity flow) source sink with
  | none => flow
  | some path => augment flow path (pathBottleneck capacity flow path)

/-- One algorithm step either preserves flow value or strictly raises it. -/
theorem flowValue_step {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source sink : Fin n) (source_ne_sink : source ≠ sink) (flow : Flow n) :
    flowValue source (step capacity source sink flow) = flowValue source flow ∨
      flowValue source flow < flowValue source (step capacity source sink flow) := by
  unfold step
  split
  · exact Or.inl rfl
  · rename_i path pathResult
    apply Or.inr
    rw [flowValue_augment source sink source_ne_sink flow path
      (pathBottleneck capacity flow path)
      (chain_true_of_chain (shortestPath_sound pathResult).1.1)]
    have positive := pathBottleneck_pos capacity flow source_ne_sink
      (shortestPath_sound pathResult).1
    omega

/-- Iterate bottleneck augmentation, stopping for equal endpoints or no residual path. -/
def run {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source sink : Fin n) : Nat → Flow n → Flow n
  | 0, flow => flow
  | fuel + 1, flow =>
      if source = sink then flow
      else
        match shortestPath (residualGraph capacity flow) source sink with
        | none => flow
        | some path => run capacity source sink fuel
            (augment flow path (pathBottleneck capacity flow path))

/-- Iteration never decreases source flow value when source and sink differ. -/
theorem flowValue_le_run {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source sink : Fin n) (source_ne_sink : source ≠ sink)
    (fuel : Nat) (flow : Flow n) :
    flowValue source flow ≤ flowValue source (run capacity source sink fuel flow) := by
  induction fuel generalizing flow with
  | zero => simp [run]
  | succ fuel induction =>
      simp only [run, source_ne_sink, ↓reduceIte]
      cases result : shortestPath (residualGraph capacity flow) source sink with
      | none =>
          change flowValue source flow ≤ flowValue source flow
          exact Int.le_refl _
      | some path =>
          change flowValue source flow ≤
            flowValue source
              (run capacity source sink fuel
                (augment flow path (pathBottleneck capacity flow path)))
          have progress := flowValue_augment source sink source_ne_sink flow path
            (pathBottleneck capacity flow path)
            (chain_true_of_chain (shortestPath_sound result).1.1)
          have positive := pathBottleneck_pos capacity flow source_ne_sink
            (shortestPath_sound result).1
          have laterProgress := induction
            (augment flow path (pathBottleneck capacity flow path))
          omega

/-- Total capacity leaving the source. -/
def sourceCapacity {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source : Fin n) : Nat :=
  ∑ target, capacity source target

/-- The executable bottleneck-augmentation flow, or zero when the endpoints coincide. -/
def edmondsKarp {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source sink : Fin n) : Flow n :=
  if source = sink then zeroFlow n
  else run capacity source sink (sourceCapacity capacity source + 1) (zeroFlow n)

private theorem step_feasible {n : Nat}
    (capacity : Fin n → Fin n → Nat) (source sink : Fin n)
    (flow : Flow n) (feasible : IsFeasible capacity source sink flow) :
    IsFeasible capacity source sink (step capacity source sink flow) := by
  unfold step
  split
  · exact feasible
  · rename_i path pathResult
    exact augment_pathBottleneck_feasible capacity source sink flow feasible path
      (shortestPath_sound pathResult).1

private theorem run_feasible {n : Nat}
    (capacity : Fin n → Fin n → Nat) (source sink : Fin n)
    (fuel : Nat) (flow : Flow n) (feasible : IsFeasible capacity source sink flow) :
    IsFeasible capacity source sink (run capacity source sink fuel flow) := by
  induction fuel generalizing flow with
  | zero => exact feasible
  | succ fuel induction =>
      by_cases source_eq_sink : source = sink
      · simpa [run, source_eq_sink] using feasible
      · simp only [run, source_eq_sink, ↓reduceIte]
        cases result : shortestPath (residualGraph capacity flow) source sink with
        | none => exact feasible
        | some path =>
            exact induction (augment flow path (pathBottleneck capacity flow path))
              (augment_pathBottleneck_feasible capacity source sink flow feasible path
                (shortestPath_sound result).1)

/-- The returned flow satisfies skew symmetry, capacity bounds, and conservation. -/
theorem edmondsKarp_feasible {n : Nat}
    (capacity : Fin n → Fin n → Nat) (source sink : Fin n) :
    IsFeasible capacity source sink (edmondsKarp capacity source sink) := by
  unfold edmondsKarp
  split
  · exact zeroFlow_feasible capacity source sink
  · exact run_feasible capacity source sink _ _
      (zeroFlow_feasible capacity source sink)

/-- The iteration stops immediately when no augmenting path exists. -/
theorem run_eq_of_no_path {n : Nat}
    (capacity : Fin n → Fin n → Nat) (source sink : Fin n)
    (flow : Flow n)
    (noPath : shortestPath (residualGraph capacity flow) source sink = none) :
    ∀ fuel, run capacity source sink fuel flow = flow := by
  intro fuel
  cases fuel <;> simp [run, noPath]

private theorem run_value_lower_bound_of_final_path {n : Nat}
    (capacity : Fin n → Fin n → Nat) (source sink : Fin n)
    (source_ne_sink : source ≠ sink) (fuel : Nat) (flow : Flow n)
    (finalPath : ∃ path, shortestPath
      (residualGraph capacity (run capacity source sink fuel flow)) source sink = some path) :
    flowValue source flow + (fuel : Int) ≤
      flowValue source (run capacity source sink fuel flow) := by
  induction fuel generalizing flow with
  | zero => simp [run]
  | succ fuel induction =>
      simp only [run, source_ne_sink, ↓reduceIte] at finalPath ⊢
      cases pathResult : shortestPath (residualGraph capacity flow) source sink with
      | none =>
          simp only [pathResult] at finalPath ⊢
          rcases finalPath with ⟨path, impossible⟩
          contradiction
      | some path =>
          simp only [pathResult] at finalPath ⊢
          change ∃ final, shortestPath
            (residualGraph capacity
              (run capacity source sink fuel
                (augment flow path (pathBottleneck capacity flow path)))) source sink =
                some final at finalPath
          have later := induction
            (augment flow path (pathBottleneck capacity flow path)) finalPath
          have progress := flowValue_augment source sink source_ne_sink flow path
            (pathBottleneck capacity flow path)
            (chain_true_of_chain (shortestPath_sound pathResult).1.1)
          have positive := pathBottleneck_pos capacity flow source_ne_sink
            (shortestPath_sound pathResult).1
          omega

/-- Every feasible flow is bounded by total capacity leaving the source. -/
theorem flowValue_le_sourceCapacity {n : Nat}
    {capacity : Fin n → Fin n → Nat} {source sink : Fin n}
    {flow : Flow n} (feasible : IsFeasible capacity source sink flow) :
    flowValue source flow ≤ (sourceCapacity capacity source : Int) := by
  unfold flowValue sourceCapacity
  have bound : (∑ target, flow source target) ≤
      ∑ target, (capacity source target : Int) :=
    Finset.sum_le_sum fun target _ => feasible.2.1 source target
  have castSum : ((∑ target, capacity source target : Nat) : Int) =
      ∑ target, (capacity source target : Int) := by
    induction (Finset.univ : Finset (Fin n)) using Finset.induction with
    | empty => simp
    | @insert target targets absent induction => simp [absent, induction]
  rw [castSum]
  exact bound

/-- The final residual graph has no source-to-sink path. -/
theorem edmondsKarp_no_augmenting_path {n : Nat}
    (capacity : Fin n → Fin n → Nat) {source sink : Fin n}
    (source_ne_sink : source ≠ sink) :
    ¬ (residualGraph capacity (edmondsKarp capacity source sink)).Reachable source sink := by
  simp only [edmondsKarp, source_ne_sink, ↓reduceIte]
  rw [← shortestPath_eq_none_iff_not_reachable]
  by_contra pathRemains
  cases pathResult : shortestPath
      (residualGraph capacity
        (run capacity source sink (sourceCapacity capacity source + 1) (zeroFlow n)))
      source sink with
  | none => exact pathRemains pathResult
  | some path =>
      have finalPath : ∃ path, shortestPath
          (residualGraph capacity
            (run capacity source sink (sourceCapacity capacity source + 1) (zeroFlow n)))
          source sink = some path :=
        ⟨path, pathResult⟩
      have valueBound := run_value_lower_bound_of_final_path
        capacity source sink source_ne_sink
        (sourceCapacity capacity source + 1) (zeroFlow n) finalPath
      have feasible := edmondsKarp_feasible capacity source sink
      simp only [edmondsKarp, source_ne_sink, ↓reduceIte] at feasible
      have bound := flowValue_le_sourceCapacity feasible
      change flowValue source (zeroFlow n) +
          ((sourceCapacity capacity source + 1 : Nat) : Int) ≤
        flowValue source
          (run capacity source sink (sourceCapacity capacity source + 1) (zeroFlow n))
          at valueBound
      have zeroValue : flowValue source (zeroFlow n) = 0 := by
        simp [flowValue, zeroFlow]
      rw [zeroValue, zero_add] at valueBound
      omega

/-- Capacity of a directed cut in the skew-flow representation. -/
def cutCapacity {n : Nat} (capacity : Fin n → Fin n → Nat)
    (cut : Finset (Fin n)) : Int :=
  ∑ u ∈ cut, ∑ v ∈ (Finset.univ : Finset (Fin n)) \ cut, (capacity u v : Int)

private theorem cutFlow_eq {n : Nat} {source sink : Fin n}
    {flow : Flow n} (skew : ∀ u v, flow u v = -flow v u)
    (conservation : ∀ v, v ≠ source → v ≠ sink → flowValue v flow = 0)
    (cut : Finset (Fin n)) (sourceMem : source ∈ cut) (sinkNotMem : sink ∉ cut) :
    flowValue source flow =
      ∑ u ∈ cut, ∑ v ∈ (Finset.univ : Finset (Fin n)) \ cut, flow u v := by
  have internalZero : ∑ u ∈ cut, ∑ v ∈ cut, flow u v = 0 := by
    have negSelf : (∑ u ∈ cut, ∑ v ∈ cut, flow u v) =
        -(∑ u ∈ cut, ∑ v ∈ cut, flow u v) := by
      calc
        (∑ u ∈ cut, ∑ v ∈ cut, flow u v) =
            ∑ u ∈ cut, ∑ v ∈ cut, -flow v u := by
              apply Finset.sum_congr rfl
              intro u _
              apply Finset.sum_congr rfl
              intro v _
              exact skew u v
        _ = -(∑ u ∈ cut, ∑ v ∈ cut, flow v u) := by simp
        _ = -(∑ u ∈ cut, ∑ v ∈ cut, flow u v) := by
          rw [Finset.sum_comm]
    omega
  have sumDivergence : ∑ u ∈ cut, flowValue u flow = flowValue source flow := by
    rw [← Finset.add_sum_erase cut (fun u => flowValue u flow) sourceMem]
    have restZero : ∑ u ∈ cut.erase source, flowValue u flow = 0 := by
      apply Finset.sum_eq_zero
      intro vertex member
      rw [Finset.mem_erase] at member
      exact conservation vertex member.1 (fun equal => sinkNotMem (equal ▸ member.2))
    rw [restZero, add_zero]
  rw [← sumDivergence]
  unfold flowValue
  calc
    (∑ u ∈ cut, ∑ target, flow u target) =
        ∑ u ∈ cut,
          ((∑ v ∈ cut, flow u v) +
            ∑ v ∈ (Finset.univ : Finset (Fin n)) \ cut, flow u v) := by
          apply Finset.sum_congr rfl
          intro u _
          have split := Finset.sum_sdiff (f := fun v => flow u v)
            (Finset.subset_univ cut)
          rw [add_comm]
          exact split.symm
    _ = (∑ u ∈ cut, ∑ v ∈ cut, flow u v) +
        ∑ u ∈ cut,
          ∑ v ∈ (Finset.univ : Finset (Fin n)) \ cut, flow u v := by
          rw [Finset.sum_add_distrib]
    _ = ∑ u ∈ cut,
          ∑ v ∈ (Finset.univ : Finset (Fin n)) \ cut, flow u v := by
          rw [internalZero, zero_add]

/-- Weak duality for every feasible skew flow and source-sink cut. -/
theorem flowValue_le_cutCapacity {n : Nat}
    (capacity : Fin n → Fin n → Nat) (source sink : Fin n)
    (flow : Flow n) (feasible : IsFeasible capacity source sink flow)
    (cut : Finset (Fin n)) (sourceMem : source ∈ cut) (sinkNotMem : sink ∉ cut) :
    flowValue source flow ≤ cutCapacity capacity cut := by
  rw [cutFlow_eq feasible.1 feasible.2.2 cut sourceMem sinkNotMem]
  unfold cutCapacity
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact feasible.2.1 u v

/-- Vertices reachable from the source in the residual graph of a flow. -/
def residualCut {n : Nat} (capacity : Fin n → Fin n → Nat)
    (flow : Flow n) (source : Fin n) : Finset (Fin n) :=
  (bfs (residualGraph capacity flow) source).order.toFinset

private theorem source_mem_residualCut {n : Nat}
    (capacity : Fin n → Fin n → Nat) (flow : Flow n) (source : Fin n) :
    source ∈ residualCut capacity flow source := by
  simp only [residualCut, List.mem_toFinset]
  rw [order_mem_iff_reachable]
  exact Relation.ReflTransGen.refl

private theorem not_mem_residualCut_of_not_reachable {n : Nat}
    (capacity : Fin n → Fin n → Nat) (flow : Flow n) (source vertex : Fin n)
    (notReachable : ¬ (residualGraph capacity flow).Reachable source vertex) :
    vertex ∉ residualCut capacity flow source := by
  simp only [residualCut, List.mem_toFinset]
  rw [order_mem_iff_reachable]
  exact notReachable

private theorem residualCut_saturated {n : Nat}
    (capacity : Fin n → Fin n → Nat) (flow : Flow n) (source : Fin n)
    (feasible : ∀ u v, flow u v ≤ (capacity u v : Int))
    {u v : Fin n} (uMem : u ∈ residualCut capacity flow source)
    (vNotMem : v ∉ residualCut capacity flow source) :
    flow u v = (capacity u v : Int) := by
  have uReachable : (residualGraph capacity flow).Reachable source u := by
    rw [residualCut, List.mem_toFinset, order_mem_iff_reachable] at uMem
    exact uMem
  have notResidual : ¬ flow u v < (capacity u v : Int) := by
    intro residual
    have edge : (residualGraph capacity flow).Edge u v :=
      (residualGraph_edge_iff capacity flow u v).mpr residual
    have vReachable : (residualGraph capacity flow).Reachable source v :=
      Relation.ReflTransGen.tail uReachable edge
    apply vNotMem
    rw [residualCut, List.mem_toFinset, order_mem_iff_reachable]
    exact vReachable
  exact le_antisymm (feasible u v) (not_lt.mp notResidual)

/-- The returned flow value equals the capacity of its residual-reachable cut. -/
theorem edmondsKarp_minCut {n : Nat}
    (capacity : Fin n → Fin n → Nat) {source sink : Fin n}
    (source_ne_sink : source ≠ sink) :
    flowValue source (edmondsKarp capacity source sink) =
      cutCapacity capacity
        (residualCut capacity (edmondsKarp capacity source sink) source) := by
  let flow := edmondsKarp capacity source sink
  let cut := residualCut capacity flow source
  have feasible := edmondsKarp_feasible capacity source sink
  have sourceMem : source ∈ cut := source_mem_residualCut capacity flow source
  have sinkNotMem : sink ∉ cut := not_mem_residualCut_of_not_reachable
    capacity flow source sink (edmondsKarp_no_augmenting_path capacity source_ne_sink)
  rw [cutFlow_eq feasible.1 feasible.2.2 cut sourceMem sinkNotMem]
  unfold cutCapacity
  apply Finset.sum_congr rfl
  intro u uMem
  apply Finset.sum_congr rfl
  intro v vMem
  exact residualCut_saturated capacity flow source feasible.2.1 uMem
    (Finset.mem_sdiff.mp vMem).2

/-- Every feasible integral flow has value at most the returned flow. -/
theorem edmondsKarp_maximal {n : Nat}
    (capacity : Fin n → Fin n → Nat) {source sink : Fin n}
    (source_ne_sink : source ≠ sink) (candidate : Flow n)
    (candidate_feasible : IsFeasible capacity source sink candidate) :
    flowValue source candidate ≤ flowValue source (edmondsKarp capacity source sink) := by
  let cut := residualCut capacity (edmondsKarp capacity source sink) source
  have sourceMem : source ∈ cut :=
    source_mem_residualCut capacity (edmondsKarp capacity source sink) source
  have sinkNotMem : sink ∉ cut := not_mem_residualCut_of_not_reachable
    capacity (edmondsKarp capacity source sink) source sink
      (edmondsKarp_no_augmenting_path capacity source_ne_sink)
  calc
    flowValue source candidate ≤ cutCapacity capacity cut :=
      flowValue_le_cutCapacity capacity source sink candidate candidate_feasible
        cut sourceMem sinkNotMem
    _ = flowValue source (edmondsKarp capacity source sink) :=
      (edmondsKarp_minCut capacity source_ne_sink).symm

end Cslib.Algorithms.Lean.EdmondsKarp
