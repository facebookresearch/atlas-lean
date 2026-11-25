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

/-- **Flow.** A flow on $n$ vertices, labelled $0, \dots, n-1$, is an integer matrix: it assigns
an integer $f(u, v)$ to each ordered pair of vertices $(u, v)$.

No condition is imposed here; skew symmetry, capacity bounds and conservation are required by
feasibility. -/
abbrev Flow (n : Nat) := Fin n → Fin n → Int

/-- **Flow value.** For a flow $f$ on $n$ vertices and a vertex $s$, the value of $f$ at $s$ is
the net flow leaving $s$, namely the integer $\sum_v f(s, v)$, where $v$ runs over all vertices. -/
def flowValue {n : Nat} (source : Fin n) (flow : Flow n) : Int :=
  ∑ target, flow source target

/-- **Feasible flow.** Let $c$ be a capacity function assigning a natural number $c(u, v)$ to
each ordered pair of vertices, and let $s$ and $t$ be vertices. A flow $f$ is feasible for $c$,
$s$ and $t$ when it is skew symmetric, $f(u, v) = -f(v, u)$ for all $u$ and $v$; it respects
the capacities, $f(u, v) \le c(u, v)$ for all $u$ and $v$; and it is conserved: for every vertex
$v$ other than $s$ and $t$, the net flow $\sum_w f(v, w)$ leaving $v$ is $0$. -/
def IsFeasible {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source sink : Fin n) (flow : Flow n) : Prop :=
  (∀ u v, flow u v = -flow v u) ∧
  (∀ u v, flow u v ≤ (capacity u v : Int)) ∧
  ∀ v, v ≠ source → v ≠ sink → flowValue v flow = 0

/-- **Zero flow.** The zero flow on the vertices $\{0, \dots, n - 1\}$ is the integer-valued matrix
$f$ with $f(u, v) = 0$ for all vertices $u$ and $v$. -/
def zeroFlow (n : Nat) : Flow n := fun _ _ => 0

/-- **The zero flow is feasible.** For every capacity matrix $c$ with natural-number entries on the
vertices $\{0, \dots, n - 1\}$ and all vertices $s$ and $t$, the zero flow is feasible for $c$ with
source $s$ and sink $t$. -/
theorem zeroFlow_feasible {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source sink : Fin n) : IsFeasible capacity source sink (zeroFlow n) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [zeroFlow]
  · intro u v
    simp [zeroFlow]
  · intro v _ _
    simp [flowValue, zeroFlow]

/-- **Two-sided capacity bounds for a feasible flow.** Let $c$ be a capacity matrix with
natural-number entries on the vertices $\{0, \dots, n-1\}$, let $s$ and $t$ be vertices,
and let $f$ be a flow that is feasible for $c$, $s$, $t$. Then for all vertices $u$ and
$v$, we have $-c(v, u) \le f(u, v) \le c(u, v)$.

The lower bound follows from skew symmetry and the upper bound on the reverse entry. -/
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

/-- **Residual graph.** Let $c$ be a capacity matrix assigning a natural number $c(u, v)$ to each
ordered pair of vertices among $0, \dots, n - 1$, and let $f$ be a flow on these vertices. The
residual graph of $c$ and $f$ is the directed adjacency graph whose vertices $0, \dots, n - 1$ are
enumerated in increasing order and in which the adjacency list of $u$ consists of the vertices $v$
with $f(u, v) < c(u, v)$, that is, with positive residual capacity $c(u, v) - f(u, v)$, in
increasing order. -/
def residualGraph {n : Nat} (capacity : Fin n → Fin n → Nat)
    (flow : Flow n) : DirectedAdjacency (Fin n) where
  vertices := List.finRange n
  vertices_nodup := List.nodup_finRange n
  vertices_complete := List.mem_finRange
  adjacency u := (List.finRange n).filter fun v => decide (flow u v < capacity u v)

/-- **Edges of the residual graph.** Let $c$ be a capacity matrix with natural-number entries and
$f$ an integer matrix (the flow) on the vertices $0, \dots, n - 1$. For all vertices $u$ and $v$,
the residual graph of $c$ and $f$ has an edge from $u$ to $v$ if and only if
$f(u, v) < c(u, v)$. -/
@[simp]
theorem residualGraph_edge_iff {n : Nat}
    (capacity : Fin n → Fin n → Nat) (flow : Flow n) (u v : Fin n) :
    (residualGraph capacity flow).Edge u v ↔ flow u v < (capacity u v : Int) := by
  simp [residualGraph, DirectedAdjacency.Edge]

/-- **Directed path.** In a directed graph $G$, a list $p$ of vertices is a path from $s$ to $t$
when it is nonempty, its first entry is $s$, its last entry is $t$, every pair of consecutive
entries $u, v$ forms a directed edge of $G$ from $u$ to $v$, and no vertex occurs twice in $p$. -/
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

/-- **Distance-guided path reconstruction.** Let $G$ be a directed graph with ordered adjacency
lists, $d$ a partial labelling of its vertices by natural numbers, $t$ a vertex, and $\equiv$ a
given Boolean test on pairs of vertices (not required to be equality). The reconstruction from
a vertex $u$ with $k$ steps left returns the one-element list $[u]$ when $k = 0$ and $u \equiv t$
holds, and fails when $k = 0$ and $u \equiv t$ fails. When $k \ge 1$, it takes the first
out-neighbour $w$ of $u$ in adjacency order with $d(w) = k - 1$; it fails if there is none, and
otherwise returns $u$ followed by the reconstruction from $w$ with $k - 1$ steps left, failing
if that fails. -/
def pathFromDistances {V : Type*} [BEq V]
    (graph : DirectedAdjacency V) (distance : V → Option Nat) (sink : V) :
    Nat → V → Option (List V)
  | 0, current => if current == sink then some [current] else none
  | remaining + 1, current =>
      match (graph.adjacency current).find? fun next => distance next == some remaining with
      | none => none
      | some next =>
          (pathFromDistances graph distance sink remaining next).map (current :: ·)

/-- **Soundness of distance-guided path reconstruction.** Let $G$ be a directed adjacency graph on
a type $V$ whose Boolean test $\equiv$ on pairs of vertices holds exactly for equal vertices, let
$d$ be a partial labelling of the vertices by natural numbers, let $t$ and $u$ be vertices, and let
$k$ be a natural number. If the distance-guided reconstruction for $G$, $d$ and $t$ from $u$ with
$k$ steps left succeeds and returns a list $p$, then $p$ is a walk from $u$ to $t$ in $G$ (it is
nonempty, its first entry is $u$, its last entry is $t$, and every pair of consecutive entries is
an edge of $G$) and $p$ has exactly $k + 1$ entries. -/
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

/-- **Shortest path via breadth-first search.** Let $G$ be a finite directed graph on the vertices
$\{0, \dots, n - 1\}$ with ordered adjacency lists, and let $s$ be a source and $t$ a sink. Run
breadth-first search from $t$ in the reverse graph of $G$; it labels each vertex $v$ from which $t$
is reachable with the distance from $v$ to $t$ in $G$. If $s$ has no label, the search returns no
path. Otherwise, starting at $s$ with label $d$, take $d$ steps, each time moving to the first
out-neighbour (in adjacency order) whose label is one less than that of the current vertex. The
search returns the list of visited vertices, from $s$ to the last one, if every step succeeds and
the last vertex is $t$, and no path otherwise. -/
def shortestPath {n : Nat} (graph : DirectedAdjacency (Fin n))
    (source sink : Fin n) : Option (List (Fin n)) :=
  let search := bfs graph.transpose sink
  match search.distance source with
  | none => none
  | some distance => pathFromDistances graph search.distance sink distance source

/-- **Soundness of the shortest-path search.** Let $G$ be a finite directed graph on the vertices
$\{0, \dots, n - 1\}$ and let $s$ and $t$ be vertices. If the breadth-first shortest-path search in
$G$ from $s$ to $t$ returns a list $P$ of vertices, then $P$ is a directed path in $G$ from $s$ to
$t$ without repeated vertices, and breadth-first search in $G$ from $s$ assigns $t$ a distance $d$
such that $P$ has exactly $d + 1$ vertices. -/
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

/-- **The shortest-path search succeeds exactly when the sink is reachable.** Let $G$ be a finite
directed graph on the vertices $\{0, \dots, n - 1\}$ and let $s$ and $t$ be vertices. The
breadth-first shortest-path search in $G$ from $s$ to $t$ returns some path if and only if $t$ is
reachable from $s$ in $G$ (every vertex counts as reachable from itself). -/
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

/-- **The shortest-path search fails exactly when the sink is unreachable.** Let $G$ be a finite
directed graph on the vertices $\{0, \dots, n - 1\}$ and let $s$ and $t$ be vertices. The
breadth-first shortest-path search in $G$ from $s$ to $t$ returns no path if and only if $t$ is not
reachable from $s$ in $G$. -/
theorem shortestPath_eq_none_iff_not_reachable {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (source sink : Fin n) :
    shortestPath graph source sink = none ↔ ¬ graph.Reachable source sink := by
  rw [← shortestPath_present_iff_reachable]
  cases shortestPath graph source sink <;> simp

/-- **Edges of a path.** The edges of a list $v_0, v_1, \dots, v_k$ are the list of its
consecutive ordered pairs $(v_0, v_1), (v_1, v_2), \dots, (v_{k-1}, v_k)$, in this order; the
empty list and one-element lists have no edges. -/
def pathEdges {V : Type*} : List V → List (V × V)
  | [] | [_] => []
  | first :: second :: rest => (first, second) :: pathEdges (second :: rest)

private theorem pathEdges_cons {V : Type*} (first second : V) (rest : List V) :
    pathEdges (first :: second :: rest) =
      (first, second) :: pathEdges (second :: rest) := rfl

/-- **Residual capacity.** Let $c$ be a capacity matrix with natural-number entries and $f$ an
integer matrix (the flow) on the vertices $0, \dots, n - 1$. The residual capacity of an ordered
pair of vertices $(u, v)$ is the integer $c(u, v) - f(u, v)$. -/
def residualAmount {n : Nat} (capacity : Fin n → Fin n → Nat)
    (flow : Flow n) (source target : Fin n) : Int :=
  (capacity source target : Int) - flow source target

/-- **Bottleneck of a path.** Let $c$ be a capacity matrix with natural-number entries and $f$
an integer matrix (the flow) on the same vertices. The bottleneck of a list of vertices
$v_0, v_1, \dots, v_k$ with $k \ge 1$ is the integer
$\min_{i < k} \bigl(c(v_i, v_{i+1}) - f(v_i, v_{i+1})\bigr)$, the least residual capacity of a
consecutive pair; a list with at most one vertex has bottleneck $0$. -/
def pathBottleneck {n : Nat} (capacity : Fin n → Fin n → Nat)
    (flow : Flow n) : List (Fin n) → Int
  | [] | [_] => 0
  | first :: second :: [] => residualAmount capacity flow first second
  | first :: second :: third :: rest =>
      min (residualAmount capacity flow first second)
        (pathBottleneck capacity flow (second :: third :: rest))

/-- **Unit skew flow along an oriented edge.** For vertices $a$, $b$, $u$, $v$,
the unit skew flow of the oriented edge $(a, b)$ at the ordered pair $(u, v)$ is the integer
$[u = a \text{ and } v = b] - [u = b \text{ and } v = a]$, where $[P]$ is $1$ if $P$ holds
and $0$ otherwise. -/
def localDelta {V : Type*} [DecidableEq V]
    (first second source target : V) : Int :=
  (if source = first ∧ target = second then 1 else 0) -
    if source = second ∧ target = first then 1 else 0

/-- **Edge delta of a path.** For a list $P$ of elements of a set $V$ and elements $u, v$
of $V$, the edge delta of $P$ at $(u, v)$ is the integer obtained as the number of
consecutive pairs of $P$ equal to $(u, v)$ minus the number of consecutive pairs of $P$
equal to $(v, u)$, counted with multiplicity. It is $0$ when $P$ has fewer than two
elements. -/
def edgeDelta {V : Type*} [DecidableEq V] : List V → V → V → Int
  | [] | [_] => fun _ _ => 0
  | first :: second :: rest => fun source target =>
      localDelta first second source target +
        edgeDelta (second :: rest) source target

/-- **Augmenting a flow along a path.** Given an integer flow matrix $f$ on the vertices
$\{0, \dots, n-1\}$, a list of vertices $P$ and an integer $a$, the augmentation of $f$
along $P$ by $a$ is the matrix whose entry at $(u, v)$ is $f(u, v) + a \cdot d$, where $d$
is the number of consecutive pairs of $P$ equal to $(u, v)$ minus the number of
consecutive pairs of $P$ equal to $(v, u)$, counted with multiplicity. -/
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

/-- **Augmenting paths have positive bottleneck.** Let $c$ be a capacity matrix with
natural-number entries and $f$ any integer matrix (the flow) on the vertices $0, \dots, n - 1$,
and let $s \ne t$ be vertices. If $p$ is a duplicate-free path from $s$ to $t$ in the residual
graph of $c$ and $f$, then the bottleneck of $p$, the minimum of $c(u, v) - f(u, v)$ over
consecutive vertices $u, v$ of $p$, is positive. -/
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

/-- **Augmentation within residual capacities preserves feasibility.** Let $c$ be a
capacity matrix with natural-number entries on the vertices $\{0, \dots, n-1\}$, let $s$
and $t$ be vertices, and let $f$ be a flow that is feasible for $c$, $s$, $t$. Let
$P = (v_0, \dots, v_k)$ be a nonempty list of pairwise distinct vertices with $v_0 = s$ and
$v_k = t$, and let $a$ be an integer with $0 \le a$ and
$a \le c(v_i, v_{i+1}) - f(v_i, v_{i+1})$ for every $i < k$. Then the augmentation of $f$
along $P$ by $a$ is feasible for $c$, $s$, $t$. -/
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

/-- **Augmenting along a path changes the flow value by the amount.** Let $s \ne t$ be vertices,
$f$ a flow, $a$ an integer, and $p$ a nonempty list of vertices whose first entry is $s$ and whose
last entry is $t$. Then the net flow leaving $s$ under the flow obtained by augmenting $f$ along
$p$ by $a$ equals the net flow leaving $s$ under $f$, plus $a$.

No feasibility of $f$, no edge condition on consecutive entries of $p$, and no duplicate-freeness
of $p$ is needed. -/
theorem flowValue_augment {n : Nat} (source sink : Fin n)
    (source_ne_sink : source ≠ sink) (flow : Flow n)
    (path : List (Fin n)) (amount : Int)
    (chain : path.IsChainFromTo (fun _ _ => True) source sink) :
    flowValue source (augment flow path amount) = flowValue source flow + amount := by
  unfold flowValue augment
  rw [Finset.sum_add_distrib, sum_mul_left, edgeDelta_sum chain]
  simp [source_ne_sink]

/-- **Bottleneck augmentation preserves feasibility.** Let $c$ be a capacity matrix with
natural-number entries on the vertices $\{0, \dots, n-1\}$, let $s$ and $t$ be vertices,
and let $f$ be a flow that is feasible for $c$, $s$, $t$. If $P$ is a path from $s$ to $t$
in the residual graph of $f$, that is, a nonempty list of pairwise distinct vertices
starting at $s$ and ending at $t$ whose consecutive pairs are residual edges, then the
augmentation of $f$ along $P$ by the bottleneck of $P$ is again feasible for $c$, $s$,
$t$. -/
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

/-- **One augmenting-path step.** Let $c$ be a capacity matrix with natural-number entries on the
vertices $\{0, \dots, n - 1\}$, let $s$ be a source and $t$ a sink, and let $f$ be a flow (an
integer-valued matrix on pairs of vertices). Run the breadth-first shortest-path search from $s$ to
$t$ in the residual graph of $f$ with respect to $c$. If it finds no path, the step returns $f$. If
it returns a path $P$, let $b$ be the bottleneck of $P$, the least residual capacity
$c(u, v) - f(u, v)$ over the edges $(u, v)$ of $P$ (and $b = 0$ if $P$ has no edges); the step
returns $f$ augmented along $P$ by $b$, that is, $b$ is added to $f(u, v)$ and subtracted from
$f(v, u)$ for each edge $(u, v)$ of $P$. -/
def step {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source sink : Fin n) (flow : Flow n) : Flow n :=
  match shortestPath (residualGraph capacity flow) source sink with
  | none => flow
  | some path => augment flow path (pathBottleneck capacity flow path)

/-- **One augmentation step keeps or strictly raises the flow value.** Let $c$ be a capacity
function and $s \ne t$ vertices. For every flow $f$, the flow obtained from $f$ by one step of
bottleneck augmentation either has the same net flow leaving $s$ as $f$, or a strictly larger
one. -/
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

/-- **Augmenting-path iteration with fuel.** Let $c$ be a capacity matrix with natural-number
entries on the vertices $\{0, \dots, n - 1\}$, let $s$ be a source and $t$ a sink, let $k$ be a fuel
bound and let $f$ be a flow (an integer-valued matrix on pairs of vertices). The iteration returns
$f$ if $k = 0$ or $s = t$. Otherwise it runs the breadth-first shortest-path search from $s$ to $t$
in the residual graph of $f$ with respect to $c$. If the search finds no path, the iteration returns
$f$. If it returns a path $P$, let $b$ be the bottleneck of $P$, the least residual capacity
$c(u, v) - f(u, v)$ over the edges $(u, v)$ of $P$; the iteration augments $f$ along $P$ by $b$,
adding $b$ to $f(u, v)$ and subtracting $b$ from $f(v, u)$ for each edge $(u, v)$ of $P$, and
continues from the augmented flow with fuel $k - 1$. -/
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

/-- **The augmentation loop never decreases the flow value.** Let $c$ be a capacity function and
$s \ne t$ vertices. For every flow $f$ and every natural number $k$, the net flow leaving $s$
after running at most $k$ rounds of bottleneck augmentation from $f$ is at least the net flow
leaving $s$ under $f$. -/
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

/-- **Source capacity.** For a capacity matrix $c$ with natural-number entries on the vertices
$\{0, \dots, n - 1\}$ and a source $s$, the source capacity is the total capacity leaving $s$,
namely $\sum_{v} c(s, v)$, where $v$ ranges over all vertices, including $s$ itself. -/
def sourceCapacity {n : Nat} (capacity : Fin n → Fin n → Nat)
    (source : Fin n) : Nat :=
  ∑ target, capacity source target

/-- **Edmonds–Karp maximum flow.** Let $c$ be a capacity function assigning a natural number
$c(u, v)$ to each ordered pair of vertices, and let $s$ and $t$ be vertices. If $s = t$, the
Edmonds–Karp flow is the zero flow. Otherwise it is the result of running at most $C + 1$ rounds
of bottleneck augmentation from the zero flow, where $C = \sum_v c(s, v)$ is the total capacity
leaving $s$: each round looks for a shortest path from $s$ to $t$ in the residual graph, stops if
there is none, and otherwise augments the flow along that path by its bottleneck. -/
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

/-- **The Edmonds–Karp flow is feasible.** For every capacity matrix $c$ with
natural-number entries on the vertices $\{0, \dots, n-1\}$ and all vertices $s$ and $t$,
the flow $f$ returned by the Edmonds–Karp algorithm on $c$, $s$, $t$ is feasible for $c$,
$s$, $t$: it is skew-symmetric, satisfies $f(u, v) \le c(u, v)$ for all vertices $u, v$,
and has zero net outflow at every vertex other than $s$ and $t$. -/
theorem edmondsKarp_feasible {n : Nat}
    (capacity : Fin n → Fin n → Nat) (source sink : Fin n) :
    IsFeasible capacity source sink (edmondsKarp capacity source sink) := by
  unfold edmondsKarp
  split
  · exact zeroFlow_feasible capacity source sink
  · exact run_feasible capacity source sink _ _
      (zeroFlow_feasible capacity source sink)

/-- **The iteration stops when there is no augmenting path.** Let $c$ be a capacity matrix with
natural-number entries on the vertices $\{0, \dots, n - 1\}$, let $s$ and $t$ be vertices, and let
$f$ be a flow (an integer-valued matrix on pairs of vertices). If the breadth-first shortest-path
search finds no path from $s$ to $t$ in the residual graph of $f$ with respect to $c$, then for
every fuel bound $k$, the augmenting-path iteration started at $f$ with fuel $k$ returns $f$. -/
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

/-- **The flow value is at most the source capacity.** Let $c$ be a capacity function, $s$ and
$t$ vertices, and $f$ a flow that is feasible for $c$, $s$ and $t$. Then the net flow leaving $s$
under $f$ is at most $\sum_v c(s, v)$, the total capacity leaving $s$. -/
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

/-- **No augmenting path remains after Edmonds–Karp.** Let $c$ be a capacity matrix with
natural-number entries on the vertices $\{0, \dots, n-1\}$ and let $s$ and $t$ be distinct
vertices. Then $t$ is not reachable from $s$ in the residual graph of the flow returned
by the Edmonds–Karp algorithm on $c$, $s$, $t$. -/
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

/-- **Cut capacity.** For a capacity matrix $c$ with natural-number entries on the vertices
$\{0, \dots, n-1\}$ and a set $S$ of vertices, the capacity of the cut $S$ is the integer
$\sum_{u \in S} \sum_{v \notin S} c(u, v)$. -/
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

/-- **Weak max-flow min-cut duality.** Let $c$ be a capacity function, $s$ and $t$ vertices, and
$f$ a flow that is feasible for $c$, $s$ and $t$. For every set $S$ of vertices with $s \in S$
and $t \notin S$, the net flow leaving $s$ under $f$ is at most the capacity of the cut $S$,
namely $\sum_{u \in S} \sum_{v \notin S} c(u, v)$. -/
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

/-- **Residual cut.** Let $c$ be a capacity matrix assigning a natural number $c(u, v)$ to each
ordered pair of vertices among $0, \dots, n - 1$, let $f$ be a flow on these vertices, and let $s$
be a vertex. The residual cut of $c$, $f$ and $s$ is the set of vertices visited by breadth-first
search from $s$ in the residual graph of $c$ and $f$, that is, the set of vertices reachable from
$s$ in that residual graph. -/
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

/-- **The Edmonds–Karp flow value equals its residual cut capacity.** Let $c$ be a capacity
matrix with natural-number entries on the vertices $\{0, \dots, n-1\}$, let $s$ and $t$ be
distinct vertices, and let $f$ be the flow returned by the Edmonds–Karp algorithm on $c$,
$s$, $t$. Then the net flow of $f$ out of $s$ equals the capacity of the cut formed by the
vertices reachable from $s$ in the residual graph of $f$. -/
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

/-- **Maximality of the Edmonds–Karp flow.** Let $c$ be a capacity matrix with
natural-number entries on the vertices $\{0, \dots, n-1\}$, let $s$ and $t$ be distinct
vertices, and let $f$ be the flow returned by the Edmonds–Karp algorithm on $c$, $s$, $t$.
Then every integer flow $g$ that is feasible for $c$, $s$, $t$ has value at $s$ at most
the value of $f$ at $s$, where the value of a flow at $s$ is its net flow out of $s$. -/
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
