/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents

import all CSLibExt.Algorithms.Lean.Graph.BreadthFirstSearch.Parents.Internal

/-! Correctness of the saved predecessor forest and its endpoint-inclusive paths. -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.BreadthFirstSearch

universe u

private lemma parentInvariant_chain_length {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (invariant : ParentInvariant graph source state) (vertex : V) (distance : Nat)
    (found : state.core.2.2[vertex]? = some distance) (chain : List V)
    (linked : chain.IsChainFromTo
      (fun parent vertex => state.parents[vertex]? = some parent) source vertex) :
    chain.length = distance + 1 := by
  have steps := linked.relatesInSteps
    (n := chain.length - 1) (by have := linked.length_pos; omega)
  have sameDistance := parentInvariant_steps_distance graph source state invariant
    source vertex (chain.length - 1) 0 steps invariant.source_zero
  rw [found] at sameDistance
  simp only [Option.some.injEq, Nat.zero_add] at sameDistance
  have := linked.length_pos
  omega

private lemma parentInvariant_chain_nodup {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (invariant : ParentInvariant graph source state) (vertex : V) (distance : Nat)
    (found : state.core.2.2[vertex]? = some distance) (chain : List V)
    (linked : chain.IsChainFromTo
      (fun parent vertex => state.parents[vertex]? = some parent) source vertex) :
    chain.Nodup := by
  by_contra duplicate
  obtain ⟨shorter, shorterLinked, shorterLength⟩ :=
    linked.exists_length_lt_of_not_nodup duplicate
  have original := parentInvariant_chain_length graph source state invariant
    vertex distance found chain linked
  have shortened := parentInvariant_chain_length graph source state invariant
    vertex distance found shorter shorterLinked
  omega

private lemma parentInvariant_chain_eq {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (invariant : ParentInvariant graph source state) (vertex : V) (distance : Nat)
    (found : state.core.2.2[vertex]? = some distance) (left right : List V)
    (leftLinked : left.IsChainFromTo
      (fun parent vertex => state.parents[vertex]? = some parent) source vertex)
    (rightLinked : right.IsChainFromTo
      (fun parent vertex => state.parents[vertex]? = some parent) source vertex) :
    left = right := by
  let next : V → V := fun child => (state.parents[child]?).getD source
  have leftChain : left.reverse.IsChain (fun child parent => next child = parent) := by
    rw [List.isChain_reverse]
    exact leftLinked.isChain.imp (fun {parent child} edge => by simp [next, edge])
  have rightChain : right.reverse.IsChain (fun child parent => next child = parent) := by
    rw [List.isChain_reverse]
    exact rightLinked.isChain.imp (fun {parent child} edge => by simp [next, edge])
  have leftZero : left.reverse[0]'(by simpa using leftLinked.length_pos) = vertex := by
    rw [List.getElem_zero, List.head_reverse]
    exact leftLinked.getLast_eq
  have rightZero : right.reverse[0]'(by simpa using rightLinked.length_pos) = vertex := by
    rw [List.getElem_zero, List.head_reverse]
    exact rightLinked.getLast_eq
  apply List.reverse_inj.mp
  apply List.ext_getElem
  · simpa only [List.length_reverse] using
      (parentInvariant_chain_length graph source state invariant
        vertex distance found left leftLinked).trans
        (parentInvariant_chain_length graph source state invariant
          vertex distance found right rightLinked).symm
  · intro index leftBound rightBound
    rw [← leftChain.iterate_eq_of_apply_eq index leftBound,
      ← rightChain.iterate_eq_of_apply_eq index rightBound, leftZero, rightZero]


private lemma parentFinal_distance {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) :
    (parentRun graph graph.vertices.length (parentInitial source).ret).ret.core.2.2[vertex]? =
      (bfs graph source).distance vertex := by
  have projection := congrArg (fun result : BFSResult V => result.distance vertex)
    (bfsWithParents_ret graph source)
  simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using projection

/-- **Each reachable vertex has a unique saved-parent chain.** Let $G$ be a finite directed graph
given by adjacency lists, and let $s$ and $v$ be vertices with $v$ reachable from $s$ in $G$.
There is exactly one list of vertices that starts at $s$, ends at $v$, and in which each vertex
after the first has the preceding vertex as its saved parent in the breadth-first search forest
of $G$ from $s$. -/
public theorem predecessor_chain_unique {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V)
    (reachable : graph.Reachable source vertex) :
    ∃! chain : List V, chain.IsChainFromTo
      (fun parent child => (bfsWithParents graph source).ret.predecessor child = some parent)
      source vertex := by
  obtain ⟨distance, found⟩ := (distance_present_iff_reachable graph source vertex).mpr reachable
  have saved := (parentFinal_distance graph source vertex).trans found
  obtain ⟨chain, linked, _⟩ :=
    (parentInvariant_steps graph source
      (parentRun graph graph.vertices.length (parentInitial source).ret).ret
      (parentFinal_invariant graph source) vertex distance saved).exists_isChainFromTo
  refine ⟨chain, ?_, ?_⟩
  · simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using linked
  · intro other otherLinked
    apply parentInvariant_chain_eq graph source
      (parentRun graph graph.vertices.length (parentInitial source).ret).ret
      (parentFinal_invariant graph source) vertex distance saved other chain
    · simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using otherLinked
    · exact linked

/-- **Saved-parent chains are simple.** Let $G$ be a finite directed graph given by adjacency
lists and let $s$ and $v$ be vertices. If a list of vertices starts at $s$, ends at $v$, and each
of its vertices after the first has the preceding vertex as its saved parent in the breadth-first
search forest of $G$ from $s$, then no vertex occurs twice in the list. -/
public theorem predecessor_chain_nodup {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) (chain : List V)
    (linked : chain.IsChainFromTo
      (fun parent child => (bfsWithParents graph source).ret.predecessor child = some parent)
      source vertex) :
    chain.Nodup := by
  have graphChain : chain.IsChainFromTo graph.Edge source vertex :=
    ⟨linked.isChain.imp (fun {parent child} edge =>
      predecessor_edge graph source child parent edge),
      linked.ne_nil, linked.head_eq, linked.getLast_eq⟩
  obtain ⟨distance, found⟩ := (distance_present_iff_reachable graph source vertex).mpr
    graphChain.reflTransGen
  apply parentInvariant_chain_nodup graph source
    (parentRun graph graph.vertices.length (parentInitial source).ret).ret
    (parentFinal_invariant graph source) vertex distance
    ((parentFinal_distance graph source vertex).trans found) chain
  simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using linked

private lemma parentInvariant_transGen_lt {V : Type u} [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (invariant : ParentInvariant graph source state) (start vertex : V)
    (path : Relation.TransGen (fun parent child => state.parents[child]? = some parent)
      start vertex) :
    ∃ first last : Nat, state.core.2.2[start]? = some first ∧
      state.core.2.2[vertex]? = some last ∧ first < last := by
  induction path with
  | single edge =>
      obtain ⟨distance, parentFound, childFound⟩ :=
        invariant.parent_distance _ _ edge
      exact ⟨distance, distance + 1, parentFound, childFound, by omega⟩
  | tail _ edge ih =>
      obtain ⟨first, middle, firstFound, middleFound, less⟩ := ih
      obtain ⟨distance, parentFound, childFound⟩ :=
        invariant.parent_distance _ _ edge
      have same := middleFound.symm.trans parentFound
      simp only [Option.some.injEq] at same
      exact ⟨first, distance + 1, firstFound, childFound, by omega⟩

/-- **The saved-parent relation is acyclic.** Let $G$ be a finite directed graph given by
adjacency lists and let $s$ and $v$ be vertices. In the breadth-first search forest of $G$ from
$s$, there is no sequence $v = x_0, x_1, \dots, x_k = v$ with $k \ge 1$ in which each $x_i$ is
the saved parent of $x_{i+1}$. -/
public theorem predecessor_relation_acyclic {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) :
    ¬ Relation.TransGen
      (fun parent child => (bfsWithParents graph source).ret.predecessor child = some parent)
      vertex vertex := by
  intro cycle
  have savedCycle :
      Relation.TransGen
        (fun parent child =>
          (parentRun graph graph.vertices.length (parentInitial source).ret).ret.parents[child]? =
            some parent) vertex vertex := by
    simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using cycle
  obtain ⟨first, last, firstFound, lastFound, less⟩ :=
    parentInvariant_transGen_lt graph source
      (parentRun graph graph.vertices.length (parentInitial source).ret).ret
      (parentFinal_invariant graph source) vertex vertex savedCycle
  have same := firstFound.symm.trans lastFound
  simp only [Option.some.injEq] at same
  omega

/-- **Path reconstruction at the source.** For every breadth-first search forest $F$ and every
vertex $s$, following the saved parents of $F$ from $s$ back to $s$ returns the one-vertex path
$[s]$. This holds for every forest, including one whose discovery order is empty. -/
public theorem BFSForest.pathTo?_source {V : Type u} [BEq V] [ReflBEq V]
    (forest : BFSForest V) (source : V) :
    (forest.pathTo? source source).ret = some [source] := by
  change (followParents forest.predecessor source forest.order.length source []).ret = _
  rw [followParents_source]

private structure PathEvents where
  comparisons : Nat
  reads : Nat
  conses : Nat

@[no_expose] private def followEvents {V : Type u} [BEq V]
    (predecessor : V → Option V) (source : V) : Nat → V → PathEvents
  | fuel, current =>
      if current == source then ⟨1, 0, 1⟩
      else
        match fuel with
        | 0 => ⟨1, 0, 0⟩
        | fuel + 1 =>
            match predecessor current with
            | none => ⟨1, 1, 0⟩
            | some parent =>
                let rest := followEvents predecessor source fuel parent
                ⟨rest.comparisons + 1, rest.reads + 1, rest.conses + 1⟩

private lemma followEvents_time {V : Type u} [BEq V]
    (predecessor : V → Option V) (source : V) (fuel : Nat)
    (current : V) (suffix : List V) :
    (followParents predecessor source fuel current suffix).time =
      (followEvents predecessor source fuel current).comparisons +
        (followEvents predecessor source fuel current).reads +
        (followEvents predecessor source fuel current).conses := by
  induction fuel generalizing current suffix with
  | zero =>
      cases same : current == source <;> simp [followParents, followEvents, same]
  | succ fuel ih =>
      cases same : current == source with
      | true => simp [followParents, followEvents, same]
      | false =>
          cases previous : predecessor current with
          | none => simp [followParents, followEvents, same, previous]
          | some parent =>
              have rest := ih parent (current :: suffix)
              simp [followParents, followEvents, same, previous]
              omega

private lemma parentInvariant_followEvents {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source : V) (state : ParentState V)
    (invariant : ParentInvariant graph source state) (vertex : V) (distance : Nat)
    (found : state.core.2.2[vertex]? = some distance) (fuel : Nat) (enough : distance ≤ fuel) :
    followEvents (fun child => state.parents[child]?) source fuel vertex =
      ⟨distance + 1, distance, distance + 1⟩ := by
  induction distance generalizing vertex fuel with
  | zero =>
      have root := (parentInvariant_steps graph source state invariant vertex 0 found).zero
      subst vertex
      cases fuel <;> simp [followEvents]
  | succ distance ih =>
      have nonsource : vertex ≠ source := by
        intro root
        subst vertex
        rw [invariant.source_zero] at found
        simp only [Option.some.injEq] at found
        omega
      cases previous : state.parents[vertex]? with
      | none =>
          rcases (invariant.parent_none vertex).mp previous with root | absent
          · exact False.elim (nonsource root)
          · rw [found] at absent
            contradiction
      | some parent =>
          obtain ⟨parentDistance, parentFound, childFound⟩ :=
            invariant.parent_distance vertex parent previous
          have same := found.symm.trans childFound
          simp only [Option.some.injEq] at same
          have equal : parentDistance = distance := by omega
          subst parentDistance
          cases fuel with
          | zero => omega
          | succ fuel =>
              have rest := ih parent parentFound fuel (by omega)
              simp [followEvents, nonsource, previous, rest, Nat.add_assoc]

private lemma followEvents_missing {V : Type u} [BEq V] [LawfulBEq V]
    (predecessor : V → Option V) (source vertex : V) (fuel : Nat)
    (positive : 0 < fuel) (nonsource : vertex ≠ source) (missing : predecessor vertex = none) :
    followEvents predecessor source fuel vertex = ⟨1, 1, 0⟩ := by
  cases fuel with
  | zero => omega
  | succ fuel => simp [followEvents, nonsource, missing]

private lemma parentFinal_follow {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) (distance : Nat)
    (found : (bfs graph source).distance vertex = some distance) :
    ∃ chain : List V, chain.IsChainFromTo
      (fun parent child => (bfsWithParents graph source).ret.predecessor child = some parent)
      source vertex ∧ chain.length = distance + 1 ∧
      (bfsWithParents graph source).ret.pathTo? source vertex =
        ⟨some chain, 3 * distance + 2⟩ := by
  have saved := (parentFinal_distance graph source vertex).trans found
  obtain ⟨chain, linked, chainLength⟩ :=
    (parentInvariant_steps graph source
      (parentRun graph graph.vertices.length (parentInitial source).ret).ret
      (parentFinal_invariant graph source) vertex distance saved).exists_isChainFromTo
  have publicLinked : chain.IsChainFromTo
      (fun parent child => (bfsWithParents graph source).ret.predecessor child = some parent)
      source vertex := by
    simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using linked
  have graphChain : chain.IsChainFromTo graph.Edge source vertex :=
    ⟨publicLinked.isChain.imp (fun {parent child} edge =>
      predecessor_edge graph source child parent edge),
      publicLinked.ne_nil, publicLinked.head_eq, publicLinked.getLast_eq⟩
  have bound : distance ≤ (bfs graph source).order.length := by
    have simple := predecessor_chain_nodup graph source vertex chain publicLinked
    have chainBound := simple.length_le_of_subset
        (fun child member =>
          (order_mem_iff_reachable graph source child).mpr
            (graphChain.reflTransGen_of_mem member))
    omega
  have decoratedBound : distance ≤ (bfsWithParents graph source).ret.order.length := by
    simpa only [bfsWithParents_ret] using bound
  obtain ⟨path, pathLinked, pathLength, actual⟩ :=
    parentInvariant_follow graph source
      (parentRun graph graph.vertices.length (parentInitial source).ret).ret
      (parentFinal_invariant graph source) vertex distance saved
      (bfsWithParents graph source).ret.order.length decoratedBound []
  refine ⟨path, ?_, pathLength, ?_⟩
  · simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using pathLinked
  · simpa only [BFSForest.pathTo?, bfsWithParents, TimeM.ret_bind, TimeM.ret_pure,
      List.append_nil] using actual

private lemma parentFinal_unreachable {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V)
    (unreachable : ¬ graph.Reachable source vertex) :
    (bfsWithParents graph source).ret.pathTo? source vertex = ⟨none, 2⟩ := by
  have nonsource : vertex ≠ source := by
    intro same
    subst vertex
    exact unreachable (Relation.ReflTransGen.refl)
  have missing := (predecessor_eq_none_iff graph source vertex).mpr (Or.inr unreachable)
  have positive : 0 < (bfs graph source).order.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem
      ((order_mem_iff_reachable graph source source).mpr Relation.ReflTransGen.refl))
  have decoratedPositive : 0 < (bfsWithParents graph source).ret.order.length := by
    simpa only [bfsWithParents_ret] using positive
  exact followParents_none (bfsWithParents graph source).ret.predecessor source vertex
    (bfsWithParents graph source).ret.order.length decoratedPositive nonsource missing

/-- **Path reconstruction fails exactly at unreachable vertices.** Let $G$ be a finite directed
graph given by adjacency lists, and let $s$ and $v$ be vertices. Following the saved parents of the
breadth-first search forest of $G$ from $s$ back from $v$ towards $s$ returns no path if and only
if $v$ is not reachable from $s$ in $G$. -/
public theorem BFSForest.pathTo?_eq_none_iff {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) :
    ((bfsWithParents graph source).ret.pathTo? source vertex).ret = none ↔
      ¬ graph.Reachable source vertex := by
  constructor
  · intro missing reachable
    obtain ⟨distance, found⟩ := (distance_present_iff_reachable graph source vertex).mpr reachable
    obtain ⟨chain, _, _, actual⟩ := parentFinal_follow graph source vertex distance found
    rw [actual] at missing
    contradiction
  · intro unreachable
    rw [parentFinal_unreachable graph source vertex unreachable]

/-- **Reconstructed BFS paths are shortest paths.** Let $G$ be a finite directed graph given by
adjacency lists, let $s$ and $v$ be vertices, and suppose that following the saved parents of the
breadth-first search forest of $G$ from $s$ back from $v$ returns a list $P$ of vertices. Then $P$
starts at $s$ and ends at $v$, each vertex of $P$ after the first has the preceding vertex as its
saved parent, $G$ has an edge from each vertex of $P$ to the next, no vertex occurs twice in $P$,
breadth-first search from $s$ reports a distance $d$ for $v$ and $P$ has $d + 1$ vertices, and
every list of vertices from $s$ to $v$ such that $G$ has an edge from each of its vertices to the
next has at least as many vertices as $P$. -/
public theorem BFSForest.pathTo?_spec {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) (chain : List V)
    (returned : ((bfsWithParents graph source).ret.pathTo? source vertex).ret = some chain) :
    chain.IsChainFromTo
        (fun parent child => (bfsWithParents graph source).ret.predecessor child = some parent)
        source vertex ∧
      chain.IsChainFromTo graph.Edge source vertex ∧ chain.Nodup ∧
      (∃ distance : Nat, (bfs graph source).distance vertex = some distance ∧
        chain.length = distance + 1) ∧
      ∀ other : List V, other.IsChainFromTo graph.Edge source vertex →
        chain.length ≤ other.length := by
  have reachable : graph.Reachable source vertex := by
    by_contra unreachable
    have missing := (BFSForest.pathTo?_eq_none_iff graph source vertex).mpr unreachable
    rw [returned] at missing
    contradiction
  obtain ⟨distance, found⟩ := (distance_present_iff_reachable graph source vertex).mpr reachable
  obtain ⟨path, linked, pathLength, actual⟩ := parentFinal_follow graph source vertex distance found
  have same := congrArg TimeM.ret actual
  rw [returned] at same
  simp only [Option.some.injEq] at same
  subst path
  have graphChain : chain.IsChainFromTo graph.Edge source vertex :=
    ⟨linked.isChain.imp (fun {parent child} edge =>
      predecessor_edge graph source child parent edge),
      linked.ne_nil, linked.head_eq, linked.getLast_eq⟩
  refine ⟨linked, graphChain, predecessor_chain_nodup graph source vertex chain linked,
    ⟨distance, found, pathLength⟩, ?_⟩
  intro other otherLinked
  have walk := otherLinked.relatesInSteps
    (n := other.length - 1) (by have := otherLinked.length_pos; omega)
  have minimal := ((distance_eq_some_iff_shortest graph source vertex distance).mp found).2
    (other.length - 1) walk
  have := otherLinked.length_pos
  omega

private lemma parentFinal_events {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) (distance : Nat)
    (found : (bfs graph source).distance vertex = some distance) :
    followEvents (bfsWithParents graph source).ret.predecessor source
      (bfsWithParents graph source).ret.order.length vertex =
        ⟨distance + 1, distance, distance + 1⟩ := by
  obtain ⟨chain, linked, chainLength, _⟩ := parentFinal_follow graph source vertex distance found
  have graphChain : chain.IsChainFromTo graph.Edge source vertex :=
    ⟨linked.isChain.imp (fun {parent child} edge =>
      predecessor_edge graph source child parent edge),
      linked.ne_nil, linked.head_eq, linked.getLast_eq⟩
  have simple := predecessor_chain_nodup graph source vertex chain linked
  have chainBound := simple.length_le_of_subset
    (fun child member => (order_mem_iff_reachable graph source child).mpr
      (graphChain.reflTransGen_of_mem member))
  have bound : distance ≤ (bfsWithParents graph source).ret.order.length := by
    have order := congrArg (fun result : BFSResult V => result.order.length)
      (bfsWithParents_ret graph source)
    omega
  have events := parentInvariant_followEvents graph source
    (parentRun graph graph.vertices.length (parentInitial source).ret).ret
    (parentFinal_invariant graph source) vertex distance
    ((parentFinal_distance graph source vertex).trans found)
    (bfsWithParents graph source).ret.order.length bound
  simpa only [bfsWithParents, TimeM.ret_bind, TimeM.ret_pure] using events

private lemma parentFinal_missing_events {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V)
    (unreachable : ¬ graph.Reachable source vertex) :
    followEvents (bfsWithParents graph source).ret.predecessor source
      (bfsWithParents graph source).ret.order.length vertex = ⟨1, 1, 0⟩ := by
  have nonsource : vertex ≠ source := by
    intro same
    subst vertex
    exact unreachable Relation.ReflTransGen.refl
  have missing := (predecessor_eq_none_iff graph source vertex).mpr (Or.inr unreachable)
  have positive : 0 < (bfs graph source).order.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem
      ((order_mem_iff_reachable graph source source).mpr Relation.ReflTransGen.refl))
  have decoratedPositive : 0 < (bfsWithParents graph source).ret.order.length := by
    simpa only [bfsWithParents_ret] using positive
  exact followEvents_missing (bfsWithParents graph source).ret.predecessor source vertex
    (bfsWithParents graph source).ret.order.length decoratedPositive nonsource missing

/-- **Cost of path reconstruction for a reachable vertex.** Let $G$ be a finite directed graph
given by adjacency lists, let $s$ and $v$ be vertices, and suppose breadth-first search from $s$
reports distance $d$ for $v$. Following the saved parents of the breadth-first search forest of
$G$ from $s$ back from $v$ costs exactly $3d + 2$, counting one unit for each comparison with $s$,
each parent lookup and each vertex prepended to the path. -/
public theorem BFSForest.pathTo?_time {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V) (distance : Nat)
    (found : (bfs graph source).distance vertex = some distance) :
    ((bfsWithParents graph source).ret.pathTo? source vertex).time =
      3 * distance + 2 := by
  have events := parentFinal_events graph source vertex distance found
  have timing := followEvents_time (bfsWithParents graph source).ret.predecessor source
    (bfsWithParents graph source).ret.order.length vertex []
  rw [events] at timing
  have total : distance + 1 + distance + (distance + 1) = 3 * distance + 2 := by omega
  simpa only [BFSForest.pathTo?, total] using timing

/-- **Cost of path reconstruction for an unreachable vertex.** Let $G$ be a finite directed graph
given by adjacency lists, and let $s$ and $v$ be vertices with $v$ not reachable from $s$ in $G$.
Following the saved parents of the breadth-first search forest of $G$ from $s$ back from $v$ costs
exactly $2$, counting one unit for each comparison with $s$, each parent lookup and each vertex
prepended to the path: one comparison of $v$ with $s$ and one lookup of the missing parent of
$v$. -/
public theorem BFSForest.pathTo?_time_of_not_reachable
    {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (source vertex : V)
    (unreachable : ¬ graph.Reachable source vertex) :
    ((bfsWithParents graph source).ret.pathTo? source vertex).time = 2 := by
  have events := parentFinal_missing_events graph source vertex unreachable
  have timing := followEvents_time (bfsWithParents graph source).ret.predecessor source
    (bfsWithParents graph source).ret.order.length vertex []
  rw [events] at timing
  simpa only [BFSForest.pathTo?] using timing

end Cslib.Algorithms.Lean.BreadthFirstSearch

end
