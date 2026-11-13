/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DepthFirstSearch

import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup

/-!
# Strongly connected components of ordered directed graphs

This module gives a deterministic executable reference implementation of
strongly connected components.  It reuses the verified depth-first search to
decide reachability and takes its vertex schedule from decreasing DFS finish
order; it does not contain a second search implementation.

If `V` is the carrier size and `L` is the total length of all adjacency lists,
including duplicate entries, each reachability decision performs expected
`O(V + L)` work under the lawful hash-table cost model.  The reference
partition makes `O(V²)` such decisions in the worst case, for expected
`O(V² (V + L))` work after one `O(V + L)` scheduling traversal.  It does not
construct a transpose.  This is deliberately not the linear-time Kosaraju
bound; the benefit is that every returned block is certified directly against
mutual reachability.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.StronglyConnectedComponents

universe u

open DepthFirstSearch

set_option warn.classDefReducibility false in
attribute [local instance 5] instDecidableEqOfLawfulBEq

/-- **Strongly connected vertices.** In a directed adjacency graph $G$, vertices $u$ and $v$ are
strongly connected when $v$ is reachable from $u$ and $u$ is reachable from $v$ in $G$. -/
public def StronglyConnected {V : Type u} (graph : DirectedAdjacency V)
    (left right : V) : Prop :=
  graph.Reachable left right ∧ graph.Reachable right left

/-- **Strong connectivity is reflexive.** In a directed graph $G$, every vertex is strongly
connected to itself. -/
@[refl]
public theorem stronglyConnected_refl {V : Type u} (graph : DirectedAdjacency V)
    (vertex : V) : StronglyConnected graph vertex vertex :=
  ⟨.refl, .refl⟩

/-- **Strong connectivity is symmetric.** In a directed graph $G$, if $u$ is strongly connected to
$v$, then $v$ is strongly connected to $u$. -/
@[symm]
public theorem StronglyConnected.symm {V : Type u} {graph : DirectedAdjacency V}
    {left right : V} (connected : StronglyConnected graph left right) :
    StronglyConnected graph right left :=
  ⟨connected.2, connected.1⟩

/-- **Strong connectivity is transitive.** In a directed graph $G$, if $u$ is strongly connected to
$v$ and $v$ is strongly connected to $w$, then $u$ is strongly connected to $w$. -/
@[trans]
public theorem StronglyConnected.trans {V : Type u} {graph : DirectedAdjacency V}
    {left middle right : V}
    (leftMiddle : StronglyConnected graph left middle)
    (middleRight : StronglyConnected graph middle right) :
    StronglyConnected graph left right :=
  ⟨leftMiddle.1.trans middleRight.1, middleRight.2.trans leftMiddle.2⟩

/-- **Strong connectivity as an equivalence relation.** For a directed graph $G$, the relation on
the vertices of $G$ that holds between $u$ and $v$ exactly when $u$ and $v$ are strongly connected
in $G$, packaged as an equivalence relation. -/
public def stronglyConnectedSetoid {V : Type u}
    (graph : DirectedAdjacency V) : Setoid V where
  r := StronglyConnected graph
  iseqv := ⟨stronglyConnected_refl graph, StronglyConnected.symm,
    StronglyConnected.trans⟩

/-- **Executable mutual-reachability test.** For a directed graph $G$ and vertices $u$ and $v$, the
test returns true exactly when $v$ occurs in the preorder of the depth-first search of $G$ from
the single root $u$, and $u$ occurs in the preorder of the depth-first search of $G$ from the
single root $v$. -/
public def sameComponentB {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (left right : V) : Bool :=
  decide (right ∈ (dfs graph [left]).preorder) &&
    decide (left ∈ (dfs graph [right]).preorder)

/-- **The mutual-reachability test is correct.** For a directed graph $G$ and vertices $u$ and $v$,
the executable mutual-reachability test on $u$ and $v$ returns true if and only if $u$ and $v$ are
strongly connected in $G$. -/
public theorem sameComponentB_eq_true {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (left right : V) :
    sameComponentB graph left right = true ↔ StronglyConnected graph left right := by
  simp [sameComponentB, StronglyConnected, mem_preorder_iff_reachable]

private def componentAt {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (vertices : List V) (pivot : V) : List V :=
  vertices.filter (sameComponentB graph pivot)

private def partitionFrom {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) (vertices : List V) : List (List V) :=
  (vertices.map (componentAt graph vertices)).dedup

private theorem mem_componentAt_iff {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (vertices : List V)
    (pivot vertex : V) :
    vertex ∈ componentAt graph vertices pivot ↔
      vertex ∈ vertices ∧ StronglyConnected graph pivot vertex := by
  simp [componentAt, sameComponentB_eq_true]

private theorem mem_partitionFrom_iff {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (vertices : List V)
    (block : List V) :
    block ∈ partitionFrom graph vertices ↔
      ∃ pivot ∈ vertices, block = componentAt graph vertices pivot := by
  rw [partitionFrom]
  simp only [List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨pivot, pivotMem, rfl⟩
    exact ⟨pivot, pivotMem, rfl⟩
  · rintro ⟨pivot, pivotMem, rfl⟩
    exact ⟨pivot, pivotMem, rfl⟩

private theorem componentAt_eq_of_connected {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (vertices : List V)
    {left right : V} (connected : StronglyConnected graph left right) :
    componentAt graph vertices left = componentAt graph vertices right := by
  apply List.filter_congr
  intro vertex _
  apply Bool.eq_iff_iff.mpr
  rw [sameComponentB_eq_true, sameComponentB_eq_true]
  exact ⟨fun relation => connected.symm.trans relation,
    fun relation => connected.trans relation⟩

private theorem mem_flatten_partitionFrom {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (vertices : List V) (vertex : V) :
    vertex ∈ (partitionFrom graph vertices).flatten ↔ vertex ∈ vertices := by
  constructor
  · intro member
    obtain ⟨block, blockMem, vertexMem⟩ := List.mem_flatten.mp member
    obtain ⟨pivot, _, rfl⟩ := (mem_partitionFrom_iff graph vertices block).1 blockMem
    exact (mem_componentAt_iff graph vertices pivot vertex).1 vertexMem |>.1
  · intro vertexMem
    refine List.mem_flatten.mpr
      ⟨componentAt graph vertices vertex, ?_,
        (mem_componentAt_iff graph vertices vertex vertex).2
          ⟨vertexMem, stronglyConnected_refl graph vertex⟩⟩
    exact (mem_partitionFrom_iff graph vertices _).2 ⟨vertex, vertexMem, rfl⟩

private theorem partitionFrom_nonempty {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (vertices : List V) :
    ∀ block ∈ partitionFrom graph vertices, block ≠ [] := by
  intro block blockMem
  obtain ⟨pivot, pivotMem, rfl⟩ := (mem_partitionFrom_iff graph vertices block).1 blockMem
  intro empty
  have pivotIn : pivot ∈ componentAt graph vertices pivot :=
    (mem_componentAt_iff graph vertices pivot pivot).2
      ⟨pivotMem, stronglyConnected_refl graph pivot⟩
  simp [empty] at pivotIn

private theorem partitionFrom_blocks_nodup {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (vertices : List V)
    (verticesNodup : vertices.Nodup) :
    ∀ block ∈ partitionFrom graph vertices, block.Nodup := by
  intro block blockMem
  obtain ⟨pivot, _, rfl⟩ := (mem_partitionFrom_iff graph vertices block).1 blockMem
  exact verticesNodup.filter _

private theorem partitionFrom_pairwise_disjoint {V : Type u} [BEq V]
    [Hashable V] [LawfulBEq V] (graph : DirectedAdjacency V) (vertices : List V) :
    (partitionFrom graph vertices).Pairwise List.Disjoint := by
  have blocksNodup : (partitionFrom graph vertices).Nodup := by
    exact List.nodup_dedup _
  have blocksDistinct := List.nodup_iff_pairwise_ne.mp blocksNodup
  apply List.Pairwise.imp_mem.mpr
  apply blocksDistinct.imp
  intro left right notEqual leftMem rightMem
  rw [List.disjoint_left]
  intro vertex vertexLeft vertexRight
  obtain ⟨leftPivot, _, rfl⟩ :=
    (mem_partitionFrom_iff graph vertices left).1 leftMem
  obtain ⟨rightPivot, _, rfl⟩ :=
    (mem_partitionFrom_iff graph vertices right).1 rightMem
  have leftConnected :=
    (mem_componentAt_iff graph vertices leftPivot vertex).1 vertexLeft |>.2
  have rightConnected :=
    (mem_componentAt_iff graph vertices rightPivot vertex).1 vertexRight |>.2
  apply notEqual
  exact componentAt_eq_of_connected graph vertices
    (leftConnected.trans rightConnected.symm)

private theorem partitionFrom_block_connected {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (vertices : List V) :
    ∀ block ∈ partitionFrom graph vertices, ∀ left ∈ block, ∀ right ∈ block,
      StronglyConnected graph left right := by
  intro block blockMem left leftMem right rightMem
  obtain ⟨pivot, _, rfl⟩ := (mem_partitionFrom_iff graph vertices block).1 blockMem
  have leftConnected :=
    (mem_componentAt_iff graph vertices pivot left).1 leftMem |>.2
  have rightConnected :=
    (mem_componentAt_iff graph vertices pivot right).1 rightMem |>.2
  exact leftConnected.symm.trans rightConnected

private theorem partitionFrom_complete {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (vertices : List V)
    (left right : V) (leftMem : left ∈ vertices) (rightMem : right ∈ vertices)
    (connected : StronglyConnected graph left right) :
    ∃ block ∈ partitionFrom graph vertices, left ∈ block ∧ right ∈ block := by
  refine ⟨componentAt graph vertices left,
    (mem_partitionFrom_iff graph vertices _).2 ⟨left, leftMem, rfl⟩, ?_, ?_⟩
  · exact (mem_componentAt_iff graph vertices left left).2
      ⟨leftMem, stronglyConnected_refl graph left⟩
  · exact (mem_componentAt_iff graph vertices left right).2 ⟨rightMem, connected⟩

private theorem block_eq_of_common_member {V : Type u} {blocks : List (List V)}
    (pairwise : blocks.Pairwise List.Disjoint) {left right : List V}
    (leftMem : left ∈ blocks) (rightMem : right ∈ blocks) {vertex : V}
    (vertexLeft : vertex ∈ left) (vertexRight : vertex ∈ right) : left = right := by
  induction blocks with
  | nil => simp at leftMem
  | cons head tail induction =>
      have pairwiseFacts := List.pairwise_cons.mp pairwise
      rcases List.mem_cons.mp leftMem with rfl | leftTail
      · rcases List.mem_cons.mp rightMem with rfl | rightTail
        · rfl
        · exact False.elim
            ((List.disjoint_left.mp (pairwiseFacts.1 right rightTail))
              vertexLeft vertexRight)
      · rcases List.mem_cons.mp rightMem with rfl | rightTail
        · exact False.elim
            ((List.disjoint_left.mp (pairwiseFacts.1 left leftTail))
              vertexRight vertexLeft)
        · exact induction pairwiseFacts.2 leftTail rightTail

/-- **Strongly connected components algorithm.** Let $G$ be a directed graph and let
$v_1, \dots, v_n$ be its vertices in decreasing order of finishing time in a depth-first search of
the whole graph that takes its roots in the vertex order of $G$. For each $i$, let $C_i$ be the
list of those $v_j$, in increasing order of $j$, such that $v_i$ and $v_j$ are strongly connected
(tested by two depth-first searches). The output is the list $C_1, \dots, C_n$ with repeated
blocks removed, keeping the last occurrence of each.

The result is deterministic: within a block, vertices appear in decreasing finish order. -/
public def components {V : Type u} [BEq V] [Hashable V] [LawfulBEq V]
    (graph : DirectedAdjacency V) : List (List V) :=
  let vertices := decreasingFinishAll graph
  (vertices.map fun pivot => vertices.filter (sameComponentB graph pivot)).dedup

private theorem components_eq_partitionFrom {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) :
    components graph = partitionFrom graph (decreasingFinishAll graph) :=
  rfl

/-- **Computed components are nonempty.** For every directed graph $G$, each block returned by the
strongly connected components algorithm on $G$ contains at least one vertex. -/
public theorem components_nonempty {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) :
    ∀ block ∈ components graph, block ≠ [] :=
  by
    rw [components_eq_partitionFrom]
    exact partitionFrom_nonempty graph (decreasingFinishAll graph)

/-- **Computed components have no repeated vertices.** For every directed graph $G$, each block
returned by the strongly connected components algorithm on $G$ contains no vertex more than
once. -/
public theorem components_nodup {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) :
    ∀ block ∈ components graph, block.Nodup :=
  by
    rw [components_eq_partitionFrom]
    exact partitionFrom_blocks_nodup graph (decreasingFinishAll graph)
      (decreasingFinishAll_nodup graph)

/-- **Computed components are pairwise disjoint.** For every directed graph $G$, any two blocks at
different positions of the list returned by the strongly connected components algorithm on $G$
have no vertex in common. -/
public theorem components_pairwise_disjoint {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) :
    (components graph).Pairwise List.Disjoint :=
  by
    rw [components_eq_partitionFrom]
    exact partitionFrom_pairwise_disjoint graph (decreasingFinishAll graph)

/-- **The computed components cover the vertex list.** For a directed graph $G$ and a vertex
$v$, $v$ belongs to some block of the computed strongly connected components of $G$ if and only
if $v$ occurs in the vertex enumeration of $G$. -/
public theorem mem_flatten_components {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (vertex : V) :
    vertex ∈ (components graph).flatten ↔ vertex ∈ graph.vertices := by
  rw [components_eq_partitionFrom, mem_flatten_partitionFrom]
  exact ⟨fun _ => graph.vertices_complete vertex,
    fun _ => mem_decreasingFinishAll graph vertex⟩

/-- **Vertices share a computed component exactly when strongly connected.** For a directed graph
$G$ and vertices $u$ and $v$, some block of the computed strongly connected components of $G$
contains both $u$ and $v$ if and only if $u$ and $v$ are strongly connected in $G$. -/
public theorem share_component_iff_stronglyConnected {V : Type u} [BEq V]
    [Hashable V] [LawfulBEq V] (graph : DirectedAdjacency V) (left right : V) :
    (∃ block ∈ components graph, left ∈ block ∧ right ∈ block) ↔
      StronglyConnected graph left right := by
  constructor
  · rintro ⟨block, blockMem, leftMem, rightMem⟩
    have blockMem' : block ∈ partitionFrom graph (decreasingFinishAll graph) := by
      rwa [components_eq_partitionFrom] at blockMem
    exact partitionFrom_block_connected graph _ block blockMem' left leftMem right rightMem
  · intro connected
    rw [components_eq_partitionFrom]
    exact partitionFrom_complete graph (decreasingFinishAll graph) left right
      (mem_decreasingFinishAll graph left) (mem_decreasingFinishAll graph right) connected

/-- **Each computed component is a full mutual-reachability class.** Let $G$ be a directed graph,
let $B$ be one of the blocks returned by the strongly connected components algorithm on $G$, and
let $m$ be a vertex of $B$. Then for every vertex $v$ of $G$, the vertices $m$ and $v$ are strongly
connected (each is reachable from the other) if and only if $v$ lies in $B$. -/
public theorem component_maximal {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) (block : List V)
    (blockMem : block ∈ components graph) (member : V) (memberMem : member ∈ block)
    (vertex : V) :
    StronglyConnected graph member vertex ↔ vertex ∈ block := by
  constructor
  · intro connected
    obtain ⟨other, otherMem, memberOther, vertexOther⟩ :=
      (share_component_iff_stronglyConnected graph member vertex).2 connected
    have blocksEqual := block_eq_of_common_member (components_pairwise_disjoint graph)
      blockMem otherMem memberMem memberOther
    simpa [blocksEqual] using vertexOther
  · intro vertexMem
    have blockMem' : block ∈ partitionFrom graph (decreasingFinishAll graph) := by
      rwa [components_eq_partitionFrom] at blockMem
    exact partitionFrom_block_connected graph _ block blockMem'
      member memberMem vertex vertexMem

/-- **SCC partition.** A list $\mathcal{B}$ of vertex lists is an SCC partition of a directed graph
$G$ when every block of $\mathcal{B}$ is nonempty and contains no vertex twice, blocks at different
positions of $\mathcal{B}$ are disjoint, a vertex lies in some block exactly when it is a vertex of
$G$, two vertices lie in a common block exactly when they are strongly connected (each is
reachable from the other), and for every block $B$, every $m \in B$ and every vertex $v$, the
vertices $m$ and $v$ are strongly connected exactly when $v \in B$. -/
public structure IsSCCPartition {V : Type u} (graph : DirectedAdjacency V)
    (blocks : List (List V)) : Prop where
  /-- Every block has a vertex. -/
  nonempty : ∀ block ∈ blocks, block ≠ []
  /-- No block repeats a vertex. -/
  blocksNodup : ∀ block ∈ blocks, block.Nodup
  /-- Different blocks are disjoint. -/
  pairwiseDisjoint : blocks.Pairwise List.Disjoint
  /-- Flattening covers exactly the certified vertex carrier. -/
  covers : ∀ vertex, vertex ∈ blocks.flatten ↔ vertex ∈ graph.vertices
  /-- Co-membership is exactly mutual reachability. -/
  characterizes : ∀ left right,
    (∃ block ∈ blocks, left ∈ block ∧ right ∈ block) ↔
      StronglyConnected graph left right
  /-- Every block is maximal under mutual reachability. -/
  maximal : ∀ block ∈ blocks, ∀ member ∈ block, ∀ vertex,
    StronglyConnected graph member vertex ↔ vertex ∈ block

/-- **The computed components form the SCC partition.** For every directed graph $G$, the list of
blocks returned by the strongly connected components algorithm on $G$ is an SCC partition of $G$:
every block is nonempty and contains no vertex twice, blocks at different positions of the list
are disjoint, every vertex of $G$ lies in some block, two vertices lie in a common block exactly
when they are strongly connected, and for every vertex $m$ of a block $B$ and every vertex $v$,
the vertices $m$ and $v$ are strongly connected exactly when $v$ lies in $B$. -/
public theorem components_isSCCPartition {V : Type u} [BEq V] [Hashable V]
    [LawfulBEq V] (graph : DirectedAdjacency V) :
    IsSCCPartition graph (components graph) where
  nonempty := components_nonempty graph
  blocksNodup := components_nodup graph
  pairwiseDisjoint := components_pairwise_disjoint graph
  covers := mem_flatten_components graph
  characterizes := share_component_iff_stronglyConnected graph
  maximal := component_maximal graph

/-- **Reachability between components.** In a directed graph $G$, a list $S$ of vertices reaches
a list $T$ of vertices when some vertex of $S$ reaches some vertex of $T$ by a directed path in
$G$, possibly of length zero. -/
public def ComponentReaches {V : Type u} (graph : DirectedAdjacency V)
    (source target : List V) : Prop :=
  ∃ sourceVertex ∈ source, ∃ targetVertex ∈ target,
    graph.Reachable sourceVertex targetVertex

/-- **Acyclic condensation.** A list $\mathcal{B}$ of vertex lists of a directed graph $G$ has an
acyclic condensation when, for all $S, T \in \mathcal{B}$, if some vertex of $S$ reaches some
vertex of $T$ in $G$ and some vertex of $T$ reaches some vertex of $S$, then $S = T$. That is,
reachability between the blocks is antisymmetric. -/
public def CondensationAcyclic {V : Type u} (graph : DirectedAdjacency V)
    (blocks : List (List V)) : Prop :=
  ∀ source ∈ blocks, ∀ target ∈ blocks,
    ComponentReaches graph source target →
      ComponentReaches graph target source → source = target

/-- **The condensation of the computed components is acyclic.** Let $G$ be a directed graph and
let $S$ and $T$ be blocks returned by the strongly connected components algorithm on $G$. If some
vertex of $S$ reaches some vertex of $T$ and some vertex of $T$ reaches some vertex of $S$, then
$S = T$.

Equivalently, the condensation relation has no nontrivial directed cycle. -/
public theorem components_condensationAcyclic {V : Type u} [BEq V]
    [Hashable V] [LawfulBEq V] (graph : DirectedAdjacency V) :
    CondensationAcyclic graph (components graph) := by
  intro source sourceMem target targetMem sourceTarget targetSource
  rcases sourceTarget with ⟨sourceVertex, sourceVertexMem,
    targetVertex, targetVertexMem, sourceTargetReach⟩
  rcases targetSource with ⟨targetWitness, targetWitnessMem,
    sourceWitness, sourceWitnessMem, targetSourceReach⟩
  have targetMem' : target ∈ partitionFrom graph (decreasingFinishAll graph) := by
    rwa [components_eq_partitionFrom] at targetMem
  have sourceMem' : source ∈ partitionFrom graph (decreasingFinishAll graph) := by
    rwa [components_eq_partitionFrom] at sourceMem
  have targetConnected : StronglyConnected graph targetVertex targetWitness :=
    partitionFrom_block_connected graph _ target targetMem'
      targetVertex targetVertexMem targetWitness targetWitnessMem
  have sourceConnected : StronglyConnected graph sourceWitness sourceVertex :=
    partitionFrom_block_connected graph _ source sourceMem'
      sourceWitness sourceWitnessMem sourceVertex sourceVertexMem
  have reverseReach : graph.Reachable targetVertex sourceVertex :=
    (targetConnected.1.trans targetSourceReach).trans sourceConnected.1
  have targetInSource : targetVertex ∈ source :=
    (component_maximal graph source sourceMem sourceVertex sourceVertexMem targetVertex).1
      ⟨sourceTargetReach, reverseReach⟩
  exact block_eq_of_common_member (components_pairwise_disjoint graph)
    sourceMem targetMem targetInSource targetVertexMem

end Cslib.Algorithms.Lean.StronglyConnectedComponents
