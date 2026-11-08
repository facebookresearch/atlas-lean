/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind
public import Mathlib.Data.List.Sort
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Deterministic Kruskal spanning forests

This module implements Kruskal's algorithm for a finite graph with vertices
`Fin n`. Input endpoints are natural numbers: an edge is admitted only when
both endpoints are below `n`. Consequently malformed endpoints are ignored,
self-loops are well-formed but rejected as cycle-forming, and parallel edges
remain distinct through their input ordinals.

Valid edges are merge-sorted lexicographically by `(weight, input ordinal)`; keys are
unique because they contain the input ordinal, so the processing order is deterministic.
The scan uses the persistent union-find API to test
whether an edge joins two current components and to merge those components.

`Connected`, `Acyclic`, and `Spans` are declarative properties of edge lists.
The checked theorems prove source containment, acyclicity, component spanning,
the stable nondecreasing processing order, and the standard Kruskal cut
property: every accepted edge is light among all valid edges crossing the
current partition. `kruskal_minimal` proves minimum total weight among all canonical
spanning forests for the retained natural-number weights, by the CLRS cut-exchange argument.
The executable merge sort uses `O(E log E)` key comparisons, followed by one
union-find query per valid edge; this module makes no RAM or inverse-Ackermann
claim because the imported union-find deliberately has neither path compression
nor union by rank.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Kruskal

open UnionFind

/-- An unchecked weighted undirected input edge. -/
public structure RawEdge where
  /-- First endpoint. -/
  source : Nat
  /-- Second endpoint. -/
  target : Nat
  /-- Nonnegative edge weight. -/
  weight : Nat
deriving DecidableEq, Repr

/-- A finite weighted multigraph on `Fin n`, represented by its input edge list. -/
public structure Graph (n : Nat) where
  /-- Input edges in deterministic order. -/
  rawEdges : List RawEdge
deriving DecidableEq, Repr

/-- A validated input edge, retaining its zero-based input ordinal. -/
public structure WeightedEdge (n : Nat) where
  /-- Zero-based position in the original input list. -/
  ordinal : Nat
  /-- Validated first endpoint. -/
  source : Fin n
  /-- Validated second endpoint. -/
  target : Fin n
  /-- Nonnegative edge weight. -/
  weight : Nat
deriving DecidableEq, Repr

/-- Lexicographic sorting key `(weight, input ordinal)`. -/
public def WeightedEdge.key {n : Nat} (edge : WeightedEdge n) : Nat × Nat :=
  (edge.weight, edge.ordinal)

/-- Lexicographic non-strict order on `(weight, input ordinal)` keys. -/
public def KeyLE (left right : Nat × Nat) : Prop :=
  left.1 < right.1 ∨ (left.1 = right.1 ∧ left.2 ≤ right.2)

/-- Lexicographic key comparison is decidable. -/
public instance keyLEDecidable (left right : Nat × Nat) : Decidable (KeyLE left right) := by
  unfold KeyLE
  infer_instance

/-- Validate one raw edge at a supplied input ordinal. -/
public def decodeAt (n ordinal : Nat) (edge : RawEdge) : Option (WeightedEdge n) :=
  if hs : edge.source < n then
    if ht : edge.target < n then
      some {
        ordinal := ordinal
        source := ⟨edge.source, hs⟩
        target := ⟨edge.target, ht⟩
        weight := edge.weight
      }
    else none
  else none

/-- Validate a suffix whose first edge has the supplied input ordinal. -/
public def validEdgesFrom (n ordinal : Nat) : List RawEdge → List (WeightedEdge n)
  | [] => []
  | edge :: rest =>
      match decodeAt n ordinal edge with
      | none => validEdgesFrom n (ordinal + 1) rest
      | some decoded => decoded :: validEdgesFrom n (ordinal + 1) rest

/-- Validate endpoints and attach original input ordinals; malformed edges are omitted. -/
public def validEdges {n : Nat} (graph : Graph n) : List (WeightedEdge n) :=
  validEdgesFrom n 0 graph.rawEdges

/-- Merge sort by `(weight, input ordinal)`; unique keys make the order deterministic. -/
public def sortEdges {n : Nat} (edges : List (WeightedEdge n)) : List (WeightedEdge n) :=
  List.mergeSort edges (fun left right => decide (KeyLE left.key right.key))

/-- Valid edges in stable nondecreasing weight order. -/
public def orderedEdges {n : Nat} (graph : Graph n) : List (WeightedEdge n) :=
  sortEdges (validEdges graph)

private theorem keyLE_trans {left middle right : Nat × Nat}
    (hlm : KeyLE left middle) (hmr : KeyLE middle right) : KeyLE left right := by
  simp only [KeyLE] at hlm hmr ⊢
  omega

private theorem keyLE_total (left right : Nat × Nat) :
    KeyLE left right ∨ KeyLE right left := by
  simp only [KeyLE]
  omega

private theorem mem_sortEdges_iff {n : Nat} (edge : WeightedEdge n)
    (edges : List (WeightedEdge n)) : edge ∈ sortEdges edges ↔ edge ∈ edges :=
  (List.mergeSort_perm edges _).mem_iff

private theorem pairwise_sortEdges {n : Nat} (edges : List (WeightedEdge n)) :
    (sortEdges edges).Pairwise fun left right => KeyLE left.key right.key := by
  have hs := List.pairwise_mergeSort
    (le := fun left right : WeightedEdge n => decide (KeyLE left.key right.key))
    (fun left middle right hlm hmr => by
      simpa using keyLE_trans (left := left.key) (middle := middle.key)
        (right := right.key) (of_decide_eq_true hlm) (of_decide_eq_true hmr))
    (fun left right => by
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using
        keyLE_total left.key right.key)
    edges
  simpa [sortEdges] using hs

/-- The discrete union-find forest used before scanning any edges. -/
public def initialForest (n : Nat) : Forest n where
  parent vertex := vertex
  depth _ := 0
  parent_lt _ h := False.elim (h rfl)

/-- Connectivity obtained by adding a reverse-chronological list of edges. -/
public def ConnectedRev {n : Nat} : List (WeightedEdge n) → Fin n → Fin n → Prop
  | [], left, right => left = right
  | edge :: edges, left, right =>
      ConnectedRev edges left right ∨
        (ConnectedRev edges left edge.source ∧
          ConnectedRev edges right edge.target) ∨
        (ConnectedRev edges left edge.target ∧
          ConnectedRev edges right edge.source)

/-- Vertices are connected when repeated endpoint-class merges identify them. -/
public def Connected {n : Nat} (edges : List (WeightedEdge n))
    (left right : Fin n) : Prop :=
  ConnectedRev edges.reverse left right

/-- Reverse-chronological acyclicity invariant used by the executable scan. -/
public def AcyclicRev {n : Nat} : List (WeightedEdge n) → Prop
  | [] => True
  | edge :: edges =>
      ¬ConnectedRev edges edge.source edge.target ∧ AcyclicRev edges

/-- Each edge joins two components created by the preceding edges. -/
public def Acyclic {n : Nat} (edges : List (WeightedEdge n)) : Prop :=
  AcyclicRev edges.reverse

/-- Every valid input edge has endpoints connected by the candidate forest. -/
public def Spans {n : Nat} (graph : Graph n) (edges : List (WeightedEdge n)) : Prop :=
  ∀ edge ∈ validEdges graph, Connected edges edge.source edge.target

/-- A source-contained acyclic edge list spanning every input component. -/
public def IsSpanningForest {n : Nat} (graph : Graph n)
    (edges : List (WeightedEdge n)) : Prop :=
  (∀ edge ∈ edges, edge ∈ validEdges graph) ∧ Acyclic edges ∧ Spans graph edges

/-- A spanning forest together with the deterministic Kruskal processing order. -/
public def IsOrderedSpanningForest {n : Nat} (graph : Graph n)
    (edges : List (WeightedEdge n)) : Prop :=
  IsSpanningForest graph edges ∧
    edges.Pairwise fun left right => KeyLE left.key right.key

/-- Sum of edge weights, counting parallel edge occurrences separately. -/
public def totalWeight {n : Nat} (edges : List (WeightedEdge n)) : Nat :=
  (edges.map WeightedEdge.weight).sum

private def partitionRev {n : Nat} : List (WeightedEdge n) → Forest n
  | [] => initialForest n
  | edge :: edges => union (partitionRev edges) edge.source edge.target

private theorem partitionRev_equivalent_iff_connectedRev {n : Nat}
    (edges : List (WeightedEdge n)) (left right : Fin n) :
    Equivalent (partitionRev edges) left right ↔ ConnectedRev edges left right := by
  induction edges generalizing left right with
  | nil =>
      simp [partitionRev, ConnectedRev, initialForest, Equivalent, find]
  | cons edge edges induction =>
      simpa only [partitionRev, ConnectedRev, induction] using
        (equivalent_union_iff (partitionRev edges) edge.source edge.target left right)

private theorem connectedRev_refl {n : Nat} (edges : List (WeightedEdge n))
    (vertex : Fin n) : ConnectedRev edges vertex vertex := by
  exact (partitionRev_equivalent_iff_connectedRev edges vertex vertex).mp rfl

/-! `State` and `scan` expose the executable fold so clients can inspect its final partition. -/

/-- Union-find state and reverse-chronological accepted edges during a Kruskal scan. -/
public structure State (n : Nat) where
  /-- Current endpoint partition. -/
  forest : Forest n
  /-- Accepted edges, newest first. -/
  chosenRev : List (WeightedEdge n)

/-- Process one edge, accepting it exactly when it joins two current classes. -/
public def State.step {n : Nat} (state : State n) (edge : WeightedEdge n) : State n :=
  if Equivalent state.forest edge.source edge.target then state
  else {
    forest := union state.forest edge.source edge.target
    chosenRev := edge :: state.chosenRev
  }

/-- Process a list of already ordered edges. -/
public def scan {n : Nat} : State n → List (WeightedEdge n) → State n
  | state, [] => state
  | state, edge :: rest => scan (state.step edge) rest

/--
At every ordered scan position whose edge joins distinct current components,
that edge has minimum stable key among all valid edges crossing the current
union-find partition.
-/
public def HasGreedyCutProperty {n : Nat} (graph : Graph n) : Prop :=
  ∀ before edge after,
    orderedEdges graph = before ++ edge :: after →
    ¬Equivalent (scan ⟨initialForest n, []⟩ before).forest edge.source edge.target →
    ∀ candidate ∈ validEdges graph,
      ¬Equivalent (scan ⟨initialForest n, []⟩ before).forest
        candidate.source candidate.target →
      KeyLE edge.key candidate.key

private def ScanInvariant {n : Nat} (state : State n) : Prop :=
  ∀ left right,
    Equivalent state.forest left right ↔ ConnectedRev state.chosenRev left right

private theorem initial_invariant (n : Nat) :
    ScanInvariant ⟨initialForest n, []⟩ := by
  intro left right
  simp [ConnectedRev, initialForest, Equivalent, find]

private theorem step_invariant {n : Nat} {state : State n}
    (invariant : ScanInvariant state) (edge : WeightedEdge n) :
    ScanInvariant (state.step edge) := by
  by_cases joined : Equivalent state.forest edge.source edge.target
  · simpa [State.step, joined] using invariant
  · intro left right
    simp only [State.step, joined, ↓reduceIte]
    rw [equivalent_union_iff]
    simp only [ConnectedRev]
    rw [invariant, invariant, invariant, invariant, invariant]

private theorem scan_invariant {n : Nat} {state : State n}
    (invariant : ScanInvariant state) (edges : List (WeightedEdge n)) :
    ScanInvariant (scan state edges) := by
  induction edges generalizing state with
  | nil => exact invariant
  | cons edge rest induction =>
      simpa [scan] using induction (step_invariant invariant edge)

private theorem step_acyclicRev {n : Nat} {state : State n}
    (invariant : ScanInvariant state) (acyclic : AcyclicRev state.chosenRev)
    (edge : WeightedEdge n) : AcyclicRev (state.step edge).chosenRev := by
  by_cases joined : Equivalent state.forest edge.source edge.target
  · simpa [State.step, joined] using acyclic
  · have separated : ¬ConnectedRev state.chosenRev edge.source edge.target :=
      fun connected => joined ((invariant _ _).mpr connected)
    simp [State.step, joined, AcyclicRev, separated, acyclic]

private theorem scan_acyclicRev {n : Nat} {state : State n}
    (invariant : ScanInvariant state) (acyclic : AcyclicRev state.chosenRev)
    (edges : List (WeightedEdge n)) : AcyclicRev (scan state edges).chosenRev := by
  induction edges generalizing state with
  | nil => exact acyclic
  | cons edge rest induction =>
      exact induction (step_invariant invariant edge)
        (step_acyclicRev invariant acyclic edge)

private theorem step_preserves_equivalent {n : Nat} (state : State n)
    (edge : WeightedEdge n) {left right : Fin n}
    (connected : Equivalent state.forest left right) :
    Equivalent (state.step edge).forest left right := by
  by_cases joined : Equivalent state.forest edge.source edge.target
  · simpa only [State.step, joined, ↓reduceIte] using connected
  · simp only [State.step, joined, ↓reduceIte]
    exact (equivalent_union_iff _ _ _ _ _).mpr (Or.inl connected)

private theorem step_connects_edge {n : Nat} (state : State n)
    (edge : WeightedEdge n) :
    Equivalent (state.step edge).forest edge.source edge.target := by
  by_cases joined : Equivalent state.forest edge.source edge.target
  · simp only [State.step, joined, ↓reduceIte]
  · simp only [State.step, joined, ↓reduceIte]
    exact union_equivalent state.forest edge.source edge.target

private theorem scan_preserves_equivalent {n : Nat} (state : State n)
    (edges : List (WeightedEdge n)) {left right : Fin n}
    (connected : Equivalent state.forest left right) :
    Equivalent (scan state edges).forest left right := by
  induction edges generalizing state with
  | nil => exact connected
  | cons edge rest induction =>
      exact induction (state := state.step edge)
        (step_preserves_equivalent state edge connected)

private theorem scan_connects_processed {n : Nat} {state : State n}
    (invariant : ScanInvariant state) (edges : List (WeightedEdge n)) :
    ∀ edge ∈ edges,
      ConnectedRev (scan state edges).chosenRev edge.source edge.target := by
  induction edges generalizing state with
  | nil => simp
  | cons head rest induction =>
      intro edge edge_mem
      simp only [List.mem_cons] at edge_mem
      have nextInvariant := step_invariant invariant head
      simp only [scan]
      rcases edge_mem with rfl | edge_mem
      · apply ((scan_invariant nextInvariant rest) edge.source edge.target).mp
        exact scan_preserves_equivalent (state.step edge) rest
          (step_connects_edge state edge)
      · exact induction nextInvariant edge edge_mem

private theorem scan_connects_processed_equivalent {n : Nat} {state : State n}
    (invariant : ScanInvariant state) (edges : List (WeightedEdge n)) :
    ∀ edge ∈ edges,
      Equivalent (scan state edges).forest edge.source edge.target := by
  intro edge edge_mem
  exact ((scan_invariant invariant edges) edge.source edge.target).mpr
    (scan_connects_processed invariant edges edge edge_mem)

private theorem scan_decompose {n : Nat} (state : State n)
    (edges : List (WeightedEdge n)) :
    ∃ picked : List (WeightedEdge n), picked.Sublist edges ∧
      (scan state edges).chosenRev = picked.reverse ++ state.chosenRev := by
  induction edges generalizing state with
  | nil => exact ⟨[], List.Sublist.slnil, by simp [scan]⟩
  | cons edge rest induction =>
      by_cases joined : Equivalent state.forest edge.source edge.target
      · obtain ⟨picked, sublist, chosen⟩ := induction state
        exact ⟨picked, sublist.cons edge, by simpa [scan, State.step, joined] using chosen⟩
      · obtain ⟨picked, sublist, chosen⟩ := induction (state.step edge)
        refine ⟨edge :: picked, ?_, ?_⟩
        · exact List.cons_sublist_cons.mpr sublist
        · simpa [scan, State.step, joined, List.reverse_cons, List.append_assoc] using chosen

/-- Run stable Kruskal selection and return accepted edges in processing order. -/
public def kruskal {n : Nat} (graph : Graph n) : List (WeightedEdge n) :=
  (scan ⟨initialForest n, []⟩ (orderedEdges graph)).chosenRev.reverse

private theorem kruskal_sublist_ordered {n : Nat} (graph : Graph n) :
    (kruskal graph).Sublist (orderedEdges graph) := by
  obtain ⟨picked, sublist, chosen⟩ :=
    scan_decompose (⟨initialForest n, []⟩ : State n) (orderedEdges graph)
  have : kruskal graph = picked := by
    simp only [kruskal, chosen, List.append_nil, List.reverse_reverse]
  simpa [this] using sublist

/-- Every selected edge is a validated occurrence from the input list. -/
public theorem kruskal_edge_mem_valid {n : Nat} (graph : Graph n)
    {edge : WeightedEdge n} (selected : edge ∈ kruskal graph) :
    edge ∈ validEdges graph := by
  have inOrdered := (kruskal_sublist_ordered graph).mem selected
  exact (mem_sortEdges_iff edge (validEdges graph)).mp inOrdered

/-- Kruskal never accepts an edge whose endpoints were already connected. -/
public theorem kruskal_acyclic {n : Nat} (graph : Graph n) :
    Acyclic (kruskal graph) := by
  have acyclic := scan_acyclicRev (initial_invariant n) (by simp [AcyclicRev])
    (orderedEdges graph)
  simpa [Acyclic, kruskal] using acyclic

/-- Kruskal connects the endpoints of every valid input edge, including in disconnected graphs. -/
public theorem kruskal_spans {n : Nat} (graph : Graph n) :
    Spans graph (kruskal graph) := by
  intro edge inValid
  have inOrdered : edge ∈ orderedEdges graph :=
    (mem_sortEdges_iff edge (validEdges graph)).mpr inValid
  have connected := scan_connects_processed (initial_invariant n)
    (orderedEdges graph) edge inOrdered
  simpa [Connected, kruskal] using connected

/-- The selected edge list is ordered by weight and then by original input ordinal. -/
public theorem kruskal_pairwise_key_le {n : Nat} (graph : Graph n) :
    (kruskal graph).Pairwise fun left right => KeyLE left.key right.key := by
  exact (pairwise_sortEdges (validEdges graph)).sublist (kruskal_sublist_ordered graph)

/-- Each accepted edge is a light edge for the cut induced by the current partition. -/
public theorem kruskal_greedy_cut_property {n : Nat} (graph : Graph n) :
    HasGreedyCutProperty graph := by
  intro before edge after decomposition _ candidate inValid crossing
  have inOrdered : candidate ∈ orderedEdges graph :=
    (mem_sortEdges_iff candidate (validEdges graph)).mpr inValid
  rw [decomposition] at inOrdered
  simp only [List.mem_append, List.mem_cons] at inOrdered
  rcases inOrdered with inBefore | rfl | inAfter
  · exact False.elim (crossing
      (scan_connects_processed_equivalent (initial_invariant n) before candidate inBefore))
  · exact (keyLE_total candidate.key candidate.key).elim id id
  · have sorted : (before ++ edge :: after).Pairwise
        (fun left right => KeyLE left.key right.key) := by
      rw [← decomposition]
      exact pairwise_sortEdges (validEdges graph)
    have tailSorted := (List.pairwise_append.mp sorted).2.1
    exact (List.pairwise_cons.mp tailSorted).1 candidate inAfter

/-- Each accepted edge has minimum weight among all edges crossing the current partition. -/
public theorem kruskal_light_edge {n : Nat} (graph : Graph n)
    (before : List (WeightedEdge n)) (edge : WeightedEdge n)
    (after : List (WeightedEdge n))
    (decomposition : orderedEdges graph = before ++ edge :: after)
    (separated :
      ¬Equivalent (scan ⟨initialForest n, []⟩ before).forest edge.source edge.target)
    (candidate : WeightedEdge n) (inValid : candidate ∈ validEdges graph)
    (crossing :
      ¬Equivalent (scan ⟨initialForest n, []⟩ before).forest
        candidate.source candidate.target) :
    edge.weight ≤ candidate.weight := by
  have keyBound := kruskal_greedy_cut_property graph before edge after decomposition
    separated candidate inValid crossing
  simp only [WeightedEdge.key, KeyLE] at keyBound
  omega

/-- Kruskal returns a source-contained acyclic edge list spanning every input component. -/
public theorem kruskal_isSpanningForest {n : Nat} (graph : Graph n) :
    IsSpanningForest graph (kruskal graph) := by
  exact ⟨fun _ selected => kruskal_edge_mem_valid graph selected,
    kruskal_acyclic graph, kruskal_spans graph⟩

/-- Kruskal returns a spanning forest in deterministic stable processing order. -/
public theorem kruskal_isOrderedSpanningForest {n : Nat} (graph : Graph n) :
    IsOrderedSpanningForest graph (kruskal graph) :=
  ⟨kruskal_isSpanningForest graph, kruskal_pairwise_key_le graph⟩

/-! ## Minimum-weight certificate

The private exchange proof operates on input occurrences. Deleting an edge breaks its
forest path, and replacing a cut edge by the next accepted edge preserves connectivity.
A spanning completion containing the scan's accepted edges never gains total weight.
At the end, acyclicity forces the completion to have precisely the accepted occurrences.
-/

private theorem connectedRev_equivalence {n : Nat} (edges : List (WeightedEdge n)) :
    Equivalence (ConnectedRev edges) := by
  refine ⟨connectedRev_refl edges, ?_, ?_⟩
  · intro left right h
    exact (partitionRev_equivalent_iff_connectedRev edges right left).mp
      ((partitionRev_equivalent_iff_connectedRev edges left right).mpr h).symm
  · intro left middle right hlm hmr
    exact (partitionRev_equivalent_iff_connectedRev edges left right).mp
      (((partitionRev_equivalent_iff_connectedRev edges left middle).mpr hlm).trans
        ((partitionRev_equivalent_iff_connectedRev edges middle right).mpr hmr))

private theorem connectedRev_mem {n : Nat} (edges : List (WeightedEdge n))
    (edge : WeightedEdge n) (h : edge ∈ edges) :
    ConnectedRev edges edge.source edge.target := by
  induction edges with
  | nil => simp at h
  | cons first rest ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (Or.inl ⟨connectedRev_refl rest edge.source,
          connectedRev_refl rest edge.target⟩)
      · exact Or.inl (ih h)

private theorem connectedRev_le {n : Nat} (edges : List (WeightedEdge n))
    (relation : Fin n → Fin n → Prop) (equivalence : Equivalence relation)
    (contains : ∀ edge ∈ edges, relation edge.source edge.target)
    {left right : Fin n} (connected : ConnectedRev edges left right) :
    relation left right := by
  induction edges generalizing left right with
  | nil =>
      change left = right at connected
      subst right
      exact equivalence.refl left
  | cons edge rest ih =>
      have tail := fun candidate h => contains candidate (List.mem_cons_of_mem edge h)
      rcases connected with h | ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact ih tail h
      · exact equivalence.trans (ih tail hl)
          (equivalence.trans (contains edge List.mem_cons_self) (equivalence.symm (ih tail hr)))
      · exact equivalence.trans (ih tail hl)
          (equivalence.trans (equivalence.symm (contains edge List.mem_cons_self))
            (equivalence.symm (ih tail hr)))

private theorem connectedRev_mono {n : Nat} {first second : List (WeightedEdge n)}
    (subset : first ⊆ second) {left right : Fin n}
    (connected : ConnectedRev first left right) : ConnectedRev second left right :=
  connectedRev_le first (ConnectedRev second) (connectedRev_equivalence second)
    (fun edge h => connectedRev_mem second edge (subset h)) connected

private theorem connectedRev_perm {n : Nat} {first second : List (WeightedEdge n)}
    (permutation : first.Perm second) (left right : Fin n) :
    ConnectedRev first left right ↔ ConnectedRev second left right :=
  ⟨connectedRev_mono permutation.subset, connectedRev_mono permutation.symm.subset⟩

private theorem acyclicRev_swap {n : Nat} (first second : WeightedEdge n)
    (edges : List (WeightedEdge n)) :
    AcyclicRev (first :: second :: edges) ↔ AcyclicRev (second :: first :: edges) := by
  have equivalence := connectedRev_equivalence edges
  simp only [AcyclicRev, ConnectedRev]
  grind only [equivalence.refl, equivalence.symm, equivalence.trans]

private theorem acyclicRev_perm {n : Nat} {first second : List (WeightedEdge n)}
    (permutation : first.Perm second) : AcyclicRev first ↔ AcyclicRev second := by
  induction permutation with
  | nil => rfl
  | cons edge permutation ih =>
      simp only [AcyclicRev, connectedRev_perm permutation, ih]
  | swap first second edges => exact acyclicRev_swap second first edges
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem acyclicRev_nodup {n : Nat} {edges : List (WeightedEdge n)}
    (acyclic : AcyclicRev edges) : edges.Nodup := by
  induction edges with
  | nil => exact List.nodup_nil
  | cons edge rest ih =>
      obtain ⟨separated, tail⟩ := acyclic
      exact List.nodup_cons.mpr ⟨fun h => separated (connectedRev_mem rest edge h), ih tail⟩

private theorem acyclicRev_erase {n : Nat} {edges : List (WeightedEdge n)}
    (acyclic : AcyclicRev edges) (edge : WeightedEdge n) (member : edge ∈ edges) :
    ¬ConnectedRev (edges.erase edge) edge.source edge.target ∧ AcyclicRev (edges.erase edge) :=
  (acyclicRev_perm (List.perm_cons_erase member)).mp acyclic

private theorem connectedRev_cons_no_reconnect {n : Nat}
    {edges smaller : List (WeightedEdge n)} (subset : smaller ⊆ edges)
    (edge : WeightedEdge n) (separated : ¬ConnectedRev edges edge.source edge.target)
    {left right : Fin n} (old : ConnectedRev edges left right)
    (broken : ¬ConnectedRev smaller left right) :
    ¬ConnectedRev (edge :: smaller) left right := by
  have equivalence := connectedRev_equivalence edges
  have monotone : ∀ u v, ConnectedRev smaller u v → ConnectedRev edges u v :=
    fun _ _ => connectedRev_mono subset
  change ¬(ConnectedRev smaller left right ∨ _ ∨ _)
  grind only [equivalence.symm, equivalence.trans]

private theorem connectedRev_cons_broken_segment {n : Nat}
    {edges smaller : List (WeightedEdge n)} (subset : smaller ⊆ edges)
    (edge : WeightedEdge n) (separated : ¬ConnectedRev edges edge.source edge.target)
    {left right first second : Fin n}
    (orientation : (first = edge.source ∧ second = edge.target) ∨
      (first = edge.target ∧ second = edge.source))
    (leftConnected : ConnectedRev edges left first)
    (rightConnected : ConnectedRev edges right second)
    (broken : ¬ConnectedRev smaller left first ∨ ¬ConnectedRev smaller right second) :
    ¬ConnectedRev (edge :: smaller) left right := by
  have equivalence := connectedRev_equivalence edges
  have monotone : ∀ u v, ConnectedRev smaller u v → ConnectedRev edges u v :=
    fun _ _ => connectedRev_mono subset
  change ¬(ConnectedRev smaller left right ∨ _ ∨ _)
  grind only [equivalence.symm, equivalence.trans]

private theorem connectedRev_cut_edge {n : Nat} (edges : List (WeightedEdge n))
    (relation : Fin n → Fin n → Prop) (equivalence : Equivalence relation)
    (acyclic : AcyclicRev edges) {left right : Fin n}
    (connected : ConnectedRev edges left right) (crossing : ¬relation left right) :
    ∃ edge ∈ edges, ¬relation edge.source edge.target ∧
      ¬ConnectedRev (edges.erase edge) left right := by
  classical
  induction edges generalizing left right with
  | nil =>
      change left = right at connected
      subst right
      exact (crossing (equivalence.refl left)).elim
  | cons first rest ih =>
      have firstNotMem := (List.nodup_cons.mp (acyclicRev_nodup acyclic)).1
      have lift (edge : WeightedEdge n) (member : edge ∈ rest)
          (cut : ¬relation edge.source edge.target)
          (broken : ¬ConnectedRev (first :: rest.erase edge) left right) :
          ∃ edge ∈ first :: rest, ¬relation edge.source edge.target ∧
            ¬ConnectedRev ((first :: rest).erase edge) left right := by
        have different : first ≠ edge := by
          intro h
          exact firstNotMem (h ▸ member)
        refine ⟨edge, List.mem_cons_of_mem first member, cut, ?_⟩
        simpa [different] using broken
      by_cases old : ConnectedRev rest left right
      · obtain ⟨edge, member, cut, broken⟩ := ih acyclic.2 old crossing
        exact lift edge member cut
          (connectedRev_cons_no_reconnect List.erase_subset first acyclic.1 old broken)
      · by_cases linked : relation first.source first.target
        · obtain ⟨a, b, orientation, hl, hr⟩ :
              ∃ a b, ((a = first.source ∧ b = first.target) ∨
                (a = first.target ∧ b = first.source)) ∧
                ConnectedRev rest left a ∧ ConnectedRev rest right b := by
            rcases connected with h | ⟨hl, hr⟩ | ⟨hl, hr⟩
            · exact (old h).elim
            · exact ⟨first.source, first.target, Or.inl ⟨rfl, rfl⟩, hl, hr⟩
            · exact ⟨first.target, first.source, Or.inr ⟨rfl, rfl⟩, hl, hr⟩
          have linked' : relation a b := by
            grind only [equivalence.symm]
          by_cases leftCut : relation left a
          · have rightCut : ¬relation right b := by
              grind only [equivalence.symm, equivalence.trans]
            obtain ⟨edge, member, cut, broken⟩ := ih acyclic.2 hr rightCut
            exact lift edge member cut
              (connectedRev_cons_broken_segment List.erase_subset first acyclic.1
                orientation hl hr (Or.inr broken))
          · obtain ⟨edge, member, cut, broken⟩ := ih acyclic.2 hl leftCut
            exact lift edge member cut
              (connectedRev_cons_broken_segment List.erase_subset first acyclic.1
                orientation hl hr (Or.inl broken))
        · refine ⟨first, List.mem_cons_self, linked, ?_⟩
          simpa using old

private theorem connectedRev_exchange_iff {n : Nat} (edges : List (WeightedEdge n))
    (oldEdge newEdge : WeightedEdge n) (member : oldEdge ∈ edges)
    (connected : ConnectedRev edges newEdge.source newEdge.target)
    (broken : ¬ConnectedRev (edges.erase oldEdge) newEdge.source newEdge.target)
    (left right : Fin n) :
    ConnectedRev (newEdge :: edges.erase oldEdge) left right ↔
      ConnectedRev edges left right := by
  have equivalence := connectedRev_equivalence (edges.erase oldEdge)
  have oldConnected : ConnectedRev (newEdge :: edges.erase oldEdge)
      oldEdge.source oldEdge.target := by
    have h := (connectedRev_perm (List.perm_cons_erase member)
      newEdge.source newEdge.target).mp connected
    rcases h with h | ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact (broken h).elim
    · exact Or.inr (Or.inl ⟨equivalence.symm hl, equivalence.symm hr⟩)
    · exact Or.inr (Or.inr ⟨equivalence.symm hr, equivalence.symm hl⟩)
  constructor
  · apply connectedRev_le _ (ConnectedRev edges) (connectedRev_equivalence edges)
    intro edge h
    rcases List.mem_cons.mp h with rfl | h
    · exact connected
    · exact connectedRev_mem edges edge (List.erase_subset h)
  · apply connectedRev_le _ (ConnectedRev (newEdge :: edges.erase oldEdge))
      (connectedRev_equivalence _)
    intro edge h
    by_cases same : edge = oldEdge
    · exact same ▸ oldConnected
    · exact Or.inl (connectedRev_mem _ edge ((List.mem_erase_of_ne same).mpr h))

private theorem totalWeight_perm {n : Nat} {first second : List (WeightedEdge n)}
    (permutation : first.Perm second) : totalWeight first = totalWeight second :=
  (permutation.map WeightedEdge.weight).sum_eq

private theorem spanningForest_exchange {n : Nat} (graph : Graph n)
    (edges accepted : List (WeightedEdge n))
    (forest : IsSpanningForest graph edges.reverse) (contains : accepted ⊆ edges)
    (newEdge : WeightedEdge n) (valid : newEdge ∈ validEdges graph)
    (crossing : ¬ConnectedRev accepted newEdge.source newEdge.target)
    (light : ∀ edge ∈ validEdges graph,
      ¬ConnectedRev accepted edge.source edge.target → newEdge.weight ≤ edge.weight) :
    ∃ completion : List (WeightedEdge n), IsSpanningForest graph completion.reverse ∧
      newEdge :: accepted ⊆ completion ∧ totalWeight completion ≤ totalWeight edges := by
  have acyclic : AcyclicRev edges := by
    simpa only [Acyclic, List.reverse_reverse] using forest.2.1
  have connected : ConnectedRev edges newEdge.source newEdge.target := by
    simpa only [Connected, List.reverse_reverse] using forest.2.2 newEdge valid
  obtain ⟨oldEdge, member, cut, broken⟩ := connectedRev_cut_edge edges
    (ConnectedRev accepted) (connectedRev_equivalence accepted) acyclic connected crossing
  have oldValid : oldEdge ∈ validEdges graph :=
    forest.1 oldEdge (List.mem_reverse.mpr member)
  have lower := light oldEdge oldValid cut
  refine ⟨newEdge :: edges.erase oldEdge, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro edge h
      rcases List.mem_cons.mp (List.mem_reverse.mp h) with rfl | h
      · exact valid
      · exact forest.1 edge (List.mem_reverse.mpr (List.erase_subset h))
    · simpa only [Acyclic, List.reverse_reverse, AcyclicRev] using
        And.intro broken (acyclicRev_erase acyclic oldEdge member).2
    · intro edge h
      simp only [Connected, List.reverse_reverse]
      apply (connectedRev_exchange_iff edges oldEdge newEdge member connected broken _ _).mpr
      simpa only [Connected, List.reverse_reverse] using forest.2.2 edge h
  · intro edge h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · have different : edge ≠ oldEdge := by
        intro same
        exact cut (same ▸ connectedRev_mem accepted edge h)
      exact List.mem_cons_of_mem newEdge ((List.mem_erase_of_ne different).mpr (contains h))
  · have oldWeight := totalWeight_perm (List.perm_cons_erase member)
    change newEdge.weight + totalWeight (edges.erase oldEdge) ≤ totalWeight edges
    change totalWeight edges = oldEdge.weight + totalWeight (edges.erase oldEdge) at oldWeight
    omega

private theorem scan_append {n : Nat} (state : State n)
    (first second : List (WeightedEdge n)) :
    scan state (first ++ second) = scan (scan state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons edge rest ih => exact ih (state.step edge)

private theorem scan_completion {n : Nat} (graph : Graph n)
    (before rest : List (WeightedEdge n))
    (decomposition : orderedEdges graph = before ++ rest)
    (edges : List (WeightedEdge n)) (forest : IsSpanningForest graph edges.reverse)
    (contains : (scan ⟨initialForest n, []⟩ before).chosenRev ⊆ edges) :
    ∃ completion : List (WeightedEdge n), IsSpanningForest graph completion.reverse ∧
      (scan ⟨initialForest n, []⟩ (orderedEdges graph)).chosenRev ⊆ completion ∧
      totalWeight completion ≤ totalWeight edges := by
  induction rest generalizing before edges with
  | nil =>
      refine ⟨edges, forest, ?_, le_rfl⟩
      simpa only [decomposition, List.append_nil] using contains
  | cons edge rest ih =>
      have next : orderedEdges graph = (before ++ [edge]) ++ rest := by
        simpa only [List.append_assoc, List.singleton_append] using decomposition
      have prefixState : scan ⟨initialForest n, []⟩ (before ++ [edge]) =
          (scan ⟨initialForest n, []⟩ before).step edge := by
        simp only [scan_append, scan]
      by_cases same : Equivalent (scan ⟨initialForest n, []⟩ before).forest
          edge.source edge.target
      · apply ih (before ++ [edge]) next edges forest
        simpa only [prefixState, State.step, ite_eq_left same] using contains
      · have invariant := scan_invariant (initial_invariant n) before
        have crossing : ¬ConnectedRev (scan ⟨initialForest n, []⟩ before).chosenRev
            edge.source edge.target := fun h => same ((invariant _ _).mpr h)
        have valid : edge ∈ validEdges graph := by
          apply (mem_sortEdges_iff edge (validEdges graph)).mp
          change edge ∈ orderedEdges graph
          rw [decomposition]
          exact List.mem_append_right before List.mem_cons_self
        have light : ∀ candidate ∈ validEdges graph,
            ¬ConnectedRev (scan ⟨initialForest n, []⟩ before).chosenRev
              candidate.source candidate.target → edge.weight ≤ candidate.weight := by
          intro candidate member cut
          exact kruskal_light_edge graph before edge rest decomposition same candidate member
            (fun h => cut ((invariant _ _).mp h))
        obtain ⟨updated, updatedForest, updatedContains, bound⟩ := spanningForest_exchange graph
          edges (scan ⟨initialForest n, []⟩ before).chosenRev forest contains edge
          valid crossing light
        have nextContains :
            (scan ⟨initialForest n, []⟩ (before ++ [edge])).chosenRev ⊆ updated := by
          simpa only [prefixState, State.step, ite_eq_right same] using updatedContains
        obtain ⟨completion, certificate, inclusion, smaller⟩ :=
          ih (before ++ [edge]) next updated updatedForest nextContains
        exact ⟨completion, certificate, inclusion, smaller.trans bound⟩

private theorem spanningForest_contains_perm {n : Nat} (graph : Graph n)
    (accepted edges : List (WeightedEdge n))
    (acceptedForest : IsSpanningForest graph accepted.reverse)
    (forest : IsSpanningForest graph edges.reverse) (contains : accepted ⊆ edges) :
    accepted.Perm edges := by
  classical
  have acceptedAcyclic : AcyclicRev accepted := by
    simpa only [Acyclic, List.reverse_reverse] using acceptedForest.2.1
  have acyclic : AcyclicRev edges := by
    simpa only [Acyclic, List.reverse_reverse] using forest.2.1
  have backwards : edges ⊆ accepted := by
    intro edge member
    by_contra missing
    have subset : accepted ⊆ edges.erase edge := by
      intro candidate h
      have different : candidate ≠ edge := fun same => missing (same ▸ h)
      exact (List.mem_erase_of_ne different).mpr (contains h)
    have valid := forest.1 edge (List.mem_reverse.mpr member)
    have connected : ConnectedRev accepted edge.source edge.target := by
      simpa only [Connected, List.reverse_reverse] using acceptedForest.2.2 edge valid
    exact (acyclicRev_erase acyclic edge member).1 (connectedRev_mono subset connected)
  exact (List.subperm_of_subset (acyclicRev_nodup acceptedAcyclic) contains).antisymm
    (List.subperm_of_subset (acyclicRev_nodup acyclic) backwards)

/-- With natural-number weights, Kruskal has minimum total weight among all canonical
spanning forests, including disconnected graphs and parallel input occurrences.
This is the cut-exchange argument of CLRS, fourth edition, §21.2. -/
public theorem kruskal_minimal {n : Nat} (graph : Graph n)
    (edges : List (WeightedEdge n)) (forest : IsSpanningForest graph edges) :
    totalWeight (kruskal graph) ≤ totalWeight edges := by
  obtain ⟨completion, certificate, contains, bound⟩ :=
    scan_completion graph [] (orderedEdges graph) rfl edges.reverse
      (by simpa only [List.reverse_reverse] using forest) (by simp [scan])
  have permutation := spanningForest_contains_perm graph
    (scan ⟨initialForest n, []⟩ (orderedEdges graph)).chosenRev completion
    (kruskal_isSpanningForest graph) certificate contains
  calc
    totalWeight (kruskal graph) =
        totalWeight (scan ⟨initialForest n, []⟩ (orderedEdges graph)).chosenRev := by
      simp only [kruskal, totalWeight, List.map_reverse, List.sum_reverse]
    _ = totalWeight completion := totalWeight_perm permutation
    _ ≤ totalWeight edges.reverse := bound
    _ = totalWeight edges := by
      simp only [totalWeight, List.map_reverse, List.sum_reverse]

end Cslib.Algorithms.Lean.Kruskal
