/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.DirectedAdjacency
public import Cslib.Algorithms.Lean.TimeM

/-!
# Dense Dijkstra shortest paths

This module implements the dense-array form of Dijkstra's algorithm for an ordered finite
directed graph. It follows Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*,
fourth edition, Section 22.3, pages 620--624.

`none` represents an infinite distance. Minimum selection scans the full vertex list on every
round, and relaxation scans every outgoing adjacency entry, including duplicates and self-loops.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DirectedAdjacency

universe u

variable {V : Type u}

/-- Sum an endpoint weight over consecutive vertices of a path. -/
@[expose] public def pathWeight (weight : V → V → Nat) : List V → Nat
  | [] | [_] => 0
  | source :: target :: rest =>
      weight source target + pathWeight weight (target :: rest)

/-- A concrete source-to-target graph path with its stated endpoint weight. -/
@[expose] public def HasPathWeight (graph : DirectedAdjacency V) (weight : V → V → Nat)
    (source target : V) (distance : Nat) : Prop :=
  ∃ path, path.IsChainFromTo graph.Edge source target ∧
    pathWeight weight path = distance

/-- Reachability is equivalent to having a concrete path of some natural weight. -/
public theorem reachable_iff_exists_hasPathWeight (graph : DirectedAdjacency V)
    (weight : V → V → Nat) (source target : V) :
    graph.Reachable source target ↔
      ∃ distance, HasPathWeight graph weight source target distance := by
  constructor
  · intro reachable
    obtain ⟨length, walk⟩ := reachable_iff_exists_walk.mp reachable
    obtain ⟨path, chain, -⟩ := walk.exists_isChainFromTo
    exact ⟨pathWeight weight path, path, chain, rfl⟩
  · rintro ⟨_, path, chain, -⟩
    exact chain.reflTransGen

private lemma pathWeight_cons_of_ne_nil (weight : V → V → Nat) (source : V)
    {path : List V} (hne : path ≠ []) :
    pathWeight weight (source :: path) =
      weight source (path.head hne) + pathWeight weight path := by
  cases path with
  | nil => contradiction
  | cons target rest => rfl

private lemma pathWeight_append_singleton (weight : V → V → Nat) {path : List V}
    (hne : path ≠ []) (target : V) :
    pathWeight weight (path ++ [target]) =
      pathWeight weight path + weight (path.getLast hne) target := by
  induction path with
  | nil => contradiction
  | cons source rest induction =>
      cases rest with
      | nil => simp [pathWeight]
      | cons next rest =>
          simp only [List.cons_append, pathWeight]
          have hinduction := induction (by simp)
          simp only [List.cons_append] at hinduction
          rw [hinduction]
          simp [List.getLast_cons, Nat.add_assoc]

private lemma HasPathWeight.cons {graph : DirectedAdjacency V} {weight : V → V → Nat}
    {source next target : V} {distance : Nat} (edge : graph.Edge source next)
    (path : HasPathWeight graph weight next target distance) :
    HasPathWeight graph weight source target (weight source next + distance) := by
  obtain ⟨vertices, chain, hweight⟩ := path
  refine ⟨source :: vertices, chain.cons edge, ?_⟩
  rw [pathWeight_cons_of_ne_nil weight source chain.ne_nil, chain.head_eq, hweight]

private lemma HasPathWeight.snoc {graph : DirectedAdjacency V} {weight : V → V → Nat}
    {source previous target : V} {distance : Nat}
    (path : HasPathWeight graph weight source previous distance)
    (edge : graph.Edge previous target) :
    HasPathWeight graph weight source target (distance + weight previous target) := by
  obtain ⟨vertices, chain, hweight⟩ := path
  refine ⟨vertices ++ [target], chain.snoc edge, ?_⟩
  rw [pathWeight_append_singleton weight chain.ne_nil, chain.getLast_eq, hweight]

private lemma first_unsettled_edge {graph : DirectedAdjacency V}
    {weight : V → V → Nat} {settled : V → Bool} {source target : V}
    {distance : Nat} (path : HasPathWeight graph weight source target distance)
    (hsource : settled source = true) (htarget : settled target = false) :
    ∃ previous next previousDistance,
      settled previous = true ∧ settled next = false ∧ graph.Edge previous next ∧
        HasPathWeight graph weight source previous previousDistance ∧
        previousDistance + weight previous next ≤ distance := by
  obtain ⟨vertices, chain, hweight⟩ := path
  induction chain using List.IsChainFromTo.head_induction_on generalizing distance with
  | h_refl =>
      rw [hsource] at htarget
      contradiction
  | @h_head first second last tail edge chainTail induction =>
      by_cases hsecond : settled second = false
      · refine ⟨first, second, 0, hsource, hsecond, edge,
          ⟨[first], List.isChainFromTo_singleton, rfl⟩, ?_⟩
        rw [← hweight, pathWeight_cons_of_ne_nil weight first chainTail.ne_nil,
          chainTail.head_eq]
        omega
      · have hsecondSettled : settled second = true := by
          cases hvalue : settled second
          · exact False.elim (hsecond hvalue)
          · rfl
        obtain ⟨previous, next, previousDistance, hprevious, hnext, hnextEdge,
            hprefix, hbound⟩ := induction hsecondSettled htarget rfl
        refine ⟨previous, next, weight first second + previousDistance,
          hprevious, hnext, hnextEdge, hprefix.cons edge, ?_⟩
        rw [← hweight, pathWeight_cons_of_ne_nil weight first chainTail.ne_nil,
          chainTail.head_eq]
        omega

/-- Number of adjacency-list entries, including duplicates and self-loops. -/
@[expose] public def adjacencyEntryCount (graph : DirectedAdjacency V) : Nat :=
  (graph.vertices.map fun vertex => (graph.adjacency vertex).length).sum

/-- Counts full minimum scans and inspected adjacency entries separately. -/
public structure DijkstraCost where
  /-- Vertex entries inspected by minimum selection. -/
  minScans : Nat
  /-- Adjacency entries inspected by relaxation. -/
  edgeRelaxations : Nat
  deriving DecidableEq

public instance : Zero DijkstraCost where
  zero := ⟨0, 0⟩

public instance : Add DijkstraCost where
  add left right :=
    ⟨left.minScans + right.minScans,
      left.edgeRelaxations + right.edgeRelaxations⟩

public instance : AddMonoid DijkstraCost where
  add_assoc left middle right := by
    rcases left with ⟨leftScan, leftRelax⟩
    rcases middle with ⟨middleScan, middleRelax⟩
    rcases right with ⟨rightScan, rightRelax⟩
    change DijkstraCost.mk (leftScan + middleScan + rightScan)
      (leftRelax + middleRelax + rightRelax) =
      DijkstraCost.mk (leftScan + (middleScan + rightScan))
        (leftRelax + (middleRelax + rightRelax))
    rw [Nat.add_assoc, Nat.add_assoc]
  zero_add cost := by
    rcases cost with ⟨scan, relax⟩
    change DijkstraCost.mk (0 + scan) (0 + relax) = DijkstraCost.mk scan relax
    simp
  add_zero cost := by
    rcases cost with ⟨scan, relax⟩
    change DijkstraCost.mk (scan + 0) (relax + 0) = DijkstraCost.mk scan relax
    simp
  nsmul count cost :=
    ⟨count * cost.minScans, count * cost.edgeRelaxations⟩
  nsmul_zero cost := by
    rcases cost with ⟨scan, relax⟩
    change DijkstraCost.mk (0 * scan) (0 * relax) = DijkstraCost.mk 0 0
    simp
  nsmul_succ count cost := by
    rcases cost with ⟨scan, relax⟩
    change DijkstraCost.mk ((count + 1) * scan) ((count + 1) * relax) =
      DijkstraCost.mk (count * scan + scan) (count * relax + relax)
    rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.one_mul]

/-- Total charged events in the dense Dijkstra cost model. -/
@[expose] public def DijkstraCost.total (cost : DijkstraCost) : Nat :=
  cost.minScans + cost.edgeRelaxations

/-- Dense Dijkstra output in fixed-length, array-backed vectors. -/
public structure DijkstraResult (n : Nat) where
  /-- The starting vertex. -/
  source : Fin n
  /-- Final distance estimates, with `none` denoting infinity. -/
  distance : Vector (Option Nat) n
  /-- Shortest-path predecessor pointers. -/
  predecessor : Vector (Option (Fin n)) n

private def followPredecessors {n : Nat} (predecessor : Vector (Option (Fin n)) n)
    (source current : Fin n) : Nat → Option (List (Fin n))
  | 0 => if current = source then some [source] else none
  | fuel + 1 =>
      if current = source then
        some [source]
      else
        match predecessor.get current with
        | none => none
        | some previous =>
            (followPredecessors predecessor source previous fuel).map
              fun path => path ++ [current]

/-- Follow predecessors for at most `n` steps, returning source-to-target order. -/
public def DijkstraResult.pathTo? {n : Nat} (result : DijkstraResult n) (target : Fin n) :
    Option (List (Fin n)) :=
  let rec @[reducible] go (current : Fin n) : Nat → Option (List (Fin n))
    | 0 => if current = result.source then some [result.source] else none
    | fuel + 1 =>
        if current = result.source then
          some [result.source]
        else
          match result.predecessor.get current with
          | none => none
          | some previous => (go previous fuel).map fun path => path ++ [current]
  go target n

/-- Dense Dijkstra with natural endpoint weights and exact abstract event counts. -/
public def dijkstra {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) :
    TimeM DijkstraCost (DijkstraResult n) :=
  let State := Vector (Option Nat) n × Vector (Option (Fin n)) n ×
    Vector Bool n × Vector (Option Nat) n × List (Fin n)
  let update {α : Type} (values : Vector α n) (index : Fin n) (value : α) :
      Vector α n :=
    values.set index.val value index.isLt
  let distanceLess (left right : Option Nat) : Bool :=
    match left, right with
    | some leftDistance, some rightDistance => leftDistance < rightDistance
    | some _, none => true
    | none, _ => false
  let consider (state : State) (best : Option (Fin n))
      (candidate : Fin n) : Option (Fin n) :=
    if state.2.2.1.get candidate then
      best
    else
      match best with
      | none => some candidate
      | some current =>
          if distanceLess (state.1.get candidate) (state.1.get current) then
            some candidate
          else
            best
  let rec @[reducible] selectLoop (state : State) :
      List (Fin n) → Option (Fin n) → TimeM DijkstraCost (Option (Fin n))
    | [], best => pure best
    | candidate :: rest, best => do
        TimeM.tick { minScans := 1, edgeRelaxations := 0 }
        selectLoop state rest (consider state best candidate)
  let relaxOne (previous target : Fin n) (state : State) : State :=
    if state.2.2.1.get target then
      state
    else
      match state.1.get previous with
      | none => state
      | some previousDistance =>
          let candidate := previousDistance + weight previous target
          match state.1.get target with
          | none =>
              (update state.1 target (some candidate),
                update state.2.1 target (some previous), state.2.2.1,
                state.2.2.2.1, state.2.2.2.2)
          | some targetDistance =>
              if candidate < targetDistance then
                (update state.1 target (some candidate),
                  update state.2.1 target (some previous), state.2.2.1,
                  state.2.2.2.1, state.2.2.2.2)
              else
                state
  let rec @[reducible] relaxLoop (previous : Fin n) :
      List (Fin n) → State → TimeM DijkstraCost State
    | [], state => pure state
    | target :: rest, state => do
        TimeM.tick { minScans := 0, edgeRelaxations := 1 }
        relaxLoop previous rest (relaxOne previous target state)
  let rec @[reducible] runRounds : Nat → Nat → State → TimeM DijkstraCost State
    | 0, _, state => pure state
    | remaining + 1, nextRank, state => do
        let selected ← selectLoop state graph.vertices none
        match selected with
        | none => runRounds remaining nextRank state
        | some vertex =>
            let state : State :=
              (state.1, state.2.1, update state.2.2.1 vertex true,
                update state.2.2.2.1 vertex (some nextRank),
                state.2.2.2.2 ++ [vertex])
            let state ← relaxLoop vertex (graph.adjacency vertex) state
            runRounds remaining (nextRank + 1) state
  let initial : State :=
    (Vector.ofFn fun vertex => if vertex = source then some 0 else none,
      Vector.ofFn fun _ => none, Vector.ofFn fun _ => false,
      Vector.ofFn fun _ => none, [])
  let run := runRounds n 0 initial
  { ret :=
      { source := source
        distance := run.ret.1
        predecessor := run.ret.2.1 }
    time := run.time }

end Cslib.Algorithms.Lean.DirectedAdjacency

@[expose] public section

namespace Cslib.Algorithms.Lean.DirectedAdjacency

universe u

variable {V : Type u}

private abbrev DijkstraState (n : Nat) :=
  Vector (Option Nat) n × Vector (Option (Fin n)) n ×
    Vector Bool n × Vector (Option Nat) n × List (Fin n)

@[simp]
private lemma zero_minScans : (0 : DijkstraCost).minScans = 0 := rfl

@[simp]
private lemma zero_edgeRelaxations : (0 : DijkstraCost).edgeRelaxations = 0 := rfl

@[simp]
private lemma add_minScans (left right : DijkstraCost) :
    (left + right).minScans = left.minScans + right.minScans := rfl

@[simp]
private lemma add_edgeRelaxations (left right : DijkstraCost) :
    (left + right).edgeRelaxations = left.edgeRelaxations + right.edgeRelaxations := rfl

private def updateVector {α : Type*} {n : Nat} (values : Vector α n)
    (index : Fin n) (value : α) : Vector α n :=
  values.set index.val value index.isLt

@[simp]
private lemma get_updateVector_same {α : Type*} {n : Nat} (values : Vector α n)
    (index : Fin n) (value : α) :
    (updateVector values index value).get index = value := by
  change (values.set index.val value index.isLt)[index.val] = value
  exact Vector.getElem_set_self index.isLt

@[simp]
private lemma get_vectorOfFn {α : Type*} {n : Nat} (function : Fin n → α)
    (index : Fin n) : (Vector.ofFn function).get index = function index := by
  change (Vector.ofFn function)[index.val] = function index
  simp

@[simp]
private lemma get_updateVector_of_ne {α : Type*} {n : Nat} (values : Vector α n)
    {updated index : Fin n} (h : updated ≠ index) (value : α) :
    (updateVector values updated value).get index = values.get index := by
  change (values.set updated.val value updated.isLt)[index.val] = values[index.val]
  exact Vector.getElem_set_ne updated.isLt index.isLt fun equality =>
    h (Fin.ext equality)

private lemma vertices_length {n : Nat} (graph : DirectedAdjacency (Fin n)) :
    graph.vertices.length = n := by
  have hfinset : graph.vertices.toFinset = Finset.univ := by
    ext vertex
    simp [graph.vertices_complete]
  calc
    graph.vertices.length = graph.vertices.toFinset.card :=
      (List.toFinset_card_of_nodup graph.vertices_nodup).symm
    _ = Finset.univ.card := congrArg Finset.card hfinset
    _ = n := Finset.card_fin n

private def DistanceLE : Option Nat → Option Nat → Prop
  | some left, some right => left ≤ right
  | some _, none => True
  | none, some _ => False
  | none, none => True

private def distanceLessCore (left right : Option Nat) : Bool :=
  match left, right with
  | some leftDistance, some rightDistance => leftDistance < rightDistance
  | some _, none => true
  | none, _ => false

private lemma DistanceLE.trans {left middle right : Option Nat}
    (hleft : DistanceLE left middle) (hright : DistanceLE middle right) :
    DistanceLE left right := by
  cases left <;> cases middle <;> cases right <;> simp [DistanceLE] at hleft hright ⊢
  omega

private lemma DistanceLE.refl (distance : Option Nat) : DistanceLE distance distance := by
  cases distance <;> simp [DistanceLE]

private lemma distanceLE_of_distanceLess_eq_true {left right : Option Nat}
    (h : distanceLessCore left right = true) : DistanceLE left right := by
  cases left <;> cases right <;> simp [distanceLessCore, DistanceLE] at h ⊢
  omega

private lemma distanceLE_of_distanceLess_eq_false {left right : Option Nat}
    (h : distanceLessCore left right = false) : DistanceLE right left := by
  cases left <;> cases right <;> simp [distanceLessCore, DistanceLE] at h ⊢
  omega

private lemma distanceLess_eq_false_of_le {left right : Option Nat}
    (h : DistanceLE left right) : distanceLessCore right left = false := by
  cases left <;> cases right <;> simp [distanceLessCore, DistanceLE] at h ⊢
  omega

private def considerCore {n : Nat} (state : DijkstraState n)
    (best : Option (Fin n)) (candidate : Fin n) : Option (Fin n) :=
  if state.2.2.1.get candidate then
    best
  else
    match best with
    | none => some candidate
    | some current =>
        if distanceLessCore (state.1.get candidate) (state.1.get current) then
          some candidate
        else
          best

private lemma considerCore_keeps_minimum {n : Nat} (state : DijkstraState n)
    (best candidate : Fin n)
    (hminimal : DistanceLE (state.1.get best) (state.1.get candidate)) :
    considerCore state (some best) candidate = some best := by
  unfold considerCore
  split <;> try rfl
  change (if distanceLessCore (state.1.get candidate) (state.1.get best) then
    some candidate else some best) = some best
  rw [distanceLess_eq_false_of_le hminimal]
  rfl

private lemma selectLoop_keeps_first_minimum {n : Nat} (state : DijkstraState n)
    (best : Fin n) (vertices : List (Fin n))
    (hminimal : ∀ vertex ∈ vertices, state.2.2.1.get vertex = false →
      DistanceLE (state.1.get best) (state.1.get vertex)) :
    (dijkstra.selectLoop considerCore state vertices (some best)).ret = some best := by
  induction vertices with
  | nil => rfl
  | cons candidate vertices induction =>
      simp only [dijkstra.selectLoop, TimeM.ret_bind]
      by_cases hcandidate : state.2.2.1.get candidate = true
      · have hconsider : considerCore state (some best) candidate = some best := by
          simp [considerCore, hcandidate]
        rw [hconsider]
        exact induction (fun vertex hmem => hminimal vertex (by simp [hmem]))
      · have hcandidateFalse : state.2.2.1.get candidate = false := by
          cases hvalue : state.2.2.1.get candidate
          · rfl
          · exact False.elim (hcandidate hvalue)
        rw [considerCore_keeps_minimum state best candidate
          (hminimal candidate (by simp) hcandidateFalse)]
        exact induction (fun vertex hmem => hminimal vertex (by simp [hmem]))

private lemma selectLoop_selects_first_minimum {n : Nat} (state : DijkstraState n)
    (first : Fin n) (rest : List (Fin n))
    (hfirst : state.2.2.1.get first = false)
    (hminimal : ∀ vertex ∈ first :: rest, state.2.2.1.get vertex = false →
      DistanceLE (state.1.get first) (state.1.get vertex)) :
    (dijkstra.selectLoop considerCore state (first :: rest) none).ret = some first := by
  simp only [dijkstra.selectLoop, TimeM.ret_bind]
  rw [show considerCore state none first = some first by simp [considerCore, hfirst]]
  exact selectLoop_keeps_first_minimum state first rest
    (fun vertex hmem => hminimal vertex (by simp [hmem]))

private lemma selectLoop_selects_first_minimum_after_settled_prefix {n : Nat}
    (state : DijkstraState n) (scannedPrefix : List (Fin n)) (first : Fin n)
    (rest : List (Fin n))
    (hprefix : ∀ vertex ∈ scannedPrefix, state.2.2.1.get vertex = true)
    (hfirst : state.2.2.1.get first = false)
    (hminimal : ∀ vertex ∈ first :: rest, state.2.2.1.get vertex = false →
      DistanceLE (state.1.get first) (state.1.get vertex)) :
    (dijkstra.selectLoop considerCore state (scannedPrefix ++ first :: rest) none).ret =
      some first := by
  induction scannedPrefix with
  | nil => exact selectLoop_selects_first_minimum state first rest hfirst hminimal
  | cons candidate scannedPrefix induction =>
      simp only [List.cons_append, dijkstra.selectLoop, TimeM.ret_bind]
      have hcandidate := hprefix candidate (by simp)
      rw [show considerCore state none candidate = none by simp [considerCore, hcandidate]]
      exact induction (fun vertex hmem => hprefix vertex (by simp [hmem]))

private def MinimumSoFar {n : Nat} (state : DijkstraState n)
    (scanned : List (Fin n)) : Option (Fin n) → Prop
  | none => ∀ vertex ∈ scanned, state.2.2.1.get vertex = true
  | some best =>
      best ∈ scanned ∧ state.2.2.1.get best = false ∧
        ∀ vertex ∈ scanned, state.2.2.1.get vertex = false →
          DistanceLE (state.1.get best) (state.1.get vertex)

private lemma consider_minimum_preserves {n : Nat} (state : DijkstraState n)
    (scanned : List (Fin n)) (best : Option (Fin n)) (candidate : Fin n)
    (hbest : MinimumSoFar state scanned best) :
    MinimumSoFar state (scanned ++ [candidate])
      (considerCore state best candidate) := by
  unfold considerCore
  cases hsettled : state.2.2.1.get candidate
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases best with
    | none =>
        refine ⟨by simp, hsettled, ?_⟩
        intro vertex hvertex hunsettled
        simp only [List.mem_append, List.mem_singleton] at hvertex
        rcases hvertex with hvertex | rfl
        · have hsettledVertex := hbest vertex hvertex
          rw [hunsettled] at hsettledVertex
          contradiction
        · exact DistanceLE.refl _
    | some current =>
        rcases hbest with ⟨hcurrent, hcurrentUnsettled, hminimal⟩
        cases hless : distanceLessCore (state.1.get candidate) (state.1.get current)
        · simp only [hless, Bool.false_eq_true, ↓reduceIte]
          refine ⟨List.mem_append_left _ hcurrent, hcurrentUnsettled, ?_⟩
          intro vertex hvertex hunsettled
          simp only [List.mem_append, List.mem_singleton] at hvertex
          rcases hvertex with hvertex | rfl
          · exact hminimal vertex hvertex hunsettled
          · exact distanceLE_of_distanceLess_eq_false hless
        · simp only [hless, ↓reduceIte]
          refine ⟨by simp, hsettled, ?_⟩
          intro vertex hvertex hunsettled
          simp only [List.mem_append, List.mem_singleton] at hvertex
          rcases hvertex with hvertex | rfl
          · exact (distanceLE_of_distanceLess_eq_true hless).trans
              (hminimal vertex hvertex hunsettled)
          · exact DistanceLE.refl _
  · simp only [↓reduceIte]
    cases best with
    | none =>
        intro vertex hvertex
        simp only [List.mem_append, List.mem_singleton] at hvertex
        rcases hvertex with hvertex | rfl
        · exact hbest vertex hvertex
        · exact hsettled
    | some current =>
        rcases hbest with ⟨hcurrent, hcurrentUnsettled, hminimal⟩
        refine ⟨List.mem_append_left _ hcurrent, hcurrentUnsettled, ?_⟩
        intro vertex hvertex hunsettled
        simp only [List.mem_append, List.mem_singleton] at hvertex
        rcases hvertex with hvertex | rfl
        · exact hminimal vertex hvertex hunsettled
        · rw [hsettled] at hunsettled
          contradiction

private lemma selectLoop_minimum {n : Nat}
    (consider : DijkstraState n → Option (Fin n) → Fin n → Option (Fin n))
    (hconsider : ∀ (state : DijkstraState n) scanned best candidate,
      MinimumSoFar state scanned best →
        MinimumSoFar state (scanned ++ [candidate]) (consider state best candidate))
    (state : DijkstraState n) (remaining scanned : List (Fin n))
    (best : Option (Fin n)) (hbest : MinimumSoFar state scanned best) :
    MinimumSoFar state (scanned ++ remaining)
      (dijkstra.selectLoop consider state remaining best).ret := by
  induction remaining generalizing scanned best with
  | nil => simpa [dijkstra.selectLoop] using hbest
  | cons candidate remaining induction =>
      simp only [dijkstra.selectLoop, TimeM.ret_bind]
      have hnext := hconsider state scanned best candidate hbest
      simpa [List.append_assoc] using
        induction (scanned ++ [candidate]) (consider state best candidate) hnext

private lemma selectMinimum_spec {n : Nat} (state : DijkstraState n)
    (vertices : List (Fin n)) :
    MinimumSoFar state vertices
      (dijkstra.selectLoop considerCore state vertices none).ret := by
  simpa using selectLoop_minimum _
    (fun state scanned best candidate => consider_minimum_preserves state scanned best candidate)
    state vertices [] none (by simp [MinimumSoFar])

private lemma selectMinimum_result {n : Nat} (graph : DirectedAdjacency (Fin n))
    (state : DijkstraState n) {selected : Fin n}
    (hselected :
      (dijkstra.selectLoop considerCore state graph.vertices none).ret = some selected) :
    state.2.2.1.get selected = false ∧
      ∀ vertex, state.2.2.1.get vertex = false →
        DistanceLE (state.1.get selected) (state.1.get vertex) := by
  have hspec := selectMinimum_spec state graph.vertices
  rw [hselected] at hspec
  exact ⟨hspec.2.1, fun vertex hunsettled =>
    hspec.2.2 vertex (graph.vertices_complete vertex) hunsettled⟩

private def SettledSpec {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source vertex : Fin n)
    (state : DijkstraState n) : Prop :=
  match state.1.get vertex with
  | none => ¬graph.Reachable source vertex
  | some distance =>
      ∀ otherDistance, HasPathWeight graph weight source vertex otherDistance →
        distance ≤ otherDistance

private def OrderInvariant {n : Nat} (nextRank : Nat) (state : DijkstraState n) : Prop :=
  state.2.2.2.2.Nodup ∧ state.2.2.2.2.length = nextRank ∧
    ∀ vertex, state.2.2.1.get vertex = true ↔ vertex ∈ state.2.2.2.2

private def FrontierSpec {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (state : DijkstraState n) : Prop :=
  ∀ previous target previousDistance,
    state.2.2.1.get previous = true → state.2.2.1.get target = false →
      graph.Edge previous target → state.1.get previous = some previousDistance →
        ∃ targetDistance, state.1.get target = some targetDistance ∧
          targetDistance ≤ previousDistance + weight previous target

private structure RoundBase {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) (nextRank : Nat)
    (state : DijkstraState n) : Prop where
  order : OrderInvariant nextRank state
  sourceSettled : state.2.2.1.get source = true
  sourceDistance : state.1.get source = some 0
  sourcePredecessor : state.2.1.get source = none
  realized : ∀ vertex distance, state.1.get vertex = some distance →
    HasPathWeight graph weight source vertex distance
  settled : ∀ vertex, state.2.2.1.get vertex = true →
    SettledSpec graph weight source vertex state
  predecessor : ∀ target previous, state.2.1.get target = some previous →
    state.2.2.1.get previous = true ∧ graph.Edge previous target ∧
      ∃ previousDistance targetDistance,
        state.1.get previous = some previousDistance ∧
        state.1.get target = some targetDistance ∧
        targetDistance = previousDistance + weight previous target
  finitePredecessor : ∀ target distance, state.1.get target = some distance →
    target ≠ source → ∃ previous, state.2.1.get target = some previous

private structure AlgorithmInvariant {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) (nextRank : Nat)
    (state : DijkstraState n) : Prop extends RoundBase graph weight source nextRank state where
  frontier : FrontierSpec graph weight state

private structure RankInvariant {n : Nat} (nextRank : Nat)
    (state : DijkstraState n) : Prop where
  rankSettled : ∀ vertex rank, state.2.2.2.1.get vertex = some rank →
    state.2.2.1.get vertex = true
  settledRank : ∀ vertex, state.2.2.1.get vertex = true →
    ∃ rank, state.2.2.2.1.get vertex = some rank
  rankBound : ∀ vertex rank, state.2.2.2.1.get vertex = some rank → rank < nextRank
  predecessorRank : ∀ target previous, state.2.1.get target = some previous →
    ∃ previousRank, state.2.2.2.1.get previous = some previousRank ∧
      (state.2.2.2.1.get target = none ∨
        ∃ targetRank, state.2.2.2.1.get target = some targetRank ∧
          previousRank < targetRank)

private lemma selected_settledSpec {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source selected : Fin n)
    (state : DijkstraState n)
    (hsourceSettled : state.2.2.1.get source = true)
    (hsettled : ∀ vertex, state.2.2.1.get vertex = true →
      SettledSpec graph weight source vertex state)
    (hfrontier : FrontierSpec graph weight state)
    (hselectedUnsettled : state.2.2.1.get selected = false)
    (hminimum : ∀ vertex, state.2.2.1.get vertex = false →
      DistanceLE (state.1.get selected) (state.1.get vertex)) :
    SettledSpec graph weight source selected state := by
  cases hselectedDistance : state.1.get selected with
  | none =>
      simp only [SettledSpec, hselectedDistance]
      intro reachable
      obtain ⟨pathDistance, path⟩ :=
        (reachable_iff_exists_hasPathWeight graph weight source selected).mp reachable
      obtain ⟨previous, next, previousWeight, hpreviousSettled, hnextUnsettled,
          edge, previousPath, -⟩ :=
        first_unsettled_edge path hsourceSettled hselectedUnsettled
      cases hpreviousDistance : state.1.get previous with
      | none =>
          have hpreviousSpec := hsettled previous hpreviousSettled
          simp only [SettledSpec, hpreviousDistance] at hpreviousSpec
          exact False.elim (hpreviousSpec
            ((reachable_iff_exists_hasPathWeight graph weight source previous).mpr
              ⟨previousWeight, previousPath⟩))
      | some previousDistance =>
          obtain ⟨nextDistance, hnextDistance, -⟩ :=
            hfrontier previous next previousDistance hpreviousSettled hnextUnsettled edge
              hpreviousDistance
          have hle := hminimum next hnextUnsettled
          simp [DistanceLE, hselectedDistance, hnextDistance] at hle
  | some selectedDistance =>
      simp only [SettledSpec, hselectedDistance]
      intro pathDistance path
      obtain ⟨previous, next, previousWeight, hpreviousSettled, hnextUnsettled,
          edge, previousPath, hprefix⟩ :=
        first_unsettled_edge path hsourceSettled hselectedUnsettled
      cases hpreviousDistance : state.1.get previous with
      | none =>
          have hpreviousSpec := hsettled previous hpreviousSettled
          simp only [SettledSpec, hpreviousDistance] at hpreviousSpec
          exact False.elim (hpreviousSpec
            ((reachable_iff_exists_hasPathWeight graph weight source previous).mpr
              ⟨previousWeight, previousPath⟩))
      | some previousDistance =>
          have hpreviousSpec := hsettled previous hpreviousSettled
          simp only [SettledSpec, hpreviousDistance] at hpreviousSpec
          have hpreviousMinimal := hpreviousSpec previousWeight previousPath
          obtain ⟨nextDistance, hnextDistance, hnextBound⟩ :=
            hfrontier previous next previousDistance hpreviousSettled hnextUnsettled edge
              hpreviousDistance
          have hselectedBound := hminimum next hnextUnsettled
          simp only [DistanceLE, hselectedDistance, hnextDistance] at hselectedBound
          omega

private def settleCore {n : Nat} (state : DijkstraState n) (vertex : Fin n)
    (nextRank : Nat) : DijkstraState n :=
  (state.1, state.2.1, updateVector state.2.2.1 vertex true,
    updateVector state.2.2.2.1 vertex (some nextRank), state.2.2.2.2 ++ [vertex])

private lemma exists_unsettled {n : Nat} {nextRank : Nat} {state : DijkstraState n}
    (hinvariant : OrderInvariant nextRank state) (hnext : nextRank < n) :
    ∃ vertex, state.2.2.1.get vertex = false := by
  by_contra hnone
  simp only [not_exists] at hnone
  have hall : ∀ vertex, state.2.2.1.get vertex = true := by
    intro vertex
    cases hvalue : state.2.2.1.get vertex
    · exact False.elim (hnone vertex hvalue)
    · rfl
  have hfinset : state.2.2.2.2.toFinset = Finset.univ := by
    ext vertex
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact (hinvariant.2.2 vertex).mp (hall vertex)
  have hlength : state.2.2.2.2.length = n := by
    calc
      state.2.2.2.2.length = state.2.2.2.2.toFinset.card :=
        (List.toFinset_card_of_nodup hinvariant.1).symm
      _ = Finset.univ.card := congrArg Finset.card hfinset
      _ = n := Finset.card_fin n
  have hnextLength := hinvariant.2.1
  omega

private lemma selectMinimum_some {n : Nat} (graph : DirectedAdjacency (Fin n))
    {nextRank : Nat} {state : DijkstraState n}
    (hinvariant : OrderInvariant nextRank state) (hnext : nextRank < n) :
    ∃ vertex,
      (dijkstra.selectLoop considerCore state graph.vertices none).ret = some vertex ∧
        state.2.2.1.get vertex = false := by
  obtain ⟨unsettled, hunsettled⟩ := exists_unsettled hinvariant hnext
  have hspec := selectMinimum_spec state graph.vertices
  cases hselected : (dijkstra.selectLoop considerCore state graph.vertices none).ret with
  | none =>
      rw [hselected] at hspec
      have := hspec unsettled (graph.vertices_complete unsettled)
      rw [hunsettled] at this
      contradiction
  | some selected =>
      rw [hselected] at hspec
      exact ⟨selected, rfl, hspec.2.1⟩

private lemma settleCore_order {n : Nat} {state : DijkstraState n} {nextRank : Nat}
    {vertex : Fin n} (hinvariant : OrderInvariant nextRank state)
    (hunsettled : state.2.2.1.get vertex = false) :
    OrderInvariant (nextRank + 1) (settleCore state vertex nextRank) := by
  have hnotMem : vertex ∉ state.2.2.2.2 := by
    intro hmem
    have := (hinvariant.2.2 vertex).mpr hmem
    rw [hunsettled] at this
    contradiction
  have hnodup : (state.2.2.2.2 ++ [vertex]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hinvariant.1, by simp, ?_⟩
    intro other hother target htarget
    simp only [List.mem_singleton] at htarget
    subst target
    intro equality
    subst other
    exact hnotMem hother
  refine ⟨hnodup, ?_, ?_⟩
  · change (state.2.2.2.2 ++ [vertex]).length = nextRank + 1
    simp [hinvariant.2.1]
  intro other
  change (updateVector state.2.2.1 vertex true).get other = true ↔
    other ∈ state.2.2.2.2 ++ [vertex]
  by_cases h : vertex = other
  · subst other
    simp
  · rw [get_updateVector_of_ne _ h]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro hsettled
      exact Or.inl ((hinvariant.2.2 other).mp hsettled)
    · rintro (hmember | equality)
      · exact (hinvariant.2.2 other).mpr hmember
      · exact False.elim (h equality.symm)

private lemma settleCore_base {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source selected : Fin n)
    (nextRank : Nat) (state : DijkstraState n)
    (hinvariant : AlgorithmInvariant graph weight source nextRank state)
    (hselectedUnsettled : state.2.2.1.get selected = false)
    (hselectedSpec : SettledSpec graph weight source selected state) :
    RoundBase graph weight source (nextRank + 1) (settleCore state selected nextRank) := by
  have hne : selected ≠ source := by
    intro equality
    subst selected
    rw [hinvariant.sourceSettled] at hselectedUnsettled
    contradiction
  constructor
  · exact settleCore_order hinvariant.order hselectedUnsettled
  · change (updateVector state.2.2.1 selected true).get source = true
    rw [get_updateVector_of_ne _ hne]
    exact hinvariant.sourceSettled
  · exact hinvariant.sourceDistance
  · exact hinvariant.sourcePredecessor
  · exact hinvariant.realized
  · intro vertex hvertex
    by_cases h : selected = vertex
    · subst vertex
      exact hselectedSpec
    · have hold : state.2.2.1.get vertex = true := by
        rw [← get_updateVector_of_ne state.2.2.1 h]
        exact hvertex
      exact hinvariant.settled vertex hold
  · intro target previous hpredecessor
    obtain ⟨hpreviousSettled, hedge, previousDistance, targetDistance,
        hpreviousDistance, htargetDistance, hequation⟩ :=
      hinvariant.predecessor target previous hpredecessor
    refine ⟨?_, hedge, previousDistance, targetDistance,
      hpreviousDistance, htargetDistance, hequation⟩
    change (updateVector state.2.2.1 selected true).get previous = true
    by_cases h : selected = previous
    · subst previous
      simp
    · rw [get_updateVector_of_ne _ h]
      exact hpreviousSettled
  · exact hinvariant.finitePredecessor

private lemma settleCore_rank {n : Nat} {nextRank : Nat} {state : DijkstraState n}
    {selected : Fin n} (hinvariant : RankInvariant nextRank state)
    (hselectedUnsettled : state.2.2.1.get selected = false) :
    RankInvariant (nextRank + 1) (settleCore state selected nextRank) := by
  constructor
  · intro vertex rank hrank
    by_cases h : selected = vertex
    · subst vertex
      simp [settleCore]
    · have hold : state.2.2.2.1.get vertex = some rank := by
        change (updateVector state.2.2.2.1 selected (some nextRank)).get vertex =
          some rank at hrank
        rwa [get_updateVector_of_ne _ h] at hrank
      have hsettled := hinvariant.rankSettled vertex rank hold
      change (updateVector state.2.2.1 selected true).get vertex = true
      rwa [get_updateVector_of_ne _ h]
  · intro vertex hsettled
    by_cases h : selected = vertex
    · subst vertex
      exact ⟨nextRank, by simp [settleCore]⟩
    · have hold : state.2.2.1.get vertex = true := by
        change (updateVector state.2.2.1 selected true).get vertex = true at hsettled
        rwa [get_updateVector_of_ne _ h] at hsettled
      obtain ⟨rank, hrank⟩ := hinvariant.settledRank vertex hold
      exact ⟨rank, by
        change (updateVector state.2.2.2.1 selected (some nextRank)).get vertex = some rank
        rwa [get_updateVector_of_ne _ h]⟩
  · intro vertex rank hrank
    by_cases h : selected = vertex
    · subst vertex
      change (updateVector state.2.2.2.1 selected (some nextRank)).get selected =
        some rank at hrank
      rw [get_updateVector_same] at hrank
      cases hrank
      omega
    · have hold : state.2.2.2.1.get vertex = some rank := by
        change (updateVector state.2.2.2.1 selected (some nextRank)).get vertex =
          some rank at hrank
        rwa [get_updateVector_of_ne _ h] at hrank
      exact Nat.lt_succ_of_lt (hinvariant.rankBound vertex rank hold)
  · intro target previous hpredecessor
    obtain ⟨previousRank, hpreviousRank, htargetRank⟩ :=
      hinvariant.predecessorRank target previous hpredecessor
    have hpreviousNe : selected ≠ previous := by
      intro equality
      subst previous
      have := hinvariant.rankSettled selected previousRank hpreviousRank
      rw [hselectedUnsettled] at this
      contradiction
    refine ⟨previousRank, ?_, ?_⟩
    · change (updateVector state.2.2.2.1 selected (some nextRank)).get previous =
        some previousRank
      rw [get_updateVector_of_ne _ hpreviousNe]
      exact hpreviousRank
    · by_cases htarget : selected = target
      · subst target
        right
        refine ⟨nextRank, by simp [settleCore], ?_⟩
        exact hinvariant.rankBound previous previousRank hpreviousRank
      · rcases htargetRank with hnone | ⟨targetRank, hrank, hlt⟩
        · left
          change (updateVector state.2.2.2.1 selected (some nextRank)).get target = none
          rwa [get_updateVector_of_ne _ htarget]
        · right
          refine ⟨targetRank, ?_, hlt⟩
          change (updateVector state.2.2.2.1 selected (some nextRank)).get target =
            some targetRank
          rwa [get_updateVector_of_ne _ htarget]

private def improveCore {n : Nat} (state : DijkstraState n)
    (previous target : Fin n) (distance : Nat) : DijkstraState n :=
  (updateVector state.1 target (some distance),
    updateVector state.2.1 target (some previous), state.2.2.1,
    state.2.2.2.1, state.2.2.2.2)

private lemma improveCore_base {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source previous target : Fin n)
    (nextRank previousDistance : Nat) (state : DijkstraState n)
    (hbase : RoundBase graph weight source nextRank state)
    (hpreviousSettled : state.2.2.1.get previous = true)
    (htargetUnsettled : state.2.2.1.get target = false)
    (hedge : graph.Edge previous target)
    (hpreviousDistance : state.1.get previous = some previousDistance) :
    RoundBase graph weight source nextRank
      (improveCore state previous target (previousDistance + weight previous target)) := by
  have htargetSource : target ≠ source := by
    intro equality
    subst target
    rw [hbase.sourceSettled] at htargetUnsettled
    contradiction
  have htargetPrevious : target ≠ previous := by
    intro equality
    subst target
    rw [hpreviousSettled] at htargetUnsettled
    contradiction
  unfold improveCore
  constructor
  · exact hbase.order
  · exact hbase.sourceSettled
  · change (updateVector state.1 target
      (some (previousDistance + weight previous target))).get source = some 0
    rw [get_updateVector_of_ne _ htargetSource]
    exact hbase.sourceDistance
  · change (updateVector state.2.1 target (some previous)).get source = none
    rw [get_updateVector_of_ne _ htargetSource]
    exact hbase.sourcePredecessor
  · intro vertex distance hdistance
    by_cases h : target = vertex
    · subst vertex
      rw [get_updateVector_same] at hdistance
      cases hdistance
      exact HasPathWeight.snoc (graph := graph) (weight := weight)
        (hbase.realized previous previousDistance hpreviousDistance) hedge
    · rw [get_updateVector_of_ne _ h] at hdistance
      exact hbase.realized vertex distance hdistance
  · intro vertex hsettled
    have hne : target ≠ vertex := by
      intro equality
      subst vertex
      rw [htargetUnsettled] at hsettled
      contradiction
    have hold := hbase.settled vertex hsettled
    unfold SettledSpec at hold ⊢
    rw [get_updateVector_of_ne _ hne]
    exact hold
  · intro vertex predecessor hpredecessor
    by_cases h : target = vertex
    · subst vertex
      rw [get_updateVector_same] at hpredecessor
      cases hpredecessor
      refine ⟨hpreviousSettled, hedge, previousDistance,
        previousDistance + weight previous target, ?_, ?_, rfl⟩
      · rw [get_updateVector_of_ne _ htargetPrevious]
        exact hpreviousDistance
      · simp
    · rw [get_updateVector_of_ne _ h] at hpredecessor
      obtain ⟨hpredecessorSettled, hpredecessorEdge, predecessorDistance,
          vertexDistance, hpredecessorDistance, hvertexDistance, hequation⟩ :=
        hbase.predecessor vertex predecessor hpredecessor
      have hpredNe : target ≠ predecessor := by
        intro equality
        subst predecessor
        rw [htargetUnsettled] at hpredecessorSettled
        contradiction
      refine ⟨hpredecessorSettled, hpredecessorEdge, predecessorDistance,
        vertexDistance, ?_, ?_, hequation⟩
      · rw [get_updateVector_of_ne _ hpredNe]
        exact hpredecessorDistance
      · rw [get_updateVector_of_ne _ h]
        exact hvertexDistance
  · intro vertex distance hdistance hneSource
    by_cases h : target = vertex
    · subst vertex
      rw [get_updateVector_same] at hdistance
      exact ⟨previous, by simp⟩
    · rw [get_updateVector_of_ne _ h] at hdistance
      obtain ⟨predecessor, hpredecessor⟩ :=
        hbase.finitePredecessor vertex distance hdistance hneSource
      exact ⟨predecessor, by simpa [improveCore, h] using hpredecessor⟩

private lemma improveCore_rank {n : Nat} {nextRank : Nat} {state : DijkstraState n}
    {previous target : Fin n} {distance : Nat}
    (hinvariant : RankInvariant nextRank state)
    (hpreviousSettled : state.2.2.1.get previous = true)
    (htargetUnsettled : state.2.2.1.get target = false) :
    RankInvariant nextRank (improveCore state previous target distance) := by
  constructor
  · exact hinvariant.rankSettled
  · exact hinvariant.settledRank
  · exact hinvariant.rankBound
  · intro vertex predecessor hpredecessor
    by_cases h : target = vertex
    · subst vertex
      change (updateVector state.2.1 target (some previous)).get target =
        some predecessor at hpredecessor
      rw [get_updateVector_same] at hpredecessor
      cases hpredecessor
      obtain ⟨previousRank, hpreviousRank⟩ :=
        hinvariant.settledRank previous hpreviousSettled
      refine ⟨previousRank, hpreviousRank, Or.inl ?_⟩
      cases htargetRank : state.2.2.2.1.get target with
      | none =>
          change state.2.2.2.1.get target = none
          exact htargetRank
      | some targetRank =>
          have := hinvariant.rankSettled target targetRank htargetRank
          rw [htargetUnsettled] at this
          contradiction
    · change (updateVector state.2.1 target (some previous)).get vertex =
        some predecessor at hpredecessor
      rw [get_updateVector_of_ne _ h] at hpredecessor
      exact hinvariant.predecessorRank vertex predecessor hpredecessor

private def relaxOneCore {n : Nat} (weight : Fin n → Fin n → Nat)
    (previous target : Fin n) (state : DijkstraState n) : DijkstraState n :=
  if state.2.2.1.get target then
    state
  else
    match state.1.get previous with
    | none => state
    | some previousDistance =>
        let candidate := previousDistance + weight previous target
        match state.1.get target with
        | none => improveCore state previous target candidate
        | some targetDistance =>
            if candidate < targetDistance then
              improveCore state previous target candidate
            else
              state

private lemma relaxOneCore_base {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source previous target : Fin n)
    (nextRank : Nat) (state : DijkstraState n)
    (hbase : RoundBase graph weight source nextRank state)
    (hpreviousSettled : state.2.2.1.get previous = true)
    (hedge : graph.Edge previous target) :
    RoundBase graph weight source nextRank (relaxOneCore weight previous target state) := by
  unfold relaxOneCore
  split
  · exact hbase
  · rename_i htargetUnsettled
    have htargetFalse : state.2.2.1.get target = false := by
      cases hvalue : state.2.2.1.get target
      · rfl
      · exact False.elim (htargetUnsettled hvalue)
    split
    · exact hbase
    · rename_i previousDistance hpreviousDistance
      split
      · exact improveCore_base graph weight source previous target nextRank previousDistance state
          hbase hpreviousSettled htargetFalse hedge hpreviousDistance
      · dsimp only
        split
        · exact improveCore_base graph weight source previous target nextRank previousDistance state
            hbase hpreviousSettled htargetFalse hedge hpreviousDistance
        · exact hbase

private lemma relaxOneCore_rank {n : Nat} (weight : Fin n → Fin n → Nat)
    {nextRank : Nat} (previous target : Fin n) (state : DijkstraState n)
    (hinvariant : RankInvariant nextRank state)
    (hpreviousSettled : state.2.2.1.get previous = true) :
    RankInvariant nextRank (relaxOneCore weight previous target state) := by
  unfold relaxOneCore
  split
  · exact hinvariant
  · rename_i htargetUnsettled
    have htargetFalse : state.2.2.1.get target = false := by
      cases hvalue : state.2.2.1.get target
      · rfl
      · exact False.elim (htargetUnsettled hvalue)
    split
    · exact hinvariant
    · split
      · exact improveCore_rank hinvariant hpreviousSettled htargetFalse
      · dsimp only
        split
        · exact improveCore_rank hinvariant hpreviousSettled htargetFalse
        · exact hinvariant

private lemma relaxOneCore_settled {n : Nat} (weight : Fin n → Fin n → Nat)
    (previous target : Fin n) (state : DijkstraState n) :
    (relaxOneCore weight previous target state).2.2.1 = state.2.2.1 := by
  unfold relaxOneCore
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  dsimp only
  split <;> rfl

private lemma relaxLoop_rank {n : Nat} (weight : Fin n → Fin n → Nat)
    {nextRank : Nat} (previous : Fin n) (vertices : List (Fin n))
    (state : DijkstraState n) (hinvariant : RankInvariant nextRank state)
    (hpreviousSettled : state.2.2.1.get previous = true) :
    RankInvariant nextRank
      (dijkstra.relaxLoop (relaxOneCore weight) previous vertices state).ret := by
  induction vertices generalizing state with
  | nil => simpa [dijkstra.relaxLoop] using hinvariant
  | cons target vertices induction =>
      simp only [dijkstra.relaxLoop, TimeM.ret_bind]
      have hnext := relaxOneCore_rank weight previous target state hinvariant hpreviousSettled
      have hsettled : (relaxOneCore weight previous target state).2.2.1.get previous = true := by
        rw [relaxOneCore_settled]
        exact hpreviousSettled
      exact induction _ hnext hsettled

private lemma relaxOneCore_distance_of_settled {n : Nat}
    (weight : Fin n → Fin n → Nat) (previous target vertex : Fin n)
    (state : DijkstraState n) (hsettled : state.2.2.1.get vertex = true) :
    (relaxOneCore weight previous target state).1.get vertex = state.1.get vertex := by
  unfold relaxOneCore
  split <;> try rfl
  rename_i htarget
  have htargetFalse : state.2.2.1.get target = false := by
    cases hvalue : state.2.2.1.get target
    · rfl
    · exact False.elim (htarget hvalue)
  have heq : target ≠ vertex := by
    intro equality
    subst vertex
    rw [hsettled] at htargetFalse
    contradiction
  split <;> try rfl
  split
  · simp [improveCore, get_updateVector_of_ne _ heq]
  · dsimp only
    split
    · simp [improveCore, get_updateVector_of_ne _ heq]
    · rfl

private lemma relaxOneCore_decreases {n : Nat} (weight : Fin n → Fin n → Nat)
    (previous target vertex : Fin n) (state : DijkstraState n) :
    DistanceLE ((relaxOneCore weight previous target state).1.get vertex)
      (state.1.get vertex) := by
  unfold relaxOneCore
  split <;> try exact DistanceLE.refl _
  split <;> try exact DistanceLE.refl _
  rename_i previousDistance hpreviousDistance
  split
  · rename_i htargetDistance
    by_cases h : target = vertex
    · subst vertex
      simp [improveCore, DistanceLE, htargetDistance]
    · simp [improveCore, get_updateVector_of_ne _ h, DistanceLE.refl]
  · rename_i targetDistance htargetDistance
    dsimp only
    split
    · by_cases h : target = vertex
      · subst vertex
        simp [improveCore, DistanceLE, htargetDistance]
        omega
      · simp [improveCore, get_updateVector_of_ne _ h, DistanceLE.refl]
    · exact DistanceLE.refl _

private lemma relaxOneCore_target_bound {n : Nat} (weight : Fin n → Fin n → Nat)
    (previous target : Fin n) (state : DijkstraState n)
    (htarget : state.2.2.1.get target = false)
    {previousDistance : Nat} (hprevious : state.1.get previous = some previousDistance) :
    ∃ targetDistance, (relaxOneCore weight previous target state).1.get target =
        some targetDistance ∧
      targetDistance ≤ previousDistance + weight previous target := by
  unfold relaxOneCore
  simp only [htarget, Bool.false_eq_true, ↓reduceIte, hprevious]
  cases htargetDistance : state.1.get target with
  | none =>
      exact ⟨previousDistance + weight previous target, by simp [improveCore], Nat.le_refl _⟩
  | some targetDistance =>
      dsimp only
      by_cases hless : previousDistance + weight previous target < targetDistance
      · exact ⟨previousDistance + weight previous target,
          by simp [hless, improveCore], Nat.le_refl _⟩
      · exact ⟨targetDistance, by simp [hless, htargetDistance], by omega⟩

private structure RelaxResult {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source previous : Fin n)
    (nextRank previousDistance : Nat) (vertices : List (Fin n))
    (before after : DijkstraState n) : Prop where
  base : RoundBase graph weight source nextRank after
  settled : after.2.2.1 = before.2.2.1
  settledDistance : ∀ vertex, before.2.2.1.get vertex = true →
    after.1.get vertex = before.1.get vertex
  decreases : ∀ vertex, DistanceLE (after.1.get vertex) (before.1.get vertex)
  bounds : ∀ target ∈ vertices, after.2.2.1.get target = false →
    ∃ targetDistance, after.1.get target = some targetDistance ∧
      targetDistance ≤ previousDistance + weight previous target

private lemma relaxLoop_result {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source previous : Fin n)
    (nextRank previousDistance : Nat) (vertices : List (Fin n))
    (state : DijkstraState n)
    (hbase : RoundBase graph weight source nextRank state)
    (hpreviousSettled : state.2.2.1.get previous = true)
    (hpreviousDistance : state.1.get previous = some previousDistance)
    (hedges : ∀ target ∈ vertices, graph.Edge previous target) :
    RelaxResult graph weight source previous nextRank previousDistance vertices state
      (dijkstra.relaxLoop (relaxOneCore weight) previous vertices state).ret := by
  induction vertices generalizing state with
  | nil =>
      exact ⟨by simpa [dijkstra.relaxLoop] using hbase, rfl, fun _ _ => rfl,
        fun _ => DistanceLE.refl _, by simp⟩
  | cons target vertices induction =>
      let nextState := relaxOneCore weight previous target state
      have hedge : graph.Edge previous target := hedges target (by simp)
      have hbaseNext := relaxOneCore_base graph weight source previous target nextRank state
        hbase hpreviousSettled hedge
      have hsettledNext : nextState.2.2.1 = state.2.2.1 :=
        relaxOneCore_settled weight previous target state
      have hpreviousSettledNext : nextState.2.2.1.get previous = true := by
        rw [hsettledNext]
        exact hpreviousSettled
      have hpreviousDistanceNext : nextState.1.get previous = some previousDistance := by
        dsimp only [nextState]
        rw [relaxOneCore_distance_of_settled weight previous target previous state
          hpreviousSettled]
        exact hpreviousDistance
      have htail := induction nextState hbaseNext hpreviousSettledNext hpreviousDistanceNext
        (fun vertex hmem => hedges vertex (by simp [hmem]))
      simp only [dijkstra.relaxLoop, TimeM.ret_bind]
      constructor
      · exact htail.base
      · exact htail.settled.trans hsettledNext
      · intro vertex hvertex
        have hvertexNext : nextState.2.2.1.get vertex = true := by
          rw [hsettledNext]
          exact hvertex
        rw [htail.settledDistance vertex hvertexNext]
        exact relaxOneCore_distance_of_settled weight previous target vertex state hvertex
      · intro vertex
        exact (htail.decreases vertex).trans
          (relaxOneCore_decreases weight previous target vertex state)
      · intro vertex hmem hvertexUnsettled
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · have hnextUnsettled : nextState.2.2.1.get vertex = false := by
            rw [htail.settled] at hvertexUnsettled
            exact hvertexUnsettled
          obtain ⟨middleDistance, hmiddleDistance, hmiddleBound⟩ :=
            relaxOneCore_target_bound weight previous vertex state
              (by simpa [hsettledNext] using hnextUnsettled) hpreviousDistance
          have hdecrease := htail.decreases vertex
          rw [hmiddleDistance] at hdecrease
          cases hfinal :
              (dijkstra.relaxLoop (relaxOneCore weight) previous vertices nextState).ret.1.get
                vertex with
          | none => simp [DistanceLE, hfinal] at hdecrease
          | some finalDistance =>
              exact ⟨finalDistance, rfl, by
                simp only [DistanceLE, hfinal] at hdecrease
                omega⟩
        · exact htail.bounds vertex hmem hvertexUnsettled

private lemma relaxLoop_eq_of_previous_none {n : Nat} (weight : Fin n → Fin n → Nat)
    (previous : Fin n) (vertices : List (Fin n)) (state : DijkstraState n)
    (hprevious : state.1.get previous = none) :
    (dijkstra.relaxLoop (relaxOneCore weight) previous vertices state).ret = state := by
  induction vertices generalizing state with
  | nil => rfl
  | cons target vertices induction =>
      simp only [dijkstra.relaxLoop, TimeM.ret_bind]
      have hone : relaxOneCore weight previous target state = state := by
        unfold relaxOneCore
        split <;> simp_all
      rw [hone]
      exact induction state hprevious

private lemma relaxAfterSettle_invariant {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source selected : Fin n)
    (nextRank : Nat) (state : DijkstraState n)
    (hinvariant : AlgorithmInvariant graph weight source nextRank state)
    (hselectedUnsettled : state.2.2.1.get selected = false)
    (hselectedSpec : SettledSpec graph weight source selected state) :
    AlgorithmInvariant graph weight source (nextRank + 1)
      (dijkstra.relaxLoop (relaxOneCore weight) selected (graph.adjacency selected)
        (settleCore state selected nextRank)).ret := by
  let settledState := settleCore state selected nextRank
  have hbase := settleCore_base graph weight source selected nextRank state hinvariant
    hselectedUnsettled hselectedSpec
  have hselectedSettled : settledState.2.2.1.get selected = true := by
    simp [settledState, settleCore]
  cases hdistance : state.1.get selected with
  | none =>
      have hsettledDistance : settledState.1.get selected = none := hdistance
      have heq := relaxLoop_eq_of_previous_none weight selected
        (graph.adjacency selected) settledState hsettledDistance
      rw [heq]
      refine ⟨hbase, ?_⟩
      intro previous target previousDistance hpreviousSettled htargetUnsettled hedge
        hpreviousDistance
      have hpreviousNe : previous ≠ selected := by
        intro equality
        subst previous
        rw [hsettledDistance] at hpreviousDistance
        contradiction
      have htargetNe : target ≠ selected := by
        intro equality
        subst target
        rw [hselectedSettled] at htargetUnsettled
        contradiction
      have hpreviousOld : state.2.2.1.get previous = true := by
        change (updateVector state.2.2.1 selected true).get previous = true at hpreviousSettled
        rw [get_updateVector_of_ne _ (Ne.symm hpreviousNe)] at hpreviousSettled
        exact hpreviousSettled
      have htargetOld : state.2.2.1.get target = false := by
        change (updateVector state.2.2.1 selected true).get target = false at htargetUnsettled
        rw [get_updateVector_of_ne _ (Ne.symm htargetNe)] at htargetUnsettled
        exact htargetUnsettled
      exact hinvariant.frontier previous target previousDistance hpreviousOld htargetOld hedge
        hpreviousDistance
  | some selectedDistance =>
      have hsettledDistance : settledState.1.get selected = some selectedDistance := hdistance
      have hresult := relaxLoop_result graph weight source selected (nextRank + 1)
        selectedDistance (graph.adjacency selected) settledState hbase hselectedSettled
        hsettledDistance (fun target hmem => hmem)
      refine ⟨hresult.base, ?_⟩
      intro previous target previousDistance hpreviousSettled htargetUnsettled hedge
        hpreviousDistance
      by_cases hprevious : previous = selected
      · subst previous
        have heqDistance := hresult.settledDistance selected hselectedSettled
        rw [hpreviousDistance, hsettledDistance] at heqDistance
        have : previousDistance = selectedDistance := Option.some.inj heqDistance
        subst previousDistance
        simpa [settledState] using hresult.bounds target hedge htargetUnsettled
      · have hpreviousSettledState : settledState.2.2.1.get previous = true := by
          rw [← hresult.settled]
          exact hpreviousSettled
        have hpreviousOld : state.2.2.1.get previous = true := by
          have hpreviousSettledState' :
              (updateVector state.2.2.1 selected true).get previous = true :=
            hpreviousSettledState
          rw [get_updateVector_of_ne _ (Ne.symm hprevious)] at hpreviousSettledState'
          exact hpreviousSettledState'
        have htargetSettledState : settledState.2.2.1.get target = false := by
          rw [← hresult.settled]
          exact htargetUnsettled
        have htargetNe : target ≠ selected := by
          intro equality
          subst target
          rw [hselectedSettled] at htargetSettledState
          contradiction
        have htargetOld : state.2.2.1.get target = false := by
          change (updateVector state.2.2.1 selected true).get target = false at htargetSettledState
          rw [get_updateVector_of_ne _ (Ne.symm htargetNe)] at htargetSettledState
          exact htargetSettledState
        have hpreviousDistanceOld : state.1.get previous = some previousDistance := by
          rw [hresult.settledDistance previous hpreviousSettledState] at hpreviousDistance
          exact hpreviousDistance
        obtain ⟨middleDistance, hmiddleDistance, hmiddleBound⟩ :=
          hinvariant.frontier previous target previousDistance hpreviousOld htargetOld hedge
            hpreviousDistanceOld
        have hdecrease := hresult.decreases target
        change DistanceLE
          ((dijkstra.relaxLoop (relaxOneCore weight) selected (graph.adjacency selected)
            settledState).ret.1.get target) (state.1.get target) at hdecrease
        rw [hmiddleDistance] at hdecrease
        cases hfinal :
            (dijkstra.relaxLoop (relaxOneCore weight) selected (graph.adjacency selected)
              settledState).ret.1.get target with
        | none => simp [DistanceLE, hfinal] at hdecrease
        | some finalDistance =>
            exact ⟨finalDistance, rfl, by
              simp only [DistanceLE, hfinal] at hdecrease
              omega⟩

private def initialCore {n : Nat} (source : Fin n) : DijkstraState n :=
  (Vector.ofFn fun vertex => if vertex = source then some 0 else none,
    Vector.ofFn fun _ => none, Vector.ofFn fun _ => false,
    Vector.ofFn fun _ => none, [])

private lemma initialCore_order {n : Nat} (source : Fin n) :
    OrderInvariant 0 (initialCore source) := by
  refine ⟨by simp [initialCore], by simp [initialCore], ?_⟩
  intro vertex
  simp [initialCore]

private lemma initialCore_rank {n : Nat} (source : Fin n) :
    RankInvariant 0 (initialCore source) := by
  constructor
  · intro vertex rank hrank
    simp [initialCore] at hrank
  · intro vertex hsettled
    simp [initialCore] at hsettled
  · intro vertex rank hrank
    simp [initialCore] at hrank
  · intro target previous hpredecessor
    simp [initialCore] at hpredecessor

private lemma initialCore_selected {n : Nat} (graph : DirectedAdjacency (Fin n))
    (source : Fin n) :
    (dijkstra.selectLoop considerCore (initialCore source) graph.vertices none).ret =
      some source := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨source⟩
  obtain ⟨selected, hselected, hunsettled⟩ :=
    selectMinimum_some graph (initialCore_order source) hn
  have hresult := selectMinimum_result graph (initialCore source) hselected
  have hsourceUnsettled : (initialCore source).2.2.1.get source = false := by
    simp [initialCore]
  have hminimum := hresult.2 source hsourceUnsettled
  have hselectedEq : selected = source := by
    by_contra hne
    have hselectedDistance : (initialCore source).1.get selected = none := by
      simp [initialCore, hne]
    have hsourceDistance : (initialCore source).1.get source = some 0 := by
      simp [initialCore]
    simp [DistanceLE, hselectedDistance, hsourceDistance] at hminimum
  simpa [hselectedEq] using hselected

private lemma initialSettled_base {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) :
    RoundBase graph weight source 1 (settleCore (initialCore source) source 0) := by
  let state := settleCore (initialCore source) source 0
  have horder := settleCore_order (initialCore_order source)
    (by simp [initialCore] : (initialCore source).2.2.1.get source = false)
  constructor
  · simpa using horder
  · simp [settleCore]
  · change (initialCore source).1.get source = some 0
    simp [initialCore]
  · change (initialCore source).2.1.get source = none
    simp [initialCore]
  · intro vertex distance hdistance
    change (initialCore source).1.get vertex = some distance at hdistance
    have hvertex : vertex = source := by
      by_contra hne
      simp [initialCore, hne] at hdistance
    subst vertex
    have : distance = 0 := by
      simpa [initialCore] using hdistance.symm
    subst distance
    exact ⟨[source], List.isChainFromTo_singleton, rfl⟩
  · intro vertex hsettled
    have hvertex : vertex = source := by
      change (updateVector (initialCore source).2.2.1 source true).get vertex = true at hsettled
      by_contra hne
      rw [get_updateVector_of_ne _ (Ne.symm hne)] at hsettled
      simp [initialCore] at hsettled
    subst vertex
    simp only [SettledSpec]
    have hdistance : state.1.get source = some 0 := by
      change (initialCore source).1.get source = some 0
      simp [initialCore]
    rw [hdistance]
    intro otherDistance _
    omega
  · intro target previous hpredecessor
    change (initialCore source).2.1.get target = some previous at hpredecessor
    simp [initialCore] at hpredecessor
  · intro target distance hdistance hne
    change (initialCore source).1.get target = some distance at hdistance
    simp [initialCore, hne] at hdistance

private lemma firstRound_invariant {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) :
    AlgorithmInvariant graph weight source 1
      (dijkstra.relaxLoop (relaxOneCore weight) source (graph.adjacency source)
        (settleCore (initialCore source) source 0)).ret := by
  let settledState := settleCore (initialCore source) source 0
  have hbase := initialSettled_base graph weight source
  have hsourceSettled : settledState.2.2.1.get source = true := by
    simp [settledState, settleCore]
  have hsourceDistance : settledState.1.get source = some 0 := by
    change (initialCore source).1.get source = some 0
    simp [initialCore]
  have hresult := relaxLoop_result graph weight source source 1 0
    (graph.adjacency source) settledState hbase hsourceSettled hsourceDistance
    (fun target hmem => hmem)
  refine ⟨hresult.base, ?_⟩
  intro previous target previousDistance hpreviousSettled htargetUnsettled hedge
    hpreviousDistance
  have hpreviousSettledBefore : settledState.2.2.1.get previous = true := by
    rw [← hresult.settled]
    exact hpreviousSettled
  have hprevious : previous = source := by
    have hpreviousSettledBefore' :
        (updateVector (initialCore source).2.2.1 source true).get previous = true :=
      hpreviousSettledBefore
    by_contra hne
    rw [get_updateVector_of_ne _ (Ne.symm hne)] at hpreviousSettledBefore'
    simp [initialCore] at hpreviousSettledBefore'
  subst previous
  have heqDistance := hresult.settledDistance source hsourceSettled
  rw [hpreviousDistance, hsourceDistance] at heqDistance
  have : previousDistance = 0 := Option.some.inj heqDistance
  subst previousDistance
  simpa [settledState] using hresult.bounds target hedge htargetUnsettled

private lemma firstRound_rank {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) :
    RankInvariant 1
      (dijkstra.relaxLoop (relaxOneCore weight) source (graph.adjacency source)
        (settleCore (initialCore source) source 0)).ret := by
  have hsettled := settleCore_rank (initialCore_rank source)
    (by simp [initialCore] : (initialCore source).2.2.1.get source = false)
  apply relaxLoop_rank weight source (graph.adjacency source)
    (settleCore (initialCore source) source 0) hsettled
  simp [settleCore]

private lemma runRounds_invariant {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n)
    (remaining nextRank : Nat) (state : DijkstraState n)
    (hbound : nextRank + remaining ≤ n)
    (hinvariant : AlgorithmInvariant graph weight source nextRank state) :
    AlgorithmInvariant graph weight source (nextRank + remaining)
      (dijkstra.runRounds graph updateVector considerCore (relaxOneCore weight)
        remaining nextRank state).ret := by
  induction remaining generalizing nextRank state with
  | zero => simpa [dijkstra.runRounds] using hinvariant
  | succ remaining induction =>
      have hnext : nextRank < n := by omega
      obtain ⟨selected, hselected, hselectedUnsettled⟩ :=
        selectMinimum_some graph hinvariant.order hnext
      have hselection := selectMinimum_result graph state hselected
      have hselectedSpec := selected_settledSpec graph weight source selected state
        hinvariant.sourceSettled hinvariant.settled hinvariant.frontier
        hselection.1 hselection.2
      have hnextInvariant := relaxAfterSettle_invariant graph weight source selected nextRank state
        hinvariant hselectedUnsettled hselectedSpec
      simp only [dijkstra.runRounds, TimeM.ret_bind, hselected]
      have hrecursive := induction (nextRank + 1)
        (dijkstra.relaxLoop (relaxOneCore weight) selected (graph.adjacency selected)
          (settleCore state selected nextRank)).ret (by omega) hnextInvariant
      simpa [settleCore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrecursive

private lemma runRounds_rank {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n)
    (remaining nextRank : Nat) (state : DijkstraState n)
    (hbound : nextRank + remaining ≤ n)
    (halgorithm : AlgorithmInvariant graph weight source nextRank state)
    (hrank : RankInvariant nextRank state) :
    RankInvariant (nextRank + remaining)
      (dijkstra.runRounds graph updateVector considerCore (relaxOneCore weight)
        remaining nextRank state).ret := by
  induction remaining generalizing nextRank state with
  | zero => simpa [dijkstra.runRounds] using hrank
  | succ remaining induction =>
      have hnext : nextRank < n := by omega
      obtain ⟨selected, hselected, hselectedUnsettled⟩ :=
        selectMinimum_some graph halgorithm.order hnext
      have hselection := selectMinimum_result graph state hselected
      have hselectedSpec := selected_settledSpec graph weight source selected state
        halgorithm.sourceSettled halgorithm.settled halgorithm.frontier
        hselection.1 hselection.2
      have hnextAlgorithm := relaxAfterSettle_invariant graph weight source selected nextRank state
        halgorithm hselectedUnsettled hselectedSpec
      have hsettledRank := settleCore_rank hrank hselectedUnsettled
      have hnextRank := relaxLoop_rank weight selected (graph.adjacency selected)
        (settleCore state selected nextRank) hsettledRank (by simp [settleCore])
      simp only [dijkstra.runRounds, TimeM.ret_bind, hselected]
      have hrecursive := induction (nextRank + 1)
        (dijkstra.relaxLoop (relaxOneCore weight) selected (graph.adjacency selected)
          (settleCore state selected nextRank)).ret (by omega) hnextAlgorithm hnextRank
      simpa [settleCore, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrecursive

private def finalCore {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) : DijkstraState n :=
  (dijkstra.runRounds graph updateVector considerCore (relaxOneCore weight)
    n 0 (initialCore source)).ret

private lemma finalCore_invariant {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) :
    AlgorithmInvariant graph weight source n (finalCore graph weight source) := by
  cases n with
  | zero => exact Fin.elim0 source
  | succ n =>
      have hfirst := firstRound_invariant graph weight source
      have hrest := runRounds_invariant graph weight source n 1
        (dijkstra.relaxLoop (relaxOneCore weight) source (graph.adjacency source)
          (settleCore (initialCore source) source 0)).ret (by omega) hfirst
      unfold finalCore
      simp only [dijkstra.runRounds, TimeM.ret_bind, initialCore_selected]
      simpa [settleCore, Nat.add_comm] using hrest

private lemma finalCore_rank {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) :
    RankInvariant n (finalCore graph weight source) := by
  cases n with
  | zero => exact Fin.elim0 source
  | succ n =>
      have hfirst := firstRound_invariant graph weight source
      have hfirstRank := firstRound_rank graph weight source
      have hrest := runRounds_rank graph weight source n 1
        (dijkstra.relaxLoop (relaxOneCore weight) source (graph.adjacency source)
          (settleCore (initialCore source) source 0)).ret (by omega) hfirst hfirstRank
      unfold finalCore
      simp only [dijkstra.runRounds, TimeM.ret_bind, initialCore_selected]
      simpa [settleCore, Nat.add_comm] using hrest

private def selectedEntryCount {n : Nat} (graph : DirectedAdjacency (Fin n))
    (vertices : List (Fin n)) : Nat :=
  (vertices.map fun vertex => (graph.adjacency vertex).length).sum

private lemma relaxOneCore_order_eq {n : Nat} (weight : Fin n → Fin n → Nat)
    (previous target : Fin n) (state : DijkstraState n) :
    (relaxOneCore weight previous target state).2.2.2.2 = state.2.2.2.2 := by
  simp only [relaxOneCore]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

private lemma relaxLoop_order_eq {n : Nat} (weight : Fin n → Fin n → Nat)
    (previous : Fin n) (vertices : List (Fin n)) (state : DijkstraState n) :
    (dijkstra.relaxLoop (relaxOneCore weight) previous vertices state).ret.2.2.2.2 =
      state.2.2.2.2 := by
  induction vertices generalizing state with
  | nil => rfl
  | cons target vertices induction =>
      simp only [dijkstra.relaxLoop, TimeM.ret_bind]
      rw [induction, relaxOneCore_order_eq]

private lemma selectLoop_time {n : Nat}
    (consider : DijkstraState n → Option (Fin n) → Fin n → Option (Fin n))
    (state : DijkstraState n) (vertices : List (Fin n)) (best : Option (Fin n)) :
    (dijkstra.selectLoop consider state vertices best).time =
      { minScans := vertices.length, edgeRelaxations := 0 } := by
  induction vertices generalizing best with
  | nil => rfl
  | cons vertex vertices induction =>
      simp only [dijkstra.selectLoop, TimeM.time_bind, TimeM.time_tick]
      rw [induction]
      change DijkstraCost.mk (1 + vertices.length) (0 + 0) =
        DijkstraCost.mk (vertices.length + 1) 0
      apply congrArg₂ DijkstraCost.mk
      · omega
      · omega

private lemma relaxLoop_time {n : Nat}
    (relaxOne : Fin n → Fin n → DijkstraState n → DijkstraState n)
    (previous : Fin n) (vertices : List (Fin n)) (state : DijkstraState n) :
    (dijkstra.relaxLoop relaxOne previous vertices state).time =
      { minScans := 0, edgeRelaxations := vertices.length } := by
  induction vertices generalizing state with
  | nil => rfl
  | cons vertex vertices induction =>
      simp only [dijkstra.relaxLoop, TimeM.time_bind, TimeM.time_tick]
      rw [induction]
      change DijkstraCost.mk (0 + 0) (1 + vertices.length) =
        DijkstraCost.mk 0 (vertices.length + 1)
      apply congrArg₂ DijkstraCost.mk
      · omega
      · omega

private lemma runRounds_edge_accounting {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (remaining nextRank : Nat)
    (state : DijkstraState n) :
    selectedEntryCount graph state.2.2.2.2 +
        (dijkstra.runRounds graph updateVector considerCore (relaxOneCore weight)
          remaining nextRank state).time.edgeRelaxations =
      selectedEntryCount graph
        (dijkstra.runRounds graph updateVector considerCore (relaxOneCore weight)
          remaining nextRank state).ret.2.2.2.2 := by
  induction remaining generalizing nextRank state with
  | zero => simp [dijkstra.runRounds]
  | succ remaining induction =>
      simp only [dijkstra.runRounds, TimeM.time_bind, TimeM.ret_bind, selectLoop_time]
      split
      · rename_i selected hselected
        simpa using induction nextRank state
      · rename_i selected hselected
        simp only [TimeM.time_bind, TimeM.ret_bind, relaxLoop_time, add_edgeRelaxations]
        let settled := settleCore state selected nextRank
        let relaxed :=
          (dijkstra.relaxLoop (relaxOneCore weight) selected (graph.adjacency selected)
            settled).ret
        have hrecursive := induction (nextRank + 1) relaxed
        have horder : relaxed.2.2.2.2 = state.2.2.2.2 ++ [selected] := by
          dsimp only [relaxed, settled]
          rw [relaxLoop_order_eq]
          rfl
        rw [horder] at hrecursive
        dsimp only [relaxed, settled, settleCore] at hrecursive ⊢
        simp only [selectedEntryCount, List.map_append, List.map_singleton, List.sum_append,
          List.sum_singleton] at hrecursive ⊢
        omega

private lemma finalCore_order_perm {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) :
    (finalCore graph weight source).2.2.2.2.Perm graph.vertices := by
  have hinvariant := (finalCore_invariant graph weight source).order
  apply (List.perm_ext_iff_of_nodup hinvariant.1 graph.vertices_nodup).mpr
  intro vertex
  have hmem : vertex ∈ (finalCore graph weight source).2.2.2.2 := by
    by_contra hnotMem
    have hnodup : (vertex :: (finalCore graph weight source).2.2.2.2).Nodup := by
      simp [hnotMem, hinvariant.1]
    have hle := List.Nodup.length_le_card hnodup
    simp [hinvariant.2.1] at hle
  exact ⟨fun _ => graph.vertices_complete vertex, fun _ => hmem⟩

private lemma finalCore_settled {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source target : Fin n) :
    (finalCore graph weight source).2.2.1.get target = true := by
  have hinvariant := finalCore_invariant graph weight source
  apply (hinvariant.order.2.2 target).mpr
  exact (finalCore_order_perm graph weight source).mem_iff.mpr
    (graph.vertices_complete target)

/-- Every finite output distance is realized by a concrete source path. -/
theorem dijkstra_distance_realized {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source target : Fin n) (distance : Nat)
    (h : (dijkstra graph weight source).ret.distance.get target = some distance) :
    HasPathWeight graph weight source target distance := by
  change (finalCore graph weight source).1.get target = some distance at h
  exact (finalCore_invariant graph weight source).realized target distance h

/-- Every finite output distance is no greater than any concrete source-path weight. -/
theorem dijkstra_distance_minimal {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source target : Fin n)
    (distance otherDistance : Nat)
    (h : (dijkstra graph weight source).ret.distance.get target = some distance)
    (path : HasPathWeight graph weight source target otherDistance) :
    distance ≤ otherDistance := by
  change (finalCore graph weight source).1.get target = some distance at h
  have hspec := (finalCore_invariant graph weight source).settled target
    (finalCore_settled graph weight source target)
  simp only [SettledSpec, h] at hspec
  exact hspec otherDistance path

/-- An infinite output distance is equivalent to graph unreachability. -/
theorem dijkstra_distance_eq_none_iff {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source target : Fin n) :
    (dijkstra graph weight source).ret.distance.get target = none ↔
      ¬graph.Reachable source target := by
  change (finalCore graph weight source).1.get target = none ↔
    ¬graph.Reachable source target
  constructor
  · intro hnone
    have hspec := (finalCore_invariant graph weight source).settled target
      (finalCore_settled graph weight source target)
    simpa [SettledSpec, hnone] using hspec
  · intro hunreachable
    cases hdistance : (finalCore graph weight source).1.get target with
    | none => rfl
    | some distance =>
        exact False.elim (hunreachable
          ((reachable_iff_exists_hasPathWeight graph weight source target).mpr
            ⟨distance, (finalCore_invariant graph weight source).realized target distance
              hdistance⟩))

/-- Every predecessor is an edge realizing the final distance equation. -/
theorem dijkstra_predecessor_spec {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source target previous : Fin n)
    (h : (dijkstra graph weight source).ret.predecessor.get target = some previous) :
    graph.Edge previous target ∧
      ∃ previousDistance targetDistance,
        (dijkstra graph weight source).ret.distance.get previous = some previousDistance ∧
        (dijkstra graph weight source).ret.distance.get target = some targetDistance ∧
        targetDistance = previousDistance + weight previous target := by
  change (finalCore graph weight source).2.1.get target = some previous at h
  obtain ⟨_, hedge, previousDistance, targetDistance, hprevious, htarget, hequation⟩ :=
    (finalCore_invariant graph weight source).predecessor target previous h
  exact ⟨hedge, previousDistance, targetDistance, hprevious, htarget, hequation⟩

private lemma final_predecessor_rank {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source target previous : Fin n)
    (hpredecessor : (finalCore graph weight source).2.1.get target = some previous) :
    ∃ previousRank targetRank,
      (finalCore graph weight source).2.2.2.1.get previous = some previousRank ∧
      (finalCore graph weight source).2.2.2.1.get target = some targetRank ∧
      previousRank < targetRank := by
  have hrank := (finalCore_rank graph weight source).predecessorRank target previous hpredecessor
  obtain ⟨previousRank, hpreviousRank, hnone | ⟨targetRank, htargetRank, hlt⟩⟩ := hrank
  · obtain ⟨targetRank, htargetRank⟩ :=
      (finalCore_rank graph weight source).settledRank target
        (finalCore_settled graph weight source target)
    rw [hnone] at htargetRank
    contradiction
  · exact ⟨previousRank, targetRank, hpreviousRank, htargetRank, hlt⟩

private lemma followPredecessors_final_spec {n : Nat}
    (graph : DirectedAdjacency (Fin n)) (weight : Fin n → Fin n → Nat)
    (source target : Fin n) (targetRank fuel distance : Nat)
    (htargetRank : (finalCore graph weight source).2.2.2.1.get target = some targetRank)
    (hfuel : targetRank < fuel)
    (hdistance : (finalCore graph weight source).1.get target = some distance) :
    ∃ path,
      followPredecessors (finalCore graph weight source).2.1 source target fuel = some path ∧
      path.IsChainFromTo graph.Edge source target ∧ path.Nodup ∧
      pathWeight weight path = distance ∧
      ∀ vertex ∈ path, ∃ rank,
        (finalCore graph weight source).2.2.2.1.get vertex = some rank ∧
        rank ≤ targetRank := by
  induction targetRank using Nat.strong_induction_on generalizing target fuel distance with
  | h targetRank induction =>
      by_cases hsource : target = source
      · subst target
        have hdistanceZero : distance = 0 := by
          rw [(finalCore_invariant graph weight source).sourceDistance] at hdistance
          exact Option.some.inj hdistance.symm
        subst distance
        cases fuel with
        | zero => omega
        | succ fuel =>
            refine ⟨[source], by simp [followPredecessors],
              List.isChainFromTo_singleton, by simp, rfl, ?_⟩
            intro vertex hmem
            simp only [List.mem_singleton] at hmem
            subst vertex
            exact ⟨targetRank, htargetRank, Nat.le_refl _⟩
      · obtain ⟨previous, hpredecessor⟩ :=
          (finalCore_invariant graph weight source).finitePredecessor target distance
            hdistance hsource
        obtain ⟨hpreviousSettled, hedge, previousDistance, targetDistance,
            hpreviousDistance, htargetDistance, hequation⟩ :=
          (finalCore_invariant graph weight source).predecessor target previous hpredecessor
        have hdistanceEq : targetDistance = distance := by
          rw [hdistance] at htargetDistance
          exact Option.some.inj htargetDistance.symm
        rw [hdistanceEq] at hequation
        obtain ⟨previousRank, targetRank', hpreviousRank, htargetRank', hrank⟩ :=
          final_predecessor_rank graph weight source target previous hpredecessor
        have htargetRankEq : targetRank' = targetRank := by
          rw [htargetRank] at htargetRank'
          exact Option.some.inj htargetRank'.symm
        subst targetRank'
        cases fuel with
        | zero => omega
        | succ fuel =>
            have hpreviousFuel : previousRank < fuel := by omega
            obtain ⟨path, hfollow, hchain, hnodup, hweight, hranks⟩ :=
              induction previousRank hrank previous fuel previousDistance hpreviousRank
                hpreviousFuel hpreviousDistance
            have htargetNotMem : target ∉ path := by
              intro hmem
              obtain ⟨rank, hrankVertex, hrankLe⟩ := hranks target hmem
              rw [htargetRank] at hrankVertex
              have : rank = targetRank := (Option.some.inj hrankVertex).symm
              omega
            refine ⟨path ++ [target], ?_, hchain.snoc hedge, (by
              rw [List.nodup_append]
              exact ⟨hnodup, by simp, by
                intro vertex hmemVertex last hmemLast
                simp only [List.mem_singleton] at hmemLast
                subst last
                exact fun equality => htargetNotMem (equality ▸ hmemVertex)⟩), ?_, ?_⟩
            · simp [followPredecessors, hsource, hpredecessor, hfollow]
            · rw [pathWeight_append_singleton weight hchain.ne_nil, hchain.getLast_eq,
                hweight, hequation]
            · intro vertex hmem
              simp only [List.mem_append, List.mem_singleton] at hmem
              rcases hmem with hmem | rfl
              · obtain ⟨rank, hrankVertex, hrankLe⟩ := hranks vertex hmem
                exact ⟨rank, hrankVertex, Nat.le_trans hrankLe (Nat.le_of_lt hrank)⟩
              · exact ⟨targetRank, htargetRank, Nat.le_refl _⟩

private lemma pathTo?_go_eq_followPredecessors {n : Nat} (result : DijkstraResult n)
    (target : Fin n) (fuel : Nat) :
    DijkstraResult.pathTo?.go result target fuel =
      followPredecessors result.predecessor result.source target fuel := by
  induction fuel generalizing target with
  | zero => simp [DijkstraResult.pathTo?.go, followPredecessors]
  | succ fuel induction =>
      by_cases hsource : target = result.source
      · simp [DijkstraResult.pathTo?.go, followPredecessors, hsource]
      · cases hpredecessor : result.predecessor.get target with
        | none => simp [DijkstraResult.pathTo?.go, followPredecessors, hsource, hpredecessor]
        | some previous =>
            simp [DijkstraResult.pathTo?.go, followPredecessors, hsource, hpredecessor,
              induction previous]

private lemma pathTo?_eq_followPredecessors {n : Nat} (result : DijkstraResult n)
    (target : Fin n) :
    result.pathTo? target =
      followPredecessors result.predecessor result.source target n := by
  unfold DijkstraResult.pathTo?
  exact pathTo?_go_eq_followPredecessors result target n

private lemma final_path_exists {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source target : Fin n) (distance : Nat)
    (hdistance : (finalCore graph weight source).1.get target = some distance) :
    ∃ path,
      followPredecessors (finalCore graph weight source).2.1 source target n = some path ∧
      path.IsChainFromTo graph.Edge source target ∧ path.Nodup ∧
      pathWeight weight path = distance := by
  obtain ⟨targetRank, htargetRank⟩ :=
    (finalCore_rank graph weight source).settledRank target
      (finalCore_settled graph weight source target)
  have hbound := (finalCore_rank graph weight source).rankBound target targetRank htargetRank
  obtain ⟨path, hfollow, hchain, hnodup, hweight, -⟩ :=
    followPredecessors_final_spec graph weight source target targetRank n distance
      htargetRank hbound hdistance
  exact ⟨path, hfollow, hchain, hnodup, hweight⟩

/-- Predecessor reconstruction fails exactly at vertices with infinite distance. -/
theorem dijkstra_pathTo?_eq_none_iff {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source target : Fin n) :
    (dijkstra graph weight source).ret.pathTo? target = none ↔
      (dijkstra graph weight source).ret.distance.get target = none := by
  change (DijkstraResult.mk source (finalCore graph weight source).1
      (finalCore graph weight source).2.1).pathTo? target = none ↔
    (finalCore graph weight source).1.get target = none
  rw [pathTo?_eq_followPredecessors]
  constructor
  · intro hnone
    cases hdistance : (finalCore graph weight source).1.get target with
    | none => rfl
    | some distance =>
        obtain ⟨path, hpath, -⟩ := final_path_exists graph weight source target distance hdistance
        rw [hpath] at hnone
        contradiction
  · intro hdistance
    have htargetSource : target ≠ source := by
      intro equality
      subst target
      rw [(finalCore_invariant graph weight source).sourceDistance] at hdistance
      contradiction
    have hpredecessor : (finalCore graph weight source).2.1.get target = none := by
      cases hpred : (finalCore graph weight source).2.1.get target with
      | none => rfl
      | some previous =>
          obtain ⟨_, _, _, targetDistance, _, htargetDistance, -⟩ :=
            (finalCore_invariant graph weight source).predecessor target previous hpred
          rw [hdistance] at htargetDistance
          contradiction
    cases n with
    | zero => exact Fin.elim0 source
    | succ n => simp [followPredecessors, htargetSource, hpredecessor]

/-- Successful reconstruction is a simple shortest source-to-target path. -/
theorem dijkstra_pathTo?_spec {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source target : Fin n) (path : List (Fin n))
    (h : (dijkstra graph weight source).ret.pathTo? target = some path) :
    ∃ distance,
      (dijkstra graph weight source).ret.distance.get target = some distance ∧
      path.head? = some source ∧ path.getLast? = some target ∧
      path.IsChain graph.Edge ∧ path.Nodup ∧ pathWeight weight path = distance := by
  change (DijkstraResult.mk source (finalCore graph weight source).1
      (finalCore graph weight source).2.1).pathTo? target = some path at h
  rw [pathTo?_eq_followPredecessors] at h
  have hfinite : (finalCore graph weight source).1.get target ≠ none := by
    intro hnone
    have := (dijkstra_pathTo?_eq_none_iff graph weight source target).mpr hnone
    change (DijkstraResult.mk source (finalCore graph weight source).1
      (finalCore graph weight source).2.1).pathTo? target = none at this
    rw [pathTo?_eq_followPredecessors] at this
    rw [h] at this
    contradiction
  cases hdistance : (finalCore graph weight source).1.get target with
  | none => exact False.elim (hfinite hdistance)
  | some distance =>
      obtain ⟨expected, hexpected, hchain, hnodup, hweight⟩ :=
        final_path_exists graph weight source target distance hdistance
      rw [h] at hexpected
      have hpath : path = expected := Option.some.inj hexpected
      subst expected
      refine ⟨distance, hdistance, ?_, ?_, hchain.isChain, hnodup, hweight⟩
      · rw [List.head?_eq_some_head hchain.ne_nil, hchain.head_eq]
      · rw [List.getLast?_eq_some_getLast hchain.ne_nil, hchain.getLast_eq]

/-- Every adjacency-list entry is inspected exactly once. -/
theorem dijkstra_edgeRelaxations {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) :
    (dijkstra graph weight source).time.edgeRelaxations = adjacencyEntryCount graph := by
  have haccounting := runRounds_edge_accounting graph weight n 0 (initialCore source)
  have hperm := finalCore_order_perm graph weight source
  have hsum := (hperm.map fun vertex => (graph.adjacency vertex).length).sum_nat
  change
    (dijkstra.runRounds graph updateVector considerCore (relaxOneCore weight)
      n 0 (initialCore source)).time.edgeRelaxations = adjacencyEntryCount graph
  simpa [selectedEntryCount, initialCore, finalCore, adjacencyEntryCount] using
    haccounting.trans hsum

private lemma runRounds_minScans {n : Nat} (graph : DirectedAdjacency (Fin n))
    (update : {α : Type} → Vector α n → Fin n → α → Vector α n)
    (consider : DijkstraState n → Option (Fin n) → Fin n → Option (Fin n))
    (relaxOne : Fin n → Fin n → DijkstraState n → DijkstraState n)
    (remaining nextRank : Nat) (state : DijkstraState n) :
    (dijkstra.runRounds graph update consider relaxOne remaining nextRank state).time.minScans =
      remaining * graph.vertices.length := by
  induction remaining generalizing nextRank state with
  | zero => simp [dijkstra.runRounds]
  | succ remaining induction =>
      simp only [dijkstra.runRounds, TimeM.time_bind, selectLoop_time]
      split
      · simp only [induction, add_minScans, Nat.succ_mul]
        exact Nat.add_comm _ _
      · simp only [TimeM.time_bind, relaxLoop_time, induction, add_minScans]
        simp only [Nat.zero_add, Nat.succ_mul]
        exact Nat.add_comm _ _

/-- Dense minimum selection inspects exactly `n * n` vertex entries. -/
theorem dijkstra_minScans {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) :
    (dijkstra graph weight source).time.minScans = n * n := by
  simp only [dijkstra]
  rw [runRounds_minScans, vertices_length]

/-- The total abstract event count is exactly `n * n` plus all adjacency entries. -/
theorem dijkstra_time {n : Nat} (graph : DirectedAdjacency (Fin n))
    (weight : Fin n → Fin n → Nat) (source : Fin n) :
    (dijkstra graph weight source).time.total = n * n + adjacencyEntryCount graph := by
  unfold DijkstraCost.total
  rw [dijkstra_minScans, dijkstra_edgeRelaxations]

end Cslib.Algorithms.Lean.DirectedAdjacency
