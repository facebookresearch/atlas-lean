/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.DAG

/-!
# Critical-path scheduling statements (SCH-001, proved module)

Activity-on-arc critical-path analysis over the existing `BellmanFord` edge
occurrences, `IsWeightedPath` bridge, and `dagShortestPaths` wrapper. Exactly
two runs supply the raw outputs: forward on negated edges from `s` (earliest
starts `ES`), and once on reversed negated edges from `t` (longest times to
sink `LT`). Derived latest starts `LS`, vertex slack, and activity float are
`Option`-valued and defined exactly where their prerequisites are; orphan
occurrences are reported, never filled with `0`.

The raw outputs are path weights: `ES v` is the longest `s`-to-`v` path weight, so the makespan
`ES t` is the longest source-to-sink path weight, and `LT v` is the longest `v`-to-`t` path
weight. When the runs succeed, `t` is reachable from `s`, the project is covered and durations
are nonnegative, `ES` is pointwise earliest on model events among feasible schedules, and the
latest starts `LS = T - LT` are pointwise latest on model events among feasible schedules
finishing by the makespan `T` (`earliestSchedule_feasible`, `latestSchedule_feasible`).
Coverage alone does not give reachability: it holds vacuously when there are no activities.
Feasibility constrains no vertex outside the model events, so when such a vertex exists no
schedule is earliest or latest on every vertex. Without coverage `ES` and the makespan are still
lower bounds on every feasible schedule (`feasible_dominates_earliest`, `makespan_le_completion`),
but an occurrence off every source-to-sink path can force a later sink.

The declarations live in the namespace `Cslib.Algorithms.Lean.Scheduling.CriticalPath`, so
they load together with the list-scheduling API of
`CSLibExt.Algorithms.Lean.Approximation.ListScheduling`, whose `makespan` is a different
quantity. `MathlibExt.Combinatorics.Graph.ArcNetworkCriticalPath` (critical-path lower bound,
earliest event dates) and `Cslib.Scheduling.ProjectNetwork` state the specification over an
arc type with `ℕ` durations, without a longest-path algorithm, backward pass or float; this
module computes these quantities with `dagShortestPaths` over integer-weighted `BellmanFord`
edge lists.

This file is a proved module: concrete definitions with no holes, and explicit
theorems with complete proofs. Clause map (`C1`-`C9` in
this file; `C10` is the separate test library):

* `C1` (model): inputs `n`, `edges`, `s`, `t`; `negEdges`, `revNegEdges`.
* `C2` (bridge, private): `negEdges_toDirectedAdjacency`,
  `isWeightedPath_negEdges_iff`, `revNegEdges_edge_iff`,
  `isWeightedPath_revNegEdges_iff`, `isAcyclic_revNegEdges`.
* `C3` (forward run): `forward_run_ok`, `earliestStart_spec`,
  `earliestStart_eq_none_iff`.
* `C4` (reversed run): `reversed_run_ok`, `longestToSink_spec`,
  `longestToSink_eq_none_iff`.
* `C5` (makespan): `makespan_exists`,
  `earliestStart_sink_none_of_unreachable`,
  `longestToSink_source_none_of_unreachable`.
* `C6` (derived/diagnostics): `latestStart_some_iff`, `latestStart_eq_none_iff`,
  `slack_some_iff`, `slack_eq_none_iff`, `activityFloat_some_iff`,
  `activityFloat_eq_none_iff`, `slackAt_defined_iff`, `floatAt_defined_iff`,
  `coverage_iff_no_orphan`.
* `C7` (vertex slack): `slackAt_spec`.
* `C8` (activity float): `floatAt_spec`.
* `C9` (scheduling law): `raw_defined_on_modelEvents`,
  `earliestSchedule_feasible`, `feasible_dominates_earliest`,
  `makespan_le_completion`, `feasible_activity_finishes_by_sink`,
  `latestSchedule_feasible`.
* `C10` (fixtures): separate test library, not in this file.

## References

* J. E. Kelley Jr. and M. R. Walker, Critical-path planning and scheduling, *Proceedings of
  the Eastern Joint Computer Conference*, 1959, pp. 160-173: the critical-path method on an
  activity-on-arc network, with earliest and latest times, float, and the project duration
  as the length of a longest source-to-sink path.
* D. G. Malcolm, J. H. Roseboom, C. E. Clark and W. Fazar, Application of a technique for
  research and development program evaluation, *Operations Research* 7 (1959), pp. 646-669:
  PERT event slack, the latest minus the earliest event time.
* T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  3rd ed., MIT Press, 2009, Section 24.2: a critical path of a weighted DAG is a longest
  path, found by running the DAG shortest-path algorithm on negated edge weights, and its
  weight is a lower bound on the time to perform all jobs.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Scheduling.CriticalPath

open BellmanFord

/-- Negate every activity duration, keeping endpoints, order, and multiplicity. (`C1`, `C2`) -/
@[expose] public def negEdges {n : Nat} (edges : List (Edge n)) : List (Edge n) :=
  edges.map fun e => { e with weight := -e.weight }

/-- Reverse every endpoint pair and negate every duration: the transposed network. (`C1`, `C2`) -/
@[expose] public def revNegEdges {n : Nat} (edges : List (Edge n)) : List (Edge n) :=
  edges.map fun e => { source := e.target, target := e.source, weight := -e.weight }

/-- Raw output of the forward run at `v`, negated back to durations: the longest `s`-to-`v`
path weight (`earliestStart_spec`), `none` off the forward reachable set. Where it is defined,
every feasible schedule puts `v` no earlier (`feasible_dominates_earliest`). When the forward run
succeeds, `t` is reachable from `s`, the project is covered and durations are nonnegative, then
for each model event `v` the returned value is the earliest feasible time at `v`
(`earliestSchedule_feasible`); these hypotheses are sufficient, not necessary. Off the model
events feasibility constrains no time, so a vertex there has no earliest feasible time. (`C3`) -/
@[expose] public def earliestStart {n : Nat} (result : Distances n) (v : Fin n) :
    Option Int :=
  (result.distance.get v).map Neg.neg

/-- Raw longest-time-to-sink output of a successful reversed run. (`C4`) -/
@[expose] public def longestToSink {n : Nat} (result : Distances n) (v : Fin n) :
    Option Int :=
  (result.distance.get v).map Neg.neg

/-- Project makespan read from the forward run at the sink: the longest source-to-sink path
weight (`makespan_exists`), `none` when the sink is unreachable. It lower-bounds the sink time of
every feasible schedule (`makespan_le_completion`). When the forward run succeeds, `t` is
reachable from `s`, the project is covered and durations are nonnegative, it is the earliest
feasible sink time (`earliestSchedule_feasible`); these hypotheses are sufficient, not necessary.
Without coverage an occurrence off every source-to-sink path can force a later sink. It is not the
largest machine load that the list-scheduling `Cslib.Algorithms.Lean.Scheduling.makespan`
measures. (`C5`) -/
@[expose] public def makespan {n : Nat} (result : Distances n) (t : Fin n) : Option Int :=
  earliestStart result t

/-- Latest start from makespan and longest-to-sink; `none` unless both are defined. (`C6`) -/
@[expose] public def latestStart (T lt : Option Int) : Option Int :=
  match T, lt with
  | some Tv, some b => some (Tv - b)
  | _, _ => none

/-- Vertex slack from earliest and latest starts; `none` unless both are defined. (`C6`) -/
@[expose] public def slack (es ls : Option Int) : Option Int :=
  match es, ls with
  | some a, some l => some (l - a)
  | _, _ => none

/-- Activity total float; `none` unless both endpoint prerequisites are defined. (`C6`) -/
@[expose] public def activityFloat (esSrc lsTgt : Option Int) (w : Int) : Option Int :=
  match esSrc, lsTgt with
  | some a, some l => some (l - a - w)
  | _, _ => none

/-- Latest-start time `T - LT v` of a vertex from a makespan `T` and the reversed run. With `T`
the makespan and `v` a model event, it is the latest time of `v` over feasible schedules finishing
by `T` when both runs succeed, `t` is reachable from `s`, the project is covered and durations are
nonnegative (`latestSchedule_feasible`); these hypotheses are sufficient, not necessary. Off the
model events feasibility gives no latest time. (`C6`) -/
@[expose] public def latestStartAt {n : Nat} (T : Option Int) (reverse : Distances n)
    (v : Fin n) : Option Int :=
  latestStart T (longestToSink reverse v)

/-- Slack of a vertex from makespan and both runs. (`C6`) -/
@[expose] public def slackAt {n : Nat} (T : Option Int) (forward reverse : Distances n)
    (v : Fin n) : Option Int :=
  slack (earliestStart forward v) (latestStartAt T reverse v)

/-- Total float of an activity occurrence from makespan and both runs. (`C6`) -/
@[expose] public def floatAt {n : Nat} (T : Option Int) (forward reverse : Distances n)
    (e : Edge n) : Option Int :=
  activityFloat (earliestStart forward e.source) (latestStartAt T reverse e.target)
    e.weight

/-- An occurrence is orphaned when a raw endpoint prerequisite is absent. (`C6`) -/
@[expose] public def isOrphan {n : Nat} (forward reverse : Distances n) (e : Edge n) :
    Prop :=
  earliestStart forward e.source = none ∨ longestToSink reverse e.target = none

/-- Every activity occurrence lies on a directed walk from `s` to `t` (a simple path on a DAG):
`s` reaches its source and its target reaches `t`. (`C6`, `C9`) -/
@[expose] public def IsCovered {n : Nat} (edges : List (Edge n)) (s t : Fin n) : Prop :=
  ∀ e ∈ edges, (toDirectedAdjacency edges).Reachable s e.source ∧
    (toDirectedAdjacency edges).Reachable e.target t

/-- Model events: the source, the sink, and every occurrence endpoint. (`C9`) -/
@[expose] public def IsModelEvent {n : Nat} (edges : List (Edge n)) (s t v : Fin n) :
    Prop :=
  v = s ∨ v = t ∨ ∃ e ∈ edges, e.source = v ∨ e.target = v

/-- A feasible event schedule: nonnegative model-event times and every precedence
constraint. Unlike `MathlibExt.Combinatorics.Graph.ArcNetwork.IsFeasibleSchedule`, which has
`ℕ` times over an arc type, times here are integers over the `BellmanFord` occurrence list
that the runs read, so nonnegativity on model events is part of the definition. (`C9`) -/
@[expose] public def IsFeasibleSchedule {n : Nat} (edges : List (Edge n)) (s t : Fin n)
    (τ : Fin n → Int) : Prop :=
  (∀ v, IsModelEvent edges s t v → 0 ≤ τ v) ∧
    ∀ e ∈ edges, τ e.source + e.weight ≤ τ e.target

/-- Weight negation is an involution on edge occurrences. -/
private theorem negEdges_involutive {n : Nat} (e : Edge n) :
    { ({ e with weight := -e.weight } : Edge n) with weight :=
        -({ e with weight := -e.weight } : Edge n).weight } = e := by
  obtain ⟨s, t, w⟩ := e
  change ({ source := s, target := t, weight := - -w } : Edge n) = ⟨s, t, w⟩
  rw [neg_neg]

/-- Mapping weight negation twice restores the occurrence list. -/
private theorem negEdges_map_involutive {n : Nat} (l : List (Edge n)) :
    ((l.map fun e => ({ e with weight := -e.weight } : Edge n)).map
      fun e => ({ e with weight := -e.weight } : Edge n)) = l := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, ih]
    congr 1
    exact negEdges_involutive e

/-- Endpoint-flipping negation is an involution on edge occurrences. -/
private theorem revNegEdges_involutive {n : Nat} (e : Edge n) :
    { source := ({ source := e.target, target := e.source, weight := -e.weight } :
        Edge n).target,
      target := ({ source := e.target, target := e.source, weight := -e.weight } :
        Edge n).source,
      weight := -({ source := e.target, target := e.source, weight := -e.weight } :
        Edge n).weight } = e := by
  obtain ⟨s, t, w⟩ := e
  change ({ source := s, target := t, weight := - -w } : Edge n) = ⟨s, t, w⟩
  rw [neg_neg]

/-- Mapping endpoint-flipping negation twice restores the occurrence list. -/
private theorem revNegEdges_map_involutive {n : Nat} (l : List (Edge n)) :
    ((l.map fun e =>
      ({ source := e.target, target := e.source, weight := -e.weight } : Edge n)).map
      fun e =>
      ({ source := e.target, target := e.source, weight := -e.weight } : Edge n)) = l := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, ih]
    congr 1
    exact revNegEdges_involutive e

/-- The mapped path weight is the negated sum. -/
private theorem pathWeight_map_neg {n : Nat} (p : List (Edge n)) :
    pathWeight (p.map fun e => ({ e with weight := -e.weight } : Edge n)) =
      -pathWeight p := by
  induction p with
  | nil => simp [pathWeight]
  | cons e es ih =>
    simp only [pathWeight] at ih ⊢
    simp only [List.map_cons, List.sum_cons, ih, neg_add]

/-- The reversed mapped path weight is the negated sum. -/
private theorem pathWeight_reverse_map {n : Nat} (p : List (Edge n)) :
    pathWeight (((p.map fun e =>
      ({ source := e.target, target := e.source, weight := -e.weight } : Edge n)).reverse)) =
      -pathWeight p := by
  induction p with
  | nil => simp [pathWeight]
  | cons e es ih =>
    have hhead : Edge.weight
        ({ source := e.target, target := e.source, weight := -e.weight } : Edge n) =
        -e.weight := rfl
    simp only [List.map_cons, List.reverse_cons]
    rw [pathWeight_append_edge, hhead, ih]
    simp only [pathWeight, List.map_cons, List.sum_cons, neg_add]
    omega

/-- The chain condition transfers through weight negation. -/
private theorem isChain_neg_map {n : Nat} (q : List (Edge n)) :
    (q.map fun e => ({ e with weight := -e.weight } : Edge n)).IsChain
        (fun left right => left.target = right.source) ↔
      q.IsChain (fun left right => left.target = right.source) := by
  induction q with
  | nil => simp
  | cons e es ih =>
    cases es with
    | nil => simp
    | cons f fs =>
      simp only [List.map_cons, List.isChain_cons_cons]
      have hrel : (({ e with weight := -e.weight } : Edge n).target =
          ({ f with weight := -f.weight } : Edge n).source) ↔
          (e.target = f.source) := Iff.rfl
      rw [hrel]
      simp only [List.map_cons] at ih
      rw [ih]

/-- The chain condition transfers through reversal and endpoint-flipping. -/
private theorem isChain_map_revneg {n : Nat} (q : List (Edge n)) :
    (q.map fun e =>
      ({ source := e.target, target := e.source, weight := -e.weight } : Edge n)).IsChain
        (fun x y => y.target = x.source) ↔
      q.IsChain (fun x y => x.target = y.source) := by
  induction q with
  | nil => simp
  | cons e es ih =>
    cases es with
    | nil => simp
    | cons f fs =>
      simp only [List.map_cons, List.isChain_cons_cons]
      have hrel : (({ source := f.target, target := f.source, weight := -f.weight } :
          Edge n).target =
          ({ source := e.target, target := e.source, weight := -e.weight } :
          Edge n).source) ↔
          (e.target = f.source) := eq_comm
      rw [hrel]
      simp only [List.map_cons] at ih
      rw [ih]

/-- Mapped last-target projection agrees with the unmapped one. -/
private theorem getLast?_map_neg_target {n : Nat} (q : List (Edge n)) :
    (((q.map fun e => ({ e with weight := -e.weight } : Edge n)).getLast?).map
      Edge.target) = ((q.getLast?).map Edge.target) := by
  induction q with
  | nil => rfl
  | cons e es ih =>
    cases es with
    | nil => rfl
    | cons d ds => exact ih

/-- Reversing and mapping twice restores the occurrence list. -/
private theorem map_reverse_involutive {n : Nat} (q : List (Edge n)) :
    (((((q.map fun e =>
      ({ source := e.target, target := e.source, weight := -e.weight } : Edge n)).reverse).map
      fun e =>
      ({ source := e.target, target := e.source, weight := -e.weight } :
        Edge n)).reverse)) = q := by
  induction q with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨s, t, w⟩ := e
    have hrev1 : ∀ y : Edge n, [y].reverse = [y] := fun y => rfl
    simp only [List.map_cons, List.reverse_cons, List.map_append,
      List.reverse_append, List.map_nil, hrev1, ih]
    have hff : ({ source := s, target := t, weight := - -w } : Edge n) = ⟨s, t, w⟩ := by
      simp only [neg_neg]
    rw [hff]
    rfl

/-- Negation preserves the weight-forgetting graph. (`C2`, private) -/
private theorem negEdges_toDirectedAdjacency {n : Nat} (edges : List (Edge n)) :
    toDirectedAdjacency (negEdges edges) = toDirectedAdjacency edges := by
  unfold negEdges toDirectedAdjacency
  congr 1
  funext s
  simp only [List.filter_map, List.map_map]
  rfl

/-- Weighted paths transfer across negation with negated total weight. (`C2`, private) -/
private theorem isWeightedPath_negEdges_iff {n : Nat} {edges : List (Edge n)}
    {a b : Fin n} {q : List (Edge n)} :
    IsWeightedPath (negEdges edges) a b q ↔
      ∃ p, IsWeightedPath edges a b p ∧
        q = p.map (fun e => { e with weight := -e.weight }) ∧
        pathWeight q = -pathWeight p := by
  constructor
  · intro h
    obtain ⟨hmem, hchain, hends⟩ := h
    unfold negEdges at hmem
    refine ⟨q.map fun e => ({ e with weight := -e.weight } : Edge n), ?_, ?_, ?_⟩
    · unfold IsWeightedPath
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        obtain ⟨x, hxq, rfl⟩ := List.mem_map.mp hy
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp (hmem x hxq)
        simpa [negEdges_involutive] using he'
      · exact (isChain_neg_map q).mpr hchain
      · cases q with
        | nil =>
          simpa using hends
        | cons first rest =>
          obtain ⟨hsrc, htgt⟩ := hends
          refine ⟨?_, ?_⟩
          · exact hsrc
          · change ((((first :: rest).map fun e =>
                ({ e with weight := -e.weight } : Edge n)).getLast?).map
                Edge.target) = some b
            rw [getLast?_map_neg_target]
            exact htgt
    · exact (negEdges_map_involutive q).symm
    · conv_lhs => rw [(negEdges_map_involutive q).symm]
      exact pathWeight_map_neg _
  · rintro ⟨p, hp, hq, hw⟩
    subst hq
    unfold IsWeightedPath at hp ⊢
    obtain ⟨hmem, hchain, hends⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · unfold negEdges
      intro x hx
      obtain ⟨e, hep, rfl⟩ := List.mem_map.mp hx
      exact List.mem_map.mpr ⟨e, hmem e hep, rfl⟩
    · exact (isChain_neg_map p).mpr hchain
    · cases p with
      | nil =>
        simpa using hends
      | cons first rest =>
        obtain ⟨hsrc, htgt⟩ := hends
        refine ⟨?_, ?_⟩
        · exact hsrc
        · change ((((first :: rest).map fun e =>
              ({ e with weight := -e.weight } : Edge n)).getLast?).map
              Edge.target) = some b
          rw [getLast?_map_neg_target]
          exact htgt

/-- The reversed negated list has the reversed edge relation. (`C2`, private) -/
private theorem revNegEdges_edge_iff {n : Nat} {edges : List (Edge n)}
    {u v : Fin n} :
    (toDirectedAdjacency (revNegEdges edges)).Edge u v ↔
      (toDirectedAdjacency edges).Edge v u := by
  simp only [edge_toDirectedAdjacency_iff]
  constructor
  · rintro ⟨e, hem, hsrc, htgt⟩
    unfold revNegEdges at hem
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hem
    exact ⟨e', he', htgt, hsrc⟩
  · rintro ⟨e', he', hsrc, htgt⟩
    unfold revNegEdges
    refine ⟨{ source := e'.target, target := e'.source, weight := -e'.weight },
      List.mem_map.mpr ⟨e', he', rfl⟩, htgt, hsrc⟩

/-- Weighted paths transfer across reversal with negated total weight. (`C2`, private) -/
private theorem isWeightedPath_revNegEdges_iff {n : Nat} {edges : List (Edge n)}
    {a b : Fin n} {q : List (Edge n)} :
    IsWeightedPath (revNegEdges edges) b a q ↔
      ∃ p, IsWeightedPath edges a b p ∧
        q = (p.map fun e =>
            { source := e.target, target := e.source, weight := -e.weight }).reverse ∧
        pathWeight q = -pathWeight p := by
  constructor
  · intro h
    obtain ⟨hmem, hchain, hends⟩ := h
    unfold revNegEdges at hmem
    refine ⟨((q.map fun e =>
      ({ source := e.target, target := e.source, weight := -e.weight } : Edge n)).reverse),
      ?_, ?_, ?_⟩
    · unfold IsWeightedPath
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        rw [List.mem_reverse] at hy
        obtain ⟨x, hxq, rfl⟩ := List.mem_map.mp hy
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp (hmem x hxq)
        simpa [revNegEdges_involutive] using he'
      · exact List.isChain_reverse.mpr ((isChain_map_revneg q).mpr hchain)
      · cases q with
        | nil =>
          simpa using hends.symm
        | cons first rest =>
          obtain ⟨hsrc, htgt⟩ := hends
          have hne : (((first :: rest).map fun e =>
              ({ source := e.target, target := e.source, weight := -e.weight } :
                Edge n)).reverse) ≠ [] := by
            simp only [List.map_cons, List.reverse_cons]
            cases hL : ((rest.map fun e =>
              ({ source := e.target, target := e.source, weight := -e.weight } :
                Edge n)).reverse) with
            | nil => simp
            | cons y ys => simp
          cases hp : (((first :: rest).map fun e =>
            ({ source := e.target, target := e.source, weight := -e.weight } :
              Edge n)).reverse) with
          | nil => exact absurd hp hne
          | cons gfirst grest =>
            refine ⟨?_, ?_⟩
            · have hhead : ((((first :: rest).map fun e =>
                ({ source := e.target, target := e.source, weight := -e.weight } :
                  Edge n)).reverse).head?) =
                (((first :: rest).getLast?).map fun e =>
                ({ source := e.target, target := e.source, weight := -e.weight } :
                  Edge n)) := by
                rw [List.head?_reverse, List.getLast?_map]
              rw [hp] at hhead
              cases hq : (first :: rest).getLast? with
              | none =>
                rw [hq] at htgt
                exact absurd htgt (by simp)
              | some x =>
                rw [hq] at hhead htgt
                have hx : x.target = a := Option.some_inj.mp htgt
                have heq := Option.some_inj.mp hhead
                rw [heq]
                exact hx
            · have hlast : ((((first :: rest).map fun e =>
                ({ source := e.target, target := e.source, weight := -e.weight } :
                  Edge n)).reverse).getLast?) =
                (((first :: rest).head?).map fun e =>
                ({ source := e.target, target := e.source, weight := -e.weight } :
                  Edge n)) := by
                rw [List.getLast?_reverse, List.head?_map]
              rw [hp] at hlast
              rw [hlast]
              change some (first.source) = some b
              rw [hsrc]
    · exact (map_reverse_involutive q).symm
    · conv_lhs => rw [(map_reverse_involutive q).symm]
      exact pathWeight_reverse_map _
  · rintro ⟨p, hp, hq, hw⟩
    subst hq
    unfold IsWeightedPath at hp ⊢
    obtain ⟨hmem, hchain, hends⟩ := hp
    refine ⟨?_, ?_, ?_⟩
    · unfold revNegEdges
      intro y hy
      rw [List.mem_reverse] at hy
      obtain ⟨x, hxp, rfl⟩ := List.mem_map.mp hy
      exact List.mem_map.mpr ⟨x, hmem x hxp, rfl⟩
    · exact List.isChain_reverse.mpr ((isChain_map_revneg p).mpr hchain)
    · cases p with
      | nil =>
        simpa using hends.symm
      | cons first rest =>
        obtain ⟨hsrc, htgt⟩ := hends
        have hne : (((first :: rest).map fun e =>
            ({ source := e.target, target := e.source, weight := -e.weight } :
              Edge n)).reverse) ≠ [] := by
          simp only [List.map_cons, List.reverse_cons]
          cases hL : ((rest.map fun e =>
            ({ source := e.target, target := e.source, weight := -e.weight } :
              Edge n)).reverse) with
          | nil => simp
          | cons y ys => simp
        cases hp : (((first :: rest).map fun e =>
          ({ source := e.target, target := e.source, weight := -e.weight } :
            Edge n)).reverse) with
        | nil => exact absurd hp hne
        | cons gfirst grest =>
          refine ⟨?_, ?_⟩
          · have hhead : ((((first :: rest).map fun e =>
              ({ source := e.target, target := e.source, weight := -e.weight } :
                Edge n)).reverse).head?) =
              (((first :: rest).getLast?).map fun e =>
              ({ source := e.target, target := e.source, weight := -e.weight } :
                Edge n)) := by
              rw [List.head?_reverse, List.getLast?_map]
            rw [hp] at hhead
            cases hq : (first :: rest).getLast? with
            | none =>
              rw [hq] at htgt
              exact absurd htgt (by simp)
            | some x =>
              rw [hq] at hhead htgt
              have hx : x.target = b := Option.some_inj.mp htgt
              have heq := Option.some_inj.mp hhead
              rw [heq]
              exact hx
          · have hlast : ((((first :: rest).map fun e =>
              ({ source := e.target, target := e.source, weight := -e.weight } :
                Edge n)).reverse).getLast?) =
              (((first :: rest).head?).map fun e =>
              ({ source := e.target, target := e.source, weight := -e.weight } :
                Edge n)) := by
              rw [List.getLast?_reverse, List.head?_map]
            rw [hp] at hlast
            rw [hlast]
            change some (first.source) = some a
            rw [hsrc]

/-- Acyclicity transfers to the reversed negated list. (`C2`, private) -/
private theorem isAcyclic_revNegEdges {n : Nat} {edges : List (Edge n)}
    (hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency edges)) :
    TopologicalSort.IsAcyclic (toDirectedAdjacency (revNegEdges edges)) := by
  intro hcon
  obtain ⟨cycle, hcyc⟩ := hcon
  obtain ⟨hne, hnodup, hchain, hclose, hmem⟩ :=
    (TopologicalSort.directedCycleIn_iff _ _ _).mp hcyc
  have hrev_ne : cycle.reverse ≠ [] := by
    cases cycle with
    | nil => exact absurd rfl hne
    | cons c cs =>
      simp only [List.reverse_cons]
      cases hL : cs.reverse with
      | nil =>
        change ([c] : List (Fin n)) ≠ []
        simp
      | cons y ys =>
        change (y :: (ys ++ [c])) ≠ []
        simp
  have hnodup' : cycle.reverse.Nodup := List.nodup_reverse.mpr hnodup
  have hchain' : cycle.reverse.IsChain (toDirectedAdjacency edges).Edge := by
    have hconv : ∀ c : List (Fin n),
        c.IsChain (toDirectedAdjacency (revNegEdges edges)).Edge →
        c.IsChain (fun a b => (toDirectedAdjacency edges).Edge b a) := by
      intro c
      induction c with
      | nil => intro; simp
      | cons e es ih =>
        intro h
        cases es with
        | nil => simp
        | cons f fs =>
          simp only [List.isChain_cons_cons] at h ⊢
          obtain ⟨hrel, hrest⟩ := h
          exact ⟨(revNegEdges_edge_iff).mp hrel, ih hrest⟩
    exact List.isChain_reverse.mpr (hconv cycle hchain)
  have hclose' : (toDirectedAdjacency edges).Edge
      (cycle.reverse.getLast hrev_ne) (cycle.reverse.head hrev_ne) := by
    have hgl : cycle.reverse.getLast hrev_ne = cycle.head hne := by
      have h1 : (cycle.reverse).getLast? = some (cycle.reverse.getLast hrev_ne) :=
        (List.getLast_eq_iff_getLast?_eq_some hrev_ne).mp rfl
      have h4 : cycle.head? = some (cycle.head hne) :=
        (List.head_eq_iff_head?_eq_some hne).mp rfl
      rw [List.getLast?_reverse, h4] at h1
      exact (Option.some_inj.mp h1).symm
    have hhd : cycle.reverse.head hrev_ne = cycle.getLast hne := by
      have h1 : (cycle.reverse).head? = some (cycle.reverse.head hrev_ne) :=
        (List.head_eq_iff_head?_eq_some hrev_ne).mp rfl
      have h4 : cycle.getLast? = some (cycle.getLast hne) :=
        (List.getLast_eq_iff_getLast?_eq_some hne).mp rfl
      rw [List.head?_reverse, h4] at h1
      exact (Option.some_inj.mp h1).symm
    rw [hgl, hhd]
    exact (revNegEdges_edge_iff).mp hclose
  have hmem' : ∀ v ∈ cycle.reverse, v ∈ (toDirectedAdjacency edges).vertices := by
    intro v hv
    rw [List.mem_reverse] at hv
    exact hmem v hv
  apply hacyc
  refine ⟨cycle.reverse, ?_⟩
  rw [TopologicalSort.directedCycleIn_iff]
  exact ⟨hrev_ne, hnodup', hchain', hclose', hmem'⟩

/-- `Option.map Neg.neg` hits `some` exactly on negated values. -/
private theorem map_neg_some_iff (o : Option Int) (a : Int) :
    o.map Neg.neg = some a ↔ o = some (-a) := by
  cases o with
  | none => simp
  | some d =>
    simp only [Option.map_some]
    simp only [Option.some.injEq]
    constructor <;> intro h <;> omega

/-- `Option.map Neg.neg` preserves `none`. -/
private theorem map_neg_none_iff (o : Option Int) :
    o.map Neg.neg = none ↔ o = none := by
  cases o <;> simp

/-- Reachability in the reversed negated graph flips endpoints. -/
private theorem reachable_revNegEdges_iff {n : Nat} (edges : List (Edge n))
    (t v : Fin n) :
    (toDirectedAdjacency (revNegEdges edges)).Reachable t v ↔
      (toDirectedAdjacency edges).Reachable v t := by
  simp only [reachable_iff_exists_isWeightedPath]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨p, hp, _, _⟩ := (isWeightedPath_revNegEdges_iff).mp hq
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    refine ⟨(p.map fun e =>
      { source := e.target, target := e.source, weight := -e.weight }).reverse, ?_⟩
    exact (isWeightedPath_revNegEdges_iff).mpr ⟨p, hp, rfl, pathWeight_reverse_map p⟩

/-- The forward run on negated edges succeeds on acyclic input. (`C3`) -/
public theorem forward_run_ok {n : Nat} (edges : List (Edge n)) (s : Fin n)
    (hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency edges)) :
    ∃ result,
      (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok result := by
  have hacyc' : TopologicalSort.IsAcyclic (toDirectedAdjacency (negEdges edges)) := by
    rw [negEdges_toDirectedAdjacency]
    exact hacyc
  exact (DAGShortestPaths.dagShortestPaths_returns_iff_acyclic _ _).mpr hacyc'

/-- Earliest starts are realized longest source-to-vertex durations. (`C3`) -/
public theorem earliestStart_spec {n : Nat} {edges : List (Edge n)} {s : Fin n}
    {result : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok result)
    (v : Fin n) (a : Int) :
    earliestStart result v = some a ↔
      ((∃ p, IsWeightedPath edges s v p ∧ pathWeight p = a) ∧
        ∀ p, IsWeightedPath edges s v p → pathWeight p ≤ a) := by
  have hmap : earliestStart result v = some a ↔ result.distance.get v = some (-a) := by
    unfold earliestStart
    exact map_neg_some_iff _ _
  rw [hmap]
  constructor
  · intro hd
    obtain ⟨hex, hmin⟩ :=
      DAGShortestPaths.dagShortestPaths_distance_spec _ _ _ hr _ _ hd
    obtain ⟨q, hq, hwq⟩ := hex
    obtain ⟨p, hp, _, hweight⟩ := (isWeightedPath_negEdges_iff).mp hq
    have hpa : pathWeight p = a := by omega
    refine ⟨⟨p, hp, hpa⟩, ?_⟩
    intro p' hp'
    have hq' : IsWeightedPath (negEdges edges) s v
        (p'.map fun e => { e with weight := -e.weight }) :=
      (isWeightedPath_negEdges_iff).mpr ⟨p', hp', rfl, pathWeight_map_neg p'⟩
    have hle := hmin _ hq'
    rw [pathWeight_map_neg p'] at hle
    omega
  · rintro ⟨⟨p, hp, hpa⟩, hmax⟩
    cases hdist : result.distance.get v with
    | none =>
      exfalso
      have hne :=
        (DAGShortestPaths.dagShortestPaths_distance_eq_none_iff _ _ _ hr _).mp hdist
      have hq : IsWeightedPath (negEdges edges) s v
          (p.map fun e => { e with weight := -e.weight }) :=
        (isWeightedPath_negEdges_iff).mpr ⟨p, hp, rfl, pathWeight_map_neg p⟩
      have hreach : (toDirectedAdjacency (negEdges edges)).Reachable s v :=
        reachable_iff_exists_isWeightedPath.mpr ⟨_, hq⟩
      exact hne hreach
    | some val =>
      have hval : val = -a := by
        obtain ⟨hex, hmin⟩ :=
          DAGShortestPaths.dagShortestPaths_distance_spec _ _ _ hr _ _ hdist
        obtain ⟨q, hq, hwq⟩ := hex
        obtain ⟨p0, hp0, _, hweight0⟩ := (isWeightedPath_negEdges_iff).mp hq
        have hq' : IsWeightedPath (negEdges edges) s v
            (p.map fun e => { e with weight := -e.weight }) :=
          (isWeightedPath_negEdges_iff).mpr ⟨p, hp, rfl, pathWeight_map_neg p⟩
        have hle := hmin _ hq'
        rw [pathWeight_map_neg p] at hle
        have hmax0 := hmax p0 hp0
        omega
      rw [hval]

/-- Earliest start is absent exactly off the forward reachable set. (`C3`) -/
public theorem earliestStart_eq_none_iff {n : Nat} {edges : List (Edge n)}
    {s : Fin n} {result : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok result)
    (v : Fin n) :
    earliestStart result v = none ↔
      ¬(toDirectedAdjacency edges).Reachable s v := by
  have hnone : earliestStart result v = none ↔ result.distance.get v = none := by
    unfold earliestStart
    exact map_neg_none_iff _
  rw [hnone]
  rw [DAGShortestPaths.dagShortestPaths_distance_eq_none_iff _ _ _ hr _]
  rw [negEdges_toDirectedAdjacency]

/-- The reversed run from the sink succeeds on acyclic input. (`C4`) -/
public theorem reversed_run_ok {n : Nat} (edges : List (Edge n)) (t : Fin n)
    (hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency edges)) :
    ∃ result,
      (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok result := by
  have hacyc' : TopologicalSort.IsAcyclic (toDirectedAdjacency (revNegEdges edges)) :=
    isAcyclic_revNegEdges hacyc
  exact (DAGShortestPaths.dagShortestPaths_returns_iff_acyclic _ _).mpr hacyc'

/-- Longest times to sink are realized longest vertex-to-sink durations. (`C4`) -/
public theorem longestToSink_spec {n : Nat} {edges : List (Edge n)} {t : Fin n}
    {result : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok result)
    (v : Fin n) (b : Int) :
    longestToSink result v = some b ↔
      ((∃ p, IsWeightedPath edges v t p ∧ pathWeight p = b) ∧
        ∀ p, IsWeightedPath edges v t p → pathWeight p ≤ b) := by
  have hmap : longestToSink result v = some b ↔ result.distance.get v = some (-b) := by
    unfold longestToSink
    exact map_neg_some_iff _ _
  rw [hmap]
  constructor
  · intro hd
    obtain ⟨hex, hmin⟩ :=
      DAGShortestPaths.dagShortestPaths_distance_spec _ _ _ hr _ _ hd
    obtain ⟨q, hq, hwq⟩ := hex
    obtain ⟨p, hp, _, hweight⟩ := (isWeightedPath_revNegEdges_iff).mp hq
    have hpb : pathWeight p = b := by omega
    refine ⟨⟨p, hp, hpb⟩, ?_⟩
    intro p' hp'
    have hq' : IsWeightedPath (revNegEdges edges) t v
        ((p'.map fun e =>
          { source := e.target, target := e.source, weight := -e.weight }).reverse) :=
      (isWeightedPath_revNegEdges_iff).mpr ⟨p', hp', rfl, pathWeight_reverse_map p'⟩
    have hle := hmin _ hq'
    rw [pathWeight_reverse_map p'] at hle
    omega
  · rintro ⟨⟨p, hp, hpb⟩, hmax⟩
    cases hdist : result.distance.get v with
    | none =>
      exfalso
      have hne :=
        (DAGShortestPaths.dagShortestPaths_distance_eq_none_iff _ _ _ hr _).mp hdist
      have hq : IsWeightedPath (revNegEdges edges) t v
          ((p.map fun e =>
            { source := e.target, target := e.source, weight := -e.weight }).reverse) :=
        (isWeightedPath_revNegEdges_iff).mpr ⟨p, hp, rfl, pathWeight_reverse_map p⟩
      have hreach : (toDirectedAdjacency (revNegEdges edges)).Reachable t v :=
        reachable_iff_exists_isWeightedPath.mpr ⟨_, hq⟩
      exact hne hreach
    | some val =>
      have hval : val = -b := by
        obtain ⟨hex, hmin⟩ :=
          DAGShortestPaths.dagShortestPaths_distance_spec _ _ _ hr _ _ hdist
        obtain ⟨q, hq, hwq⟩ := hex
        obtain ⟨p0, hp0, _, hweight0⟩ := (isWeightedPath_revNegEdges_iff).mp hq
        have hq' : IsWeightedPath (revNegEdges edges) t v
            ((p.map fun e =>
              { source := e.target, target := e.source, weight := -e.weight }).reverse) :=
          (isWeightedPath_revNegEdges_iff).mpr ⟨p, hp, rfl, pathWeight_reverse_map p⟩
        have hle := hmin _ hq'
        rw [pathWeight_reverse_map p] at hle
        have hmax0 := hmax p0 hp0
        omega
      rw [hval]

/-- Longest time to sink is absent exactly off the backward reachable set. (`C4`) -/
public theorem longestToSink_eq_none_iff {n : Nat} {edges : List (Edge n)}
    {t : Fin n} {result : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok result)
    (v : Fin n) :
    longestToSink result v = none ↔
      ¬(toDirectedAdjacency edges).Reachable v t := by
  have hnone : longestToSink result v = none ↔ result.distance.get v = none := by
    unfold longestToSink
    exact map_neg_none_iff _
  rw [hnone]
  rw [DAGShortestPaths.dagShortestPaths_distance_eq_none_iff _ _ _ hr _]
  rw [reachable_revNegEdges_iff]

/-- Makespan: when both runs succeed and `t` is reachable from `s`, the makespan is defined, equals
the longest time to sink at `s`, and is the attained maximum source-to-sink path weight. (`C5`) -/
public theorem makespan_exists {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (hst : (toDirectedAdjacency edges).Reachable s t) :
    ∃ T, makespan forward t = some T ∧ longestToSink reverse s = some T ∧
      (∃ p, IsWeightedPath edges s t p ∧ pathWeight p = T) ∧
      ∀ p, IsWeightedPath edges s t p → pathWeight p ≤ T := by
  cases hET : earliestStart forward t with
  | none =>
    exfalso
    exact ((earliestStart_eq_none_iff hf t).mp hET) hst
  | some T =>
    obtain ⟨hex, hmax⟩ := (earliestStart_spec hf t T).mp hET
    have hLT : longestToSink reverse s = some T :=
      (longestToSink_spec hr s T).mpr ⟨hex, hmax⟩
    have hM : makespan forward t = some T := hET
    exact ⟨T, hM, hLT, hex, hmax⟩

/-- Without source-to-sink reachability the sink earliest start is absent. (`C5`) -/
public theorem earliestStart_sink_none_of_unreachable {n : Nat}
    {edges : List (Edge n)} {s t : Fin n} {forward : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hst : ¬(toDirectedAdjacency edges).Reachable s t) :
    earliestStart forward t = none := by
  exact (earliestStart_eq_none_iff hf t).mpr hst

/-- Without source-to-sink reachability the source longest-to-sink is absent. (`C5`) -/
public theorem longestToSink_source_none_of_unreachable {n : Nat}
    {edges : List (Edge n)} {s t : Fin n} {reverse : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (hst : ¬(toDirectedAdjacency edges).Reachable s t) :
    longestToSink reverse s = none := by
  exact (longestToSink_eq_none_iff hr s).mpr hst

/-- Latest start is defined exactly when makespan and longest-to-sink are. (`C6`) -/
public theorem latestStart_some_iff (T lt : Option Int) (l : Int) :
    latestStart T lt = some l ↔
      ∃ Tv b, T = some Tv ∧ lt = some b ∧ l = Tv - b := by
  constructor
  · intro h
    cases T with
    | none => cases lt <;> simp [latestStart] at h
    | some Tv =>
      cases lt with
      | none => simp [latestStart] at h
      | some b =>
        simp [latestStart] at h
        exact ⟨Tv, b, rfl, rfl, h.symm⟩
  · rintro ⟨Tv, b, rfl, rfl, rfl⟩
    simp [latestStart]

/-- Latest start is absent exactly when a prerequisite is absent. (`C6`) -/
public theorem latestStart_eq_none_iff (T lt : Option Int) :
    latestStart T lt = none ↔ T = none ∨ lt = none := by
  cases T <;> cases lt <;> simp [latestStart]

/-- Slack is defined exactly when earliest and latest starts are. (`C6`) -/
public theorem slack_some_iff (es ls : Option Int) (σ : Int) :
    slack es ls = some σ ↔ ∃ a l, es = some a ∧ ls = some l ∧ σ = l - a := by
  constructor
  · intro h
    cases es with
    | none => cases ls <;> simp [slack] at h
    | some a =>
      cases ls with
      | none => simp [slack] at h
      | some l =>
        simp [slack] at h
        exact ⟨a, l, rfl, rfl, h.symm⟩
  · rintro ⟨a, l, rfl, rfl, rfl⟩
    simp [slack]

/-- Slack is absent exactly when a prerequisite is absent. (`C6`) -/
public theorem slack_eq_none_iff (es ls : Option Int) :
    slack es ls = none ↔ es = none ∨ ls = none := by
  cases es <;> cases ls <;> simp [slack]

/-- Float is defined exactly when both endpoint prerequisites are. (`C6`) -/
public theorem activityFloat_some_iff (esSrc lsTgt : Option Int) (w φ : Int) :
    activityFloat esSrc lsTgt w = some φ ↔
      ∃ a l, esSrc = some a ∧ lsTgt = some l ∧ φ = l - a - w := by
  constructor
  · intro h
    cases esSrc with
    | none => cases lsTgt <;> simp [activityFloat] at h
    | some a =>
      cases lsTgt with
      | none => simp [activityFloat] at h
      | some l =>
        simp [activityFloat] at h
        exact ⟨a, l, rfl, rfl, h.symm⟩
  · rintro ⟨a, l, rfl, rfl, rfl⟩
    simp [activityFloat]

/-- Float is absent exactly when a prerequisite is absent. (`C6`) -/
public theorem activityFloat_eq_none_iff (esSrc lsTgt : Option Int) (w : Int) :
    activityFloat esSrc lsTgt w = none ↔ esSrc = none ∨ lsTgt = none := by
  cases esSrc <;> cases lsTgt <;> simp [activityFloat]

/-- Earliest start is defined exactly on forward-reachable vertices. -/
private theorem earliestStart_defined_iff {n : Nat} {edges : List (Edge n)}
    {s : Fin n} {result : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok result)
    (v : Fin n) :
    (∃ a, earliestStart result v = some a) ↔
      (toDirectedAdjacency edges).Reachable s v := by
  constructor
  · rintro ⟨a, ha⟩
    by_contra hnr
    have hnone := (earliestStart_eq_none_iff hf v).mpr hnr
    rw [ha] at hnone
    simp at hnone
  · intro hreach
    cases hES : earliestStart result v with
    | none =>
      exfalso
      exact ((earliestStart_eq_none_iff hf v).mp hES) hreach
    | some a =>
      rw [←hES]
      exact ⟨a, hES⟩

/-- Longest time to sink is defined exactly on backward-reachable vertices. -/
private theorem longestToSink_defined_iff {n : Nat} {edges : List (Edge n)}
    {t : Fin n} {result : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok result)
    (v : Fin n) :
    (∃ b, longestToSink result v = some b) ↔
      (toDirectedAdjacency edges).Reachable v t := by
  constructor
  · rintro ⟨b, hb⟩
    by_contra hnr
    have hnone := (longestToSink_eq_none_iff hr v).mpr hnr
    rw [hb] at hnone
    simp at hnone
  · intro hreach
    cases hLT : longestToSink result v with
    | none =>
      exfalso
      exact ((longestToSink_eq_none_iff hr v).mp hLT) hreach
    | some b =>
      rw [←hLT]
      exact ⟨b, hLT⟩

/-- Reachability composes through an intermediate vertex. -/
private theorem reachable_trans_middle {n : Nat} {edges : List (Edge n)}
    {u v w : Fin n}
    (h1 : (toDirectedAdjacency edges).Reachable u v)
    (h2 : (toDirectedAdjacency edges).Reachable v w) :
    (toDirectedAdjacency edges).Reachable u w := by
  rw [DirectedAdjacency.reachable_iff_exists_walk] at h1 h2 ⊢
  obtain ⟨n1, w1⟩ := h1
  obtain ⟨n2, w2⟩ := h2
  exact ⟨n1 + n2, DirectedAdjacency.Walk.append w1 w2⟩

/-- An occurrence gives reachability from its source to its target. -/
private theorem reachable_of_mem_edge {n : Nat} {edges : List (Edge n)}
    {e : Edge n} (hem : e ∈ edges) :
    (toDirectedAdjacency edges).Reachable e.source e.target := by
  have hEdge : (toDirectedAdjacency edges).Edge e.source e.target :=
    edge_toDirectedAdjacency_iff.mpr ⟨e, hem, rfl, rfl⟩
  have hRT : Relation.ReflTransGen (toDirectedAdjacency edges).Edge e.source
      e.target :=
    Relation.RelatesInSteps.reflTransGen (Relation.RelatesInSteps.single hEdge)
  exact hRT

/-- Slack is defined exactly on vertices of some source-to-sink path. (`C6`) -/
public theorem slackAt_defined_iff {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (v : Fin n) :
    (∃ σ, slackAt (makespan forward t) forward reverse v = some σ) ↔
      (toDirectedAdjacency edges).Reachable s v ∧
        (toDirectedAdjacency edges).Reachable v t := by
  constructor
  · rintro ⟨σ, hσ⟩
    unfold slackAt latestStartAt at hσ
    obtain ⟨a, l, ha, hl, _⟩ := (slack_some_iff _ _ σ).mp hσ
    obtain ⟨_, b, _, hb, _⟩ := (latestStart_some_iff _ _ l).mp hl
    exact ⟨(earliestStart_defined_iff hf v).mp ⟨a, ha⟩,
      (longestToSink_defined_iff hr v).mp ⟨b, hb⟩⟩
  · rintro ⟨hsv, hvt⟩
    have hst : (toDirectedAdjacency edges).Reachable s t :=
      reachable_trans_middle hsv hvt
    obtain ⟨a, ha⟩ := (earliestStart_defined_iff hf v).mpr hsv
    obtain ⟨b, hb⟩ := (longestToSink_defined_iff hr v).mpr hvt
    obtain ⟨Tv, hTv⟩ := (earliestStart_defined_iff hf t).mpr hst
    have hT : makespan forward t = some Tv := hTv
    have hl : latestStartAt (makespan forward t) reverse v = some (Tv - b) := by
      unfold latestStartAt
      rw [hT, hb]
      simp [latestStart]
    refine ⟨(Tv - b) - a, ?_⟩
    unfold slackAt
    rw [ha, hl]
    simp [slack]

/-- Float is defined exactly on occurrences with both endpoint prerequisites. (`C6`) -/
public theorem floatAt_defined_iff {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (e : Edge n) (hem : e ∈ edges) :
    (∃ φ, floatAt (makespan forward t) forward reverse e = some φ) ↔
      (toDirectedAdjacency edges).Reachable s e.source ∧
        (toDirectedAdjacency edges).Reachable e.target t := by
  constructor
  · rintro ⟨φ, hφ⟩
    unfold floatAt latestStartAt at hφ
    obtain ⟨a, l, ha, hl, _⟩ := (activityFloat_some_iff _ _ _ φ).mp hφ
    obtain ⟨_, b, _, hb, _⟩ := (latestStart_some_iff _ _ l).mp hl
    exact ⟨(earliestStart_defined_iff hf e.source).mp ⟨a, ha⟩,
      (longestToSink_defined_iff hr e.target).mp ⟨b, hb⟩⟩
  · rintro ⟨hsv, hvt⟩
    have hedge : (toDirectedAdjacency edges).Reachable e.source e.target :=
      reachable_of_mem_edge hem
    have hst : (toDirectedAdjacency edges).Reachable s t :=
      reachable_trans_middle (reachable_trans_middle hsv hedge) hvt
    obtain ⟨a, ha⟩ := (earliestStart_defined_iff hf e.source).mpr hsv
    obtain ⟨b, hb⟩ := (longestToSink_defined_iff hr e.target).mpr hvt
    obtain ⟨Tv, hTv⟩ := (earliestStart_defined_iff hf t).mpr hst
    have hT : makespan forward t = some Tv := hTv
    have hl : latestStartAt (makespan forward t) reverse e.target
        = some (Tv - b) := by
      unfold latestStartAt
      rw [hT, hb]
      simp [latestStart]
    refine ⟨(Tv - b) - a - e.weight, ?_⟩
    unfold floatAt
    rw [ha, hl]
    simp [activityFloat]

/-- Coverage holds exactly when no occurrence is orphaned. (`C6`) -/
public theorem coverage_iff_no_orphan {n : Nat} {edges : List (Edge n)}
    {s t : Fin n} {forward reverse : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse) :
    IsCovered edges s t ↔ ∀ e ∈ edges, ¬isOrphan forward reverse e := by
  constructor
  · intro hcover
    unfold IsCovered at hcover
    intro e hem horph
    unfold isOrphan at horph
    obtain hnone | hnone := horph
    · exact ((earliestStart_eq_none_iff hf e.source).mp hnone) ((hcover e hem).1)
    · exact ((longestToSink_eq_none_iff hr e.target).mp hnone) ((hcover e hem).2)
  · intro hno
    unfold IsCovered
    intro e hem
    have hne : ¬isOrphan forward reverse e := hno e hem
    unfold isOrphan at hne
    constructor
    · by_contra hnr
      exact hne (Or.inl ((earliestStart_eq_none_iff hf e.source).mpr hnr))
    · by_contra hnr
      exact hne (Or.inr ((longestToSink_eq_none_iff hr e.target).mpr hnr))

/-- Path weight distributes over append. -/
private theorem pathWeight_append {n : Nat} (p1 p2 : List (Edge n)) :
    pathWeight (p1 ++ p2) = pathWeight p1 + pathWeight p2 := by
  simp [pathWeight]

/-- Singleton path weight is the edge weight. -/
private theorem pathWeight_singleton {n : Nat} (e : Edge n) :
    pathWeight [e] = e.weight := by
  simp [pathWeight]

/-- Empty path is a weighted path from a vertex to itself. -/
private theorem isWeightedPath_nil {n : Nat} (edges : List (Edge n)) (s : Fin n) :
    IsWeightedPath edges s s [] := by
  simp [IsWeightedPath]

/-- A single input edge is a weighted path between its endpoints. -/
private theorem isWeightedPath_singleton {n : Nat} {edges : List (Edge n)}
    {e : Edge n} (hem : e ∈ edges) :
    IsWeightedPath edges e.source e.target [e] := by
  unfold IsWeightedPath
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rw [hy]
    exact hem
  · simp
  · exact ⟨rfl, rfl⟩

/-- Prepending an input edge to a weighted path preserves validity. -/
private theorem isWeightedPath_cons {n : Nat} {edges : List (Edge n)}
    {s t : Fin n} {f : Edge n} {r : List (Edge n)}
    (hem : f ∈ edges) (hsrc : f.source = s)
    (hrest : IsWeightedPath edges f.target t r) :
    IsWeightedPath edges s t (f :: r) := by
  cases r with
  | nil =>
    unfold IsWeightedPath at hrest ⊢
    obtain ⟨_, _, hends⟩ := hrest
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rw [hy]
      exact hem
    · simp
    · refine ⟨hsrc, ?_⟩
      have hlast : (([f].getLast?).map Edge.target) = some f.target := rfl
      rw [hlast]
      rw [hends]
  | cons g gs =>
    unfold IsWeightedPath at hrest ⊢
    obtain ⟨hmem, hchain, hends⟩ := hrest
    obtain ⟨hgsrc, htgt⟩ := hends
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      simp only [List.mem_cons] at hy
      cases hy with
      | inl heq =>
        rw [heq]
        exact hem
      | inr hmem2 =>
        exact hmem y (List.mem_cons.mpr hmem2)
    · simp only [List.isChain_cons_cons]
      exact ⟨hgsrc.symm, hchain⟩
    · exact ⟨hsrc, htgt⟩

/-- Concatenating weighted paths at a shared vertex preserves validity. -/
private theorem isWeightedPath_append {n : Nat} {edges : List (Edge n)}
    {s v t : Fin n} {p1 p2 : List (Edge n)}
    (h1 : IsWeightedPath edges s v p1)
    (h2 : IsWeightedPath edges v t p2) :
    IsWeightedPath edges s t (p1 ++ p2) := by
  induction p1 generalizing s with
  | nil =>
    unfold IsWeightedPath at h1
    obtain ⟨_, _, hends⟩ := h1
    subst hends
    simpa using h2
  | cons f r ih =>
    have htail : IsWeightedPath edges f.target v r := isWeightedPath_tail h1
    have hmem : f ∈ edges := by
      unfold IsWeightedPath at h1
      exact h1.1 f (by simp)
    have hsrc : f.source = s := by
      unfold IsWeightedPath at h1
      exact h1.2.2.1
    have hihr : IsWeightedPath edges f.target t (r ++ p2) := ih htail
    have hcons : IsWeightedPath edges s t (f :: (r ++ p2)) :=
      isWeightedPath_cons hmem hsrc hihr
    simpa using hcons

/-- The endpoint of a weighted path appears among its vertices. -/
private theorem mem_pathVertices_of_isWeightedPath {n : Nat} {edges : List (Edge n)}
    {s v : Fin n} {p1 : List (Edge n)}
    (h : IsWeightedPath edges s v p1) : v ∈ pathVertices s p1 := by
  induction p1 generalizing s with
  | nil =>
    unfold IsWeightedPath at h
    obtain ⟨_, _, hends⟩ := h
    subst hends
    simp [pathVertices]
  | cons f r ih =>
    have htail : IsWeightedPath edges f.target v r := isWeightedPath_tail h
    have hihr : v ∈ pathVertices f.target r := ih htail
    unfold pathVertices at hihr ⊢
    simp only [List.map_cons] at ⊢
    exact List.mem_cons.mpr (Or.inr hihr)

/-- Vertices of a prefix persist after appending a suffix. -/
private theorem mem_pathVertices_append_left {n : Nat} (s : Fin n)
    (p1 p2 : List (Edge n)) (v : Fin n)
    (h : v ∈ pathVertices s p1) : v ∈ pathVertices s (p1 ++ p2) := by
  unfold pathVertices at h ⊢
  simp only [List.map_append] at ⊢
  simp only [List.mem_cons] at h ⊢
  cases h with
  | inl heq => exact Or.inl heq
  | inr hmem =>
    exact Or.inr (List.mem_append.mpr (Or.inl hmem))

/-- A vertex on a weighted path splits it into prefix and suffix. -/
private theorem isWeightedPath_split_at_vertex {n : Nat} {edges : List (Edge n)}
    {s t v : Fin n} {p : List (Edge n)}
    (h : IsWeightedPath edges s t p) (hmem : v ∈ pathVertices s p) :
    ∃ p1 p2, p = p1 ++ p2 ∧ IsWeightedPath edges s v p1 ∧
      IsWeightedPath edges v t p2 := by
  induction p generalizing s with
  | nil =>
    unfold IsWeightedPath at h
    obtain ⟨_, _, hends⟩ := h
    subst hends
    unfold pathVertices at hmem
    simp only [List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    exact ⟨[], [], rfl, isWeightedPath_nil _ _, isWeightedPath_nil _ _⟩
  | cons f r ih =>
    have hmem_or : v = s ∨ v ∈ pathVertices f.target r := by
      simpa [pathVertices] using hmem
    by_cases hs : v = s
    · subst hs
      exact ⟨[], f :: r, rfl, isWeightedPath_nil _ _, h⟩
    · have htail : IsWeightedPath edges f.target t r := isWeightedPath_tail h
      have hmem' : v ∈ pathVertices f.target r := by
        obtain heq | hrest := hmem_or
        · exact absurd heq hs
        · exact hrest
      obtain ⟨p1', p2, heq, h1', h2'⟩ := ih htail hmem'
      have hmem_f : f ∈ edges := by
        unfold IsWeightedPath at h
        exact h.1 f (by simp)
      have hsrc : f.source = s := by
        unfold IsWeightedPath at h
        exact h.2.2.1
      have hcons : IsWeightedPath edges s v (f :: p1') :=
        isWeightedPath_cons hmem_f hsrc h1'
      refine ⟨f :: p1', p2, by cases heq; rfl, hcons, h2'⟩

/-- An edge on a weighted path splits it around that occurrence. -/
private theorem isWeightedPath_split_at_edge {n : Nat} {edges : List (Edge n)}
    {s t : Fin n} {p : List (Edge n)} {e : Edge n}
    (h : IsWeightedPath edges s t p) (hmem : e ∈ p) :
    ∃ p1 p2, p = p1 ++ [e] ++ p2 ∧ IsWeightedPath edges s e.source p1 ∧
      IsWeightedPath edges e.target t p2 := by
  induction p generalizing s with
  | nil =>
    simp at hmem
  | cons f r ih =>
    simp only [List.mem_cons] at hmem
    obtain heq | hmem' := hmem
    · have hsrc : f.source = s := by
        unfold IsWeightedPath at h
        exact h.2.2.1
      have htail : IsWeightedPath edges f.target t r := isWeightedPath_tail h
      have hnil : IsWeightedPath edges s e.source [] := by
        rw [heq]
        unfold IsWeightedPath
        simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.IsChain.nil, true_and]
        exact hsrc.symm
      have htail' : IsWeightedPath edges e.target t r := by
        rw [heq]
        exact htail
      refine ⟨[], r, by simp [heq], hnil, htail'⟩
    · have htail : IsWeightedPath edges f.target t r := isWeightedPath_tail h
      obtain ⟨p1', p2, heq2, h1', h2'⟩ := ih htail hmem'
      have hmem_f : f ∈ edges := by
        unfold IsWeightedPath at h
        exact h.1 f (by simp)
      have hsrc : f.source = s := by
        unfold IsWeightedPath at h
        exact h.2.2.1
      have hcons : IsWeightedPath edges s e.source (f :: p1') :=
        isWeightedPath_cons hmem_f hsrc h1'
      refine ⟨f :: p1', p2, by cases heq2; rfl, hcons, h2'⟩

/-- Defined slack is nonnegative and vanishes exactly on longest-path vertices. (`C7`) -/
public theorem slackAt_spec {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n} {T σ : Int}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (hT : makespan forward t = some T)
    (v : Fin n) (hslack : slackAt (some T) forward reverse v = some σ) :
    0 ≤ σ ∧
      (σ = 0 ↔
        ∃ p, IsWeightedPath edges s t p ∧ pathWeight p = T ∧
          v ∈ pathVertices s p) := by
  unfold slackAt latestStartAt at hslack
  obtain ⟨a, l, ha, hl, hσ⟩ := (slack_some_iff _ _ σ).mp hslack
  obtain ⟨Tv, b, hTv, hb, hl_eq⟩ := (latestStart_some_iff _ _ l).mp hl
  simp at hTv
  have hET : earliestStart forward t = some T := hT
  obtain ⟨_, hmaxT⟩ := (earliestStart_spec hf t T).mp hET
  obtain ⟨⟨p1, hp1, hw1⟩, hmax1⟩ := (earliestStart_spec hf v a).mp ha
  obtain ⟨⟨p2, hp2, hw2⟩, hmax2⟩ := (longestToSink_spec hr v b).mp hb
  have happ : IsWeightedPath edges s t (p1 ++ p2) :=
    isWeightedPath_append hp1 hp2
  have hw_app : pathWeight (p1 ++ p2) = a + b := by
    rw [pathWeight_append, hw1, hw2]
  have hle : a + b ≤ T := by
    have h := hmaxT _ happ
    rw [hw_app] at h
    exact h
  have hnonneg : 0 ≤ σ := by omega
  refine ⟨hnonneg, ?_⟩
  constructor
  · intro hzero
    have hab : a + b = T := by omega
    have hmem1 : v ∈ pathVertices s p1 :=
      mem_pathVertices_of_isWeightedPath hp1
    have hmem : v ∈ pathVertices s (p1 ++ p2) :=
      mem_pathVertices_append_left s p1 p2 v hmem1
    refine ⟨p1 ++ p2, happ, by rw [hw_app, hab], hmem⟩
  · rintro ⟨p, hp, hwp, hmem⟩
    obtain ⟨q1, q2, heq, hq1, hq2⟩ :=
      isWeightedPath_split_at_vertex hp hmem
    have hw_split : pathWeight p = pathWeight q1 + pathWeight q2 := by
      rw [heq, pathWeight_append]
    have hle1 := hmax1 _ hq1
    have hle2 := hmax2 _ hq2
    omega

/-- Defined float is nonnegative and vanishes exactly on longest-path arcs. (`C8`) -/
public theorem floatAt_spec {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n} {T φ : Int}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (hT : makespan forward t = some T)
    (e : Edge n) (hem : e ∈ edges)
    (hfloat : floatAt (some T) forward reverse e = some φ) :
    0 ≤ φ ∧
      (φ = 0 ↔
        ∃ p, IsWeightedPath edges s t p ∧ pathWeight p = T ∧ e ∈ p) := by
  unfold floatAt latestStartAt at hfloat
  obtain ⟨a, l, ha, hl, hφ⟩ := (activityFloat_some_iff _ _ _ φ).mp hfloat
  obtain ⟨Tv, b, hTv, hb, hl_eq⟩ := (latestStart_some_iff _ _ l).mp hl
  simp at hTv
  have hET : earliestStart forward t = some T := hT
  obtain ⟨_, hmaxT⟩ := (earliestStart_spec hf t T).mp hET
  obtain ⟨⟨p1, hp1, hw1⟩, hmax1⟩ := (earliestStart_spec hf e.source a).mp ha
  obtain ⟨⟨p2, hp2, hw2⟩, hmax2⟩ := (longestToSink_spec hr e.target b).mp hb
  have hsingle : IsWeightedPath edges e.source e.target [e] :=
    isWeightedPath_singleton hem
  have happ1 : IsWeightedPath edges s e.target (p1 ++ [e]) :=
    isWeightedPath_append hp1 hsingle
  have happ : IsWeightedPath edges s t ((p1 ++ [e]) ++ p2) :=
    isWeightedPath_append happ1 hp2
  have hw_single : pathWeight [e] = e.weight := pathWeight_singleton e
  have hw_app : pathWeight ((p1 ++ [e]) ++ p2) = a + e.weight + b := by
    rw [pathWeight_append, pathWeight_append, hw1, hw_single, hw2]
  have hle : a + e.weight + b ≤ T := by
    have h := hmaxT _ happ
    rw [hw_app] at h
    exact h
  have hnonneg : 0 ≤ φ := by omega
  refine ⟨hnonneg, ?_⟩
  constructor
  · intro hzero
    have hab : a + e.weight + b = T := by omega
    have hmem_e : e ∈ ([e] : List (Edge n)) := by simp
    have hmem1 : e ∈ p1 ++ [e] := List.mem_append.mpr (Or.inr hmem_e)
    have hmem : e ∈ (p1 ++ [e]) ++ p2 := List.mem_append.mpr (Or.inl hmem1)
    refine ⟨(p1 ++ [e]) ++ p2, happ, by rw [hw_app, hab], hmem⟩
  · rintro ⟨p, hp, hwp, hmem⟩
    obtain ⟨q1, q2, heq, hq1, hq2⟩ :=
      isWeightedPath_split_at_edge hp hmem
    have hw_split : pathWeight p = pathWeight q1 + e.weight + pathWeight q2 := by
      rw [heq, pathWeight_append, pathWeight_append, pathWeight_singleton]
    have hle1 := hmax1 _ hq1
    have hle2 := hmax2 _ hq2
    omega

/-- Model events are forward-reachable from the source on covered projects in which `t` is
reachable from `s`. (`C9`, private) -/
private theorem modelEvent_reachable_src {n : Nat} {edges : List (Edge n)}
    {s t : Fin n} (hcover : IsCovered edges s t)
    (hst : (toDirectedAdjacency edges).Reachable s t) (v : Fin n)
    (hv : IsModelEvent edges s t v) :
    (toDirectedAdjacency edges).Reachable s v := by
  unfold IsModelEvent at hv
  obtain rfl | rfl | ⟨e, hem, rfl | rfl⟩ := hv
  · exact reachable_iff_exists_isWeightedPath.mpr
      ⟨[], isWeightedPath_nil edges _⟩
  · exact hst
  · exact (hcover e hem).1
  · exact reachable_trans_middle (hcover e hem).1 (reachable_of_mem_edge hem)

/-- Model events reach the sink on covered projects in which `t` is reachable from `s`. (`C9`,
private) -/
private theorem modelEvent_reachable_tgt {n : Nat} {edges : List (Edge n)}
    {s t : Fin n} (hcover : IsCovered edges s t)
    (hst : (toDirectedAdjacency edges).Reachable s t) (v : Fin n)
    (hv : IsModelEvent edges s t v) :
    (toDirectedAdjacency edges).Reachable v t := by
  unfold IsModelEvent at hv
  obtain rfl | rfl | ⟨e, hem, rfl | rfl⟩ := hv
  · exact hst
  · exact reachable_iff_exists_isWeightedPath.mpr
      ⟨[], isWeightedPath_nil edges _⟩
  · exact reachable_trans_middle (reachable_of_mem_edge hem) (hcover e hem).2
  · exact (hcover e hem).2

/-- Path weights are nonnegative under nonnegative activity durations. (`C9`, private) -/
private theorem pathWeight_nonneg {n : Nat} {edges : List (Edge n)}
    (hnn : ∀ e ∈ edges, 0 ≤ e.weight) (p : List (Edge n)) :
    (∀ y ∈ p, y ∈ edges) → 0 ≤ pathWeight p := by
  induction p with
  | nil =>
    intro hmem
    simp [pathWeight]
  | cons f r ih =>
    intro hmem
    have hf : f ∈ edges := hmem f (by simp)
    have hr : ∀ y ∈ r, y ∈ edges :=
      fun y hy => hmem y (List.mem_cons.mpr (Or.inr hy))
    have hihr := ih hr
    have hfnn := hnn f hf
    have hcons : pathWeight (f :: r) = f.weight + pathWeight r := by
      simp [pathWeight]
    omega

/-- A feasible schedule dominates every weighted path it spans. (`C9`, private) -/
private theorem pathWeight_le_tau_sub {n : Nat} {edges : List (Edge n)}
    {τ : Fin n → Int}
    (hle : ∀ e ∈ edges, τ e.source + e.weight ≤ τ e.target)
    (p : List (Edge n)) :
    ∀ {u v : Fin n}, IsWeightedPath edges u v p → pathWeight p ≤ τ v - τ u := by
  induction p with
  | nil =>
    intro u v h
    unfold IsWeightedPath at h
    obtain ⟨_, _, hends⟩ := h
    subst hends
    simp [pathWeight]
  | cons f r ih =>
    intro u v h
    have htail : IsWeightedPath edges f.target v r := isWeightedPath_tail h
    have hmem : f ∈ edges := by
      unfold IsWeightedPath at h
      exact h.1 f (by simp)
    have hsrc : f.source = u := by
      unfold IsWeightedPath at h
      exact h.2.2.1
    have hihr := ih htail
    have hstep := hle f hmem
    have hcons : pathWeight (f :: r) = f.weight + pathWeight r := by
      simp [pathWeight]
    rw [hsrc] at hstep
    omega

/-- Earliest start at the source is zero by the doubling argument. (`C9`, private) -/
private theorem earliestStart_at_source {n : Nat} {edges : List (Edge n)}
    {s : Fin n} {forward : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward) :
    earliestStart forward s = some 0 := by
  have hreach : (toDirectedAdjacency edges).Reachable s s :=
    reachable_iff_exists_isWeightedPath.mpr ⟨[], isWeightedPath_nil edges s⟩
  obtain ⟨a, ha⟩ := (earliestStart_defined_iff hf s).mpr hreach
  obtain ⟨⟨p, hp, hwp⟩, hmax⟩ := (earliestStart_spec hf s a).mp ha
  have hnil : pathWeight ([] : List (Edge n)) ≤ a :=
    hmax [] (isWeightedPath_nil edges s)
  have hnil0 : pathWeight ([] : List (Edge n)) = 0 := by simp [pathWeight]
  have h0 : (0 : Int) ≤ a := by omega
  have happ : IsWeightedPath edges s s (p ++ p) := isWeightedPath_append hp hp
  have h2a := hmax _ happ
  rw [pathWeight_append, hwp] at h2a
  have ha0 : a = 0 := by omega
  rw [ha0] at ha
  exact ha

/-- Longest time to sink at the sink is zero by the doubling argument. (`C9`, private) -/
private theorem longestToSink_at_sink {n : Nat} {edges : List (Edge n)}
    {t : Fin n} {reverse : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse) :
    longestToSink reverse t = some 0 := by
  have hreach : (toDirectedAdjacency edges).Reachable t t :=
    reachable_iff_exists_isWeightedPath.mpr ⟨[], isWeightedPath_nil edges t⟩
  obtain ⟨b, hb⟩ := (longestToSink_defined_iff hr t).mpr hreach
  obtain ⟨⟨p, hp, hwp⟩, hmax⟩ := (longestToSink_spec hr t b).mp hb
  have hnil : pathWeight ([] : List (Edge n)) ≤ b :=
    hmax [] (isWeightedPath_nil edges t)
  have hnil0 : pathWeight ([] : List (Edge n)) = 0 := by simp [pathWeight]
  have h0 : (0 : Int) ≤ b := by omega
  have happ : IsWeightedPath edges t t (p ++ p) := isWeightedPath_append hp hp
  have h2b := hmax _ happ
  rw [pathWeight_append, hwp] at h2b
  have hb0 : b = 0 := by omega
  rw [hb0] at hb
  exact hb

/-- When both runs succeed, `t` is reachable from `s` and the project is covered, both raw outputs
are defined on every model event. Coverage alone does not suffice: it holds vacuously when there
are no activities, and then `earliestStart` is undefined at the model event `t` when `s ≠ t`.
(`C9`) -/
public theorem raw_defined_on_modelEvents {n : Nat} {edges : List (Edge n)}
    {s t : Fin n} {forward reverse : Distances n}
    (hcover : IsCovered edges s t)
    (hst : (toDirectedAdjacency edges).Reachable s t)
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (v : Fin n) (hv : IsModelEvent edges s t v) :
    (∃ a, earliestStart forward v = some a) ∧
      ∃ b, longestToSink reverse v = some b := by
  refine ⟨?_, ?_⟩
  · exact (earliestStart_defined_iff hf v).mpr
      (modelEvent_reachable_src hcover hst v hv)
  · exact (longestToSink_defined_iff hr v).mpr
      (modelEvent_reachable_tgt hcover hst v hv)

/-- When the forward run succeeds, `t` is reachable from `s`, the project is covered and durations
are nonnegative, the earliest-start schedule is feasible, starts at zero, completes at `T`, and
agrees with `earliestStart` on model events, where it is pointwise earliest among feasible
schedules (`feasible_dominates_earliest`). (`C9`) -/
public theorem earliestSchedule_feasible {n : Nat} {edges : List (Edge n)}
    {s t : Fin n} {forward : Distances n} {T : Int}
    (hnn : ∀ e ∈ edges, 0 ≤ e.weight)
    (hcover : IsCovered edges s t)
    (hst : (toDirectedAdjacency edges).Reachable s t)
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hT : makespan forward t = some T) :
    ∃ τ : Fin n → Int,
      (∀ v, IsModelEvent edges s t v → earliestStart forward v = some (τ v)) ∧
        IsFeasibleSchedule edges s t τ ∧ τ s = 0 ∧ τ t = T := by
  refine ⟨fun v => (earliestStart forward v).getD 0, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨a, ha⟩ := (earliestStart_defined_iff hf v).mpr
      (modelEvent_reachable_src hcover hst v hv)
    change earliestStart forward v = some ((earliestStart forward v).getD 0)
    rw [ha]
    rfl
  · unfold IsFeasibleSchedule
    refine ⟨?_, ?_⟩
    · intro v hv
      obtain ⟨a, ha⟩ := (earliestStart_defined_iff hf v).mpr
        (modelEvent_reachable_src hcover hst v hv)
      obtain ⟨⟨p, hp, hwp⟩, _⟩ := (earliestStart_spec hf v a).mp ha
      have hnn_p := pathWeight_nonneg hnn p hp.1
      have hτv : (fun v => (earliestStart forward v).getD 0) v = a := by
        change (earliestStart forward v).getD 0 = a
        rw [ha]
        rfl
      rw [hτv]
      omega
    · intro e hem
      have hsrcM : IsModelEvent edges s t e.source :=
        Or.inr (Or.inr ⟨e, hem, Or.inl rfl⟩)
      have htgtM : IsModelEvent edges s t e.target :=
        Or.inr (Or.inr ⟨e, hem, Or.inr rfl⟩)
      obtain ⟨a, ha⟩ := (earliestStart_defined_iff hf e.source).mpr
        (modelEvent_reachable_src hcover hst _ hsrcM)
      obtain ⟨a', ha'⟩ := (earliestStart_defined_iff hf e.target).mpr
        (modelEvent_reachable_src hcover hst _ htgtM)
      obtain ⟨⟨p1, hp1, hw1⟩, _⟩ := (earliestStart_spec hf e.source a).mp ha
      obtain ⟨_, hmax'⟩ := (earliestStart_spec hf e.target a').mp ha'
      have happ := isWeightedPath_append hp1 (isWeightedPath_singleton hem)
      have hle := hmax' _ happ
      rw [pathWeight_append, pathWeight_singleton, hw1] at hle
      have hτs : (fun v => (earliestStart forward v).getD 0) e.source = a := by
        change (earliestStart forward e.source).getD 0 = a
        rw [ha]
        rfl
      have hτt : (fun v => (earliestStart forward v).getD 0) e.target = a' := by
        change (earliestStart forward e.target).getD 0 = a'
        rw [ha']
        rfl
      rw [hτs, hτt]
      omega
  · have hs0 : earliestStart forward s = some 0 := earliestStart_at_source hf
    change (earliestStart forward s).getD 0 = 0
    rw [hs0]
    rfl
  · have htT : earliestStart forward t = some T := hT
    change (earliestStart forward t).getD 0 = T
    rw [htT]
    rfl

/-- Every feasible schedule dominates the raw earliest starts: `a ≤ τ v` wherever
`earliestStart forward v = some a`. Only the successful forward run and feasibility are needed;
no acyclicity, coverage, reachability, nonnegative durations or model-event membership. (`C9`) -/
public theorem feasible_dominates_earliest {n : Nat} {edges : List (Edge n)}
    {s t : Fin n} {forward : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (τ : Fin n → Int) (hτ : IsFeasibleSchedule edges s t τ)
    (v : Fin n) (a : Int)
    (hes : earliestStart forward v = some a) :
    a ≤ τ v := by
  obtain ⟨⟨p, hp, hwp⟩, _⟩ := (earliestStart_spec hf v a).mp hes
  have hle : ∀ e ∈ edges, τ e.source + e.weight ≤ τ e.target := hτ.2
  have hpath := pathWeight_le_tau_sub hle p hp
  have hs0 : 0 ≤ τ s := hτ.1 s (Or.inl rfl)
  omega

/-- The makespan lower-bounds the sink time of every feasible schedule. Only the successful
forward run, a defined makespan and feasibility are needed; on a project that is not covered the
bound can be strict. (`C9`) -/
public theorem makespan_le_completion {n : Nat} {edges : List (Edge n)}
    {s t : Fin n} {forward : Distances n} {T : Int}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hT : makespan forward t = some T)
    (τ : Fin n → Int) (hτ : IsFeasibleSchedule edges s t τ) :
    T ≤ τ t := by
  have hes : earliestStart forward t = some T := hT
  exact feasible_dominates_earliest hf τ hτ t T hes

/-- On covered projects with nonnegative durations, every feasible schedule finishes every
activity by the sink event time. (`C9`) -/
public theorem feasible_activity_finishes_by_sink {n : Nat}
    {edges : List (Edge n)} {s t : Fin n}
    (hnn : ∀ e ∈ edges, 0 ≤ e.weight)
    (hcover : IsCovered edges s t)
    (τ : Fin n → Int) (hτ : IsFeasibleSchedule edges s t τ)
    (e : Edge n) (hem : e ∈ edges) :
    τ e.target ≤ τ t := by
  obtain ⟨_, hvt⟩ := hcover e hem
  obtain ⟨p, hp⟩ := reachable_iff_exists_isWeightedPath.mp hvt
  have hle : ∀ e ∈ edges, τ e.source + e.weight ≤ τ e.target := hτ.2
  have hpath := pathWeight_le_tau_sub hle p hp
  have hnn_p := pathWeight_nonneg hnn p hp.1
  omega

/-- When both runs succeed, `t` is reachable from `s`, the project is covered and durations are
nonnegative, the latest-start schedule is feasible, finishes at `T`, and is pointwise latest on
model events among the feasible schedules finishing by `T`: each of them puts every model event no
later. Feasibility constrains no vertex outside the model events (an isolated vertex can take any
time), so when such a vertex exists no schedule is latest on every vertex. (`C9`) -/
public theorem latestSchedule_feasible {n : Nat} {edges : List (Edge n)}
    {s t : Fin n} {forward reverse : Distances n} {T : Int}
    (hnn : ∀ e ∈ edges, 0 ≤ e.weight)
    (hcover : IsCovered edges s t)
    (hst : (toDirectedAdjacency edges).Reachable s t)
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (hT : makespan forward t = some T) :
    ∃ τ : Fin n → Int,
      (∀ v, IsModelEvent edges s t v →
        latestStartAt (some T) reverse v = some (τ v)) ∧
        IsFeasibleSchedule edges s t τ ∧ τ t = T ∧
        ∀ τ' : Fin n → Int, IsFeasibleSchedule edges s t τ' → τ' t ≤ T →
          ∀ v, IsModelEvent edges s t v → τ' v ≤ τ v := by
  refine ⟨fun v => (latestStartAt (some T) reverse v).getD 0, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨b, hb⟩ := (longestToSink_defined_iff hr v).mpr
      (modelEvent_reachable_tgt hcover hst v hv)
    have hls : latestStartAt (some T) reverse v = some (T - b) := by
      unfold latestStartAt
      rw [hb]
      simp [latestStart]
    change latestStartAt (some T) reverse v
      = some ((latestStartAt (some T) reverse v).getD 0)
    rw [hls]
    rfl
  · unfold IsFeasibleSchedule
    refine ⟨?_, ?_⟩
    · intro v hv
      obtain ⟨b, hb⟩ := (longestToSink_defined_iff hr v).mpr
        (modelEvent_reachable_tgt hcover hst v hv)
      obtain ⟨a, ha⟩ := (earliestStart_defined_iff hf v).mpr
        (modelEvent_reachable_src hcover hst v hv)
      obtain ⟨⟨p1, hp1, hw1⟩, _⟩ := (earliestStart_spec hf v a).mp ha
      obtain ⟨⟨p2, hp2, hw2⟩, _⟩ := (longestToSink_spec hr v b).mp hb
      obtain ⟨_, hmaxT⟩ := (earliestStart_spec hf t T).mp hT
      have happ := isWeightedPath_append hp1 hp2
      have hleT := hmaxT _ happ
      rw [pathWeight_append, hw1, hw2] at hleT
      have hnn1 := pathWeight_nonneg hnn p1 hp1.1
      have hls : latestStartAt (some T) reverse v = some (T - b) := by
        unfold latestStartAt
        rw [hb]
        simp [latestStart]
      have hτv : (fun v => (latestStartAt (some T) reverse v).getD 0) v
          = T - b := by
        change (latestStartAt (some T) reverse v).getD 0 = T - b
        rw [hls]
        rfl
      rw [hτv]
      omega
    · intro e hem
      have hsrcM : IsModelEvent edges s t e.source :=
        Or.inr (Or.inr ⟨e, hem, Or.inl rfl⟩)
      have htgtM : IsModelEvent edges s t e.target :=
        Or.inr (Or.inr ⟨e, hem, Or.inr rfl⟩)
      obtain ⟨bs, hs⟩ := (longestToSink_defined_iff hr e.source).mpr
        (modelEvent_reachable_tgt hcover hst _ hsrcM)
      obtain ⟨bt, ht⟩ := (longestToSink_defined_iff hr e.target).mpr
        (modelEvent_reachable_tgt hcover hst _ htgtM)
      obtain ⟨_, hmaxS⟩ := (longestToSink_spec hr e.source bs).mp hs
      obtain ⟨⟨q, hq, hwq⟩, _⟩ := (longestToSink_spec hr e.target bt).mp ht
      have hcons := isWeightedPath_cons hem rfl hq
      have hle := hmaxS _ hcons
      have hconseq : pathWeight (e :: q) = e.weight + pathWeight q := by
        simp [pathWeight]
      have hlsS : latestStartAt (some T) reverse e.source
          = some (T - bs) := by
        unfold latestStartAt
        rw [hs]
        simp [latestStart]
      have hlsT : latestStartAt (some T) reverse e.target
          = some (T - bt) := by
        unfold latestStartAt
        rw [ht]
        simp [latestStart]
      have hτs : (fun v => (latestStartAt (some T) reverse v).getD 0) e.source
          = T - bs := by
        change (latestStartAt (some T) reverse e.source).getD 0 = T - bs
        rw [hlsS]
        rfl
      have hτt : (fun v => (latestStartAt (some T) reverse v).getD 0) e.target
          = T - bt := by
        change (latestStartAt (some T) reverse e.target).getD 0 = T - bt
        rw [hlsT]
        rfl
      rw [hτs, hτt]
      omega
  · have ht0 : longestToSink reverse t = some 0 := longestToSink_at_sink hr
    have hlt : latestStartAt (some T) reverse t = some T := by
      unfold latestStartAt
      rw [ht0]
      simp [latestStart]
    change (latestStartAt (some T) reverse t).getD 0 = T
    rw [hlt]
    rfl
  · intro τ' hτ' hleT v hv
    obtain ⟨b, hb⟩ := (longestToSink_defined_iff hr v).mpr
      (modelEvent_reachable_tgt hcover hst v hv)
    obtain ⟨⟨q, hq, hwq⟩, _⟩ := (longestToSink_spec hr v b).mp hb
    have hle : ∀ e ∈ edges, τ' e.source + e.weight ≤ τ' e.target := hτ'.2
    have hpath := pathWeight_le_tau_sub hle q hq
    have hls : latestStartAt (some T) reverse v = some (T - b) := by
      unfold latestStartAt
      rw [hb]
      simp [latestStart]
    have hτv : (fun v => (latestStartAt (some T) reverse v).getD 0) v
        = T - b := by
      change (latestStartAt (some T) reverse v).getD 0 = T - b
      rw [hls]
      rfl
    rw [hτv]
    omega

end Cslib.Algorithms.Lean.Scheduling.CriticalPath
