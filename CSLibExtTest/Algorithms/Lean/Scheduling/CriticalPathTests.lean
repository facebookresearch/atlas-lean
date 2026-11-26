/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Scheduling.CriticalPath
public import CSLibExt.Algorithms.Lean.Approximation.ListScheduling

/-! # Critical-path fixtures (SCH-001, C10).

Kernel-elaborated contract checks over the frozen production definitions:

* pure `Option` arithmetic (`latestStart`, `slack`, `activityFloat`) by `rfl`,
  including every none-propagation case;
* `negEdges` / `revNegEdges` on one concrete edge list by `rfl`;
* API-shape `example`s whose proof term is exactly a production theorem;
* concrete end-to-end fixtures whose forward/reverse run values are derived
  from `forward_run_ok` / `reversed_run_ok` via `earliestStart_spec`,
  `longestToSink_spec` and the none-iff lemmas, never invented;
* an integration check that this module imports the list-scheduling API too, whose
  `makespan` (largest machine load) is a different declaration from
  `CriticalPath.makespan` (longest source-to-sink path weight).

Each fixture uses explicit tiny `IsWeightedPath` witnesses for attainment, a
potential upper bound proved by path induction for maximality, and a closed
vertex-predicate invariant for non-reachability. Nothing is executed: no
evaluation commands, no IO harness, and `decide` only for tiny literal `Fin`,
list, integer, or equality facts that do not evaluate a production algorithm.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Scheduling.CriticalPath.Tests

open Cslib.Algorithms.Lean.BellmanFord
open Cslib.Algorithms.Lean.DAGShortestPaths
open Cslib.Algorithms.Lean.Scheduling.CriticalPath

-- Pure `Option` arithmetic: `latestStart`, by `rfl` on literals.

example : latestStart (some 10) (some 3) = some 7 := rfl
example : latestStart (some 4) (some 4) = some 0 := rfl
example : latestStart (some 4) (some 9) = some (-5) := rfl
example : latestStart none (some 3) = none := rfl
example : latestStart (some 10) none = none := rfl
example : latestStart none none = none := rfl

-- Pure `Option` arithmetic: `slack`, by `rfl` on literals.

example : slack (some 5) (some 9) = some 4 := rfl
example : slack (some 0) (some 0) = some 0 := rfl
example : slack (some 10) (some 10) = some 0 := rfl
example : slack none (some 9) = none := rfl
example : slack (some 5) none = none := rfl
example : slack none none = none := rfl

-- Pure `Option` arithmetic: `activityFloat`, by `rfl` on literals.

example : activityFloat (some 5) (some 14) 4 = some 5 := rfl
example : activityFloat (some 0) (some 4) 4 = some 0 := rfl
example : activityFloat (some 2) (some 9) 3 = some 4 := rfl
example : activityFloat none (some 4) 4 = none := rfl
example : activityFloat (some 0) none 4 = none := rfl
example : activityFloat none none 4 = none := rfl

-- One concrete edge list for the `negEdges` / `revNegEdges` checks.

def w0 : Fin 2 := ⟨0, by decide⟩
def w1 : Fin 2 := ⟨1, by decide⟩
def wE : Edge 2 := { source := w0, target := w1, weight := 4 }
def wEdges : List (Edge 2) := [wE]

example : negEdges wEdges = [{ source := w0, target := w1, weight := -4 }] := rfl
example : revNegEdges wEdges = [{ source := w1, target := w0, weight := -4 }] := rfl

-- API-shape checks: each proof term is exactly a production theorem.

example {n : Nat} {edges : List (Edge n)} {s : Fin n} {result : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok result)
    (v : Fin n) (a : Int) :
    earliestStart result v = some a ↔
      ((∃ p, IsWeightedPath edges s v p ∧ pathWeight p = a) ∧
        ∀ p, IsWeightedPath edges s v p → pathWeight p ≤ a) :=
  earliestStart_spec hr v a
example {n : Nat} {edges : List (Edge n)} {s : Fin n} {result : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok result)
    (v : Fin n) :
    earliestStart result v = none ↔
      ¬(toDirectedAdjacency edges).Reachable s v :=
  earliestStart_eq_none_iff hr v
example {n : Nat} {edges : List (Edge n)} {t : Fin n} {result : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok result)
    (v : Fin n) (b : Int) :
    longestToSink result v = some b ↔
      ((∃ p, IsWeightedPath edges v t p ∧ pathWeight p = b) ∧
        ∀ p, IsWeightedPath edges v t p → pathWeight p ≤ b) :=
  longestToSink_spec hr v b
example {n : Nat} {edges : List (Edge n)} {t : Fin n} {result : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok result)
    (v : Fin n) :
    longestToSink result v = none ↔
      ¬(toDirectedAdjacency edges).Reachable v t :=
  longestToSink_eq_none_iff hr v
example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (hst : (toDirectedAdjacency edges).Reachable s t) :
    ∃ T, makespan forward t = some T ∧ longestToSink reverse s = some T ∧
      (∃ p, IsWeightedPath edges s t p ∧ pathWeight p = T) ∧
      ∀ p, IsWeightedPath edges s t p → pathWeight p ≤ T :=
  makespan_exists hf hr hst
example {n : Nat} {edges : List (Edge n)} {s t : Fin n} {forward : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hst : ¬(toDirectedAdjacency edges).Reachable s t) :
    earliestStart forward t = none :=
  earliestStart_sink_none_of_unreachable hf hst
example {n : Nat} {edges : List (Edge n)} {s t : Fin n} {reverse : Distances n}
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (hst : ¬(toDirectedAdjacency edges).Reachable s t) :
    longestToSink reverse s = none :=
  longestToSink_source_none_of_unreachable hr hst
example (T lt : Option Int) (l : Int) :
    latestStart T lt = some l ↔
      ∃ Tv b, T = some Tv ∧ lt = some b ∧ l = Tv - b :=
  latestStart_some_iff T lt l
example (T lt : Option Int) :
    latestStart T lt = none ↔ T = none ∨ lt = none :=
  latestStart_eq_none_iff T lt
example (es ls : Option Int) (sig : Int) :
    slack es ls = some sig ↔ ∃ a l, es = some a ∧ ls = some l ∧ sig = l - a :=
  slack_some_iff es ls sig
example (es ls : Option Int) :
    slack es ls = none ↔ es = none ∨ ls = none :=
  slack_eq_none_iff es ls
example (esSrc lsTgt : Option Int) (w phi : Int) :
    activityFloat esSrc lsTgt w = some phi ↔
      ∃ a l, esSrc = some a ∧ lsTgt = some l ∧ phi = l - a - w :=
  activityFloat_some_iff esSrc lsTgt w phi
example (esSrc lsTgt : Option Int) (w : Int) :
    activityFloat esSrc lsTgt w = none ↔ esSrc = none ∨ lsTgt = none :=
  activityFloat_eq_none_iff esSrc lsTgt w
example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (v : Fin n) :
    (∃ sig, slackAt (makespan forward t) forward reverse v = some sig) ↔
      (toDirectedAdjacency edges).Reachable s v ∧
        (toDirectedAdjacency edges).Reachable v t :=
  slackAt_defined_iff hf hr v
example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (e : Edge n) (hem : e ∈ edges) :
    (∃ phi, floatAt (makespan forward t) forward reverse e = some phi) ↔
      (toDirectedAdjacency edges).Reachable s e.source ∧
        (toDirectedAdjacency edges).Reachable e.target t :=
  floatAt_defined_iff hf hr e hem
example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse) :
    IsCovered edges s t ↔ ∀ e ∈ edges, ¬isOrphan forward reverse e :=
  coverage_iff_no_orphan hf hr
example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n} {T sig : Int}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (hT : makespan forward t = some T)
    (v : Fin n) (hslack : slackAt (some T) forward reverse v = some sig) :
    0 ≤ sig ∧
      (sig = 0 ↔
        ∃ p, IsWeightedPath edges s t p ∧ pathWeight p = T ∧
          v ∈ pathVertices s p) :=
  slackAt_spec hf hr hT v hslack
example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n} {T phi : Int}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (hT : makespan forward t = some T)
    (e : Edge n) (hem : e ∈ edges)
    (hfloat : floatAt (some T) forward reverse e = some phi) :
    0 ≤ phi ∧
      (phi = 0 ↔
        ∃ p, IsWeightedPath edges s t p ∧ pathWeight p = T ∧ e ∈ p) :=
  floatAt_spec hf hr hT e hem hfloat

-- Run-existence statements the fixtures build on.

example {n : Nat} (edges : List (Edge n)) (s : Fin n)
    (hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency edges)) :
    ∃ result,
      (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok result :=
  forward_run_ok edges s hacyc
example {n : Nat} (edges : List (Edge n)) (t : Fin n)
    (hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency edges)) :
    ∃ result,
      (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok result :=
  reversed_run_ok edges t hacyc

-- Test-private helpers shared by the fixtures below.

/-- A `<`-chain over a vertex rank never returns below its head. -/
private theorem chain_le_of_isChain {n : Nat} {rank : Fin n → Nat} (l : List (Fin n)) :
    ∀ {x z : Fin n}, l.head? = some x → l.getLast? = some z →
    l.IsChain (fun (u v : Fin n) => rank u < rank v) → rank x ≤ rank z := by
  induction l with
  | nil =>
    intro x z hh hl hc
    have hnil : ([ ] : List (Fin n)).head? = none := rfl
    rw [hnil] at hh
    simp at hh
  | cons x xs ih =>
    intro y z hh hl hc
    have hxy : x = y := Option.some_inj.mp hh
    subst hxy
    clear hh
    revert ih hl hc
    cases xs with
    | nil =>
      intro _ hl _
      have hxz : x = z := Option.some_inj.mp hl
      subst hxz
      exact le_refl _
    | cons w ws =>
      intro ih2 hl hc
      simp only [List.isChain_cons_cons] at hc
      obtain ⟨hlt, hrest⟩ := hc
      have hlt' : rank x < rank w := hlt
      have hl' : (w :: ws).getLast? = some z := hl
      have hhw : (w :: ws).head? = some w := rfl
      have hle : rank w ≤ rank z := ih2 hhw hl' hrest
      omega

/-- Edges from smaller to larger `Fin.val` preclude directed cycles. -/
private theorem isAcyclic_of_forall_mem_val_lt {n : Nat} {edges : List (Edge n)}
    (hlt : ∀ e ∈ edges, e.source.val < e.target.val) :
    TopologicalSort.IsAcyclic (toDirectedAdjacency edges) := by
  intro hcon
  obtain ⟨cycle, hcyc⟩ := hcon
  obtain ⟨hne, hnodup, hchain, hclose, hmem⟩ :=
    (TopologicalSort.directedCycleIn_iff _ _ _).mp hcyc
  have hedge : ∀ u v : Fin n, (toDirectedAdjacency edges).Edge u v → u.val < v.val := by
    intro u v huv
    obtain ⟨e, hem, rfl, rfl⟩ := edge_toDirectedAdjacency_iff.mp huv
    exact hlt e hem
  have hchain' : cycle.IsChain (fun (u v : Fin n) => u.val < v.val) :=
    hchain.imp (fun _ _ h => hedge _ _ h)
  have hclose' : (cycle.getLast hne).val < (cycle.head hne).val := hedge _ _ hclose
  have hhead? : cycle.head? = some (cycle.head hne) :=
    (List.head_eq_iff_head?_eq_some hne).mp rfl
  have hlast? : cycle.getLast? = some (cycle.getLast hne) :=
    (List.getLast_eq_iff_getLast?_eq_some hne).mp rfl
  have hle : (cycle.head hne).val ≤ (cycle.getLast hne).val :=
    chain_le_of_isChain cycle hhead? hlast? hchain'
  have _ := hnodup
  have _ := hmem
  omega

/-- Edges from smaller to larger vertex rank preclude directed cycles. -/
private theorem isAcyclic_of_forall_mem_rank_lt {n : Nat} {edges : List (Edge n)}
    {rank : Fin n → Nat}
    (hlt : ∀ e ∈ edges, rank e.source < rank e.target) :
    TopologicalSort.IsAcyclic (toDirectedAdjacency edges) := by
  intro hcon
  obtain ⟨cycle, hcyc⟩ := hcon
  obtain ⟨hne, hnodup, hchain, hclose, hmem⟩ :=
    (TopologicalSort.directedCycleIn_iff _ _ _).mp hcyc
  have hedge : ∀ u v : Fin n, (toDirectedAdjacency edges).Edge u v → rank u < rank v := by
    intro u v huv
    obtain ⟨e, hem, rfl, rfl⟩ := edge_toDirectedAdjacency_iff.mp huv
    exact hlt e hem
  have hchain' : cycle.IsChain (fun (u v : Fin n) => rank u < rank v) :=
    hchain.imp (fun _ _ h => hedge _ _ h)
  have hclose' : rank (cycle.getLast hne) < rank (cycle.head hne) := hedge _ _ hclose
  have hhead? : cycle.head? = some (cycle.head hne) :=
    (List.head_eq_iff_head?_eq_some hne).mp rfl
  have hlast? : cycle.getLast? = some (cycle.getLast hne) :=
    (List.getLast_eq_iff_getLast?_eq_some hne).mp rfl
  have hle : rank (cycle.head hne) ≤ rank (cycle.getLast hne) :=
    chain_le_of_isChain cycle hhead? hlast? hchain'
  have _ := hnodup
  have _ := hmem
  omega

/-- A potential upper-bounds every weighted-path weight by telescoping. -/
private theorem pathWeight_le_pot {n : Nat} {edges : List (Edge n)} {p : Fin n → Int}
    (hedge : ∀ e ∈ edges, p e.source + e.weight ≤ p e.target)
    {path : List (Edge n)} :
    ∀ {s v : Fin n}, IsWeightedPath edges s v path → pathWeight path ≤ p v - p s := by
  induction path with
  | nil =>
    intro s v h
    unfold IsWeightedPath at h
    obtain ⟨_, _, hsv⟩ := h
    subst hsv
    have h0 : pathWeight ([] : List (Edge n)) = 0 := by simp [pathWeight]
    omega
  | cons f r ih =>
    intro s v h
    have hmem : f ∈ edges := h.1 f (by simp)
    have hsrc : f.source = s := h.2.2.1
    have htail : IsWeightedPath edges f.target v r := isWeightedPath_tail h
    have hihr : pathWeight r ≤ p v - p f.target := ih htail
    have hstep : p f.source + f.weight ≤ p f.target := hedge f hmem
    rw [hsrc] at hstep
    have hcons : pathWeight (f :: r) = f.weight + pathWeight r := by simp [pathWeight]
    omega

/-- A predicate closed under edges holds at every path endpoint. -/
private theorem path_invariant {n : Nat} {edges : List (Edge n)} (P : Fin n → Prop)
    (hPstep : ∀ e ∈ edges, P e.source → P e.target)
    {path : List (Edge n)} :
    ∀ {s v : Fin n}, P s → IsWeightedPath edges s v path → P v := by
  induction path with
  | nil =>
    intro s v hP0 h
    unfold IsWeightedPath at h
    obtain ⟨_, _, hsv⟩ := h
    subst hsv
    exact hP0
  | cons f r ih =>
    intro s v hP0 h
    have hmem : f ∈ edges := h.1 f (by simp)
    have hsrc : f.source = s := h.2.2.1
    have htail : IsWeightedPath edges f.target v r := isWeightedPath_tail h
    have hPf : P f.source := by
      rw [hsrc]
      exact hP0
    have hPt : P f.target := hPstep f hmem hPf
    exact ih hPt htail

/-- A single input edge is a weighted path between its endpoints. -/
private theorem isWeightedPath_singleton_of_mem {n : Nat} {edges : List (Edge n)}
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

/-- Two chained input edges form a weighted path. -/
private theorem isWeightedPath_pair_of_mem {n : Nat} {edges : List (Edge n)}
    {e1 e2 : Edge n} (hem1 : e1 ∈ edges) (hem2 : e2 ∈ edges)
    (hchain : e1.target = e2.source) :
    IsWeightedPath edges e1.source e2.target [e1, e2] := by
  unfold IsWeightedPath
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    obtain rfl | rfl := hy
    · exact hem1
    · exact hem2
  · simp only [List.isChain_cons_cons]
    refine ⟨hchain, by simp⟩
  · exact ⟨rfl, rfl⟩

/-- Three chained input edges form a weighted path. -/
private theorem isWeightedPath_triple_of_mem {n : Nat} {edges : List (Edge n)}
    {e1 e2 e3 : Edge n} (hem1 : e1 ∈ edges) (hem2 : e2 ∈ edges) (hem3 : e3 ∈ edges)
    (hc1 : e1.target = e2.source) (hc2 : e2.target = e3.source) :
    IsWeightedPath edges e1.source e3.target [e1, e2, e3] := by
  unfold IsWeightedPath
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    obtain rfl | rfl | rfl := hy
    · exact hem1
    · exact hem2
    · exact hem3
  · simp only [List.isChain_cons_cons]
    refine ⟨hc1, ?_⟩
    refine ⟨hc2, by simp⟩
  · exact ⟨rfl, rfl⟩

-- Fixture 1: single edge, n = 2, [0 → 1 (4)], s = 0, t = 1.

def f1_v0 : Fin 2 := ⟨0, by decide⟩
def f1_v1 : Fin 2 := ⟨1, by decide⟩
def f1_e0 : Edge 2 := { source := f1_v0, target := f1_v1, weight := 4 }
def f1_edges : List (Edge 2) := [f1_e0]
def f1_pot : Fin 2 → Int := fun v => if v.val = 0 then 0 else 4

private theorem f1_hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency f1_edges) := by
  apply isAcyclic_of_forall_mem_val_lt; intro e hem
  simp only [f1_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl := hem; decide

private theorem f1_hedge : ∀ e ∈ f1_edges, f1_pot e.source + e.weight ≤ f1_pot e.target := by
  intro e hem; simp only [f1_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl := hem; decide

example : ∃ result, (DAGShortestPaths.dagShortestPaths (negEdges f1_edges) f1_v0).ret = .ok result :=
  forward_run_ok f1_edges f1_v0 f1_hacyc
example : ∃ result, (DAGShortestPaths.dagShortestPaths (revNegEdges f1_edges) f1_v1).ret = .ok result :=
  reversed_run_ok f1_edges f1_v1 f1_hacyc
example (forward : Distances 2) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f1_edges) f1_v0).ret = .ok forward) :
    earliestStart forward f1_v0 = some 0 := by
  apply (earliestStart_spec hf f1_v0 0).mpr; refine ⟨⟨[], by simp [IsWeightedPath], rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f1_hedge hp
  have hred : f1_pot f1_v0 - f1_pot f1_v0 = 0 := rfl; omega
example (forward : Distances 2) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f1_edges) f1_v0).ret = .ok forward) :
    earliestStart forward f1_v1 = some 4 := by
  apply (earliestStart_spec hf f1_v1 4).mpr
  refine ⟨⟨[f1_e0], isWeightedPath_singleton_of_mem (edges := f1_edges) (e := f1_e0) (by simp [f1_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f1_hedge hp
  have hred : f1_pot f1_v1 - f1_pot f1_v0 = 4 := rfl; omega
example (reverse : Distances 2) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f1_edges) f1_v1).ret = .ok reverse) :
    longestToSink reverse f1_v0 = some 4 := by
  apply (longestToSink_spec hr f1_v0 4).mpr
  refine ⟨⟨[f1_e0], isWeightedPath_singleton_of_mem (edges := f1_edges) (e := f1_e0) (by simp [f1_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f1_hedge hp
  have hred : f1_pot f1_v1 - f1_pot f1_v0 = 4 := rfl; omega
example (reverse : Distances 2) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f1_edges) f1_v1).ret = .ok reverse) :
    longestToSink reverse f1_v1 = some 0 := by
  apply (longestToSink_spec hr f1_v1 0).mpr; refine ⟨⟨[], by simp [IsWeightedPath], rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f1_hedge hp
  have hred : f1_pot f1_v1 - f1_pot f1_v1 = 0 := rfl; omega
example (forward : Distances 2) (hES : earliestStart forward f1_v1 = some 4) : makespan forward f1_v1 = some 4 := hES
example (forward reverse : Distances 2) (hT : makespan forward f1_v1 = some 4) (ha : earliestStart forward f1_v0 = some 0) (hb : longestToSink reverse f1_v0 = some 4) :
    slackAt (makespan forward f1_v1) forward reverse f1_v0 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 2) (hT : makespan forward f1_v1 = some 4) (ha : earliestStart forward f1_v1 = some 4) (hb : longestToSink reverse f1_v1 = some 0) :
    slackAt (makespan forward f1_v1) forward reverse f1_v1 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 2) (hT : makespan forward f1_v1 = some 4) (ha : earliestStart forward f1_e0.source = some 0) (hb : longestToSink reverse f1_e0.target = some 0) :
    floatAt (makespan forward f1_v1) forward reverse f1_e0 = some 0 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl

-- Fixture 2: parallel short arc, n = 3, [0 → 1 (5), 1 → 2 (5), 0 → 1 (1)].

def f2_v0 : Fin 3 := ⟨0, by decide⟩
def f2_v1 : Fin 3 := ⟨1, by decide⟩
def f2_v2 : Fin 3 := ⟨2, by decide⟩
def f2_e0 : Edge 3 := { source := f2_v0, target := f2_v1, weight := 5 }
def f2_e1 : Edge 3 := { source := f2_v1, target := f2_v2, weight := 5 }
def f2_e2 : Edge 3 := { source := f2_v0, target := f2_v1, weight := 1 }
def f2_edges : List (Edge 3) := [f2_e0, f2_e1, f2_e2]
def f2_pot : Fin 3 → Int := fun v => if v.val = 0 then 0 else if v.val = 1 then 5 else 10

private theorem f2_hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency f2_edges) := by
  apply isAcyclic_of_forall_mem_val_lt; intro e hem
  simp only [f2_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl | rfl | rfl := hem
  · decide
  · decide
  · decide

private theorem f2_hedge : ∀ e ∈ f2_edges, f2_pot e.source + e.weight ≤ f2_pot e.target := by
  intro e hem; simp only [f2_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl | rfl | rfl := hem
  · decide
  · decide
  · decide

example : ∃ result, (DAGShortestPaths.dagShortestPaths (negEdges f2_edges) f2_v0).ret = .ok result :=
  forward_run_ok f2_edges f2_v0 f2_hacyc
example : ∃ result, (DAGShortestPaths.dagShortestPaths (revNegEdges f2_edges) f2_v2).ret = .ok result :=
  reversed_run_ok f2_edges f2_v2 f2_hacyc
example (forward : Distances 3) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f2_edges) f2_v0).ret = .ok forward) :
    earliestStart forward f2_v0 = some 0 := by
  apply (earliestStart_spec hf f2_v0 0).mpr; refine ⟨⟨[], by simp [IsWeightedPath], rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f2_hedge hp
  have hred : f2_pot f2_v0 - f2_pot f2_v0 = 0 := rfl; omega
example (forward : Distances 3) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f2_edges) f2_v0).ret = .ok forward) :
    earliestStart forward f2_v1 = some 5 := by
  apply (earliestStart_spec hf f2_v1 5).mpr
  refine ⟨⟨[f2_e0], isWeightedPath_singleton_of_mem (edges := f2_edges) (e := f2_e0) (by simp [f2_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f2_hedge hp
  have hred : f2_pot f2_v1 - f2_pot f2_v0 = 5 := rfl; omega
example (forward : Distances 3) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f2_edges) f2_v0).ret = .ok forward) :
    earliestStart forward f2_v2 = some 10 := by
  apply (earliestStart_spec hf f2_v2 10).mpr
  refine ⟨⟨[f2_e0, f2_e1], isWeightedPath_pair_of_mem (edges := f2_edges) (e1 := f2_e0) (e2 := f2_e1) (by simp [f2_edges]) (by simp [f2_edges]) rfl, rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f2_hedge hp
  have hred : f2_pot f2_v2 - f2_pot f2_v0 = 10 := rfl; omega
example (reverse : Distances 3) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f2_edges) f2_v2).ret = .ok reverse) :
    longestToSink reverse f2_v0 = some 10 := by
  apply (longestToSink_spec hr f2_v0 10).mpr
  refine ⟨⟨[f2_e0, f2_e1], isWeightedPath_pair_of_mem (edges := f2_edges) (e1 := f2_e0) (e2 := f2_e1) (by simp [f2_edges]) (by simp [f2_edges]) rfl, rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f2_hedge hp
  have hred : f2_pot f2_v2 - f2_pot f2_v0 = 10 := rfl; omega
example (reverse : Distances 3) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f2_edges) f2_v2).ret = .ok reverse) :
    longestToSink reverse f2_v1 = some 5 := by
  apply (longestToSink_spec hr f2_v1 5).mpr
  refine ⟨⟨[f2_e1], isWeightedPath_singleton_of_mem (edges := f2_edges) (e := f2_e1) (by simp [f2_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f2_hedge hp
  have hred : f2_pot f2_v2 - f2_pot f2_v1 = 5 := rfl; omega
example (reverse : Distances 3) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f2_edges) f2_v2).ret = .ok reverse) :
    longestToSink reverse f2_v2 = some 0 := by
  apply (longestToSink_spec hr f2_v2 0).mpr; refine ⟨⟨[], by simp [IsWeightedPath], rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f2_hedge hp
  have hred : f2_pot f2_v2 - f2_pot f2_v2 = 0 := rfl; omega
example (forward : Distances 3) (hES : earliestStart forward f2_v2 = some 10) : makespan forward f2_v2 = some 10 := hES
example (reverse : Distances 3) (hb : longestToSink reverse f2_v0 = some 10) :
    latestStartAt (some 10) reverse f2_v0 = some 0 := by
  unfold latestStartAt; rw [hb]; rfl
example (reverse : Distances 3) (hb : longestToSink reverse f2_v1 = some 5) :
    latestStartAt (some 10) reverse f2_v1 = some 5 := by
  unfold latestStartAt; rw [hb]; rfl
example (reverse : Distances 3) (hb : longestToSink reverse f2_v2 = some 0) :
    latestStartAt (some 10) reverse f2_v2 = some 10 := by
  unfold latestStartAt; rw [hb]; rfl
example (forward reverse : Distances 3) (hT : makespan forward f2_v2 = some 10) (ha : earliestStart forward f2_v0 = some 0) (hb : longestToSink reverse f2_v0 = some 10) :
    slackAt (makespan forward f2_v2) forward reverse f2_v0 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 3) (hT : makespan forward f2_v2 = some 10) (ha : earliestStart forward f2_v1 = some 5) (hb : longestToSink reverse f2_v1 = some 5) :
    slackAt (makespan forward f2_v2) forward reverse f2_v1 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 3) (hT : makespan forward f2_v2 = some 10) (ha : earliestStart forward f2_v2 = some 10) (hb : longestToSink reverse f2_v2 = some 0) :
    slackAt (makespan forward f2_v2) forward reverse f2_v2 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 3) (hT : makespan forward f2_v2 = some 10) (ha : earliestStart forward f2_e0.source = some 0) (hb : longestToSink reverse f2_e0.target = some 5) :
    floatAt (makespan forward f2_v2) forward reverse f2_e0 = some 0 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 3) (hT : makespan forward f2_v2 = some 10) (ha : earliestStart forward f2_e1.source = some 5) (hb : longestToSink reverse f2_e1.target = some 0) :
    floatAt (makespan forward f2_v2) forward reverse f2_e1 = some 0 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl
-- The short arc has zero-slack endpoints but positive float 4.
example (forward reverse : Distances 3) (hT : makespan forward f2_v2 = some 10) (ha : earliestStart forward f2_e2.source = some 0) (hb : longestToSink reverse f2_e2.target = some 5) :
    floatAt (makespan forward f2_v2) forward reverse f2_e2 = some 4 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl

-- The covered parallel-arc project exercises the C9 scheduling law.
example (forward reverse : Distances 3)
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges f2_edges) f2_v0).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f2_edges) f2_v2).ret = .ok reverse)
    (hES1 : earliestStart forward f2_v1 = some 5) (hES2 : earliestStart forward f2_v2 = some 10)
    (hLS0 : latestStartAt (some 10) reverse f2_v0 = some 0)
    (hLS1 : latestStartAt (some 10) reverse f2_v1 = some 5)
    (_hLS2 : latestStartAt (some 10) reverse f2_v2 = some 10) :
    ∃ τ σ : Fin 3 → Int,
      τ f2_v0 = 0 ∧ τ f2_v1 = 5 ∧ τ f2_v2 = 10 ∧
      σ f2_v0 = 0 ∧ σ f2_v1 = 5 ∧ σ f2_v2 = 10 ∧
      IsFeasibleSchedule f2_edges f2_v0 f2_v2 τ ∧
      IsFeasibleSchedule f2_edges f2_v0 f2_v2 σ ∧
      5 ≤ τ f2_v1 ∧ 10 ≤ τ f2_v2 ∧ τ f2_v1 ≤ τ f2_v2 := by
  have hT : makespan forward f2_v2 = some 10 := hES2
  have hnn2 : ∀ e ∈ f2_edges, 0 ≤ e.weight := by
    intro e hem; simp only [f2_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
    obtain rfl | rfl | rfl := hem
    · decide
    · decide
    · decide
  have hcover2 : IsCovered f2_edges f2_v0 f2_v2 := by
    unfold IsCovered; intro e hem
    simp only [f2_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
    obtain rfl | rfl | rfl := hem
    · refine ⟨?_, ?_⟩
      · exact Relation.ReflTransGen.refl
      · exact (reachable_iff_exists_isWeightedPath (edges := f2_edges) (source := f2_v1) (target := f2_v2)).mpr ⟨[f2_e1], isWeightedPath_singleton_of_mem (edges := f2_edges) (e := f2_e1) (by simp [f2_edges])⟩
    · refine ⟨?_, ?_⟩
      · exact (reachable_iff_exists_isWeightedPath (edges := f2_edges) (source := f2_v0) (target := f2_v1)).mpr ⟨[f2_e0], isWeightedPath_singleton_of_mem (edges := f2_edges) (e := f2_e0) (by simp [f2_edges])⟩
      · exact Relation.ReflTransGen.refl
    · refine ⟨?_, ?_⟩
      · exact Relation.ReflTransGen.refl
      · exact (reachable_iff_exists_isWeightedPath (edges := f2_edges) (source := f2_v1) (target := f2_v2)).mpr ⟨[f2_e1], isWeightedPath_singleton_of_mem (edges := f2_edges) (e := f2_e1) (by simp [f2_edges])⟩
  have hst2 : (toDirectedAdjacency f2_edges).Reachable f2_v0 f2_v2 :=
    (reachable_iff_exists_isWeightedPath (edges := f2_edges) (source := f2_v0) (target := f2_v2)).mpr ⟨[f2_e0, f2_e1], isWeightedPath_pair_of_mem (edges := f2_edges) (e1 := f2_e0) (e2 := f2_e1) (by simp [f2_edges]) (by simp [f2_edges]) rfl⟩
  obtain ⟨τ, hτdef, hτfeas, hτs0, hτtT⟩ :=
    earliestSchedule_feasible hnn2 hcover2 hst2 hf hT
  obtain ⟨σ, hσdef, hσfeas, hσtT, _hle⟩ :=
    latestSchedule_feasible hnn2 hcover2 hst2 hf hr hT
  have hmem0 : f2_e0 ∈ f2_edges := by simp [f2_edges]
  have hv1 : IsModelEvent f2_edges f2_v0 f2_v2 f2_v1 :=
    Or.inr (Or.inr ⟨f2_e0, hmem0, Or.inr rfl⟩)
  have hτ1 : τ f2_v1 = 5 := by
    have h1 := hτdef f2_v1 hv1; rw [hES1] at h1; exact (Option.some_inj.mp h1).symm
  have hσ0 : σ f2_v0 = 0 := by
    have h0 := hσdef f2_v0 (Or.inl rfl); rw [hLS0] at h0; exact (Option.some_inj.mp h0).symm
  have hσ1 : σ f2_v1 = 5 := by
    have h1 := hσdef f2_v1 hv1; rw [hLS1] at h1; exact (Option.some_inj.mp h1).symm
  have hσ2 : σ f2_v2 = 10 := hσtT
  have hdom : 5 ≤ τ f2_v1 :=
    feasible_dominates_earliest hf τ hτfeas f2_v1 5 hES1
  have hml : 10 ≤ τ f2_v2 :=
    makespan_le_completion hf hT τ hτfeas
  have hfin : τ f2_v1 ≤ τ f2_v2 :=
    feasible_activity_finishes_by_sink hnn2 hcover2 τ hτfeas f2_e0 hmem0
  exact ⟨τ, σ, hτs0, hτ1, hτtT, hσ0, hσ1, hσ2, hτfeas, hσfeas, hdom, hml, hfin⟩

-- Fixture 3: ties and zero dummies, n = 5,
-- [0 → 1 (3), 0 → 2 (3), 1 → 3 (0), 2 → 3 (0), 3 → 4 (2)], s = 0, t = 4.

def f3_v0 : Fin 5 := ⟨0, by decide⟩
def f3_v1 : Fin 5 := ⟨1, by decide⟩
def f3_v2 : Fin 5 := ⟨2, by decide⟩
def f3_v3 : Fin 5 := ⟨3, by decide⟩
def f3_v4 : Fin 5 := ⟨4, by decide⟩
def f3_e0 : Edge 5 := { source := f3_v0, target := f3_v1, weight := 3 }
def f3_e1 : Edge 5 := { source := f3_v0, target := f3_v2, weight := 3 }
def f3_e2 : Edge 5 := { source := f3_v1, target := f3_v3, weight := 0 }
def f3_e3 : Edge 5 := { source := f3_v2, target := f3_v3, weight := 0 }
def f3_e4 : Edge 5 := { source := f3_v3, target := f3_v4, weight := 2 }
def f3_edges : List (Edge 5) := [f3_e0, f3_e1, f3_e2, f3_e3, f3_e4]
def f3_pot : Fin 5 → Int := fun v => if v.val = 0 then 0 else if v.val = 1 then 3 else if v.val = 2 then 3 else if v.val = 3 then 3 else 5

private theorem f3_hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency f3_edges) := by
  apply isAcyclic_of_forall_mem_val_lt; intro e hem
  simp only [f3_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl | rfl | rfl | rfl | rfl := hem
  · decide
  · decide
  · decide
  · decide
  · decide

private theorem f3_hedge : ∀ e ∈ f3_edges, f3_pot e.source + e.weight ≤ f3_pot e.target := by
  intro e hem; simp only [f3_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl | rfl | rfl | rfl | rfl := hem
  · decide
  · decide
  · decide
  · decide
  · decide

example : ∃ result, (DAGShortestPaths.dagShortestPaths (negEdges f3_edges) f3_v0).ret = .ok result :=
  forward_run_ok f3_edges f3_v0 f3_hacyc
example : ∃ result, (DAGShortestPaths.dagShortestPaths (revNegEdges f3_edges) f3_v4).ret = .ok result :=
  reversed_run_ok f3_edges f3_v4 f3_hacyc
example (forward : Distances 5) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f3_edges) f3_v0).ret = .ok forward) :
    earliestStart forward f3_v0 = some 0 := by
  apply (earliestStart_spec hf f3_v0 0).mpr; refine ⟨⟨[], by simp [IsWeightedPath], rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f3_hedge hp
  have hred : f3_pot f3_v0 - f3_pot f3_v0 = 0 := rfl; omega
example (forward : Distances 5) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f3_edges) f3_v0).ret = .ok forward) :
    earliestStart forward f3_v1 = some 3 := by
  apply (earliestStart_spec hf f3_v1 3).mpr
  refine ⟨⟨[f3_e0], isWeightedPath_singleton_of_mem (edges := f3_edges) (e := f3_e0) (by simp [f3_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f3_hedge hp
  have hred : f3_pot f3_v1 - f3_pot f3_v0 = 3 := rfl; omega
example (forward : Distances 5) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f3_edges) f3_v0).ret = .ok forward) :
    earliestStart forward f3_v2 = some 3 := by
  apply (earliestStart_spec hf f3_v2 3).mpr
  refine ⟨⟨[f3_e1], isWeightedPath_singleton_of_mem (edges := f3_edges) (e := f3_e1) (by simp [f3_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f3_hedge hp
  have hred : f3_pot f3_v2 - f3_pot f3_v0 = 3 := rfl; omega
example (forward : Distances 5) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f3_edges) f3_v0).ret = .ok forward) :
    earliestStart forward f3_v3 = some 3 := by
  apply (earliestStart_spec hf f3_v3 3).mpr
  refine ⟨⟨[f3_e0, f3_e2], isWeightedPath_pair_of_mem (edges := f3_edges) (e1 := f3_e0) (e2 := f3_e2) (by simp [f3_edges]) (by simp [f3_edges]) rfl, rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f3_hedge hp
  have hred : f3_pot f3_v3 - f3_pot f3_v0 = 3 := rfl; omega
example (forward : Distances 5) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f3_edges) f3_v0).ret = .ok forward) :
    earliestStart forward f3_v4 = some 5 := by
  apply (earliestStart_spec hf f3_v4 5).mpr
  refine ⟨⟨[f3_e0, f3_e2, f3_e4], isWeightedPath_triple_of_mem (edges := f3_edges) (e1 := f3_e0) (e2 := f3_e2) (e3 := f3_e4) (by simp [f3_edges]) (by simp [f3_edges]) (by simp [f3_edges]) rfl rfl, rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f3_hedge hp
  have hred : f3_pot f3_v4 - f3_pot f3_v0 = 5 := rfl; omega
example (reverse : Distances 5) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f3_edges) f3_v4).ret = .ok reverse) :
    longestToSink reverse f3_v0 = some 5 := by
  apply (longestToSink_spec hr f3_v0 5).mpr
  refine ⟨⟨[f3_e0, f3_e2, f3_e4], isWeightedPath_triple_of_mem (edges := f3_edges) (e1 := f3_e0) (e2 := f3_e2) (e3 := f3_e4) (by simp [f3_edges]) (by simp [f3_edges]) (by simp [f3_edges]) rfl rfl, rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f3_hedge hp
  have hred : f3_pot f3_v4 - f3_pot f3_v0 = 5 := rfl; omega
example (reverse : Distances 5) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f3_edges) f3_v4).ret = .ok reverse) :
    longestToSink reverse f3_v1 = some 2 := by
  apply (longestToSink_spec hr f3_v1 2).mpr
  refine ⟨⟨[f3_e2, f3_e4], isWeightedPath_pair_of_mem (edges := f3_edges) (e1 := f3_e2) (e2 := f3_e4) (by simp [f3_edges]) (by simp [f3_edges]) rfl, rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f3_hedge hp
  have hred : f3_pot f3_v4 - f3_pot f3_v1 = 2 := rfl; omega
example (reverse : Distances 5) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f3_edges) f3_v4).ret = .ok reverse) :
    longestToSink reverse f3_v2 = some 2 := by
  apply (longestToSink_spec hr f3_v2 2).mpr
  refine ⟨⟨[f3_e3, f3_e4], isWeightedPath_pair_of_mem (edges := f3_edges) (e1 := f3_e3) (e2 := f3_e4) (by simp [f3_edges]) (by simp [f3_edges]) rfl, rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f3_hedge hp
  have hred : f3_pot f3_v4 - f3_pot f3_v2 = 2 := rfl; omega
example (reverse : Distances 5) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f3_edges) f3_v4).ret = .ok reverse) :
    longestToSink reverse f3_v3 = some 2 := by
  apply (longestToSink_spec hr f3_v3 2).mpr
  refine ⟨⟨[f3_e4], isWeightedPath_singleton_of_mem (edges := f3_edges) (e := f3_e4) (by simp [f3_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f3_hedge hp
  have hred : f3_pot f3_v4 - f3_pot f3_v3 = 2 := rfl; omega
example (reverse : Distances 5) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f3_edges) f3_v4).ret = .ok reverse) :
    longestToSink reverse f3_v4 = some 0 := by
  apply (longestToSink_spec hr f3_v4 0).mpr; refine ⟨⟨[], by simp [IsWeightedPath], rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f3_hedge hp
  have hred : f3_pot f3_v4 - f3_pot f3_v4 = 0 := rfl; omega
example (forward : Distances 5) (hES : earliestStart forward f3_v4 = some 5) : makespan forward f3_v4 = some 5 := hES
example (forward reverse : Distances 5) (hT : makespan forward f3_v4 = some 5) (ha : earliestStart forward f3_v0 = some 0) (hb : longestToSink reverse f3_v0 = some 5) :
    slackAt (makespan forward f3_v4) forward reverse f3_v0 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f3_v4 = some 5) (ha : earliestStart forward f3_v1 = some 3) (hb : longestToSink reverse f3_v1 = some 2) :
    slackAt (makespan forward f3_v4) forward reverse f3_v1 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f3_v4 = some 5) (ha : earliestStart forward f3_v2 = some 3) (hb : longestToSink reverse f3_v2 = some 2) :
    slackAt (makespan forward f3_v4) forward reverse f3_v2 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f3_v4 = some 5) (ha : earliestStart forward f3_v3 = some 3) (hb : longestToSink reverse f3_v3 = some 2) :
    slackAt (makespan forward f3_v4) forward reverse f3_v3 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f3_v4 = some 5) (ha : earliestStart forward f3_v4 = some 5) (hb : longestToSink reverse f3_v4 = some 0) :
    slackAt (makespan forward f3_v4) forward reverse f3_v4 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f3_v4 = some 5) (ha : earliestStart forward f3_e0.source = some 0) (hb : longestToSink reverse f3_e0.target = some 2) :
    floatAt (makespan forward f3_v4) forward reverse f3_e0 = some 0 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f3_v4 = some 5) (ha : earliestStart forward f3_e1.source = some 0) (hb : longestToSink reverse f3_e1.target = some 2) :
    floatAt (makespan forward f3_v4) forward reverse f3_e1 = some 0 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f3_v4 = some 5) (ha : earliestStart forward f3_e2.source = some 3) (hb : longestToSink reverse f3_e2.target = some 2) :
    floatAt (makespan forward f3_v4) forward reverse f3_e2 = some 0 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f3_v4 = some 5) (ha : earliestStart forward f3_e3.source = some 3) (hb : longestToSink reverse f3_e3.target = some 2) :
    floatAt (makespan forward f3_v4) forward reverse f3_e3 = some 0 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f3_v4 = some 5) (ha : earliestStart forward f3_e4.source = some 3) (hb : longestToSink reverse f3_e4.target = some 0) :
    floatAt (makespan forward f3_v4) forward reverse f3_e4 = some 0 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl

-- Fixture 4: uncovered dangling, n = 5,
-- [0 → 1 (2), 1 → 2 (2), 0 → 3 (7), 4 → 2 (9)], s = 0, t = 2.

def f4_v0 : Fin 5 := ⟨0, by decide⟩
def f4_v1 : Fin 5 := ⟨1, by decide⟩
def f4_v2 : Fin 5 := ⟨2, by decide⟩
def f4_v3 : Fin 5 := ⟨3, by decide⟩
def f4_v4 : Fin 5 := ⟨4, by decide⟩
def f4_e0 : Edge 5 := { source := f4_v0, target := f4_v1, weight := 2 }
def f4_e1 : Edge 5 := { source := f4_v1, target := f4_v2, weight := 2 }
def f4_e2 : Edge 5 := { source := f4_v0, target := f4_v3, weight := 7 }
def f4_e3 : Edge 5 := { source := f4_v4, target := f4_v2, weight := 9 }
def f4_edges : List (Edge 5) := [f4_e0, f4_e1, f4_e2, f4_e3]
def f4_potES : Fin 5 → Int := fun v => if v.val = 0 then 0 else if v.val = 1 then 2 else if v.val = 2 then 4 else if v.val = 3 then 7 else -5
def f4_potLT : Fin 5 → Int := fun v => if v.val = 0 then -4 else if v.val = 1 then -2 else if v.val = 2 then 0 else if v.val = 3 then 3 else -9
/-- Custom vertex rank for `f4_edges`: 4 first, then 0, 1, 3, 2. -/
def f4_rank : Fin 5 → Nat := fun v => if v.val = 4 then 0 else if v.val = 0 then 1 else if v.val = 1 then 2 else if v.val = 3 then 3 else 4

private theorem f4_hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency f4_edges) := by
  apply isAcyclic_of_forall_mem_rank_lt (rank := f4_rank); intro e hem
  simp only [f4_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl | rfl | rfl | rfl := hem
  · decide
  · decide
  · decide
  · decide

private theorem f4_hedgeES : ∀ e ∈ f4_edges, f4_potES e.source + e.weight ≤ f4_potES e.target := by
  intro e hem; simp only [f4_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl | rfl | rfl | rfl := hem
  · decide
  · decide
  · decide
  · decide

private theorem f4_hedgeLT : ∀ e ∈ f4_edges, f4_potLT e.source + e.weight ≤ f4_potLT e.target := by
  intro e hem; simp only [f4_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl | rfl | rfl | rfl := hem
  · decide
  · decide
  · decide
  · decide

example : ∃ result, (DAGShortestPaths.dagShortestPaths (negEdges f4_edges) f4_v0).ret = .ok result :=
  forward_run_ok f4_edges f4_v0 f4_hacyc
example : ∃ result, (DAGShortestPaths.dagShortestPaths (revNegEdges f4_edges) f4_v2).ret = .ok result :=
  reversed_run_ok f4_edges f4_v2 f4_hacyc
example (forward : Distances 5) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f4_edges) f4_v0).ret = .ok forward) :
    earliestStart forward f4_v0 = some 0 := by
  apply (earliestStart_spec hf f4_v0 0).mpr; refine ⟨⟨[], by simp [IsWeightedPath], rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f4_hedgeES hp
  have hred : f4_potES f4_v0 - f4_potES f4_v0 = 0 := rfl; omega
example (forward : Distances 5) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f4_edges) f4_v0).ret = .ok forward) :
    earliestStart forward f4_v1 = some 2 := by
  apply (earliestStart_spec hf f4_v1 2).mpr
  refine ⟨⟨[f4_e0], isWeightedPath_singleton_of_mem (edges := f4_edges) (e := f4_e0) (by simp [f4_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f4_hedgeES hp
  have hred : f4_potES f4_v1 - f4_potES f4_v0 = 2 := rfl; omega
example (forward : Distances 5) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f4_edges) f4_v0).ret = .ok forward) :
    earliestStart forward f4_v2 = some 4 := by
  apply (earliestStart_spec hf f4_v2 4).mpr
  refine ⟨⟨[f4_e0, f4_e1], isWeightedPath_pair_of_mem (edges := f4_edges) (e1 := f4_e0) (e2 := f4_e1) (by simp [f4_edges]) (by simp [f4_edges]) rfl, rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f4_hedgeES hp
  have hred : f4_potES f4_v2 - f4_potES f4_v0 = 4 := rfl; omega
example (forward : Distances 5) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f4_edges) f4_v0).ret = .ok forward) :
    earliestStart forward f4_v3 = some 7 := by
  apply (earliestStart_spec hf f4_v3 7).mpr
  refine ⟨⟨[f4_e2], isWeightedPath_singleton_of_mem (edges := f4_edges) (e := f4_e2) (by simp [f4_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f4_hedgeES hp
  have hred : f4_potES f4_v3 - f4_potES f4_v0 = 7 := rfl; omega
example (forward : Distances 5) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f4_edges) f4_v0).ret = .ok forward) :
    earliestStart forward f4_v4 = none := by
  apply (earliestStart_eq_none_iff hf f4_v4).mpr; intro hreach
  obtain ⟨p, hp⟩ := reachable_iff_exists_isWeightedPath.mp hreach
  have hP0 : f4_v0 ≠ f4_v4 := by decide
  have hPstep : ∀ e ∈ f4_edges, e.source ≠ f4_v4 → e.target ≠ f4_v4 := by
    intro e hem; simp only [f4_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
    obtain rfl | rfl | rfl | rfl := hem
    · intro _; decide
    · intro _; decide
    · intro _; decide
    · intro _; decide
  have hPv : ¬f4_v4 ≠ f4_v4 := by decide
  exact hPv (path_invariant (fun w => w ≠ f4_v4) hPstep hP0 hp)
example (reverse : Distances 5) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f4_edges) f4_v2).ret = .ok reverse) :
    longestToSink reverse f4_v0 = some 4 := by
  apply (longestToSink_spec hr f4_v0 4).mpr
  refine ⟨⟨[f4_e0, f4_e1], isWeightedPath_pair_of_mem (edges := f4_edges) (e1 := f4_e0) (e2 := f4_e1) (by simp [f4_edges]) (by simp [f4_edges]) rfl, rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f4_hedgeLT hp
  have hred : f4_potLT f4_v2 - f4_potLT f4_v0 = 4 := rfl; omega
example (reverse : Distances 5) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f4_edges) f4_v2).ret = .ok reverse) :
    longestToSink reverse f4_v1 = some 2 := by
  apply (longestToSink_spec hr f4_v1 2).mpr
  refine ⟨⟨[f4_e1], isWeightedPath_singleton_of_mem (edges := f4_edges) (e := f4_e1) (by simp [f4_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f4_hedgeLT hp
  have hred : f4_potLT f4_v2 - f4_potLT f4_v1 = 2 := rfl; omega
example (reverse : Distances 5) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f4_edges) f4_v2).ret = .ok reverse) :
    longestToSink reverse f4_v2 = some 0 := by
  apply (longestToSink_spec hr f4_v2 0).mpr; refine ⟨⟨[], by simp [IsWeightedPath], rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f4_hedgeLT hp
  have hred : f4_potLT f4_v2 - f4_potLT f4_v2 = 0 := rfl; omega
example (reverse : Distances 5) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f4_edges) f4_v2).ret = .ok reverse) :
    longestToSink reverse f4_v3 = none := by
  apply (longestToSink_eq_none_iff hr f4_v3).mpr; intro hreach
  obtain ⟨p, hp⟩ := reachable_iff_exists_isWeightedPath.mp hreach
  have hP0 : f4_v3 = f4_v3 := rfl
  have hPstep : ∀ e ∈ f4_edges, e.source = f4_v3 → e.target = f4_v3 := by
    intro e hem; simp only [f4_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
    obtain rfl | rfl | rfl | rfl := hem
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
  have hPv : ¬f4_v2 = f4_v3 := by decide
  exact hPv (path_invariant (fun w => w = f4_v3) hPstep hP0 hp)
example (reverse : Distances 5) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f4_edges) f4_v2).ret = .ok reverse) :
    longestToSink reverse f4_v4 = some 9 := by
  apply (longestToSink_spec hr f4_v4 9).mpr
  refine ⟨⟨[f4_e3], isWeightedPath_singleton_of_mem (edges := f4_edges) (e := f4_e3) (by simp [f4_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f4_hedgeLT hp
  have hred : f4_potLT f4_v2 - f4_potLT f4_v4 = 9 := rfl; omega
example (forward : Distances 5) (hES : earliestStart forward f4_v2 = some 4) : makespan forward f4_v2 = some 4 := hES
example (forward reverse : Distances 5) (hT : makespan forward f4_v2 = some 4) (ha : earliestStart forward f4_v0 = some 0) (hb : longestToSink reverse f4_v0 = some 4) :
    slackAt (makespan forward f4_v2) forward reverse f4_v0 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f4_v2 = some 4) (ha : earliestStart forward f4_v1 = some 2) (hb : longestToSink reverse f4_v1 = some 2) :
    slackAt (makespan forward f4_v2) forward reverse f4_v1 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f4_v2 = some 4) (ha : earliestStart forward f4_v2 = some 4) (hb : longestToSink reverse f4_v2 = some 0) :
    slackAt (makespan forward f4_v2) forward reverse f4_v2 = some 0 := by
  unfold slackAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f4_v2 = some 4) (ha : earliestStart forward f4_v3 = some 7) (hn : longestToSink reverse f4_v3 = none) :
    slackAt (makespan forward f4_v2) forward reverse f4_v3 = none := by
  unfold slackAt latestStartAt; rw [hT, ha, hn]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f4_v2 = some 4) (hn : earliestStart forward f4_v4 = none) (hb : longestToSink reverse f4_v4 = some 9) :
    slackAt (makespan forward f4_v2) forward reverse f4_v4 = none := by
  unfold slackAt latestStartAt; rw [hT, hn, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f4_v2 = some 4) (ha : earliestStart forward f4_e0.source = some 0) (hb : longestToSink reverse f4_e0.target = some 2) :
    floatAt (makespan forward f4_v2) forward reverse f4_e0 = some 0 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f4_v2 = some 4) (ha : earliestStart forward f4_e1.source = some 2) (hb : longestToSink reverse f4_e1.target = some 0) :
    floatAt (makespan forward f4_v2) forward reverse f4_e1 = some 0 := by
  unfold floatAt latestStartAt; rw [hT, ha, hb]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f4_v2 = some 4) (ha : earliestStart forward f4_e2.source = some 0) (hn : longestToSink reverse f4_e2.target = none) :
    floatAt (makespan forward f4_v2) forward reverse f4_e2 = none := by
  unfold floatAt latestStartAt; rw [hT, ha, hn]; rfl
example (forward reverse : Distances 5) (hT : makespan forward f4_v2 = some 4) (hn : earliestStart forward f4_e3.source = none) (hb : longestToSink reverse f4_e3.target = some 0) :
    floatAt (makespan forward f4_v2) forward reverse f4_e3 = none := by
  unfold floatAt latestStartAt; rw [hT, hn, hb]; rfl
example (forward reverse : Distances 5) (ha : earliestStart forward f4_e0.source = some 0) (hb : longestToSink reverse f4_e0.target = some 2) :
    ¬isOrphan forward reverse f4_e0 := by
  unfold isOrphan; rintro (h | h)
  · simp [ha] at h
  · simp [hb] at h
example (forward reverse : Distances 5) (ha : earliestStart forward f4_e1.source = some 2) (hb : longestToSink reverse f4_e1.target = some 0) :
    ¬isOrphan forward reverse f4_e1 := by
  unfold isOrphan; rintro (h | h)
  · simp [ha] at h
  · simp [hb] at h
example (forward reverse : Distances 5) (hn : longestToSink reverse f4_e2.target = none) :
    isOrphan forward reverse f4_e2 := by
  unfold isOrphan; exact Or.inr hn
example (forward reverse : Distances 5) (hn : earliestStart forward f4_e3.source = none) :
    isOrphan forward reverse f4_e3 := by
  unfold isOrphan; exact Or.inl hn

-- The uncovered fixture needs sink time 9, above the makespan 4.
def f4_sched : Fin 5 → Int := fun v => if v.val = 0 then 0 else if v.val = 1 then 2 else if v.val = 2 then 9 else if v.val = 3 then 7 else 0

private theorem f4_sched_feasible : IsFeasibleSchedule f4_edges f4_v0 f4_v2 f4_sched := by
  unfold IsFeasibleSchedule; refine ⟨?_, ?_⟩
  · intro v hv; unfold IsModelEvent at hv
    obtain rfl | rfl | ⟨e, hem, he⟩ := hv
    · decide
    · decide
    · simp only [f4_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
      obtain rfl | rfl | rfl | rfl := hem
      · obtain rfl | rfl := he
        · decide
        · decide
      · obtain rfl | rfl := he
        · decide
        · decide
      · obtain rfl | rfl := he
        · decide
        · decide
      · obtain rfl | rfl := he
        · decide
        · decide
  · intro e hem; simp only [f4_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
    obtain rfl | rfl | rfl | rfl := hem
    · decide
    · decide
    · decide
    · decide

example : IsFeasibleSchedule f4_edges f4_v0 f4_v2 f4_sched ∧ f4_sched f4_v2 = 9 :=
  ⟨f4_sched_feasible, rfl⟩

example (τ : Fin 5 → Int) (hτ : IsFeasibleSchedule f4_edges f4_v0 f4_v2 τ) : 9 ≤ τ f4_v2 := by
  have hmem : f4_e3 ∈ f4_edges := by simp [f4_edges]
  have h4nn : 0 ≤ τ f4_v4 := hτ.1 f4_v4 (Or.inr (Or.inr ⟨f4_e3, hmem, Or.inl rfl⟩))
  have hc : τ f4_e3.source + f4_e3.weight ≤ τ f4_e3.target := hτ.2 f4_e3 hmem
  have hc' : τ f4_v4 + 9 ≤ τ f4_v2 := hc; omega

example (forward : Distances 5) (hT : makespan forward f4_v2 = some 4) :
    ∃ T, makespan forward f4_v2 = some T ∧ T < f4_sched f4_v2 := by
  refine ⟨4, hT, ?_⟩; have hsched : f4_sched f4_v2 = 9 := rfl; omega

-- The lower bounds need no coverage: on the uncovered fixture the makespan 4 still bounds
-- the feasible sink time 9 from below, and the raw earliest start 7 of the dangling event
-- bounds every feasible schedule there.
example (forward : Distances 5)
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges f4_edges) f4_v0).ret = .ok forward)
    (hT : makespan forward f4_v2 = some 4) : 4 ≤ f4_sched f4_v2 :=
  makespan_le_completion hf hT f4_sched f4_sched_feasible
example (forward : Distances 5)
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges f4_edges) f4_v0).ret = .ok forward)
    (hES : earliestStart forward f4_v3 = some 7) (τ : Fin 5 → Int)
    (hτ : IsFeasibleSchedule f4_edges f4_v0 f4_v2 τ) : 7 ≤ τ f4_v3 :=
  feasible_dominates_earliest hf τ hτ f4_v3 7 hES

-- Fixture 5: cyclic input, n = 2, [0 → 1 (1), 1 → 0 (1)]; both runs fail.

def f5_v0 : Fin 2 := ⟨0, by decide⟩
def f5_v1 : Fin 2 := ⟨1, by decide⟩
def f5_e0 : Edge 2 := { source := f5_v0, target := f5_v1, weight := 1 }
def f5_e1 : Edge 2 := { source := f5_v1, target := f5_v0, weight := 1 }
def f5_edges : List (Edge 2) := [f5_e0, f5_e1]

example (r : Distances 2) :
    (DAGShortestPaths.dagShortestPaths (negEdges f5_edges) f5_v0).ret ≠ .ok r := by
  intro hok; have hacyc := (DAGShortestPaths.dagShortestPaths_returns_iff_acyclic _ _).mp ⟨r, hok⟩
  have h01 : (toDirectedAdjacency (negEdges f5_edges)).Edge f5_v0 f5_v1 := by
    rw [edge_toDirectedAdjacency_iff]
    refine ⟨{ source := f5_v0, target := f5_v1, weight := (-1 : Int) }, ?_, rfl, rfl⟩
    refine List.mem_map.mpr ⟨f5_e0, ?_, ?_⟩; simp [f5_edges]; rfl
  have h10 : (toDirectedAdjacency (negEdges f5_edges)).Edge f5_v1 f5_v0 := by
    rw [edge_toDirectedAdjacency_iff]
    refine ⟨{ source := f5_v1, target := f5_v0, weight := (-1 : Int) }, ?_, rfl, rfl⟩
    refine List.mem_map.mpr ⟨f5_e1, ?_, ?_⟩; simp [f5_edges]; rfl
  have h01ne : f5_v0 ≠ f5_v1 := by decide
  have hnodup : List.Nodup [f5_v0, f5_v1] :=
    List.nodup_cons.mpr ⟨fun h => h01ne (List.mem_singleton.mp h), List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
  have hchain : ([f5_v0, f5_v1].IsChain (toDirectedAdjacency (negEdges f5_edges)).Edge) := by
    simp only [List.isChain_cons_cons]; refine ⟨h01, by simp⟩
  have hne : [f5_v0, f5_v1] ≠ [] := by decide
  have hclose : (toDirectedAdjacency (negEdges f5_edges)).Edge ([f5_v0, f5_v1].getLast hne) ([f5_v0, f5_v1].head hne) := h10
  have hmem : ∀ v ∈ [f5_v0, f5_v1], v ∈ (toDirectedAdjacency (negEdges f5_edges)).vertices := by
    intro v _; exact (toDirectedAdjacency (negEdges f5_edges)).vertices_complete v
  exact hacyc ⟨[f5_v0, f5_v1], (TopologicalSort.directedCycleIn_iff _ _ _).mpr ⟨hne, hnodup, hchain, hclose, hmem⟩⟩

example (r : Distances 2) :
    (DAGShortestPaths.dagShortestPaths (revNegEdges f5_edges) f5_v1).ret ≠ .ok r := by
  intro hok; have hacyc := (DAGShortestPaths.dagShortestPaths_returns_iff_acyclic _ _).mp ⟨r, hok⟩
  have h01 : (toDirectedAdjacency (revNegEdges f5_edges)).Edge f5_v0 f5_v1 := by
    rw [edge_toDirectedAdjacency_iff]
    refine ⟨{ source := f5_v0, target := f5_v1, weight := (-1 : Int) }, ?_, rfl, rfl⟩
    refine List.mem_map.mpr ⟨f5_e1, ?_, ?_⟩; simp [f5_edges]; rfl
  have h10 : (toDirectedAdjacency (revNegEdges f5_edges)).Edge f5_v1 f5_v0 := by
    rw [edge_toDirectedAdjacency_iff]
    refine ⟨{ source := f5_v1, target := f5_v0, weight := (-1 : Int) }, ?_, rfl, rfl⟩
    refine List.mem_map.mpr ⟨f5_e0, ?_, ?_⟩; simp [f5_edges]; rfl
  have h01ne : f5_v0 ≠ f5_v1 := by decide
  have hnodup : List.Nodup [f5_v0, f5_v1] :=
    List.nodup_cons.mpr ⟨fun h => h01ne (List.mem_singleton.mp h), List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩⟩
  have hchain : ([f5_v0, f5_v1].IsChain (toDirectedAdjacency (revNegEdges f5_edges)).Edge) := by
    simp only [List.isChain_cons_cons]; refine ⟨h01, by simp⟩
  have hne : [f5_v0, f5_v1] ≠ [] := by decide
  have hclose : (toDirectedAdjacency (revNegEdges f5_edges)).Edge ([f5_v0, f5_v1].getLast hne) ([f5_v0, f5_v1].head hne) := h10
  have hmem : ∀ v ∈ [f5_v0, f5_v1], v ∈ (toDirectedAdjacency (revNegEdges f5_edges)).vertices := by
    intro v _; exact (toDirectedAdjacency (revNegEdges f5_edges)).vertices_complete v
  exact hacyc ⟨[f5_v0, f5_v1], (TopologicalSort.directedCycleIn_iff _ _ _).mpr ⟨hne, hnodup, hchain, hclose, hmem⟩⟩

-- Fixture 6: source equals sink, n = 2, [0 → 1 (4)], s = t = 0.

def f6_v0 : Fin 2 := ⟨0, by decide⟩
def f6_v1 : Fin 2 := ⟨1, by decide⟩
def f6_e0 : Edge 2 := { source := f6_v0, target := f6_v1, weight := 4 }
def f6_edges : List (Edge 2) := [f6_e0]
def f6_pot : Fin 2 → Int := fun v => if v.val = 0 then 0 else 4

private theorem f6_hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency f6_edges) := by
  apply isAcyclic_of_forall_mem_val_lt; intro e hem
  simp only [f6_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl := hem; decide

private theorem f6_hedge : ∀ e ∈ f6_edges, f6_pot e.source + e.weight ≤ f6_pot e.target := by
  intro e hem; simp only [f6_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl := hem; decide

example : ∃ result, (DAGShortestPaths.dagShortestPaths (negEdges f6_edges) f6_v0).ret = .ok result :=
  forward_run_ok f6_edges f6_v0 f6_hacyc
example : ∃ result, (DAGShortestPaths.dagShortestPaths (revNegEdges f6_edges) f6_v0).ret = .ok result :=
  reversed_run_ok f6_edges f6_v0 f6_hacyc
example (forward : Distances 2) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f6_edges) f6_v0).ret = .ok forward) :
    earliestStart forward f6_v0 = some 0 := by
  apply (earliestStart_spec hf f6_v0 0).mpr; refine ⟨⟨[], by simp [IsWeightedPath], rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f6_hedge hp
  have hred : f6_pot f6_v0 - f6_pot f6_v0 = 0 := rfl; omega
example (forward : Distances 2) (hES : earliestStart forward f6_v0 = some 0) : makespan forward f6_v0 = some 0 := hES
example (reverse : Distances 2) (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges f6_edges) f6_v0).ret = .ok reverse) :
    longestToSink reverse f6_v1 = none := by
  apply (longestToSink_eq_none_iff hr f6_v1).mpr; intro hreach
  obtain ⟨p, hp⟩ := reachable_iff_exists_isWeightedPath.mp hreach
  have hP0 : f6_v1 = f6_v1 := rfl
  have hPstep : ∀ e ∈ f6_edges, e.source = f6_v1 → e.target = f6_v1 := by
    intro e hem; simp only [f6_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
    obtain rfl := hem; intro h; exact absurd h (by decide)
  have hPv : ¬f6_v0 = f6_v1 := by decide
  exact hPv (path_invariant (fun w => w = f6_v1) hPstep hP0 hp)
example (forward reverse : Distances 2) (hn : longestToSink reverse f6_e0.target = none) :
    isOrphan forward reverse f6_e0 := by
  unfold isOrphan; exact Or.inr hn

-- Fixture 7: negative duration, n = 3, [0 → 1 (-3), 1 → 2 (5)], s = 0.

def f7_v0 : Fin 3 := ⟨0, by decide⟩
def f7_v1 : Fin 3 := ⟨1, by decide⟩
def f7_v2 : Fin 3 := ⟨2, by decide⟩
def f7_e0 : Edge 3 := { source := f7_v0, target := f7_v1, weight := -3 }
def f7_e1 : Edge 3 := { source := f7_v1, target := f7_v2, weight := 5 }
def f7_edges : List (Edge 3) := [f7_e0, f7_e1]
def f7_pot : Fin 3 → Int := fun v => if v.val = 0 then 0 else if v.val = 1 then -3 else 2

private theorem f7_hacyc : TopologicalSort.IsAcyclic (toDirectedAdjacency f7_edges) := by
  apply isAcyclic_of_forall_mem_val_lt; intro e hem
  simp only [f7_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl | rfl := hem
  · decide
  · decide

private theorem f7_hedge : ∀ e ∈ f7_edges, f7_pot e.source + e.weight ≤ f7_pot e.target := by
  intro e hem; simp only [f7_edges, List.mem_cons, List.not_mem_nil, or_false] at hem
  obtain rfl | rfl := hem
  · decide
  · decide

example : ∃ result, (DAGShortestPaths.dagShortestPaths (negEdges f7_edges) f7_v0).ret = .ok result :=
  forward_run_ok f7_edges f7_v0 f7_hacyc
example (forward : Distances 3) (hf : (DAGShortestPaths.dagShortestPaths (negEdges f7_edges) f7_v0).ret = .ok forward) :
    earliestStart forward f7_v1 = some (-3) := by
  apply (earliestStart_spec hf f7_v1 (-3)).mpr
  refine ⟨⟨[f7_e0], isWeightedPath_singleton_of_mem (edges := f7_edges) (e := f7_e0) (by simp [f7_edges]), rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f7_hedge hp
  have hred : f7_pot f7_v1 - f7_pot f7_v0 = -3 := rfl; omega
-- The all-nonnegative hypothesis fails on this edge list.
example : ¬∀ e ∈ f7_edges, 0 ≤ e.weight := by
  intro h; have h0 : (0 : Int) ≤ f7_e0.weight := h f7_e0 (by simp [f7_edges])
  have hw : f7_e0.weight = -3 := rfl; omega

-- Nor nonnegative durations: with sink `2` the makespan is the longest path weight `2`, a
-- lower bound on every feasible sink time, while every feasible schedule puts the sink at `5`
-- or later, since the negative arc cannot pull event `1` below time `0`.
example (forward : Distances 3)
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges f7_edges) f7_v0).ret = .ok forward) :
    earliestStart forward f7_v2 = some 2 := by
  apply (earliestStart_spec hf f7_v2 2).mpr
  refine ⟨⟨[f7_e0, f7_e1], isWeightedPath_pair_of_mem (edges := f7_edges) (e1 := f7_e0)
    (e2 := f7_e1) (by simp [f7_edges]) (by simp [f7_edges]) rfl, rfl⟩, ?_⟩
  intro p hp; have hle := pathWeight_le_pot f7_hedge hp
  have hred : f7_pot f7_v2 - f7_pot f7_v0 = 2 := rfl; omega
example (forward : Distances 3)
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges f7_edges) f7_v0).ret = .ok forward)
    (hT : makespan forward f7_v2 = some 2) (τ : Fin 3 → Int)
    (hτ : IsFeasibleSchedule f7_edges f7_v0 f7_v2 τ) : 2 ≤ τ f7_v2 :=
  makespan_le_completion hf hT τ hτ
example (τ : Fin 3 → Int) (hτ : IsFeasibleSchedule f7_edges f7_v0 f7_v2 τ) : 5 ≤ τ f7_v2 := by
  have hmem : f7_e1 ∈ f7_edges := by simp [f7_edges]
  have h1nn : 0 ≤ τ f7_v1 := hτ.1 f7_v1 (Or.inr (Or.inr ⟨f7_e1, hmem, Or.inl rfl⟩))
  have hc : τ f7_e1.source + f7_e1.weight ≤ τ f7_e1.target := hτ.2 f7_e1 hmem
  have hc' : τ f7_v1 + 5 ≤ τ f7_v2 := hc; omega

-- C9 signature checks: each proof term is exactly a production theorem.

example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n}
    (hcover : IsCovered edges s t)
    (hst : (toDirectedAdjacency edges).Reachable s t)
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hr : (DAGShortestPaths.dagShortestPaths (revNegEdges edges) t).ret = .ok reverse)
    (v : Fin n) (hv : IsModelEvent edges s t v) :
    (∃ a, earliestStart forward v = some a) ∧
      ∃ b, longestToSink reverse v = some b :=
  raw_defined_on_modelEvents hcover hst hf hr v hv
example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward : Distances n} {T : Int}
    (hnn : ∀ e ∈ edges, 0 ≤ e.weight)
    (hcover : IsCovered edges s t)
    (hst : (toDirectedAdjacency edges).Reachable s t)
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hT : makespan forward t = some T) :
    ∃ τ : Fin n → Int,
      (∀ v, IsModelEvent edges s t v → earliestStart forward v = some (τ v)) ∧
        IsFeasibleSchedule edges s t τ ∧ τ s = 0 ∧ τ t = T :=
  earliestSchedule_feasible hnn hcover hst hf hT
example {n : Nat} {edges : List (Edge n)} {s t : Fin n} {forward : Distances n}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (τ : Fin n → Int) (hτ : IsFeasibleSchedule edges s t τ)
    (v : Fin n) (a : Int)
    (hes : earliestStart forward v = some a) :
    a ≤ τ v :=
  feasible_dominates_earliest hf τ hτ v a hes
example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward : Distances n} {T : Int}
    (hf : (DAGShortestPaths.dagShortestPaths (negEdges edges) s).ret = .ok forward)
    (hT : makespan forward t = some T)
    (τ : Fin n → Int) (hτ : IsFeasibleSchedule edges s t τ) :
    T ≤ τ t :=
  makespan_le_completion hf hT τ hτ
example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    (hnn : ∀ e ∈ edges, 0 ≤ e.weight)
    (hcover : IsCovered edges s t)
    (τ : Fin n → Int) (hτ : IsFeasibleSchedule edges s t τ)
    (e : Edge n) (hem : e ∈ edges) :
    τ e.target ≤ τ t :=
  feasible_activity_finishes_by_sink hnn hcover τ hτ e hem
example {n : Nat} {edges : List (Edge n)} {s t : Fin n}
    {forward reverse : Distances n} {T : Int}
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
          ∀ v, IsModelEvent edges s t v → τ' v ≤ τ v :=
  latestSchedule_feasible hnn hcover hst hf hr hT

-- Integration: the list-scheduling and critical-path APIs load into one environment, and
-- their makespans are different declarations: the largest machine load of a machine
-- assignment, and the longest source-to-sink path weight read from the forward run.

example : (Cslib.Algorithms.Lean.Scheduling.makespan : (Fin 2 → List ℕ) → ℕ) =
    fun σ => Finset.univ.sup fun i => (σ i).sum := rfl
example : (Cslib.Algorithms.Lean.Scheduling.CriticalPath.makespan :
    Distances 2 → Fin 2 → Option Int) = fun result t => earliestStart result t := rfl

-- Public-name checks for the main definitions and theorems.

#check negEdges
#check revNegEdges
#check earliestStart
#check longestToSink
#check makespan
#check latestStart
#check slack
#check activityFloat
#check latestStartAt
#check slackAt
#check floatAt
#check isOrphan
#check IsCovered
#check IsModelEvent
#check IsFeasibleSchedule
#check forward_run_ok
#check reversed_run_ok
#check earliestStart_spec
#check longestToSink_spec
#check makespan_exists
#check slackAt_spec
#check floatAt_spec
#check coverage_iff_no_orphan
#check raw_defined_on_modelEvents
#check earliestSchedule_feasible
#check feasible_dominates_earliest
#check makespan_le_completion
#check feasible_activity_finishes_by_sink
#check latestSchedule_feasible

end Cslib.Algorithms.Lean.Scheduling.CriticalPath.Tests
