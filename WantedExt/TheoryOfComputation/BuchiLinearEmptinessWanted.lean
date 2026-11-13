/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Büchi emptiness via Kosaraju-Sharir SCC decomposition (abstract transition-count bound)
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.Graph.DepthFirstSearch
public import CSLibExt.Algorithms.Lean.Graph.DepthFirstSearchCosts
public import CSLibExt.Algorithms.Lean.Graph.StronglyConnectedComponents
public import CSLibExt.Computability.Automata.NA.BuchiEmptiness
public import Mathlib.Data.Finset.Card
public import Std.Data.HashSet.Lemmas

@[expose] public section

namespace Cslib.BuchiLinearEmptinessWanted

open Filter ωSequence Cslib.Automata.ωAcceptor
open Cslib.Automata.NA
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.DepthFirstSearch
open Cslib.Algorithms.Lean.StronglyConnectedComponents

/-!
# Büchi emptiness via Kosaraju-Sharir SCC decomposition (abstract transition-count bound)

The phase-1 emptiness test `Buchi.isEmptyB` (`CSLibExt/Computability/Automata/NA/
BuchiEmptiness.lean`) runs `f + 1` fixed-point reachability closures (`f` the number of
reachable accepting states): one closure from all start states, then one cycle closure per
reachable accepting state. The Kosaraju-Sharir replacement is the
strongly-connected-components decomposition (`kosarajuSCCs`): two depth-first
traversals of the symbol-forgetting transition graph — one forward pass to order the
states by decreasing finish time, one backward pass on the reversed graph in that
order — whose DFS trees are exactly the strongly connected components. A Büchi
automaton is nonempty iff some accepting state, reachable from a start state, lies in
a *cyclic* component (a component with at least two distinct states, or a state
with a self-loop).

The emptiness procedure is three DFS passes plus a split and a scanner, with
no reachability oracle and no `O(n³)` closure. `kosarajuSCCs` is a computable
function over the existing `DirectedAdjacency` / `DepthFirstSearch` API (not
a classical chooser): two DFS passes — `dfsAll`, then `dfs` on the transpose
in decreasing finish order — whose trees are the SCCs. Start-reachability is
computed once, by a third DFS from the start states (`startReachable`), and
the scanner (`kosarajuIsEmptyB`) tests SCC blocks against that single visited
set (`startReachableSet`, one `Std.HashSet` construction): a block witnesses
nonemptiness iff it is cyclic and contains one state that is both accepting
and in the visited set. The second-pass trees are extracted by splitting the
second pass's preorder at its forest roots (`splitPreorder`): in a DFS
preorder the vertices of one tree are contiguous and each tree starts with
its root, so one pass with one `Std.HashSet.contains` test (plus one
`List.isEmpty` test) per vertex suffices.

Scope of the cost claim in this file — abstract DFS transition counts plus
costed split/scanner evaluators. The three DFS passes have exactly the
`Internal.Step` transition counts pinned by `buchi_emptiness_dfs_counts`
(`n₁ = 2V + E`, `n₂`, `n₃` from `dfs_exact_steps` / `dfsAll_exact_steps`).
The split and scanner costs are *not* hand-written formulas equated to
existential variables: they are the outputs of instrumented evaluators
that return `(result, cost)` pairs, with proved result-correctness and
cost-bound lemmas. `splitPreorderC` returns the same blocks as
`splitPreorder` (proved `splitPreorderC_fst`) and its cost counts one
hash-table insertion per forest root for the `Std.HashSet.ofList`
construction (`roots.length`, where `roots` is the second pass's
`forestRoots` — not `decreasingFinishAll.length`, which can be `V` when
there is one DFS tree and one root), plus the accumulator's per-step
tests: one `rootsSet.contains` test per preorder vertex, one
`cur.isEmpty` test only when `contains` is true (short-circuit `&&`),
plus one final `cur.isEmpty` test (`splitPreorderC_cost_le`:
`≤ roots.length + 2 * preorder.length + 1`; the combined bound carries the same
`+ 1` for that final test (it is not absorbed by `14V`, which is `0` for the
empty state type). `kosarajuIsEmptyBC` returns
the same `Bool` as `kosarajuIsEmptyB` (proved `kosarajuIsEmptyBC_fst`)
and its cost counts one hash-table insertion per start-reachable vertex
for the visited-set construction, plus per-block/per-state tests: one
length test per block (`blockCyclicBC` short-circuits via `||`: if the
block has length `≥ 2` the self-loop scan is skipped), one accept `decide`
per examined state, one visited-set `contains` test only when accept is
true (short-circuit `&&`), and adjacency-entry scans for self-loop tests
(`listMemC` stops at the first matching entry; `List.any`-style loops stop
at the first `true` block/state). The proved scanner bound is
`kosarajuIsEmptyBC_cost_le`. The combined bound in
`buchi_emptiness_via_kosaraju_wanted` is stated in terms of these
evaluator outputs (not hand-written expressions) plus their proved
bounds; closing it needs the SCC partition (pairwise disjointness +
block `Nodup`, i.e. `kosaraju_correct_wanted`) and arithmetic, which is
wanted. These are counts of abstract machine steps plus hash-table /
adjacency-entry operations in the same cost model as
`DepthFirstSearch` (one unit per hash-table operation or adjacency-entry
scan); they are *not* an end-to-end wall-clock `O(V + E)` bound, because
the abstract model omits the cost of *evaluating* the adjacency functions,
and adjacency here is a function, not a memoized structure: every query
recomputes the list. For the `buchiGraph` instantiation, with `V` the
number of vertices and `S` the number of symbols, one
`buchiGraph.adjacency s` evaluation filters over all `V` vertices, and
each filter test decides `Buchi.Step s t`, i.e. `∃ x, na.Tr s x t`,
by scanning all `S` symbols: `O(V·S)` `Tr` decisions per evaluation
(exactly `V·S` on the empty automaton, where no test short-circuits).
Each DFS pass queries the adjacency list at most once per visited vertex
(`DepthFirstSearch.loop`, discover step), so the forward and
start-reachability passes already cost `O(V²·S)` `Tr` decisions
(`Θ(V²·S)` on the empty automaton), none of it in `n₁` / `n₃`. Worse,
the second pass runs on `DirectedAdjacency.transpose`, whose `adjacency`
function is `graph.vertices.filter fun source => target ∈
graph.adjacency source`: one transpose evaluation re-evaluates the
forward adjacency list of each of the `V` sources (`O(V²·S)` `Tr`
decisions) plus a membership scan per source, and the second DFS
queries up to `V` transpose lists, for `O(V³·S)` `Tr` decisions in
total (`Θ(V³·S)` on the empty automaton). The earlier `Θ(V²)` figure
counted only the transpose's outer filter predicates and missed this
inner re-evaluation. The scanner's self-loop tests re-evaluate
adjacency lists yet again (`hasEdge` / `listMemC` over
`graph.adjacency s`): `c_scan` charges scanning the entries of
produced lists, not producing them. End-to-end linear time would need
materialized forward *and* reverse adjacency built once, and that is
not reachable from this API alone: `na.Tr` is a ternary relation
`State → Symbol → State → Prop`, so a `(state, symbol)` pair does not
enumerate its successors. With only the supplied decision procedure
for `Tr`, materializing either adjacency means testing
`(source, symbol, target)` triples — up to `V²·S` `Tr` decisions —
not `O(V·S)`. `O(V + E)` materialization would need changing the
automaton representation to provide explicit successor lists, so
successors are enumerated rather than tested. Building only a
reverse adjacency on top of on-demand forward lists does *not*
suffice, since each reverse evaluation still re-evaluates the
forward lists. This file builds neither; that is future work, and
the wanted theorem below is stated only about the abstract counts
above. The *correctness* of the
decomposition — that the second-pass trees are exactly the SCCs
(`StronglyConnectedComponents.IsSCCPartition`, including block `Nodup`,
coverage, characterization by mutual reachability, and maximality) — is the
wanted content (`kosaraju_correct_wanted`): it needs the Kosaraju finish-time
lemma (a vertex finishes after every vertex it can reach in the transpose's
DFS order). The bridge from a Büchi automaton to a `DirectedAdjacency` graph (`buchiGraph`, with
`Edge ↔ Buchi.Step` and `Reachable ↔ ReflTransGen Buchi.Step`) is proved and
computable: `buchiGraph` takes the explicit vertex enumeration that
`DirectedAdjacency` already requires, and its adjacency lists are `List.filter`
over that enumeration using the `DecidableRel na.Step` instance imported
from `BuchiEmptiness.lean` (`Fintype Symbol` + decidable `Tr`; its section's
`DecidablePred` hypotheses on `start`/`accept` are not parameters of
that instance, since the construction `∃ x, na.Tr s x t` does not use
them). It does *not* call `Finset.univ.toList`:
that function is `noncomputable` (it goes through `Quot.out`), so an abstract
`Fintype` enumeration cannot be a plain `def` — the enumeration is instead a
parameter, as it is for every `DirectedAdjacency` graph. For a concrete state
type the enumeration is an explicit list; existence for an abstract `Fintype`
follows noncomputably from `Finset.univ.toList`, but the executable path takes
the list as input.
-/

/-- The split accumulator: walk the preorder, closing the current block
when a forest root starts a new tree. -/
def splitPreorder.go {V : Type*} [BEq V] [Hashable V]
    (rootsSet : Std.HashSet V) : List V → List V → List (List V)
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | v :: rest, cur =>
      if rootsSet.contains v && !cur.isEmpty then
        cur.reverse :: splitPreorder.go rootsSet rest [v]
      else
        splitPreorder.go rootsSet rest (v :: cur)

/-- The second-pass DFS trees of a traversal: split its preorder at its forest
roots. In a DFS preorder the vertices of one tree are contiguous and each tree
starts with its root, so one pass with one `Std.HashSet.contains` test per
vertex suffices (in the hash-table cost model; this split is *not* counted in
the abstract DFS transition counts `n₁` / `n₂` below). Computable: the split
tests are `Bool`-valued (`contains`, `List.isEmpty`). -/
def splitPreorder {V : Type*} [BEq V] [Hashable V] [_inst : LawfulBEq V]
    (roots : List V) (preorder : List V) : List (List V) :=
  splitPreorder.go (Std.HashSet.ofList roots) preorder []

/-- Costed split accumulator: the same walk as `splitPreorder.go`, returning
`(blocks, cost)` where `cost` counts the Boolean tests the walk performs,
with short-circuit accounting: each step charges `1` for the
`rootsSet.contains` test, plus `1` more for the `cur.isEmpty` test only
when `contains` is true (short-circuit `&&`); the empty-input case charges
`1` for the final `cur.isEmpty` test. The cost is produced by the same
recursive evaluation that produces the blocks, not by a separate formula. -/
def splitPreorder.goC {V : Type*} [BEq V] [Hashable V]
    (rootsSet : Std.HashSet V) : List V → List V → (List (List V) × ℕ)
  | [], cur => (if cur.isEmpty then [] else [cur.reverse], 1)
  | v :: rest, cur =>
    if rootsSet.contains v then
      if !cur.isEmpty then
        let (blocks, c) := splitPreorder.goC rootsSet rest [v]
        (cur.reverse :: blocks, 2 + c)
      else
        let (blocks, c) := splitPreorder.goC rootsSet rest (v :: cur)
        (blocks, 2 + c)
    else
      let (blocks, c) := splitPreorder.goC rootsSet rest (v :: cur)
      (blocks, 1 + c)

/-- The costed split accumulator returns the same blocks as the uncosted one. -/
theorem splitPreorder.goC_fst {V : Type*} [BEq V] [Hashable V]
    (rootsSet : Std.HashSet V) (xs cur : List V) :
    (splitPreorder.goC rootsSet xs cur).1 = splitPreorder.go rootsSet xs cur := by
  induction xs generalizing cur with
  | nil =>
    cases cur with
    | nil => simp [splitPreorder.goC, splitPreorder.go]
    | cons v rest => simp [splitPreorder.goC, splitPreorder.go]
  | cons v rest ih =>
    cases hc : rootsSet.contains v <;> cases he : cur.isEmpty <;>
      simp [splitPreorder.goC, splitPreorder.go, hc, he, ih]

/-- The costed split accumulator's cost is at most two tests per preorder
vertex plus the final test. -/
theorem splitPreorder.goC_cost_le {V : Type*} [BEq V] [Hashable V]
    (rootsSet : Std.HashSet V) (xs cur : List V) :
    (splitPreorder.goC rootsSet xs cur).2 ≤ 2 * xs.length + 1 := by
  induction xs generalizing cur with
  | nil =>
    cases cur with
    | nil => simp [splitPreorder.goC]
    | cons v rest => simp [splitPreorder.goC]
  | cons v rest ih =>
    have h1 := ih [v]
    have h2 := ih (v :: cur)
    cases hc : rootsSet.contains v <;> cases he : cur.isEmpty <;>
      simp [splitPreorder.goC, hc, he] <;> omega

/-- Costed split: the same blocks as `splitPreorder`, plus the cost. The
cost counts one hash-table insertion per root for the `Std.HashSet.ofList`
construction plus the accumulator's tests (`splitPreorder.goC`). -/
def splitPreorderC {V : Type*} [BEq V] [Hashable V]
    (roots : List V) (preorder : List V) : List (List V) × ℕ :=
  let (blocks, c) := splitPreorder.goC (Std.HashSet.ofList roots) preorder []
  (blocks, roots.length + c)

/-- The costed split returns the same blocks as the uncosted split. -/
theorem splitPreorderC_fst {V : Type*} [BEq V] [Hashable V]
    [_inst : LawfulBEq V]
    (roots : List V) (preorder : List V) :
    (splitPreorderC roots preorder).1 = splitPreorder roots preorder := by
  simp only [splitPreorderC, splitPreorder]
  exact splitPreorder.goC_fst _ _ _

/-- The costed split's cost: one insertion per root plus at most two tests
per preorder vertex plus the final test. In `kosarajuSCCs` the roots are
the second pass's `forestRoots`, so the construction charges
`forestRoots.length` insertions — not `decreasingFinishAll.length`. -/
theorem splitPreorderC_cost_le {V : Type*} [BEq V] [Hashable V]
    (roots : List V) (preorder : List V) :
    (splitPreorderC roots preorder).2 ≤ roots.length + 2 * preorder.length + 1 := by
  simp only [splitPreorderC]
  have hle := splitPreorder.goC_cost_le (Std.HashSet.ofList roots) preorder []
  omega

/-- The split preserves total length: the blocks' lengths sum to the preorder
length plus the pending block's length. The scanner's per-block work is
bounded by the blocks' total length, so this lemma is what turns the
second-preorder length into a scanner work bound. -/
theorem splitPreorder_go_length_sum {V : Type*} [BEq V] [Hashable V]
    (rootsSet : Std.HashSet V) (xs cur : List V) :
    ((splitPreorder.go rootsSet xs cur).map List.length).sum = xs.length + cur.length := by
  induction xs generalizing cur with
  | nil =>
    cases cur with
    | nil => simp [splitPreorder.go]
    | cons v rest => simp [splitPreorder.go]
  | cons v rest ih =>
    cases hc : rootsSet.contains v && !cur.isEmpty <;>
      simp [splitPreorder.go, hc, ih, List.length_cons] <;> omega

/-- The Kosaraju-Sharir SCC decomposition: first pass `dfsAll` (decreasing
finish order), second pass `dfs` on the transpose in that order, blocks =
second-pass DFS trees. Computable, hence executable — but *not* linear-time
to evaluate end-to-end: adjacency evaluation is not counted at all
(adjacency is a function, re-evaluated on every query: a DFS pass queries
it at most once per visited vertex, and each transpose evaluation
re-evaluates forward adjacency for all `V` sources; for the `buchiGraph`
instantiation the second pass costs `Θ(V³·S)` `Tr` decisions on the
empty automaton — see the module docstring). The `O(V + E)`-shaped claim in this file is about the
abstract DFS transition counts `n₁` / `n₂` (`kosaraju_dfs_counts`,
`kosaraju_correct_wanted`) plus the proved split/scanner cost bounds
(`splitPreorderC_cost_le`, `kosarajuIsEmptyBC_cost_le`). -/
def kosarajuSCCs {V : Type*} [BEq V] [Hashable V] [LawfulBEq V]
    [DecidableEq V] (graph : DirectedAdjacency V) : List (List V) :=
  let second := dfs graph.transpose (decreasingFinishAll graph)
  splitPreorder second.forestRoots second.preorder

/-- **Proved cost shape (abstract DFS transition counts).** The two DFS passes
of `kosarajuSCCs` have exactly the `Internal.Step` transition counts given by
the proved DFS cost lemmas: `2 * V + E` for the first (whole-graph) pass, and
`R + P + E₂` for the second pass (`R` the number of roots, `P` the second
pass's preorder length, `E₂` the transpose's adjacency-entry count over that
preorder). These are counts of abstract machine steps in
`Relation.RelatesInSteps` traces; they do *not* include the cost of
evaluating the adjacency functions at all (forward adjacency, queried at
most once per visited vertex; transpose adjacency, which re-evaluates
forward adjacency per source — for `buchiGraph`, `Θ(V³·S)` `Tr`
decisions over the second pass on the empty automaton; see the module
docstring), so they are not a wall-clock `O(V + E)` bound. -/
theorem kosaraju_dfs_counts {V : Type*} [BEq V] [Hashable V] [LawfulBEq V]
    [DecidableEq V] (graph : DirectedAdjacency V) :
    ∃ (n₁ n₂ : ℕ),
      (∃ final : Internal.Machine V, final.work = [] ∧
        Internal.finish final = dfsAll graph ∧
          Relation.RelatesInSteps (Internal.Step graph graph.vertices)
            (Internal.initial graph.vertices) final n₁) ∧
      (∃ final : Internal.Machine V, final.work = [] ∧
        Internal.finish final = dfs graph.transpose (decreasingFinishAll graph) ∧
          Relation.RelatesInSteps
            (Internal.Step graph.transpose (decreasingFinishAll graph))
            (Internal.initial (decreasingFinishAll graph)) final n₂) ∧
      n₁ = 2 * graph.vertices.length +
        (graph.vertices.map fun v => (graph.adjacency v).length).sum ∧
      n₂ = (decreasingFinishAll graph).length +
        (dfs graph.transpose (decreasingFinishAll graph)).preorder.length +
          ((dfs graph.transpose (decreasingFinishAll graph)).preorder.map
            fun v => (graph.transpose.adjacency v).length).sum := by
  obtain ⟨final₁, hfinal₁, hfinish₁, hsteps₁⟩ := dfsAll_exact_steps graph
  obtain ⟨final₂, hfinal₂, hfinish₂, hsteps₂⟩ :=
    dfs_exact_steps graph.transpose (decreasingFinishAll graph)
  exact ⟨_, _,
    ⟨final₁, hfinal₁, hfinish₁, hsteps₁⟩,
    ⟨final₂, hfinal₂, hfinish₂, hsteps₂⟩, rfl, rfl⟩

/-- The Kosaraju blocks' lengths sum to the second pass's preorder length:
the split only re-chunks the preorder. -/
theorem kosaraju_blocks_length_sum {V : Type*} [BEq V] [Hashable V] [LawfulBEq V]
    [DecidableEq V] (graph : DirectedAdjacency V) :
    ((kosarajuSCCs graph).map List.length).sum =
      (dfs graph.transpose (decreasingFinishAll graph)).preorder.length := by
  unfold kosarajuSCCs splitPreorder
  rw [splitPreorder_go_length_sum]
  simp

/-- The vertices reachable from a start state, computed by *one* DFS from
the start states — not by a per-state reachability oracle and not by an
`O(n³)` closure. This is the visited set the emptiness scanner tests SCC
blocks against. -/
def startReachable {V : Type*} [BEq V] [Hashable V] [LawfulBEq V]
    (start : V → Prop) [DecidablePred start] (graph : DirectedAdjacency V) :
    List V :=
  (dfs graph (graph.vertices.filter fun v => decide (start v))).preorder

/-- DFS preorder from the start states enumerates exactly the vertices
reachable from a start state (`mem_preorder_iff_reachable`, with the roots
being the filtered start vertices). -/
theorem mem_startReachable_iff {V : Type*} [BEq V] [Hashable V] [LawfulBEq V]
    (start : V → Prop) [DecidablePred start] (graph : DirectedAdjacency V)
    (s : V) :
    s ∈ startReachable start graph ↔ ∃ s₀, start s₀ ∧ graph.Reachable s₀ s := by
  unfold startReachable
  rw [mem_preorder_iff_reachable]
  constructor
  · rintro ⟨root, hroot, hreach⟩
    have hstart : start root := of_decide_eq_true (List.mem_filter.mp hroot).2
    exact ⟨root, hstart, hreach⟩
  · rintro ⟨s₀, hstart, hreach⟩
    exact ⟨s₀, List.mem_filter.mpr ⟨graph.vertices_complete s₀, by simp [hstart]⟩,
      hreach⟩

/-- The start-reachable visited set as a hash set: one construction, then
one `contains` test per scanned state. -/
def startReachableSet {V : Type*} [BEq V] [Hashable V] [LawfulBEq V]
    (start : V → Prop) [DecidablePred start] (graph : DirectedAdjacency V) :
    Std.HashSet V :=
  Std.HashSet.ofList (startReachable start graph)

/-- Hash-set membership in the visited set is exactly start-reachability. -/
theorem startReachableSet_contains {V : Type*} [BEq V] [Hashable V] [LawfulBEq V]
    (start : V → Prop) [DecidablePred start] (graph : DirectedAdjacency V)
    (s : V) :
    (startReachableSet start graph).contains s = true ↔
      ∃ s₀, start s₀ ∧ graph.Reachable s₀ s := by
  unfold startReachableSet
  rw [Std.HashSet.contains_ofList]
  exact (List.contains_iff_mem).trans (mem_startReachable_iff start graph s)

/-- **Proved cost shape: three DFS passes.** The SCC decomposition's two
passes (`kosaraju_dfs_counts`) plus the start-reachability pass each have
exactly the `Internal.Step` transition counts given by the proved DFS cost
lemmas. The third pass counts its start-vertex roots, its preorder length,
and one transition per adjacency entry scanned from a reached vertex. -/
theorem buchi_emptiness_dfs_counts {V : Type*} [BEq V] [Hashable V]
    [LawfulBEq V] [DecidableEq V] (start : V → Prop) [DecidablePred start]
    (graph : DirectedAdjacency V) :
    ∃ (n₁ n₂ n₃ : ℕ),
      (∃ final : Internal.Machine V, final.work = [] ∧
        Internal.finish final = dfsAll graph ∧
          Relation.RelatesInSteps (Internal.Step graph graph.vertices)
            (Internal.initial graph.vertices) final n₁) ∧
      (∃ final : Internal.Machine V, final.work = [] ∧
        Internal.finish final = dfs graph.transpose (decreasingFinishAll graph) ∧
          Relation.RelatesInSteps
            (Internal.Step graph.transpose (decreasingFinishAll graph))
            (Internal.initial (decreasingFinishAll graph)) final n₂) ∧
      (∃ final : Internal.Machine V, final.work = [] ∧
        Internal.finish final = dfs graph
          (graph.vertices.filter fun v => decide (start v)) ∧
          Relation.RelatesInSteps
            (Internal.Step graph (graph.vertices.filter fun v => decide (start v)))
            (Internal.initial (graph.vertices.filter fun v => decide (start v)))
            final n₃) ∧
      n₁ = 2 * graph.vertices.length +
        (graph.vertices.map fun v => (graph.adjacency v).length).sum ∧
      n₂ = (decreasingFinishAll graph).length +
        (dfs graph.transpose (decreasingFinishAll graph)).preorder.length +
          ((dfs graph.transpose (decreasingFinishAll graph)).preorder.map
            fun v => (graph.transpose.adjacency v).length).sum ∧
      n₃ = (graph.vertices.filter fun v => decide (start v)).length +
        (startReachable start graph).length +
          ((startReachable start graph).map
            fun v => (graph.adjacency v).length).sum := by
  obtain ⟨final₁, hfinal₁, hfinish₁, hsteps₁⟩ := dfsAll_exact_steps graph
  obtain ⟨final₂, hfinal₂, hfinish₂, hsteps₂⟩ :=
    dfs_exact_steps graph.transpose (decreasingFinishAll graph)
  obtain ⟨final₃, hfinal₃, hfinish₃, hsteps₃⟩ :=
    dfs_exact_steps graph (graph.vertices.filter fun v => decide (start v))
  exact ⟨_, _, _,
    ⟨final₁, hfinal₁, hfinish₁, hsteps₁⟩,
    ⟨final₂, hfinal₂, hfinish₂, hsteps₂⟩,
    ⟨final₃, hfinal₃, hfinish₃, hsteps₃⟩, rfl, rfl, rfl⟩

/-- **Kosaraju correctness (wanted).** The blocks of `kosarajuSCCs` are
exactly the SCC partition (`IsSCCPartition`, including block `Nodup`), and the
two DFS passes take `n₁ + n₂` *abstract* `Internal.Step` transitions in
total, bounded as stated (`E` the original adjacency-entry count, `E₂` the
transpose's). The bound uses that both passes' vertex orders are
duplicate-free and cover all vertices, and that the transpose has at most one
adjacency entry per distinct edge. It is a bound on abstract transition
counts only: it does *not* bound the evaluation cost of the adjacency
functions at all (a DFS pass queries forward adjacency at most once per
visited vertex; each transpose evaluation re-evaluates forward adjacency
for all `V` sources; for the concrete `buchiGraph` instantiation the
forward pass costs `Θ(V²·S)` `Tr` decisions and the second pass
`Θ(V³·S)` on the empty automaton, `S` the number of symbols — see the
module docstring), and hence is not an end-to-end wall-clock `O(V + E)`
bound; that would need materialized forward *and* reverse adjacency
built once, not reverse adjacency alone on top of on-demand forward
lists — and with only the decision procedure for the ternary `Tr`,
materializing either adjacency costs up to `V²·S` `Tr` decisions
(triple tests, since a `(state, symbol)` pair does not enumerate its
successors), so `O(V + E)` would need a representation change to
explicit successor lists. This file builds neither; that is future
work.
Source: M. Sharir, "A strong-connectivity algorithm and its applications in
data flow analysis", *Computers & Mathematics with Applications* 7 (1981),
67-72; A. V. Aho, J. E. Hopcroft, and J. D. Ullman, *The Design and Analysis
of Computer Algorithms*, Addison-Wesley 1974, Section 5.5 (Kosaraju's
algorithm). The full emptiness procedure adds a third DFS pass
(start-reachability) plus split and scanner phases; its combined bound is
in `buchi_emptiness_via_kosaraju_wanted`. -/
public theorem_wanted kosaraju_correct_wanted :
    ∀ {V : Type*} [BEq V] [Hashable V] [LawfulBEq V] [DecidableEq V]
      (graph : DirectedAdjacency V),
      IsSCCPartition graph (kosarajuSCCs graph) ∧
      ∃ (n₁ n₂ : ℕ),
        (∃ final : Internal.Machine V, final.work = [] ∧
          Internal.finish final = dfsAll graph ∧
            Relation.RelatesInSteps (Internal.Step graph graph.vertices)
              (Internal.initial graph.vertices) final n₁) ∧
        (∃ final : Internal.Machine V, final.work = [] ∧
          Internal.finish final = dfs graph.transpose (decreasingFinishAll graph) ∧
            Relation.RelatesInSteps
              (Internal.Step graph.transpose (decreasingFinishAll graph))
              (Internal.initial (decreasingFinishAll graph)) final n₂) ∧
        n₁ = 2 * graph.vertices.length +
          (graph.vertices.map fun v => (graph.adjacency v).length).sum ∧
        n₂ = (decreasingFinishAll graph).length +
          (dfs graph.transpose (decreasingFinishAll graph)).preorder.length +
            ((dfs graph.transpose (decreasingFinishAll graph)).preorder.map
              fun v => (graph.transpose.adjacency v).length).sum ∧
        n₁ + n₂ ≤ 4 * graph.vertices.length + 2 *
          ((graph.vertices.map fun v => (graph.adjacency v).length).sum +
            (graph.transpose.vertices.map
              fun v => (graph.transpose.adjacency v).length).sum)

/-- The symbol-forgetting transition graph of a Büchi automaton, as an
explicit `DirectedAdjacency` graph: vertices are the given enumeration, and
the adjacency list of `s` is the `List.filter` of that enumeration by
`Buchi.Step s`. Computable (`def`, not `noncomputable`): the filter uses the
`DecidableRel na.Step` instance imported from `BuchiEmptiness.lean`
(finite symbol type + decidable `Tr`), not classical decidability, and the vertex enumeration is a
parameter rather than `Finset.univ.toList` (which is `noncomputable`). No
evaluation-cost claim is made for `buchiGraph`: one adjacency evaluation
costs `O(V·S)` `Tr` decisions (see the module docstring). -/
def buchiGraph {State Symbol : Type*} [Fintype Symbol]
    [_instDec : DecidableEq State] [BEq State] [_instHash : Hashable State]
    [_instLaw : LawfulBEq State]
    (vertices : List State) (vertices_nodup : vertices.Nodup)
    (vertices_complete : ∀ v, v ∈ vertices)
    (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)] :
    DirectedAdjacency State where
  vertices := vertices
  vertices_nodup := vertices_nodup
  vertices_complete := vertices_complete
  adjacency := fun s => vertices.filter (fun t => na.Step s t)

/-- Edges of `buchiGraph` are exactly `Buchi.Step` transitions. -/
theorem buchiGraph_edge {State Symbol : Type*} [Fintype Symbol]
    [DecidableEq State] [BEq State] [Hashable State] [LawfulBEq State]
    (vertices : List State) (vertices_nodup : vertices.Nodup)
    (vertices_complete : ∀ v, v ∈ vertices)
    (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)]
    (s t : State) :
    (buchiGraph vertices vertices_nodup vertices_complete na).Edge s t ↔
      na.Step s t := by
  change t ∈ vertices.filter (fun t => na.Step s t) ↔ na.Step s t
  constructor
  · intro h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  · intro h
    exact List.mem_filter.mpr ⟨vertices_complete t, by simp [h]⟩

/-- Reachability in `buchiGraph` is exactly `ReflTransGen Buchi.Step`. -/
theorem buchiGraph_reachable {State Symbol : Type*} [Fintype Symbol]
    [DecidableEq State] [BEq State] [Hashable State] [LawfulBEq State]
    (vertices : List State) (vertices_nodup : vertices.Nodup)
    (vertices_complete : ∀ v, v ∈ vertices)
    (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)]
    (s t : State) :
    (buchiGraph vertices vertices_nodup vertices_complete na).Reachable s t ↔
      Relation.ReflTransGen na.Step s t := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h' he ih => exact ih.tail ((buchiGraph_edge _ _ _ _ _ _).mp he)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h' he ih => exact ih.tail ((buchiGraph_edge _ _ _ _ _ _).mpr he)

/-- A block is *cyclic* if it contains two distinct states, or one state
with a self-loop in the graph. The distinctness matters: a list such as
`[s, s]` has length `2` but only one state, and is cyclic only if `s` has a
self-loop. -/
def blockCyclic {V : Type*} (graph : DirectedAdjacency V) (block : List V) : Prop :=
  (∃ s ∈ block, ∃ t ∈ block, s ≠ t) ∨ ∃ s ∈ block, graph.Edge s s

/-- Boolean cyclic test for a block: `true` iff the block's length is at
least two, or it contains a state with a self-loop in `graph`. Computable
with no edge oracle: a self-loop is adjacency-list membership, tested by
`DirectedAdjacency.hasEdge`. The length test is only a valid test for
two distinct states under `block.Nodup` (carried explicitly in
`blockCyclicB_eq_true`): without it, `[s, s]` would pass the length test
with no self-loop. -/
def blockCyclicB {V : Type*} [DecidableEq V]
    (graph : DirectedAdjacency V) (block : List V) : Bool :=
  2 ≤ block.length || block.any fun s => graph.hasEdge s s

/-- A duplicate-free block of length at least two contains two distinct states. -/
theorem nodup_two_distinct_of_length {V : Type*} {block : List V}
    (hNodup : block.Nodup) (hlen : 2 ≤ block.length) :
    ∃ s ∈ block, ∃ t ∈ block, s ≠ t := by
  cases block with
  | nil => simp at hlen
  | cons a rest =>
    cases rest with
    | nil => simp at hlen
    | cons b rest' =>
      refine ⟨a, List.mem_cons_self, b, ?_, ?_⟩
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · intro h
        subst h
        exact (List.nodup_cons.mp hNodup).1 List.mem_cons_self

/-- Two distinct members force length at least two. -/
theorem two_le_length_of_two_distinct {V : Type*} {block : List V}
    (h : ∃ s ∈ block, ∃ t ∈ block, s ≠ t) : 2 ≤ block.length := by
  obtain ⟨s, hs, t, ht, hne⟩ := h
  cases block with
  | nil => simp at hs
  | cons a rest =>
    cases rest with
    | nil =>
      have ha : s = a := by simpa using hs
      have hb : t = a := by simpa using ht
      exact absurd (ha.trans hb.symm) hne
    | cons b rest' =>
      simp only [List.length_cons]
      omega

/-- The Boolean cyclic test reflects `blockCyclic`, given the block is
duplicate-free. The `Nodup` hypothesis is what justifies reading the
length test as "two distinct states"; the scanner threads it from the
SCC partition (`IsSCCPartition.blocksNodup` in `kosaraju_correct_wanted`). -/
theorem blockCyclicB_eq_true {V : Type*} [DecidableEq V]
    (graph : DirectedAdjacency V) (block : List V) (hNodup : block.Nodup) :
    blockCyclicB graph block = true ↔ blockCyclic graph block := by
  simp only [blockCyclicB, Bool.or_eq_true, List.any_eq_true]
  constructor
  · rintro (hlen | ⟨s, hs, hself⟩)
    · exact Or.inl (nodup_two_distinct_of_length hNodup (of_decide_eq_true hlen))
    · exact Or.inr ⟨s, hs, (DirectedAdjacency.hasEdge_eq_true graph s s).mp hself⟩
  · rintro (⟨s, hs, t, ht, hne⟩ | ⟨s, hs, hself⟩)
    · have h2 := two_le_length_of_two_distinct ⟨s, hs, t, ht, hne⟩
      exact Or.inl (by simp [h2])
    · exact Or.inr ⟨s, hs, (DirectedAdjacency.hasEdge_eq_true graph s s).mpr hself⟩

/-- Costed list-membership test: the same `Bool` as `decide (t ∈ l)`, plus
the number of entries examined. It stops at the first matching entry
(short-circuit), so the cost is the index of the first match plus one,
or the full length when `t` is absent. -/
def listMemC {V : Type*} [DecidableEq V] (t : V) : List V → Bool × ℕ
  | [] => (false, 0)
  | x :: xs =>
    if decide (t = x) then (true, 1)
    else let (b, c) := listMemC t xs; (b, 1 + c)

/-- The costed membership test returns the same `Bool` as `decide (t ∈ l)`. -/
theorem listMemC_fst {V : Type*} [DecidableEq V] (t : V) (l : List V) :
    (listMemC t l).1 = decide (t ∈ l) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : t = x <;> simp [listMemC, h, ih, List.mem_cons]

/-- The costed membership test examines at most the whole list. -/
theorem listMemC_cost_le {V : Type*} [DecidableEq V] (t : V) (l : List V) :
    (listMemC t l).2 ≤ l.length := by
  induction l with
  | nil => simp [listMemC]
  | cons x xs ih =>
    by_cases h : t = x <;> simp [listMemC, h]; omega

/-- Costed self-loop scan: the same `Bool` as
`block.any fun s => graph.hasEdge s s`, plus the adjacency-entry scans.
`List.any` stops at the first `true` state; `listMemC` stops at the first
matching entry. -/
def anySelfLoopC {V : Type*} [DecidableEq V] (graph : DirectedAdjacency V) :
    List V → Bool × ℕ
  | [] => (false, 0)
  | s :: rest =>
    let (b, c) := listMemC s (graph.adjacency s)
    if b then (true, c)
    else let (b2, c2) := anySelfLoopC graph rest; (b2, c + c2)

/-- The costed self-loop scan returns the same `Bool` as the uncosted `any`. -/
theorem anySelfLoopC_fst {V : Type*} [DecidableEq V] (graph : DirectedAdjacency V)
    (block : List V) :
    (anySelfLoopC graph block).1 = block.any fun s => graph.hasEdge s s := by
  induction block with
  | nil => rfl
  | cons s rest ih =>
    have hmem : (listMemC s (graph.adjacency s)).1 = graph.hasEdge s s := by
      rw [listMemC_fst]; rfl
    cases hb : (listMemC s (graph.adjacency s)).1
    · have h1 : anySelfLoopC graph (s :: rest) =
          ((anySelfLoopC graph rest).1,
            (listMemC s (graph.adjacency s)).2 + (anySelfLoopC graph rest).2) := by
        simp [anySelfLoopC, hb]
      rw [h1, ih]
      simp [List.any_cons, ← hmem, hb]
    · have h1 : anySelfLoopC graph (s :: rest) =
          (true, (listMemC s (graph.adjacency s)).2) := by
        simp [anySelfLoopC, hb]
      rw [h1]
      simp [List.any_cons, ← hmem, hb]

/-- The costed self-loop scan's adjacency-entry scans are bounded by the
sum of the block's adjacency lengths. -/
theorem anySelfLoopC_cost_le {V : Type*} [DecidableEq V]
    (graph : DirectedAdjacency V) (block : List V) :
    (anySelfLoopC graph block).2 ≤
      (block.map fun s => (graph.adjacency s).length).sum := by
  induction block with
  | nil => simp [anySelfLoopC]
  | cons s rest ih =>
    have h1 := listMemC_cost_le s (graph.adjacency s)
    cases hb : (listMemC s (graph.adjacency s)).1 <;>
      simp [anySelfLoopC, hb] <;> omega

/-- Costed Boolean cyclic test: the same `Bool` as `blockCyclicB`, plus the
cost. One length test always; the self-loop scan runs only when the
block has length `< 2` (short-circuit `||`). -/
def blockCyclicBC {V : Type*} [DecidableEq V] (graph : DirectedAdjacency V)
    (block : List V) : Bool × ℕ :=
  if 2 ≤ block.length then (true, 1)
  else let (b, c) := anySelfLoopC graph block; (b, 1 + c)

/-- The costed cyclic test returns the same `Bool` as `blockCyclicB`. -/
theorem blockCyclicBC_fst {V : Type*} [DecidableEq V] (graph : DirectedAdjacency V)
    (block : List V) :
    (blockCyclicBC graph block).1 = blockCyclicB graph block := by
  by_cases h : 2 ≤ block.length <;>
    simp [blockCyclicBC, blockCyclicB, h, anySelfLoopC_fst]

/-- The costed cyclic test costs at most one length test plus the block's
adjacency-entry scans. -/
theorem blockCyclicBC_cost_le {V : Type*} [DecidableEq V]
    (graph : DirectedAdjacency V) (block : List V) :
    (blockCyclicBC graph block).2 ≤
      1 + (block.map fun s => (graph.adjacency s).length).sum := by
  by_cases h : 2 ≤ block.length <;>
    simp [blockCyclicBC, h]
  have hle := anySelfLoopC_cost_le graph block
  omega

/-- Costed accept-and-reachable scan: the same `Bool` as
`block.any fun s => decide (accept s) && reachSet.contains s`, plus the
test count. Each examined state charges `1` for the `decide`, plus `1`
more for the `contains` test only when `decide` is true (short-circuit
`&&`); the scan stops at the first `true` state. -/
def anyAcceptReachC {V : Type*} [BEq V] [Hashable V] (reachSet : Std.HashSet V)
    (accept : V → Prop) [DecidablePred accept] : List V → Bool × ℕ
  | [] => (false, 0)
  | s :: rest =>
    if decide (accept s) then
      if reachSet.contains s then (true, 2)
      else let (b, c) := anyAcceptReachC reachSet accept rest; (b, 2 + c)
    else let (b, c) := anyAcceptReachC reachSet accept rest; (b, 1 + c)

/-- The costed accept-and-reachable scan returns the same `Bool` as the
uncosted `any`. -/
theorem anyAcceptReachC_fst {V : Type*} [BEq V] [Hashable V]
    (reachSet : Std.HashSet V) (accept : V → Prop) [DecidablePred accept]
    (block : List V) :
    (anyAcceptReachC reachSet accept block).1 =
      block.any fun s => decide (accept s) && reachSet.contains s := by
  induction block with
  | nil => rfl
  | cons s rest ih =>
    cases hacc : decide (accept s) <;> cases hcon : reachSet.contains s <;>
      simp [anyAcceptReachC, List.any_cons, hacc, hcon, ih]

/-- The costed accept-and-reachable scan performs at most two tests per
state. -/
theorem anyAcceptReachC_cost_le {V : Type*} [BEq V] [Hashable V]
    (reachSet : Std.HashSet V) (accept : V → Prop) [DecidablePred accept]
    (block : List V) :
    (anyAcceptReachC reachSet accept block).2 ≤ 2 * block.length := by
  induction block with
  | nil => simp [anyAcceptReachC]
  | cons s rest ih =>
    cases hacc : decide (accept s) <;> cases hcon : reachSet.contains s <;>
      simp [anyAcceptReachC, hacc, hcon] <;> omega

/-- Costed block scan: the same `Bool` as
`blocks.any fun block => blockCyclicB graph block &&
block.any fun s => decide (accept s) && reachSet.contains s`, plus the
total cost. Per block: the cyclic test's cost, plus the
accept-and-reachable cost only when the block is cyclic (short-circuit
`&&`); the scan stops at the first `true` block. -/
def scanBlocksC {V : Type*} [DecidableEq V] [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (reachSet : Std.HashSet V)
    (accept : V → Prop) [DecidablePred accept] : List (List V) → Bool × ℕ
  | [] => (false, 0)
  | block :: rest =>
    let (cyc, cc) := blockCyclicBC graph block
    if cyc then
      let (acc, ac) := anyAcceptReachC reachSet accept block
      if acc then (true, cc + ac)
      else let (b, c) := scanBlocksC graph reachSet accept rest; (b, cc + ac + c)
    else
      let (b, c) := scanBlocksC graph reachSet accept rest; (b, cc + c)

/-- The costed block scan returns the same `Bool` as the uncosted `any`. -/
theorem scanBlocksC_fst {V : Type*} [DecidableEq V] [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (reachSet : Std.HashSet V)
    (accept : V → Prop) [DecidablePred accept] (blocks : List (List V)) :
    (scanBlocksC graph reachSet accept blocks).1 =
      blocks.any fun block => blockCyclicB graph block &&
        block.any fun s => decide (accept s) && reachSet.contains s := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    have hcf := blockCyclicBC_fst graph block
    have haf := anyAcceptReachC_fst reachSet accept block
    cases hcyc : (blockCyclicBC graph block).1 <;>
      cases hacc : (anyAcceptReachC reachSet accept block).1
    · have hb : blockCyclicB graph block = false := by rw [← hcf, hcyc]
      have ha : (block.any fun s => decide (accept s) && reachSet.contains s) = false := by
        rw [← haf]; exact hacc
      simp only [scanBlocksC, hcyc, hacc, ih, hb, ha, List.any_cons,
        Bool.false_eq_true, ite_false,
        Bool.false_and, Bool.false_or]
    · have hb : blockCyclicB graph block = false := by rw [← hcf, hcyc]
      have ha : (block.any fun s => decide (accept s) && reachSet.contains s) = true := by
        rw [← haf]; exact hacc
      simp only [scanBlocksC, hcyc, hacc, ih, hb, ha, List.any_cons,
        Bool.false_eq_true, ite_false, ite_true,
        Bool.false_and, Bool.false_or]
    · have hb : blockCyclicB graph block = true := by rw [← hcf, hcyc]
      have ha : (block.any fun s => decide (accept s) && reachSet.contains s) = false := by
        rw [← haf]; exact hacc
      simp only [scanBlocksC, hcyc, hacc, ih, hb, ha, List.any_cons,
        Bool.false_eq_true, ite_false, ite_true,
        Bool.true_and, Bool.false_or]
    · have hb : blockCyclicB graph block = true := by rw [← hcf, hcyc]
      have ha : (block.any fun s => decide (accept s) && reachSet.contains s) = true := by
        rw [← haf]; exact hacc
      simp only [scanBlocksC, hcyc, hacc, ih, hb, ha, List.any_cons,
        ite_true,
        Bool.true_and, Bool.true_or]

/-- The costed block scan's cost is bounded by the per-block budget: one
length test plus the block's adjacency-entry scans plus two tests per
block state. -/
theorem scanBlocksC_cost_le {V : Type*} [DecidableEq V] [BEq V] [Hashable V]
    (graph : DirectedAdjacency V) (reachSet : Std.HashSet V)
    (accept : V → Prop) [DecidablePred accept] (blocks : List (List V)) :
    (scanBlocksC graph reachSet accept blocks).2 ≤
      (blocks.map fun block => 1 +
        (block.map fun s => (graph.adjacency s).length).sum +
        2 * block.length).sum := by
  induction blocks with
  | nil => simp [scanBlocksC]
  | cons block rest ih =>
    have hc := blockCyclicBC_cost_le graph block
    have ha := anyAcceptReachC_cost_le reachSet accept block
    have hmid : (scanBlocksC graph reachSet accept (block :: rest)).2 ≤
        (1 + (block.map fun s => (graph.adjacency s).length).sum +
          2 * block.length) +
        (scanBlocksC graph reachSet accept rest).2 := by
      cases hcyc : (blockCyclicBC graph block).1 <;>
        cases hacc : (anyAcceptReachC reachSet accept block).1 <;>
        simp only [scanBlocksC, hcyc, hacc, Bool.false_eq_true,
          ite_false, ite_true] <;> omega
    have hsplit : ((block :: rest).map fun b => 1 +
        (b.map fun s => (graph.adjacency s).length).sum +
        2 * b.length).sum =
        (1 + (block.map fun s => (graph.adjacency s).length).sum +
          2 * block.length) +
        (rest.map fun b => 1 +
          (b.map fun s => (graph.adjacency s).length).sum +
          2 * b.length).sum := by
      simp [List.map_cons, List.sum_cons]
    rw [hsplit]
    exact le_trans hmid (by omega)

/-- **Computable Büchi emptiness decision via Kosaraju.** With decidable
`start` and `accept` membership (the `DecidablePred` instances that
`Buchi.isEmptyB` already assumes), the Boolean scanner decides emptiness:
`kosarajuIsEmptyB = true` iff the language is empty, *once
`kosaraju_correct_wanted` holds*. The scanner takes no reachability or edge
oracle: start-reachability is the one DFS-visited set
`startReachableSet (· ∈ na.start) graph` (built once, by the `let`), and
self-loops are tested by `blockCyclicB` via `DirectedAdjacency.hasEdge`. For
each Kosaraju block it checks the block is cyclic *and* contains a single
state that is both accepting and in the visited set. -/
def kosarajuIsEmptyB {State Symbol : Type*} [Fintype Symbol]
    [DecidableEq State] [BEq State] [Hashable State] [LawfulBEq State]
    (vertices : List State) (vertices_nodup : vertices.Nodup)
    (vertices_complete : ∀ v, v ∈ vertices)
    (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)]
    [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)]
    (graph : DirectedAdjacency State)
    (_hgraph : graph = buchiGraph vertices vertices_nodup vertices_complete na) :
    Bool :=
  let reachSet := startReachableSet (· ∈ na.start) graph
  !(kosarajuSCCs graph).any fun block =>
    blockCyclicB graph block &&
      block.any fun s => decide (s ∈ na.accept) && reachSet.contains s

/-- The Boolean emptiness scanner reflects the Kosaraju lasso condition:
`kosarajuIsEmptyB = true` iff there is no cyclic accepting block reachable
from a start state (with the same state accepting and reachable). This proof
does not need `kosaraju_correct_wanted` except for one hypothesis: every
Kosaraju block is duplicate-free (`hNodup`), which is what justifies reading
the scanner's length test as "two distinct states" (see
`blockCyclicB_eq_true`). In the wanted theorem this hypothesis is discharged
by `IsSCCPartition.blocksNodup` from `kosaraju_correct_wanted`. -/
theorem kosarajuIsEmptyB_iff {State Symbol : Type*} [Fintype Symbol]
    [DecidableEq State] [BEq State] [Hashable State] [LawfulBEq State]
    (vertices : List State) (vertices_nodup : vertices.Nodup)
    (vertices_complete : ∀ v, v ∈ vertices)
    (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)]
    [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)]
    (graph : DirectedAdjacency State)
    (hgraph : graph = buchiGraph vertices vertices_nodup vertices_complete na)
    (hNodup : ∀ block ∈ kosarajuSCCs graph, block.Nodup) :
    kosarajuIsEmptyB vertices vertices_nodup vertices_complete na graph hgraph = true ↔
      ¬ ∃ block ∈ kosarajuSCCs graph, ∃ s ∈ block, s ∈ na.accept ∧
        blockCyclic graph block ∧ (∃ s₀, s₀ ∈ na.start ∧ graph.Reachable s₀ s) := by
  constructor
  · intro h hex
    obtain ⟨block, hblock, s, hs, hacc, hcyc, s₀, hs₀, hreach⟩ := hex
    have htrue : (kosarajuSCCs graph).any (fun block =>
        blockCyclicB graph block &&
          block.any fun s => decide (s ∈ na.accept) &&
            (startReachableSet (· ∈ na.start) graph).contains s) = true := by
      refine List.any_eq_true.mpr ⟨block, hblock, ?_⟩
      have h1 : blockCyclicB graph block = true :=
        (blockCyclicB_eq_true graph block (hNodup block hblock)).mpr hcyc
      have h2 : (block.any fun s => decide (s ∈ na.accept) &&
          (startReachableSet (· ∈ na.start) graph).contains s) = true := by
        refine List.any_eq_true.mpr ⟨s, hs, ?_⟩
        rw [Bool.and_eq_true]
        exact ⟨by simp [hacc], (startReachableSet_contains (· ∈ na.start) graph s).mpr
          ⟨s₀, hs₀, hreach⟩⟩
      rw [Bool.and_eq_true, h1, h2]
      exact ⟨rfl, rfl⟩
    rw [show kosarajuIsEmptyB vertices vertices_nodup vertices_complete na graph hgraph =
        !((kosarajuSCCs graph).any fun block =>
          blockCyclicB graph block &&
            block.any fun s => decide (s ∈ na.accept) &&
              (startReachableSet (· ∈ na.start) graph).contains s) from rfl,
      htrue] at h
    exact Bool.false_ne_true h
  · intro h
    rw [show kosarajuIsEmptyB vertices vertices_nodup vertices_complete na graph hgraph =
        !((kosarajuSCCs graph).any fun block =>
          blockCyclicB graph block &&
            block.any fun s => decide (s ∈ na.accept) &&
              (startReachableSet (· ∈ na.start) graph).contains s) from rfl,
      Bool.not_eq_true', Bool.eq_false_iff]
    intro hfalse
    obtain ⟨block, hblock, hpred⟩ := List.any_eq_true.mp hfalse
    simp only [Bool.and_eq_true] at hpred
    obtain ⟨h1, h2⟩ := hpred
    obtain ⟨s, hs, hpair⟩ := List.any_eq_true.mp h2
    simp only [Bool.and_eq_true] at hpair
    obtain ⟨hacc, hreach'⟩ := hpair
    have hacc' : s ∈ na.accept := of_decide_eq_true hacc
    obtain ⟨s₀, hs₀, hreach⟩ :=
      (startReachableSet_contains (· ∈ na.start) graph s).mp hreach'
    exact h ⟨block, hblock, s, hs, hacc',
      (blockCyclicB_eq_true graph block (hNodup block hblock)).mp h1, s₀, hs₀, hreach⟩

/-- Costed Büchi emptiness scanner: the same `Bool` as `kosarajuIsEmptyB`,
plus the cost. The reachable preorder is bound once (`reachPre`); the
hash set is built from that binding and its length is reused for the
cost — so the start-reachability DFS runs once, not twice (calling
`startReachable` again for the length would be a second DFS). The cost
counts one hash-table insertion per start-reachable vertex for the
visited-set construction plus the block scan's cost (`scanBlocksC`);
the visited set is built once and shared across the scan. -/
def kosarajuIsEmptyBC {State Symbol : Type*} [Fintype Symbol]
    [DecidableEq State] [BEq State] [Hashable State] [LawfulBEq State]
    (vertices : List State) (vertices_nodup : vertices.Nodup)
    (vertices_complete : ∀ v, v ∈ vertices)
    (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)]
    [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)]
    (graph : DirectedAdjacency State)
    (_hgraph : graph = buchiGraph vertices vertices_nodup vertices_complete na) :
    Bool × ℕ :=
  let reachPre := startReachable (· ∈ na.start) graph
  let reachSet := Std.HashSet.ofList reachPre
  let (found, c) := scanBlocksC graph reachSet (· ∈ na.accept) (kosarajuSCCs graph)
  (!found, reachPre.length + c)

/-- The costed scanner returns the same `Bool` as the uncosted scanner. -/
theorem kosarajuIsEmptyBC_fst {State Symbol : Type*} [Fintype Symbol]
    [DecidableEq State] [BEq State] [Hashable State] [LawfulBEq State]
    (vertices : List State) (vertices_nodup : vertices.Nodup)
    (vertices_complete : ∀ v, v ∈ vertices)
    (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)]
    [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)]
    (graph : DirectedAdjacency State)
    (hgraph : graph = buchiGraph vertices vertices_nodup vertices_complete na) :
    (kosarajuIsEmptyBC vertices vertices_nodup vertices_complete na graph hgraph).1 =
      kosarajuIsEmptyB vertices vertices_nodup vertices_complete na graph hgraph := by
  have hsc := scanBlocksC_fst graph (startReachableSet (· ∈ na.start) graph)
    (· ∈ na.accept) (kosarajuSCCs graph)
  have hset : Std.HashSet.ofList (startReachable (· ∈ na.start) graph) =
      startReachableSet (· ∈ na.start) graph := rfl
  simp only [kosarajuIsEmptyBC, kosarajuIsEmptyB, hset, hsc]

/-- The costed scanner's cost: one insertion per start-reachable vertex
plus the per-block budget (one length test plus the block's
adjacency-entry scans plus two tests per block state). -/
theorem kosarajuIsEmptyBC_cost_le {State Symbol : Type*} [Fintype Symbol]
    [DecidableEq State] [BEq State] [Hashable State] [LawfulBEq State]
    (vertices : List State) (vertices_nodup : vertices.Nodup)
    (vertices_complete : ∀ v, v ∈ vertices)
    (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)]
    [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)]
    (graph : DirectedAdjacency State)
    (hgraph : graph = buchiGraph vertices vertices_nodup vertices_complete na) :
    (kosarajuIsEmptyBC vertices vertices_nodup vertices_complete na graph hgraph).2 ≤
      (startReachable (· ∈ na.start) graph).length +
        ((kosarajuSCCs graph).map fun block => 1 +
          (block.map fun s => (graph.adjacency s).length).sum +
          2 * block.length).sum := by
  have hle := scanBlocksC_cost_le graph (startReachableSet (· ∈ na.start) graph)
    (· ∈ na.accept) (kosarajuSCCs graph)
  have hset : Std.HashSet.ofList (startReachable (· ∈ na.start) graph) =
      startReachableSet (· ∈ na.start) graph := rfl
  simp only [kosarajuIsEmptyBC, hset]
  omega

/-- **Büchi emptiness via Kosaraju (wanted).** A Büchi automaton has a lasso
iff some accepting state, reachable from a start state, lies in a cyclic block
of the Kosaraju decomposition of its transition graph (a block with
`blockCyclic`: two distinct states, or a state with a self-loop). With the additional decidable
`start`/`accept` hypotheses (the `DecidablePred` instances that
`Buchi.isEmptyB` already assumes), the computable scanner `kosarajuIsEmptyB`
decides this with no oracle: `kosarajuIsEmptyB_iff` (proved) reflects the
scanner into the lasso condition, so `kosarajuIsEmptyB = true` iff the
language is empty, once `kosaraju_correct_wanted` holds (which upgrades
`buchiGraph.Reachable` to `Buchi.Step`-reachability for `HasLasso`).
Start-reachability is computed once, by the third DFS pass
(`startReachable`), not by a per-state reachability oracle or an `O(n³)`
closure. The final conjunct is the full cost statement: the three DFS
passes have the exact `Internal.Step` counts `n₁`, `n₂`, `n₃` of
`buchi_emptiness_dfs_counts` (proved); the split cost `c_split` is the
output of the costed evaluator `splitPreorderC` on the second pass's
`forestRoots` and preorder (proved `splitPreorderC_fst`,
`splitPreorderC_cost_le`: one insertion per forest root, at most two
tests per preorder vertex plus the final test); and the scanner cost
`c_scan` is the output of the costed evaluator `kosarajuIsEmptyBC`
(proved `kosarajuIsEmptyBC_fst`, `kosarajuIsEmptyBC_cost_le`: one
insertion per start-reachable vertex plus the per-block budget). The
combined bound is
`n₁ + n₂ + n₃ + c_split + c_scan ≤ 14V + 3(E + E₂) + 1`, closing which needs
the SCC partition (`kosaraju_correct_wanted`) and arithmetic. This is the
wanted replacement for the `f + 1` fixed-point closures of `Buchi.isEmptyB`
(BACKLOG B31) — the first two DFS passes, the start-reachability pass, the
split, and the scanner are all counted in the abstract transition-count /
hash-table-operation cost model. That model omits the cost of *evaluating*
the adjacency functions, which dominates end-to-end: one
`buchiGraph.adjacency` evaluation costs `O(V·S)` `Tr` decisions (`S` the
number of symbols); the forward and start-reachability passes evaluate it
once per visited vertex (`Θ(V²·S)` on the empty automaton); each transpose
evaluation re-evaluates it for all `V` sources, so the second pass costs
`Θ(V³·S)` `Tr` decisions on the empty automaton; and the scanner's self-loop
tests re-evaluate adjacency lists again (`c_scan` charges scanning the
entries of produced lists, not producing them). Building only a reverse
adjacency does not fix this: with only the decision procedure for
the ternary `Tr`, materializing either adjacency costs up to `V²·S`
`Tr` decisions (triple tests, since a `(state, symbol)` pair does not
enumerate its successors), so `O(V + E)` needs a representation
change to explicit successor lists (see the module docstring).
The bound is therefore not an end-to-end wall-clock linear-time bound.
Source: R. E. Courcoubetis, M. Y. Vardi,
P. Wolper, and M. Yannakakis, "Memory-efficient algorithms for the verification
of temporal properties", *Formal Methods in System Design* 1 (1992), 275-288. -/
public theorem_wanted buchi_emptiness_via_kosaraju_wanted :
    ∀ {State Symbol : Type*} [Fintype State] [Fintype Symbol] [DecidableEq State]
      [BEq State] [Hashable State] [LawfulBEq State]
      (vertices : List State) (vertices_nodup : vertices.Nodup)
      (vertices_complete : ∀ v, v ∈ vertices)
      (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)]
      [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)],
      (kosarajuIsEmptyB vertices vertices_nodup vertices_complete na
          (buchiGraph vertices vertices_nodup vertices_complete na) rfl = true ↔
        language na = ⊥) ∧
      (Buchi.HasLasso na ↔ ∃ s₀ ∈ na.start, ∃ s ∈ na.accept,
        Relation.ReflTransGen na.Step s₀ s ∧
          ∃ block ∈ kosarajuSCCs
            (buchiGraph vertices vertices_nodup vertices_complete na), s ∈ block ∧
            blockCyclic (buchiGraph vertices vertices_nodup vertices_complete na)
              block) ∧
      (language na = ⊥ ↔ ¬ ∃ block ∈ kosarajuSCCs
          (buchiGraph vertices vertices_nodup vertices_complete na),
        ∃ s₀ ∈ na.start, ∃ s ∈ na.accept, s ∈ block ∧
          Relation.ReflTransGen na.Step s₀ s ∧
          blockCyclic (buchiGraph vertices vertices_nodup vertices_complete na)
            block) ∧
      (∃ (n₁ n₂ n₃ c_split c_scan : ℕ),
        (∃ final : Internal.Machine State, final.work = [] ∧
          Internal.finish final =
            dfsAll (buchiGraph vertices vertices_nodup vertices_complete na) ∧
            Relation.RelatesInSteps
              (Internal.Step (buchiGraph vertices vertices_nodup vertices_complete na)
                (buchiGraph vertices vertices_nodup vertices_complete na).vertices)
              (Internal.initial
                (buchiGraph vertices vertices_nodup vertices_complete na).vertices)
              final n₁) ∧
        (∃ final : Internal.Machine State, final.work = [] ∧
          Internal.finish final = dfs
            (buchiGraph vertices vertices_nodup vertices_complete na).transpose
            (decreasingFinishAll
              (buchiGraph vertices vertices_nodup vertices_complete na)) ∧
            Relation.RelatesInSteps
              (Internal.Step
                (buchiGraph vertices vertices_nodup vertices_complete na).transpose
                (decreasingFinishAll
                  (buchiGraph vertices vertices_nodup vertices_complete na)))
              (Internal.initial (decreasingFinishAll
                (buchiGraph vertices vertices_nodup vertices_complete na))) final n₂) ∧
        (∃ final : Internal.Machine State, final.work = [] ∧
          Internal.finish final = dfs
            (buchiGraph vertices vertices_nodup vertices_complete na)
            ((buchiGraph vertices vertices_nodup vertices_complete na).vertices.filter
              fun v => decide (v ∈ na.start)) ∧
            Relation.RelatesInSteps
              (Internal.Step (buchiGraph vertices vertices_nodup vertices_complete na)
                ((buchiGraph vertices vertices_nodup vertices_complete na).vertices.filter
                  fun v => decide (v ∈ na.start)))
              (Internal.initial
                ((buchiGraph vertices vertices_nodup vertices_complete na).vertices.filter
                  fun v => decide (v ∈ na.start))) final n₃) ∧
        n₁ = 2 * (buchiGraph vertices vertices_nodup vertices_complete na).vertices.length +
          ((buchiGraph vertices vertices_nodup vertices_complete na).vertices.map
            fun v => ((buchiGraph vertices vertices_nodup vertices_complete na).adjacency
              v).length).sum ∧
        n₂ = (decreasingFinishAll
            (buchiGraph vertices vertices_nodup vertices_complete na)).length +
          (dfs (buchiGraph vertices vertices_nodup vertices_complete na).transpose
            (decreasingFinishAll
              (buchiGraph vertices vertices_nodup vertices_complete na))).preorder.length +
          ((dfs (buchiGraph vertices vertices_nodup vertices_complete na).transpose
            (decreasingFinishAll
              (buchiGraph vertices vertices_nodup vertices_complete na))).preorder.map
            fun v => ((buchiGraph vertices vertices_nodup vertices_complete na).transpose.adjacency
              v).length).sum ∧
        n₃ = ((buchiGraph vertices vertices_nodup vertices_complete na).vertices.filter
            fun v => decide (v ∈ na.start)).length +
          (startReachable (· ∈ na.start)
            (buchiGraph vertices vertices_nodup vertices_complete na)).length +
          ((startReachable (· ∈ na.start)
            (buchiGraph vertices vertices_nodup vertices_complete na)).map
            fun v => ((buchiGraph vertices vertices_nodup vertices_complete na).adjacency
              v).length).sum ∧
        c_split = (splitPreorderC
            (dfs (buchiGraph vertices vertices_nodup vertices_complete na).transpose
              (decreasingFinishAll
                (buchiGraph vertices vertices_nodup vertices_complete na))).forestRoots
            (dfs (buchiGraph vertices vertices_nodup vertices_complete na).transpose
              (decreasingFinishAll
                (buchiGraph vertices vertices_nodup vertices_complete na))).preorder).2 ∧
        c_split ≤ (dfs (buchiGraph vertices vertices_nodup vertices_complete na).transpose
              (decreasingFinishAll
                (buchiGraph vertices vertices_nodup vertices_complete na))).forestRoots.length +
            2 * (dfs (buchiGraph vertices vertices_nodup vertices_complete na).transpose
              (decreasingFinishAll
                (buchiGraph vertices vertices_nodup vertices_complete na))).preorder.length +
            1 ∧
        c_scan = (kosarajuIsEmptyBC vertices vertices_nodup vertices_complete na
            (buchiGraph vertices vertices_nodup vertices_complete na) rfl).2 ∧
        c_scan ≤ (startReachable (· ∈ na.start)
            (buchiGraph vertices vertices_nodup vertices_complete na)).length +
          ((kosarajuSCCs
              (buchiGraph vertices vertices_nodup vertices_complete na)).map
            fun block => 1 +
              (block.map fun s =>
                ((buchiGraph vertices vertices_nodup vertices_complete na).adjacency
                  s).length).sum +
              2 * block.length).sum ∧
        n₁ + n₂ + n₃ + c_split + c_scan ≤
          14 * (buchiGraph vertices vertices_nodup vertices_complete na).vertices.length +
          1 +
          3 * (((buchiGraph vertices vertices_nodup vertices_complete na).vertices.map
              fun v => ((buchiGraph vertices vertices_nodup vertices_complete na).adjacency
                v).length).sum +
            ((buchiGraph vertices vertices_nodup vertices_complete na).transpose.vertices.map
            fun v => ((buchiGraph vertices vertices_nodup vertices_complete na).transpose.adjacency
              v).length).sum))

end Cslib.BuchiLinearEmptinessWanted
