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
public import CSLibExt.Computability.Automata.NA.BuchiKosarajuEmptiness

@[expose] public section

namespace Cslib.BuchiLinearEmptinessWanted

open Filter ωSequence Cslib.Automata.ωAcceptor
open Cslib.Automata.NA
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.DepthFirstSearch
open Cslib.Algorithms.Lean.StronglyConnectedComponents
open Cslib.BuchiKosarajuEmptiness

/-!
# Büchi emptiness via Kosaraju-Sharir SCC decomposition: deferred statements

The executable decomposition `kosarajuSCCs`, the transition graph `buchiGraph`, the emptiness
scanner `kosarajuIsEmptyB` and the costed evaluators `splitPreorderC` and `kosarajuIsEmptyBC`,
with their proved correctness and cost lemmas, are in
`CSLibExt.Computability.Automata.NA.BuchiKosarajuEmptiness`; its module documentation describes
the abstract cost model and what it leaves out (the cost of evaluating adjacency lists). This file
states what is deferred:

* `kosaraju_correct_wanted`: the second-pass DFS trees are exactly the strongly connected
  components (`IsSCCPartition`), and the two DFS passes take at most `4V + 2(E + E₂)` abstract
  transitions.
* `buchi_emptiness_via_kosaraju_wanted`: the scanner decides Büchi emptiness, and the three DFS
  passes, the split and the scanner together cost at most `14V + 3(E + E₂) + 1` in the abstract
  cost model.
-/

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
