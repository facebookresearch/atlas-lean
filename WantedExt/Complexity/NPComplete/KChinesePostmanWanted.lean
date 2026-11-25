/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-CHINESE POSTMAN is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MINIMUM K-CHINESE POSTMAN PROBLEM;
G. N. Frederickson, M. S. Hecht and C. E. Kim, "Approximation algorithms for some routing
problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017 (the k-person
minimax Chinese postman problem, among the NP-complete routing problems treated there).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ChinesePostmanMixedGraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KChinesePostman

open ChinesePostmanMixedGraphs (ChinesePostmanMixedGraphsInstance Step stepEnds stepLength)

/-!
# k-CHINESE POSTMAN is NP-complete

INSTANCE: a multigraph `G = (V, E)`, an initial vertex `s ∈ V`, a length `l(e) ∈ ℕ` for each
`e ∈ E`, a positive integer `k`, and a positive integer `K`. QUESTION: is there a collection of
`k` cycles, each containing `s`, that together traverse every edge of `G` at least once, such
that the longest of the `k` cycles has length at most `K`?

This is the decision version of MINIMUM K-CHINESE POSTMAN PROBLEM in the compendium of Crescenzi
and Kann, whose measure is the maximum length of the `k` cycles.

The vertices are `0, …, n - 1` and the edges are a list of triples `(u, v, l)` (joining `u` and
`v`, length `l`); repeated triples are parallel edges and `(v, v, l)` is a loop. As in postman
problems, a cycle is a closed walk from `s`, which may repeat vertices and edges, and its length
counts every traversal. Walks reuse the steps of `ChinesePostmanMixedGraphsWanted`, reading the
multigraph as a mixed graph without directed edges: the step `(false, j, true)` traverses edge
`j = (u, v, l)` from `u` to `v`, and `(false, j, false)` from `v` to `u`. Consecutive steps
meet, the first step starts at `s` and the last ends at `s`; the empty walk (staying at `s`, of
length `0`) is allowed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, the edges `(u, v, l)`, the initial vertex `s`, the number `k`
of cycles, and the bound `K`. -/
abbrev KChinesePostmanInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The multigraph as a mixed graph with no directed edges, whose steps are reused. -/
def mixed (i : KChinesePostmanInstance) : ChinesePostmanMixedGraphsInstance :=
  (i.1, [], i.2.1, i.2.2.2.2)

/-- A cycle through `s`: a walk of undirected steps along edges of the multigraph in which
consecutive steps meet, the first step starts at `s`, and the last step ends at `s`. -/
def IsCycleFrom (i : KChinesePostmanInstance) (w : List Step) : Prop :=
  (∀ st ∈ w, st.1 = false ∧ st.2.1 < i.2.1.length) ∧
    w.IsChain (fun a b => (stepEnds (mixed i) a).2 = (stepEnds (mixed i) b).1) ∧
    (∀ st ∈ w.head?, (stepEnds (mixed i) st).1 = i.2.2.1) ∧
    ∀ st ∈ w.getLast?, (stepEnds (mixed i) st).2 = i.2.2.1

/-- Well-formedness of an instance: every edge joins vertices below `n`, `s` is a vertex, and `k`
and `K` are positive. -/
def WellFormed (i : KChinesePostmanInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1) ∧ i.2.2.1 < i.1 ∧ 0 < i.2.2.2.1 ∧ 0 < i.2.2.2.2

/-- Some `k` cycles through `s`, each of length at most `K`, together traverse every edge. -/
def KChinesePostmanFeasible (i : KChinesePostmanInstance) : Prop :=
  ∃ cycles : List (List Step), cycles.length = i.2.2.2.1 ∧
    (∀ w ∈ cycles, IsCycleFrom i w ∧ (w.map (stepLength (mixed i))).sum ≤ i.2.2.2.2) ∧
    ∀ j < i.2.1.length, ∃ w ∈ cycles, ∃ st ∈ w, st.2.1 = j

open Classical in
/-- k-CHINESE POSTMAN as a decision problem over bitstrings. -/
noncomputable def kChinesePostmanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KChinesePostmanInstance) x with
  | some i => decide (WellFormed i ∧ KChinesePostmanFeasible i)
  | none => false

/-- **k-CHINESE POSTMAN is NP-complete.** Source: Crescenzi and Kann, MINIMUM K-CHINESE POSTMAN
PROBLEM; Frederickson, Hecht and Kim (1978). -/
public theorem_wanted kChinesePostman_npComplete :
    kChinesePostmanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kChinesePostmanDec

end MetaMathlibExt.Complexity.NPComplete.KChinesePostman
