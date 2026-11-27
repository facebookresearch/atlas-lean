/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# P_4-BIPARTITE GRAPH RECOGNITION is NP-complete

Source:
C. T. Hoàng and V. B. Le, "P₄-free colorings and P₄-bipartite graphs", Discrete Mathematics and
Theoretical Computer Science 4 (2001), 109-122, doi:10.46298/dmtcs.272 (Lemma 1);
D. Achlioptas, "The complexity of G-free colourability", Discrete Mathematics 165/166 (1997),
21-30, doi:10.1016/S0012-365X(97)84217-3;
ISGCI (https://www.graphclasses.org/classes/gc_5.html), problem "Recognition" on
`P_4`-bipartite graphs: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ThreeColorabilityP4BipartiteWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.P4BipartiteRecognition

/-!
# P_4-BIPARTITE GRAPH RECOGNITION is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` `P_4`-bipartite, that is, can `V` be partitioned into two sets each of which
induces a graph with no induced path on four vertices (a `P_4`-free 2-coloring)?

Hoàng and Le (2001): "A vertex partition of a graph into disjoint subsets `V_i` is said to be a
`P_4`-free coloring if each color class `V_i` induces a subgraph without a chordless path on
four vertices (denoted by `P_4`). Examples of `P_4`-free 2-colorable graphs (also called
`P_4`-bipartite graphs) include …". Their Lemma 1 states: "Given a comparability graph `G`, it is
NP-complete to decide whether `G` is `P_4`-bipartite", so the problem is NP-complete on all
graphs (membership in NP: the partition is a certificate, checked over all quadruples).
Achlioptas (1997) had shown the more general `G`-free colourability results implying this for
two colours, as Hoàng and Le recall.

The class predicate is `ThreeColorabilityP4Bipartite.IsP4Bipartite` of
`ThreeColorabilityP4BipartiteWanted`, reused unchanged: a set `A` and its complement `Aᶜ`
(either may be empty), each inducing (Mathlib's `G.induce`) a graph with no induced copy of
Mathlib's `SimpleGraph.pathGraph 4`. The graph is given by an edge list on `Fin n` as in the
other graph statements of this directory (`Cslib.Complexity.Karp.edgeGraph`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev P4BipartiteRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : P4BipartiteRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : P4BipartiteRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph of the instance is `P_4`-bipartite. -/
def P4BipartiteRecognitionFeasible (i : P4BipartiteRecognitionInstance) : Prop :=
  ThreeColorabilityP4Bipartite.IsP4Bipartite (Graph i)

open Classical in
/-- P_4-BIPARTITE GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def p4BipartiteRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := P4BipartiteRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ P4BipartiteRecognitionFeasible i)
  | none => false

/-- **P_4-BIPARTITE GRAPH RECOGNITION is NP-complete.** Source: Hoàng and Le (2001), Lemma 1;
Achlioptas (1997). -/
public theorem_wanted p4BipartiteRecognition_npComplete :
    p4BipartiteRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L p4BipartiteRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.P4BipartiteRecognition
