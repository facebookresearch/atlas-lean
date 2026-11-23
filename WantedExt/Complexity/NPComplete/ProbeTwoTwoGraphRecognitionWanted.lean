/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PROBE (2,2)-GRAPH RECOGNITION is NP-complete

Source:
S. Dantas, L. Faria, C. M. H. de Figueiredo and R. B. Teixeira, "The (k, ℓ) unpartitioned probe
problem NP-complete versus polynomial dichotomy", Information Processing Letters 116 (2016),
294-298, doi:10.1016/j.ipl.2015.11.004;
S. Dantas, L. Faria, C. M. H. de Figueiredo and R. B. Teixeira, "The generalized split probe
problem", Electronic Notes in Discrete Mathematics 44 (2013), 39-45,
doi:10.1016/j.endm.2013.10.007;
ISGCI (https://www.graphclasses.org/classes/gc_1269.html), problem "Recognition" on probe
(2,2)-colorable graphs: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ProbeTwoTwoGraphRecognition

/-!
# PROBE (2,2)-GRAPH RECOGNITION is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)`.
QUESTION: is `G` a probe `(2,2)`-graph, that is, can `V` be partitioned into probes `P` and an
independent set `N` of non-probes such that, after adding some edges between non-probes, the
graph has a partition into at most two independent sets and two cliques?

Dantas, Faria, de Figueiredo and Teixeira (2016), abstract: "A graph `G = (V, E)` is `C` probe if
`V` can be partitioned into two sets, probes `P` and non-probes `N`, where `N` is independent and
new edges may be added between non-probes such that the resulting graph is in the graph class
`C`. […] The `C` unpartitioned probe problem consists of an input graph `G` and the question: Is
`G` a `C` probe graph? A `(k, ℓ)`-partition of a graph `G` is a partition of its vertex set into
at most `k` independent sets and `ℓ` cliques. A graph is `(k, ℓ)` if it has a
`(k, ℓ)`-partition. We prove the full complexity dichotomy into NP-complete and polynomial for
`(k, ℓ)` unpartitioned probe problems: they are NP-complete if `k + ℓ ≥ 3`, and polynomial
otherwise." This is the case `k = ℓ = 2`. ISGCI cites the authors' 2013 conference paper on
generalized split probe problems. Recognizing `(2,2)`-graphs themselves is polynomial
(Brandstädt; Feder et al.). Membership in NP: the probe partition, the added edges and the
`(2,2)`-partition are a polynomial-size certificate.

`IsTwoTwoGraph H` asks for a labelling `c : Fin n → Fin 4` whose classes `0` and `1` are
independent sets and whose classes `2` and `3` are cliques of `H` (Mathlib's
`SimpleGraph.IsIndepSet` and `SimpleGraph.IsClique`); classes may be empty, so this is "at most
two independent sets and two cliques". `IsProbeTwoTwoGraph G` asks for the non-probes `N`, an
independent set of `G`, and a supergraph `H ≥ G` whose extra edges join two non-probes, with `H`
a `(2,2)`-graph; the probes are `Nᶜ`. The graph is given by an edge list on `Fin n` as in the
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
abbrev ProbeTwoTwoGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ProbeTwoTwoGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : ProbeTwoTwoGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `H` is a `(2,2)`-graph: its vertex set splits into at most two independent sets (labels `0`
and `1`) and at most two cliques (labels `2` and `3`). -/
def IsTwoTwoGraph {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ c : Fin n → Fin 4, H.IsIndepSet {v | c v = 0} ∧ H.IsIndepSet {v | c v = 1} ∧
    H.IsClique {v | c v = 2} ∧ H.IsClique {v | c v = 3}

/-- `G` is a probe `(2,2)`-graph: some independent set `N` of non-probes admits a supergraph
`H ≥ G`, adding only edges between non-probes, that is a `(2,2)`-graph. -/
def IsProbeTwoTwoGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ N : Set (Fin n), G.IsIndepSet N ∧
    ∃ H : SimpleGraph (Fin n), G ≤ H ∧ (∀ u v, H.Adj u v → G.Adj u v ∨ (u ∈ N ∧ v ∈ N)) ∧
      IsTwoTwoGraph H

/-- The graph of the instance is a probe `(2,2)`-graph. -/
def ProbeTwoTwoGraphRecognitionFeasible (i : ProbeTwoTwoGraphRecognitionInstance) : Prop :=
  IsProbeTwoTwoGraph (Graph i)

open Classical in
/-- PROBE (2,2)-GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def probeTwoTwoGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ProbeTwoTwoGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ ProbeTwoTwoGraphRecognitionFeasible i)
  | none => false

/-- **PROBE (2,2)-GRAPH RECOGNITION is NP-complete.** Source: Dantas, Faria, de Figueiredo and
Teixeira (2016; announced 2013). -/
public theorem_wanted probeTwoTwoGraphRecognition_npComplete :
    probeTwoTwoGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L probeTwoTwoGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.ProbeTwoTwoGraphRecognition
