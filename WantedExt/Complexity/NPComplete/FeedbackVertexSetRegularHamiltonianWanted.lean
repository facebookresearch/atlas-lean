/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEEDBACK VERTEX SET on k-regular Hamiltonian graphs (k ≥ 4) is NP-complete

Source:
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Section 3.3, Theorem 3.29
(and Theorem 3.30 for `k = 5`, Theorem 3.5 for `k = 4`);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT7] FEEDBACK VERTEX SET (undirected version in
the comment; the parent problem);
ISGCI, *Information System on Graph Classes and their Inclusions*, class
"5-regular ∩ hamiltonian" (gc_1317), problem Feedback vertex set: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetRegularHamiltonian

open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSet
  (FeedbackVertexSetInstance Graph FeedbackVertexSetFeasible)

/-!
# FEEDBACK VERTEX SET on k-regular Hamiltonian graphs (k ≥ 4) is NP-complete

For each fixed `k ≥ 4`: INSTANCE: a graph `G = (V, E)` that is `k`-regular (every vertex has
degree `k`) and Hamiltonian (has a cycle through every vertex), and a bound `K`. QUESTION: is
there a set `S ⊆ V` of at most `K` vertices such that `G - S` is acyclic (a forest)?

Cavallaro, Section 3.3: "we will show that Feedback Vertex Set is NP-complete on `k`-regular
Hamiltonian graphs for every fixed `k ≥ 4`"; Theorem 3.29: "Feedback Vertex Set on `k`-regular
Hamiltonian graphs of even order with known Hamilton-cycle is NP-complete for every fixed
`k ≥ 4`". Its proof is an induction on `k ≥ 5`: the base is Theorem 3.30 ("Feedback Vertex Set
is NP-complete on 5-regular Hamiltonian graphs with known Hamilton-cycle"), and Lemma 3.40
reduces the `k`-regular case to the `(k + 1)`-regular one; the case `k = 4` is, as the thesis
notes, a special case of Theorem 3.5 (planar 4-regular Hamiltonian graphs). Feedback Vertex Set
asks, "given a graph `G` and some integer `k`, [...] whether there is a set of size `k` whose
deletion leaves `G` acyclic"; this module asks for at most `K` vertices, as the parent does, and
a superset of a feedback vertex set is one, so the two readings agree for `K ≤ |V|`. Hardness on
the subclasses the reductions output (even order, planar) gives hardness here, and dropping the
Hamiltonian cycle the reductions output gives a reduction to the problem stated here, where the
cycle is not part of the instance. For `k = 3` the problem is polynomial (Li and Liu, cited by
Cavallaro as Theorem 3.27; Corollary 3.28), so `4` is where hardness starts.

The instance type (vertex count `n`, edge list, bound `K`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`), its well-formedness (a simple edge list) and the
question (some `Finset` `S` with `|S| ≤ K` whose complement induces a subgraph satisfying Mathlib's
`SimpleGraph.IsAcyclic`) are those of FEEDBACK VERTEX SET (`FeedbackVertexSetWanted`); this module
adds the class to well-formedness: Mathlib's `SimpleGraph.IsRegularOfDegree k`, and a closed walk
that is a Hamiltonian cycle in Mathlib's sense (`SimpleGraph.Walk.IsHamiltonianCycle`: a cycle
visiting every vertex exactly once). In particular the graph with no vertices, which is vacuously
`k`-regular, is excluded, since a cycle needs a vertex. (Mathlib's `SimpleGraph.IsHamiltonian`
differs from this only on the one-vertex graph, where it holds vacuously.) Membership in NP takes
`S` together with a Hamiltonian cycle as the certificate; degrees are checked in polynomial time.
Every vertex has degree `k ≥ 4`, so `n ≤ |E|` and the binary vertex count does not make the encoding
succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open Classical in
/-- Well-formedness of an instance for a fixed `k`: a well-formed FEEDBACK VERTEX SET instance
(a simple edge list on `Fin n`) whose graph is `k`-regular and has a Hamiltonian cycle. -/
def WellFormed (k : ℕ) (i : FeedbackVertexSetInstance) : Prop :=
  FeedbackVertexSet.WellFormed i ∧ (Graph i).IsRegularOfDegree k ∧
    ∃ (a : Fin i.1) (p : (Graph i).Walk a a), p.IsHamiltonianCycle

open Classical in
/-- FEEDBACK VERTEX SET on `k`-regular Hamiltonian graphs as a decision problem over
bitstrings. -/
noncomputable def feedbackVertexSetRegularHamiltonianDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FeedbackVertexSetInstance) x with
  | some i => decide (WellFormed k i ∧ FeedbackVertexSetFeasible i)
  | none => false

/-- **FEEDBACK VERTEX SET on `k`-regular Hamiltonian graphs is NP-complete for every fixed
`k ≥ 4`.** Source: Cavallaro (2019), Theorem 3.29; Garey and Johnson (1979), [GT7] (parent
problem). -/
public theorem_wanted feedbackVertexSetRegularHamiltonian_npComplete (k : ℕ) (_hk : 4 ≤ k) :
    feedbackVertexSetRegularHamiltonianDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (feedbackVertexSetRegularHamiltonianDec k)

end MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetRegularHamiltonian
