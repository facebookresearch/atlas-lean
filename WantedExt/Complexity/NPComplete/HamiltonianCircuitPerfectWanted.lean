/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT for perfect graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
T. Akiyama, T. Nishizeki and N. Saito, "NP-completeness of the Hamiltonian cycle problem for
bipartite graphs", Journal of Information Processing 3 (1980), 73-76;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1;
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.PerfectGraph
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitPerfect

open HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance Graph HamiltonianCycleUndirectedFeasible)
open MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted (IsPerfect)

/-!
# HAMILTONIAN CIRCUIT for perfect graphs is NP-complete

INSTANCE: a perfect graph `G = (V, E)`.
QUESTION: does `G` contain a Hamiltonian circuit?

This is HAMILTONIAN CIRCUIT ([GT37], `HamiltonianCycleUndirectedWanted`) restricted to perfect
graphs. Johnson's 1985 table and its 2022 revision by de Figueiredo, de Melo, Sasaki and Silva list
the entry as NP-complete. Akiyama, Nishizeki and Saito prove HAMILTONIAN CIRCUIT NP-complete for
bipartite graphs (planar, of maximum degree 3: `HamiltonianCircuitPlanarBipartiteSubcubicWanted`).
Bipartite graphs are perfect (an induced subgraph with an edge has chromatic number and clique
number 2, one without edges has both equal to 1, or 0 when empty), so that reduction produces
instances of this class. Membership in NP: a Hamiltonian circuit is a certificate, and whether a
graph is perfect is decidable in polynomial time: perfect graphs are the Berge graphs (no odd hole
or odd antihole) by the strong perfect graph theorem of Chudnovsky, Robertson, Seymour and Thomas
(Annals of Mathematics 164 (2006), 51-229, doi:10.4007/annals.2006.164.51), and Berge graphs are
recognized in polynomial time by Chudnovsky, Cornuéjols, Liu, Seymour and Vušković ("Recognizing
Berge graphs", Combinatorica 25 (2005), 143-186, doi:10.1007/s00493-005-0012-8). Adding or removing
isolated vertices does not change whether a graph is perfect, so the binary vertex count does not
make the problem succinct (an isolated vertex rules out a Hamiltonian circuit).

The instance, the graph, the parent well-formedness (at least one vertex and a simple edge list)
and the question are those of HAMILTONIAN CIRCUIT
(`HamiltonianCycleUndirected.HamiltonianCycleUndirectedInstance`,
`HamiltonianCycleUndirected.Graph`, `HamiltonianCycleUndirected.WellFormed`,
`HamiltonianCycleUndirected.HamiltonianCycleUndirectedFeasible`: at least three vertices and
Mathlib's `SimpleGraph.IsHamiltonian`); the restriction adds to `WellFormed` that the graph is
perfect.

A graph is perfect when every induced subgraph has chromatic number equal to its clique number;
this is MathlibExt's `MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect` (every
induced subgraph `G.induce s`, `s : Set V`, has `chromaticNumber = cliqueNum`), as in
`FeedbackVertexSetPerfectWanted`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance (at least one
vertex and a simple edge list on the vertices `0, ..., n - 1`) whose graph is perfect. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ IsPerfect (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT for perfect graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitPerfectDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT for perfect graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT37]; Akiyama, Nishizeki and Saito (1980); de Figueiredo, de Melo, Sasaki and Silva (2022),
Table 1. -/
public theorem_wanted hamiltonianCircuitPerfect_npComplete :
    hamiltonianCircuitPerfectDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitPerfectDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitPerfect
