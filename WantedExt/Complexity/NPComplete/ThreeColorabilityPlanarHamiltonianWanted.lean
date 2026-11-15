/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY on planar Hamiltonian graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the parent
problem);
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 4.5 and Lemma 4.6;
D. P. Dailey, "Uniqueness of colorability and colorability of planar 4-regular graphs are
NP-complete", Discrete Mathematics 30(3) (1980), 289-293, doi:10.1016/0012-365X(80)90236-8 (the
source problem of Cavallaro's reduction);
ISGCI, *Information System on Graph Classes and their Inclusions*, class
"hamiltonian ∩ planar" (gc_1294), problem 3-Colourability: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityPlanarHamiltonian

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# 3-COLORABILITY on planar Hamiltonian graphs is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` that is planar and Hamiltonian (has a
cycle through every vertex).
QUESTION: is `G` 3-colorable, that is, is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)` for
every edge `uv`?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`, Garey and Johnson [GT4]) with `K = 3`,
restricted to planar Hamiltonian graphs. The instance, the graph and the question are those of
`GraphColoringWanted`, reused unchanged: vertex count, edge list on `Fin n` and number of colors
`K`, with `GraphColoring.WellFormed` (a simple edge list), `GraphColoring.Graph` and
`GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable K`). The restriction adds to
well-formedness `K = 3`, planarity, the shared MathlibExt predicate `SimpleGraph.IsPlanar` (a
crossing-free straight-line drawing; by Fáry's theorem this is planarity for finite simple
graphs, as in `PlanarDegreeFourThreeColorabilityWanted`), and Hamiltonicity: at least 3
vertices and Mathlib's `SimpleGraph.IsHamiltonian` (a Hamiltonian cycle exists), as in
`HamiltonianCycleUndirectedWanted`; the bound excludes the one-vertex graph, which Mathlib counts
as Hamiltonian although it has no cycle. The Hamiltonian cycle is not part of the instance;
membership in NP takes a 3-coloring together with a Hamiltonian cycle as the certificate, and
planarity is checked in polynomial time.

Cavallaro's thesis proves Theorem 4.5, "3-Coloring is NP-complete on planar Hamiltonian
graphs", by Lemma 4.6: from a 4-regular planar graph `G` one constructs in polynomial time a
planar Hamiltonian graph that is 3-colorable if and only if `G` is (merging the cycles of a
2-factor through added degree-2 vertices), and 3-colorability of planar 4-regular graphs is
NP-complete by Dailey.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance (a simple edge
list on `Fin n`) with `K = 3` whose graph is planar and Hamiltonian (`n ≥ 3` and a Hamiltonian
cycle exists). -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ (Graph i).IsPlanar ∧ 3 ≤ i.1 ∧
    (Graph i).IsHamiltonian

open Classical in
/-- 3-COLORABILITY on planar Hamiltonian graphs as a decision problem over bitstrings. -/
noncomputable def threeColorabilityPlanarHamiltonianDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **3-COLORABILITY on planar Hamiltonian graphs is NP-complete.** Source: Cavallaro (2019),
Theorem 4.5; Dailey (1980); Garey and Johnson (1979), [GT4] (parent problem). -/
public theorem_wanted threeColorabilityPlanarHamiltonian_npComplete :
    threeColorabilityPlanarHamiltonianDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threeColorabilityPlanarHamiltonianDec

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityPlanarHamiltonian
