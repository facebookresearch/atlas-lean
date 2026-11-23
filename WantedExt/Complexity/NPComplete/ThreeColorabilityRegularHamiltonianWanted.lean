/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY on k-regular Hamiltonian graphs (k ≥ 4) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the parent
problem);
H. Fleischner and G. Sabidussi, "3-colorability of 4-regular Hamiltonian graphs", Journal of
Graph Theory 42(2) (2003), 125-140, doi:10.1002/jgt.10079 (`k = 4`);
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 4.9 (`k = 4`,
attributed to Fleischner and Sabidussi) and Theorem 4.10 (every fixed `k ≥ 4`);
ISGCI, *Information System on Graph Classes and their Inclusions*, classes
"4-regular ∩ hamiltonian" (gc_1318) and "5-regular ∩ hamiltonian" (gc_1317), problem
3-Colourability: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityRegularHamiltonian

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# 3-COLORABILITY on k-regular Hamiltonian graphs (k ≥ 4) is NP-complete

For each fixed `k ≥ 4`: INSTANCE: a finite simple undirected graph `G = (V, E)` that is
`k`-regular (every vertex has degree `k`) and Hamiltonian (has a cycle through every vertex).
QUESTION: is `G` 3-colorable, that is, is there a map `c : V → {1, 2, 3}` with `c(u) ≠ c(v)` for
every edge `uv`?

This is GRAPH K-COLORABILITY (`GraphColoringWanted`, Garey and Johnson [GT4]) with `K = 3`,
restricted to `k`-regular Hamiltonian graphs, one decision problem for each `k`. The instance,
the graph and the question are those of `GraphColoringWanted`, reused unchanged: vertex count,
edge list on `Fin n` and number of colors `K`, with `GraphColoring.WellFormed` (a simple edge
list), `GraphColoring.Graph` and `GraphColoring.GraphColoringFeasible` (`(Graph i).Colorable K`).
The restriction adds to well-formedness `K = 3`, `k`-regularity (Mathlib's
`SimpleGraph.IsRegularOfDegree k`) and Hamiltonicity (Mathlib's `SimpleGraph.IsHamiltonian`: a
Hamiltonian cycle exists; Mathlib counts the one-vertex graph as Hamiltonian, which is not
`k`-regular for `k ≥ 4`). The Hamiltonian cycle is not part of the instance; membership in NP
takes a 3-coloring together with a Hamiltonian cycle as the certificate, and regularity is
checked in polynomial time.

Fleischner and Sabidussi prove 3-colorability NP-complete for 4-regular Hamiltonian graphs
whose edges off a given Hamiltonian cycle form non-selfcrossing cycles of a constant length
`≥ 4`, a subclass of the 4-regular Hamiltonian graphs. Cavallaro's thesis records the 4-regular
case as Theorem 4.9 and proves Theorem 4.10: 3-COLORING on `k`-regular Hamiltonian graphs with
known Hamiltonian cycle is NP-complete for every fixed `k ≥ 4`, by reductions from the
`k`-regular to the `(k + 1)`-regular case. Since the reductions produce Hamiltonian graphs, they
also reduce to this problem, whose instances omit the cycle. For `k = 3`, Brooks' theorem makes
the problem polynomial-time solvable (Cavallaro, Corollary 4.8).

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
/-- Well-formedness of an instance for a fixed `k`: a well-formed GRAPH K-COLORABILITY instance
(a simple edge list on `Fin n`) with `K = 3` whose graph is `k`-regular and Hamiltonian. -/
def WellFormed (k : ℕ) (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ (Graph i).IsRegularOfDegree k ∧
    (Graph i).IsHamiltonian

open Classical in
/-- 3-COLORABILITY on `k`-regular Hamiltonian graphs as a decision problem over bitstrings. -/
noncomputable def threeColorabilityRegularHamiltonianDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed k i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

/-- **3-COLORABILITY on `k`-regular Hamiltonian graphs is NP-complete for every fixed
`k ≥ 4`.** Source: Fleischner and Sabidussi (2003) (`k = 4`); Cavallaro (2019), Theorem 4.10;
Garey and Johnson (1979), [GT4] (parent problem). -/
public theorem_wanted threeColorabilityRegularHamiltonian_npComplete (k : ℕ) (_hk : 4 ≤ k) :
    threeColorabilityRegularHamiltonianDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (threeColorabilityRegularHamiltonianDec k)

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityRegularHamiltonian
