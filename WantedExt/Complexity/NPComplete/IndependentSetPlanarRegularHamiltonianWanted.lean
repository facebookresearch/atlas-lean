/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on planar k-regular Hamiltonian graphs (k = 4, 5) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET (the parent
problem);
H. Fleischner, G. Sabidussi and V. I. Sarvanov, "Maximum independent sets in 3- and 4-regular
Hamiltonian graphs", Discrete Mathematics 310(20) (2010), 2742-2749,
doi:10.1016/j.disc.2010.05.028 (`k = 4`; Proposition 4.3 as cited by Cavallaro);
D. Cavallaro, *Hamiltonicity and the computational complexity of graph problems*, Bachelor
thesis, Technische Universität Berlin (2019),
https://fpt.akt.tu-berlin.de/publications/theses/BA-Cavallaro.pdf, Theorem 5.7 (`k = 4`,
attributed to Fleischner, Sabidussi and Sarvanov) and Theorem 5.8 (`k = 5`);
ISGCI, *Information System on Graph Classes and their Inclusions*, classes
"4-regular ∩ hamiltonian ∩ planar" (gc_1315) and "5-regular ∩ hamiltonian ∩ planar" (gc_1320),
problem Independent set: NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.IndependentSetPlanarRegularHamiltonianDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetPlanarRegularHamiltonian

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-!
# INDEPENDENT SET on planar k-regular Hamiltonian graphs (k = 4, 5) is NP-complete

For `k = 4` and for `k = 5`: INSTANCE: a graph `G = (V, E)` that is planar, `k`-regular (every
vertex has degree `k`) and Hamiltonian (has a cycle through every vertex), and a positive integer
`K ≤ |V|`. QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset
`V' ⊆ V` with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) restricted to planar `k`-regular Hamiltonian graphs, one
decision problem for each `k`. The instance type (vertex count `n`, edge list, bound `K`), the
graph (`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (a `Finset` of at least
`K` vertices whose coercion is Mathlib's `SimpleGraph.IsIndepSet`) are those of the edge-list
INDEPENDENT SET statement on `main`, `WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`,
whose triangle-free restriction lives only in its `WellFormed`, which this module does not use.
`WellFormed` here asks for a simple edge list on `Fin n`, `0 < K ≤ |V|` ([GT20]'s instance
class), and the class: planar, the shared MathlibExt predicate `SimpleGraph.IsPlanar` (a
crossing-free straight-line drawing; by Fáry's theorem this is planarity for finite simple
graphs, as in `PlanarDegreeFourThreeColorabilityWanted`), `k`-regular, Mathlib's
`SimpleGraph.IsRegularOfDegree k`, and Hamiltonian, Mathlib's `SimpleGraph.IsHamiltonian`.
The Hamiltonian cycle is not part of the instance; membership in NP takes `V'` together with a
Hamiltonian cycle as the certificate, and regularity and planarity are checked in polynomial
time.

Fleischner, Sabidussi and Sarvanov prove INDEPENDENT SET NP-complete on planar cubic Hamiltonian
graphs and, from that, on 4-regular Hamiltonian graphs; Cavallaro's thesis records the planar
4-regular case as their Proposition 4.3 (Theorem 5.7 there) and proves the planar 5-regular
case (Theorem 5.8) by a reduction from the planar cubic Hamiltonian case. ISGCI records both
classes as NP-complete. For `k ≥ 6` no planar `k`-regular graph exists. Binary encoding of all
numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **INDEPENDENT SET on planar `k`-regular Hamiltonian graphs is NP-complete for `k = 4` and
`k = 5`.** Source: Fleischner, Sabidussi and Sarvanov (2010) (`k = 4`); Cavallaro (2019),
Theorem 5.8 (`k = 5`); Garey and Johnson (1979), [GT20] (parent problem). -/
public theorem_wanted independentSetPlanarRegularHamiltonian_npComplete (k : ℕ)
    (_hk : k = 4 ∨ k = 5) :
    independentSetPlanarRegularHamiltonianDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (independentSetPlanarRegularHamiltonianDec k)

end MetaMathlibExt.Complexity.NPComplete.IndependentSetPlanarRegularHamiltonian
