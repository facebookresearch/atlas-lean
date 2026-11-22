/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT for squares of graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT, p. 199,
comment (3): "if G is the square of a graph", credited there to V. Chvátal (1976, private
communication);
P. Underground, "On graphs with Hamiltonian squares", Discrete Mathematics 21 (1978), 323,
doi:10.1016/0012-365X(78)90164-4 (deciding whether the square of a given graph is Hamiltonian is
NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphSquareRootWanted
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitSquares

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT for squares of graphs is NP-complete

INSTANCE: a graph `G = (V, E)` that is the square of a graph, i.e. `G = H²` for some graph `H`
on `V` (distinct vertices are adjacent in `H²` when their distance in `H` is `1` or `2`).
QUESTION: does `G` contain a Hamiltonian circuit?

This is restriction (3) of [GT37] HAMILTONIAN CIRCUIT in Garey and Johnson's comment. The
instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted` (a simple graph on `Fin n`,
`n > 0`, given by an edge list; a Hamiltonian circuit needs at least three vertices). The
restriction adds that the graph has a square root,
`GraphSquareRoot.GraphSquareRootFeasible` of
`WantedExt.Complexity.NPComplete.GraphSquareRootWanted`: some `H` on `Fin n` has
`H.square = G` (MathlibExt's `SimpleGraph.square`).

Underground proves that deciding whether the square of a given graph `H` is Hamiltonian is
NP-complete; computing `H²` from `H` takes polynomial time and gives an instance of this
problem. The root `H` is not part of the instance; it and a Hamiltonian circuit together are a
polynomial-size certificate, so the restriction does not affect membership in NP.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph is
the square of a graph on the same vertices. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ GraphSquareRoot.GraphSquareRootFeasible i

open Classical in
/-- HAMILTONIAN CIRCUIT for squares of graphs as a decision problem over bitstrings. -/
noncomputable def hamiltonianCircuitSquaresDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT for squares of graphs is NP-complete.** Source: Garey and Johnson
(1979), [GT37], comment (3); Underground (1978). -/
public theorem_wanted hamiltonianCircuitSquares_npComplete :
    hamiltonianCircuitSquaresDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCircuitSquaresDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCircuitSquares
