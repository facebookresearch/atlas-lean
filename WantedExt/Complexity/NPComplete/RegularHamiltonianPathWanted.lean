/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on k-regular graphs (fixed k ≥ 3) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH;
C. Picouleau, "Complexity of the Hamiltonian cycle in regular graph problem", Theoretical
Computer Science 131 (1994), 463-473, doi:10.1016/0304-3975(94)90185-6;
M. R. Garey, D. S. Johnson and R. E. Tarjan, "The planar Hamiltonian circuit problem is
NP-complete", SIAM Journal on Computing 5 (1976), 704-714, doi:10.1137/0205049.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegularHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected

/-!
# HAMILTONIAN PATH on k-regular graphs (fixed k ≥ 3) is NP-complete

Fix an integer `k ≥ 3`.
INSTANCE: a `k`-regular graph `G = (V, E)`, that is, a finite simple graph in which every vertex
has degree exactly `k`.
QUESTION: does `G` contain a Hamiltonian path, that is, a simple path through every vertex
(endpoints not specified)?

Picouleau (1994, abstract): "The problem of deciding whether a 3-regular graph has a hamiltonian
cycle (or path) was proved NP-complete. In this paper, we prove that for any fixed k [larger
than 3], deciding whether a k-regular graph has a hamiltonian cycle (or path) is a NP-complete
problem." The case `k = 3` is in Garey and Johnson: the [GT39] comment reads "Remains
NP-complete under restrictions (1) and (2) for HAMILTONIAN CIRCUIT", restriction (1) of [GT37]
being "G is planar, cubic, 3-connected, and has no face with fewer than 5 edges" (Garey, Johnson
and Tarjan 1976).

`k` is fixed, not part of the instance: the decision problem is
`regularHamiltonianPathDec k`, and the theorem holds for every `k ≥ 3`. The instance, its
well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted` ([GT39]: a simple graph on
`Fin n`, `n > 0`, given by an edge list; a Hamiltonian path is an ordering of all vertices in
which consecutive vertices are adjacent). The restriction adds that the graph is `k`-regular,
Mathlib's `SimpleGraph.IsRegularOfDegree k`.

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
/-- Well-formedness of an instance for the fixed degree `k`: a well-formed HAMILTONIAN PATH
instance whose graph is `k`-regular (every vertex has degree exactly `k`). -/
def WellFormed (k : ℕ) (i : HamiltonianPathUndirectedInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed i ∧ (Graph i).IsRegularOfDegree k

open Classical in
/-- HAMILTONIAN PATH on `k`-regular graphs, for the fixed `k`, as a decision problem over
bitstrings. -/
noncomputable def regularHamiltonianPathDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed k i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN PATH on k-regular graphs is NP-complete for every fixed `k ≥ 3`.**
Source: Garey and Johnson (1979), [GT39]; Picouleau (1994). -/
public theorem_wanted regularHamiltonianPath_npComplete (k : ℕ) (_hk : 3 ≤ k) :
    regularHamiltonianPathDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (regularHamiltonianPathDec k)

end MetaMathlibExt.Complexity.NPComplete.RegularHamiltonianPath
