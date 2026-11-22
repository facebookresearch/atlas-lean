/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH (UNDIRECTED) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), HAMILTONIAN PATH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected

/-!
# HAMILTONIAN PATH (UNDIRECTED) is NP-complete

An undirected graph on vertices 0, …, n - 1, given by an explicit edge list. The question is
whether the graph has a Hamiltonian path: a permutation of all vertices in which consecutive
vertices are adjacent.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list. -/
abbrev HamiltonianPathUndirectedInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : HamiltonianPathUndirectedInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2


/-- Well-formedness of an instance. -/
def WellFormed (i : HamiltonianPathUndirectedInstance) : Prop :=
  0 < i.1 ∧ i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- A Hamiltonian path. -/
def HamiltonianPathUndirectedFeasible
    (i : HamiltonianPathUndirectedInstance) : Prop :=
  ∃ path : List (Fin i.1), path.Nodup ∧ path.length = i.1 ∧ (∀ v, v ∈ path) ∧
    ∀ j (h : j + 1 < path.length),
      (Graph i).Adj (path[j]'(by omega)) (path[j + 1]'h)

open Classical in
/-- HAMILTONIAN PATH (UNDIRECTED) as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathUndirectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN PATH (UNDIRECTED) is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), HAMILTONIAN PATH. -/
public theorem_wanted hamiltonianPathUndirected_npComplete :
    hamiltonianPathUndirectedDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathUndirectedDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected
