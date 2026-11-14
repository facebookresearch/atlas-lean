/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST CIRCUIT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND28] LONGEST
CIRCUIT (transformation from HAMILTONIAN CIRCUIT);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
Computer Computations*, Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestCircuit

/-!
# LONGEST CIRCUIT is NP-complete

INSTANCE: a graph `G = (V, E)`, a length `l(e) ∈ ℤ⁺` for each `e ∈ E`, and a positive integer
`K`. QUESTION: is there a simple circuit in `G` whose length (the sum of the lengths of its
edges) is `K` or more?

This is the edge-weighted problem; its special case with every length `1`, where the length of
a circuit is its number of edges, is `MetaMathlibExt.Complexity.NPComplete.LongestCycle`. With
unit lengths and `K = |V|` the question is HAMILTONIAN CIRCUIT, Garey and Johnson's
transformation. A simple circuit is Mathlib's `SimpleGraph.Walk.IsCycle` (a closed walk of
length at least three with no repeated vertex other than its endpoints).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list with lengths (an entry
`(u, v, l)` is the edge `{u, v}` of length `l`), and the bound `K`. -/
abbrev LongestCircuitInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : LongestCircuitInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- The length of an edge `s`: the length recorded for the list entry whose endpoints are the
endpoints of `s` (unique under `WellFormed`). -/
def edgeLength (i : LongestCircuitInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2).getD 0

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), every length is
positive, and `0 < K`. -/
def WellFormed (i : LongestCircuitInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    (∀ e ∈ i.2.1, 0 < e.2.2) ∧ 0 < i.2.2

/-- Some simple circuit has length at least `K`: a closed walk `c` that is a cycle and whose edge
lengths sum to at least `K`. -/
def LongestCircuitFeasible (i : LongestCircuitInstance) : Prop :=
  ∃ v, ∃ c : (Graph i).Walk v v, c.IsCycle ∧ i.2.2 ≤ (c.edges.map (edgeLength i)).sum

open Classical in
/-- LONGEST CIRCUIT as a decision problem over bitstrings. -/
noncomputable def longestCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestCircuitInstance) x with
  | some i => decide (WellFormed i ∧ LongestCircuitFeasible i)
  | none => false

/-- **LONGEST CIRCUIT is NP-complete.** Source: Garey and Johnson (1979), [ND28]; Karp (1972). -/
public theorem_wanted longestCircuit_npComplete :
    longestCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestCircuitDec

end MetaMathlibExt.Complexity.NPComplete.LongestCircuit
