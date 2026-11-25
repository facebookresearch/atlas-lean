/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST CIRCUIT with negative lengths is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND28] LONGEST CIRCUIT, comment
(p. 213: "The analogous directed and undirected problems, which ask for a simple circuit of
length K or less, can be solved in polynomial time ..., but are NP-complete if negative lengths
are allowed"), and problem [GT37] HAMILTONIAN CIRCUIT (all lengths `-1`, `K = -|V|`);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
Computer Computations*, Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCircuitNegativeLengths

/-!
# SHORTEST CIRCUIT with negative lengths is NP-complete

INSTANCE: a graph `G = (V, E)`, an integer length `l(e) ∈ ℤ` for each `e ∈ E` (negative lengths
allowed), and an integer `K`. QUESTION: is there a simple circuit in `G` whose length (the sum of
the lengths of its edges) is `K` or less?

This is the undirected problem recorded in the comment of Garey and Johnson's [ND28] LONGEST
CIRCUIT (`LongestCircuitWanted`), with the inequality reversed and negative lengths allowed;
with non-negative lengths it is solvable in polynomial time. With every length `-1` and
`K = -|V|` the question is HAMILTONIAN CIRCUIT. A simple circuit is Mathlib's
`SimpleGraph.Walk.IsCycle` (a closed walk of length at least three with no repeated vertex other
than its endpoints). An integer is encoded as a pair of naturals `(positive part, negative part)`
whose difference it is, as in `ZeroOneILPWanted`; numbers use the binary encoding. The comment's
directed analogue is a separate problem and is not stated here.

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
`(u, v, (l⁺, l⁻))` is the edge `{u, v}` of length `l⁺ - l⁻`), and the bound `K` as
`(K⁺, K⁻)`, with `K = K⁺ - K⁻`. -/
abbrev ShortestCircuitNegativeLengthsInstance := ℕ × List (ℕ × ℕ × (ℕ × ℕ)) × (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ShortestCircuitNegativeLengthsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- The length of an edge `s`: the integer length recorded for the list entry whose endpoints
are the endpoints of `s` (unique under `WellFormed`). -/
def edgeLength (i : ShortestCircuitNegativeLengthsInstance) (s : Sym2 (Fin i.1)) : ℤ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map
    fun e => (e.2.2.1 : ℤ) - e.2.2.2).getD 0

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : ShortestCircuitNegativeLengthsInstance) : Prop :=
  (i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)

/-- Some simple circuit has total length at most `K`. -/
def ShortestCircuitNegativeLengthsFeasible (i : ShortestCircuitNegativeLengthsInstance) :
    Prop :=
  ∃ v, ∃ c : (Graph i).Walk v v, c.IsCycle ∧
    (c.edges.map (edgeLength i)).sum ≤ (i.2.2.1 : ℤ) - i.2.2.2

open Classical in
/-- SHORTEST CIRCUIT with negative lengths as a decision problem over bitstrings. -/
noncomputable def shortestCircuitNegativeLengthsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestCircuitNegativeLengthsInstance) x with
  | some i => decide (WellFormed i ∧ ShortestCircuitNegativeLengthsFeasible i)
  | none => false

/-- **SHORTEST CIRCUIT with negative lengths is NP-complete.** Source: Garey and Johnson (1979),
[ND28], comment, and [GT37]; Karp (1972). -/
public theorem_wanted shortestCircuitNegativeLengths_npComplete :
    shortestCircuitNegativeLengthsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestCircuitNegativeLengthsDec

end MetaMathlibExt.Complexity.NPComplete.ShortestCircuitNegativeLengths
