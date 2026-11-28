/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST CIRCUIT with negative lengths: definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCircuitNegativeLengths

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

end MetaMathlibExt.Complexity.NPComplete.ShortestCircuitNegativeLengths
