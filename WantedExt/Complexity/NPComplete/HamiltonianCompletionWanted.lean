/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN COMPLETION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT34] HAMILTONIAN COMPLETION;
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9 (HAMILTONIAN CIRCUIT);
D. Gamarnik and M. Sviridenko, "Hamiltonian completions of sparse random graphs", Discrete
Applied Mathematics 152 (2005), 139-158, doi:10.1016/j.dam.2005.05.001.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCompletion

/-!
# HAMILTONIAN COMPLETION is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is there a superset
`E'` containing `E` such that `|E' - E| ≤ K` and the graph `G' = (V, E')` has a Hamiltonian
circuit?

The superset `E'` is a simple graph `H ≥ G` on the same vertices, `|E' - E|` is
`(H.edgeSet \ G.edgeSet).ncard`, and a Hamiltonian circuit is a closed walk `p` with
`p.IsHamiltonianCycle` (a cycle through every vertex exactly once). Mathlib's
`SimpleGraph.IsHamiltonian` holds vacuously on one vertex, so the existence of a Hamiltonian
cycle is stated directly; it fails on fewer than three vertices.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev HamiltonianCompletionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : HamiltonianCompletionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |V|`. -/
def WellFormed (i : HamiltonianCompletionInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some simple graph `H ≥ G` on the same vertices has at most `K` edges outside `G` and a
Hamiltonian cycle. -/
def HamiltonianCompletionFeasible (i : HamiltonianCompletionInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), Graph i ≤ H ∧
    (H.edgeSet \ (Graph i).edgeSet).ncard ≤ i.2.2 ∧
    ∃ v, ∃ p : H.Walk v v, p.IsHamiltonianCycle

open Classical in
/-- HAMILTONIAN COMPLETION as a decision problem over bitstrings. -/
noncomputable def hamiltonianCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCompletionInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCompletionFeasible i)
  | none => false

/-- **HAMILTONIAN COMPLETION is NP-complete.** Source: Garey and Johnson (1979), [GT34];
Karp (1972); Gamarnik and Sviridenko (2005). -/
public theorem_wanted hamiltonianCompletion_npComplete :
    hamiltonianCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianCompletionDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCompletion
