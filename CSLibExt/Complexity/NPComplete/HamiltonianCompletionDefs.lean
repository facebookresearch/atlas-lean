/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN COMPLETION: definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianCompletion

/-- An instance: vertex list (well-formed when it is `[0, 1, ..., n - 1]`; vertices `Fin n`),
edge list, bound `K`. -/
abbrev HamiltonianCompletionInstance := List ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : HamiltonianCompletionInstance) : SimpleGraph (Fin i.1.length) :=
  Cslib.Complexity.Karp.edgeGraph i.1.length i.2.1

/-- Well-formedness of an instance: the vertex list is `[0, 1, ..., n - 1]` with `n` its length,
the edge list describes a simple graph on `Fin n` (no duplicate edges in either orientation, no
self-loops, endpoints in range), and `0 < K ≤ |V| = n`. -/
def WellFormed (i : HamiltonianCompletionInstance) : Prop :=
  i.1 = List.range i.1.length ∧
    (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2 < i.1.length ∧ e.1 ≠ e.2 ∧
      (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1.length

/-- Some simple graph `H ≥ G` on the same vertices has at most `K` edges outside `G` and a
Hamiltonian cycle. -/
def HamiltonianCompletionFeasible (i : HamiltonianCompletionInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1.length), Graph i ≤ H ∧
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

end MetaMathlibExt.Complexity.NPComplete.HamiltonianCompletion
