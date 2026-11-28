/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH BETWEEN TWO POINTS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH, comment, and
Section 3.1.4, p. 60 (HAMILTONIAN PATH BETWEEN TWO POINTS, by a modification of the
transformation from VERTEX COVER to HAMILTONIAN CIRCUIT);
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations* (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import CSLibExt.Complexity.NPComplete.HamiltonianPathUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathBetweenTwoPoints

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, start vertex `u`, end
vertex `v`. -/
abbrev HamiltonianPathBetweenTwoPointsInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : HamiltonianPathBetweenTwoPointsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the vertex count and edge list form a well-formed
HAMILTONIAN PATH instance (`0 < n`, no duplicate edges in either orientation, no self-loops,
endpoints in range), and `u` and `v` are vertices below `n`. -/
def WellFormed (i : HamiltonianPathBetweenTwoPointsInstance) : Prop :=
  HamiltonianPathUndirected.WellFormed (i.1, i.2.1) ∧ i.2.2.1 < i.1 ∧ i.2.2.2 < i.1

/-- Some walk from `u` to `v` visits every vertex exactly once. -/
def HamiltonianPathBetweenTwoPointsFeasible (i : HamiltonianPathBetweenTwoPointsInstance) :
    Prop :=
  ∃ (hu : i.2.2.1 < i.1) (hv : i.2.2.2 < i.1)
    (p : (Graph i).Walk ⟨i.2.2.1, hu⟩ ⟨i.2.2.2, hv⟩), p.IsHamiltonian

open Classical in
/-- HAMILTONIAN PATH BETWEEN TWO POINTS as a decision problem over bitstrings. -/
noncomputable def hamiltonianPathBetweenTwoPointsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianPathBetweenTwoPointsInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianPathBetweenTwoPointsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathBetweenTwoPoints
