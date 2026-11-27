/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH BETWEEN TWO POINTS is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HamiltonianPathBetweenTwoPoints

/-!
# HAMILTONIAN PATH BETWEEN TWO POINTS is NP-complete

INSTANCE: a graph `G = (V, E)` and two vertices `u, v ∈ V`.
QUESTION: does `G` contain a Hamiltonian path beginning at `u` and ending at `v`?

Garey and Johnson define the problem in Section 3.1.4 ("HAMILTONIAN PATH BETWEEN TWO POINTS is
the same as HAMILTONIAN PATH, except that two vertices `u` and `v` are specified as part of each
instance, and we are asked whether `G` contains a Hamiltonian path beginning with `u` and ending
with `v`") and prove it NP-complete there by modifying their transformation from VERTEX COVER
to HAMILTONIAN CIRCUIT; the comment to [GT39] repeats that the variants with a specified
starting point, ending point, or both are NP-complete. Karp's 1972 paper proves HAMILTONIAN
CIRCUIT NP-complete. This is the undirected problem; the directed one with both endpoints
given is the proved HAMPATH of `CSLibExt.Computability.Complexity.Karp.HamPath`.

The graph is a vertex count `n` (vertices `Fin n`) with an edge list, as in HAMILTONIAN PATH
(`HamiltonianPathUndirectedWanted`), whose well-formedness is reused for that part
(`HamiltonianPathUndirected.WellFormed`: `0 < n` and a simple edge list). The two specified
vertices are below `n`; they need not be distinct (for `u = v` a Hamiltonian path from `u` to
`u` exists only when `n = 1`). A Hamiltonian path from `u` to `v` is a walk from `u` to `v` in
Mathlib's sense that visits every vertex exactly once (`SimpleGraph.Walk.IsHamiltonian`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **HAMILTONIAN PATH BETWEEN TWO POINTS is NP-complete.** Source: Garey and Johnson (1979),
[GT39] and Section 3.1.4; Karp (1972). -/
public theorem_wanted hamiltonianPathBetweenTwoPoints_npComplete :
    hamiltonianPathBetweenTwoPointsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hamiltonianPathBetweenTwoPointsDec

end MetaMathlibExt.Complexity.NPComplete.HamiltonianPathBetweenTwoPoints
