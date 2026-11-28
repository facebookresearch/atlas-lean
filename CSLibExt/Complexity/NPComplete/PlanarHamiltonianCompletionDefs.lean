/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR HAMILTONIAN COMPLETION: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3
(1982), 288-300, doi:10.1016/0196-6774(82)90026-8 (fourth edition, discussion of
HAMILTONIAN CIRCUIT [GT37]);
A. Wigderson, "The complexity of the Hamiltonian circuit problem for maximal planar graphs",
Report No. 298, EECS Department, Princeton University (1982).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarHamiltonianCompletion

/-- An instance: the vertex list `[0, …, n - 1]` (explicit, so that isolated vertices count
toward the input size, as in `HamiltonianCompletionWanted`) and the edge list. -/
abbrev PlanarHamiltonianCompletionInstance := List ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PlanarHamiltonianCompletionInstance) : SimpleGraph (Fin i.1.length) :=
  Cslib.Complexity.Karp.edgeGraph i.1.length i.2

/-- Well-formedness of an instance: the vertex list is `[0, …, n - 1]`, the edge list is
simple on `Fin n` (no loops, no repeated or reversed edges), and the graph is planar. -/
def WellFormed (i : PlanarHamiltonianCompletionInstance) : Prop :=
  i.1 = List.range i.1.length ∧
    (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1.length ∧ e.2 < i.1.length ∧ e.1 ≠ e.2 ∧
      (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsPlanar

/-- Edges can be added to `G` (no new vertices) so that the result is planar and has a
Hamiltonian cycle. -/
def PlanarHamiltonianCompletionFeasible (i : PlanarHamiltonianCompletionInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1.length), Graph i ≤ H ∧ H.IsPlanar ∧
    ∃ v, ∃ p : H.Walk v v, p.IsHamiltonianCycle

open Classical in
/-- PLANAR HAMILTONIAN COMPLETION as a decision problem over bitstrings. -/
noncomputable def planarHamiltonianCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PlanarHamiltonianCompletionInstance) x with
  | some i => decide (WellFormed i ∧ PlanarHamiltonianCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PlanarHamiltonianCompletion
