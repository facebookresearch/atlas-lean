/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR HAMILTONIAN COMPLETION is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3
(1982), 288-300, doi:10.1016/0196-6774(82)90026-8 (fourth edition, discussion of
HAMILTONIAN CIRCUIT [GT37]);
A. Wigderson, "The complexity of the Hamiltonian circuit problem for maximal planar graphs",
Report No. 298, EECS Department, Princeton University (1982).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import MathlibExt.Combinatorics.SimpleGraph.Planarity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarHamiltonianCompletion

/-!
# PLANAR HAMILTONIAN COMPLETION is NP-complete

Johnson's column (1982) states the problem: "Given a planar graph `G`, can we add new edges
(but not new vertices) so as to render the resulting graph Hamiltonian, while still keeping the
graph planar?" Wigderson (1982) showed HAMILTONIAN CIRCUIT NP-complete for maximal planar
graphs, "a result that implies NP-completeness" of this variant: a maximal planar graph admits
no new edge that keeps it planar, so it has a planar Hamiltonian completion exactly when it is
Hamiltonian. NP membership: a completion is planar and Hamiltonian exactly when `G` together
with the edges of some Hamiltonian cycle is planar, which a Hamiltonian cycle certifies
(planarity is testable in polynomial time).

The question is whether some supergraph `H ≥ G` on the same vertex set is planar and has a
Hamiltonian cycle (Mathlib's `Walk.IsHamiltonianCycle`, which needs at least three vertices).
Planarity is `SimpleGraph.IsPlanar` (a crossing-free straight-line drawing, equivalent to
planarity for finite simple graphs by Fáry's theorem).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **PLANAR HAMILTONIAN COMPLETION is NP-complete.** Source: Johnson (1982); Wigderson
(1982). -/
public theorem_wanted planarHamiltonianCompletion_npComplete :
    planarHamiltonianCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarHamiltonianCompletionDec

end MetaMathlibExt.Complexity.NPComplete.PlanarHamiltonianCompletion
