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
public import CSLibExt.Complexity.NPComplete.PlanarHamiltonianCompletionDefs

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

/-- **PLANAR HAMILTONIAN COMPLETION is NP-complete.** Source: Johnson (1982); Wigderson
(1982). -/
public theorem_wanted planarHamiltonianCompletion_npComplete :
    planarHamiltonianCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarHamiltonianCompletionDec

end MetaMathlibExt.Complexity.NPComplete.PlanarHamiltonianCompletion
