/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR 3SAT WITH VARIABLE CYCLE is NP-complete

Source:
D. Lichtenstein, "Planar formulae and their uses", SIAM Journal on Computing 11(2) (1982),
329-343, doi:10.1137/0211025;
A. Pilz, "Planar 3-SAT with a clause/variable cycle", Discrete Mathematics & Theoretical
Computer Science 21(3) (2019), doi:10.23638/DMTCS-21-3-18.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarThreeSatVariableCycleDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarThreeSatVariableCycle

/-!
# PLANAR 3SAT WITH VARIABLE CYCLE is NP-complete

INSTANCE: a 3-CNF formula `F` over variables `u₀, …, u_{n-1}` (`n ≥ 3`) such that the
variable-clause incidence graph together with the cycle edges `{uᵢ, uᵢ₊₁}` (indices mod `n`) is
planar.
QUESTION: is `F` satisfiable?

This is the restriction of PLANAR 3SAT (`WantedExt.Complexity.NPComplete.PlanarThreeSatWanted`)
in which the incidence graph stays planar after adding the cycle through the variables in the
order of their indices, the form in which Lichtenstein (1982) proves NP-completeness: Pilz
(2019) records that "the problem remains NP-complete even if the graph remains planar after
adding a cycle whose vertices are exactly the variables of the formula", and that
"Lichtenstein's definition of planar 3-SAT already requires the cycle through the variables".
The instance type, the incidence graph, the parent well-formedness condition and the question
are those of the parent module (`PlanarThreeSat.PlanarThreeSatInstance`,
`PlanarThreeSat.IncidenceGraph`, `PlanarThreeSat.WellFormed`,
`PlanarThreeSat.PlanarThreeSatFeasible`). The cycle is Mathlib's `SimpleGraph.cycleGraph n` on
the variable vertices (`i ~ j` iff `i - j = ±1` in `Fin n`), placed on the left summand of the
vertex type by the disjoint sum `⊕g` with the empty graph on the clauses. A cycle through the
variables needs at least three of them (`cycleGraph n` is a cycle only for `n ≥ 3`), so
`WellFormed` adds `3 ≤ n` and that the union of the two graphs is planar.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PLANAR 3SAT WITH VARIABLE CYCLE is NP-complete.** Source: Lichtenstein (1982); Pilz
(2019). -/
public theorem_wanted planarThreeSatVariableCycle_npComplete :
    planarThreeSatVariableCycleDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarThreeSatVariableCycleDec

end MetaMathlibExt.Complexity.NPComplete.PlanarThreeSatVariableCycle
