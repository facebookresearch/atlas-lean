/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on circle graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
P. Damaschke, "The Hamiltonian circuit problem for circle graphs is NP-complete",
Information Processing Letters 32 (1989), 1-2, doi:10.1016/0020-0190(89)90059-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CircleGraphHamiltonianCircuitDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircleGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.DominatingSetCircleGraph (circleGraph)

/-!
# HAMILTONIAN CIRCUIT on circle graphs is NP-complete

INSTANCE: a circle graph `G`, given by a chord model: a family of chords of a circle, one per
vertex, two vertices being adjacent when their chords intersect.
QUESTION: does `G` have a Hamiltonian circuit?

The chord model and the circle graph are those of
`WantedExt.Complexity.NPComplete.DominatingSetCircleGraphWanted`: a chord is given by its two
endpoints, natural numbers `a < b` naming points in clockwise order on the circle; the endpoints
of all chords are distinct; `DominatingSetCircleGraph.circleGraph` joins two chords when their
endpoints interleave (`a < c < b < d`, symmetrized by `SimpleGraph.fromRel`), which for distinct
endpoints is exactly when they intersect. Every circle graph has such a model. `WellFormed`
states the chord conditions of `DominatingSetCircleGraph.WellFormed` (that predicate also
constrains a domination bound, which this problem does not have).

The question is the one of HAMILTONIAN CIRCUIT ([GT37], `HamiltonianCycleUndirectedDefs`):
at least three vertices and a Hamiltonian cycle (Mathlib's `SimpleGraph.IsHamiltonian`), asked
of the circle graph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN CIRCUIT on circle graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT37]; Damaschke (1989). -/
public theorem_wanted circleGraphHamiltonianCircuit_npComplete :
    circleGraphHamiltonianCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circleGraphHamiltonianCircuitDec

end MetaMathlibExt.Complexity.NPComplete.CircleGraphHamiltonianCircuit
