/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CliqueCoverDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueCover

/-!
# CLIQUE COVER is NP-complete

Karp, *Reducibility among combinatorial problems*, in R. E. Miller and J. W. Thatcher (eds.),
*Complexity of Computer Computations*, Plenum Press, 1972, 85–103, Main Theorem, problem 13
(p. 95): given a graph `G'` and a positive integer `ℓ`, decide whether the vertex set is the union
of `ℓ` or fewer cliques. Karp reduces CHROMATIC NUMBER to it by taking the complement graph and
`ℓ = k` (p. 99).

Encoding: an instance is a vertex count `n`, an edge list on `0, …, n - 1` and the bound `ℓ`,
decoded from a bitstring with the repository's canonical `MetaMathlibExt.BitstringEncoding`, as
for GRAPH COLORING (`MetaMathlibExt.Complexity.NPComplete.GraphColoring`). Undecodable bitstrings,
and bitstrings decoding to malformed instances, are no-instances. A cover by at most `ℓ` cliques
is a map from the vertices to `ℓ` labels whose classes are cliques: subsets of cliques are
cliques, so covers and partitions give the same problem.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in `MetaMathlibExt.ComplexityTheory.NP`, plus
a polynomial-time many-one reduction from every language in `NP` (`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLIQUE COVER is NP-complete.** The CLIQUE COVER decision problem lies in NP, and every
problem in NP reduces to it by a polynomial-time many-one reduction (R. M. Karp, "Reducibility
among combinatorial problems", 1972, Main Theorem, problem 13, by the reduction
CHROMATIC NUMBER ∝ CLIQUE COVER on p. 99). -/
public theorem_wanted cliqueCover_npComplete :
    cliqueCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueCoverDec

end MetaMathlibExt.Complexity.NPComplete.CliqueCover
