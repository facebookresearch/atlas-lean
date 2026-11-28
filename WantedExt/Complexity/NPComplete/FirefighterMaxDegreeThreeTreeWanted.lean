/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIREFIGHTER on trees of maximum degree three is NP-complete

Source:
S. Finbow, A. King, G. MacGillivray and R. Rizzi, "The firefighter problem for graphs of
maximum degree three", Discrete Mathematics 307 (2007), 2094-2105,
doi:10.1016/j.disc.2005.12.053.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FirefighterMaxDegreeThreeTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FirefighterMaxDegreeThreeTree

/-!
# FIREFIGHTER on trees of maximum degree three is NP-complete

The firefighter process on a rooted graph `(G, r)` (Hartnell 1995): at time `0` a fire breaks
out at `r`. At each subsequent time step the firefighter defends some vertex which is not on
fire, and then the fire spreads to all undefended neighbours of each burning vertex. Once
defended, a vertex remains so. The process ends when the fire can no longer spread.

INSTANCE (Finbow, King, MacGillivray and Rizzi, problem 3T-FIRE): a triple `(T, r, k)`, where
`(T, r)` is a rooted tree with maximum degree at most `3` and `k` is a positive integer.
QUESTION: when the fire begins at `r`, is there a strategy such that at most `k` vertices burn?

A strategy is the list `d` of defended vertices, `d[s]` being defended at time `s + 1`.
`Burning T r d t v` says that `v` is on fire at time `t`: only `r` at time `0`, and at time
`t + 1` the vertices burning at time `t` together with every neighbour of one of them that is
not among `d[0], …, d[t]`. The strategy defends at each time a vertex that is not on fire, and
it runs until the fire can no longer spread: after `|d|` steps every neighbour of a burning
vertex is burning or defended. The vertices that burn are those burning at that time.

The tree is given by its vertex count `n` (vertices `0, …, n - 1`) and an edge list, as a
`SimpleGraph (Fin n)` through `Cslib.Complexity.Karp.edgeGraph`; trees and degrees are Mathlib's
`SimpleGraph.IsTree` and `SimpleGraph.degree`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FIREFIGHTER on trees of maximum degree three is NP-complete.** Source: Finbow, King,
MacGillivray and Rizzi (2007). -/
public theorem_wanted firefighterMaxDegreeThreeTree_npComplete :
    firefighterMaxDegreeThreeTreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L firefighterMaxDegreeThreeTreeDec

end MetaMathlibExt.Complexity.NPComplete.FirefighterMaxDegreeThreeTree
