/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RAINBOW CONNECTION NUMBER AT MOST 2 is NP-complete

Source:
S. Chakraborty, E. Fischer, A. Matsliah, and R. Yuster, "Hardness and algorithms for rainbow
connection", Journal of Combinatorial Optimization 21(3) (2011), 330-347,
doi:10.1007/s10878-009-9250-9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.RainbowConnectionTwoDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RainbowConnectionTwo

/-!
# RAINBOW CONNECTION NUMBER AT MOST 2 is NP-complete

INSTANCE: a connected graph `G = (V, E)` (finite, simple, undirected).
QUESTION: can the edges of `G` be colored with `2` colors so that every pair of vertices is
joined by a path whose edges have distinct colors, that is, is the rainbow connection number
`rc(G)` at most `2`?

An edge coloring is a Mathlib `SimpleGraph.EdgeLabeling` of `G` with labels `Fin 2`. A rainbow
path from `u` to `v` is a Mathlib walk `p : G.Walk u v` with `p.IsPath` whose edges, listed
along `p` by its darts, carry pairwise distinct labels (`List.Nodup`). With two colors a rainbow
path has at most two edges. Connectivity is part of the instance class, so it is a conjunct of
`WellFormed` (Mathlib's `SimpleGraph.Connected`, which also requires a vertex).

Chakraborty, Fischer, Matsliah and Yuster prove that deciding `rc(G) = 2` is NP-complete. The
question here is `rc(G) ≤ 2`; the two differ only on complete graphs (`rc(G) ≤ 1` exactly when
any two distinct vertices are adjacent), which are recognized in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RAINBOW CONNECTION NUMBER AT MOST 2 is NP-complete.** Source: Chakraborty, Fischer,
Matsliah, and Yuster (2011). -/
public theorem_wanted rainbowConnectionTwo_npComplete :
    rainbowConnectionTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rainbowConnectionTwoDec

end MetaMathlibExt.Complexity.NPComplete.RainbowConnectionTwo
