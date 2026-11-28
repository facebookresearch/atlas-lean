/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VERTEX K-CUT is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM VERTEX K-CUT, citing N. Garg, V. V. Vazirani and M. Yannakakis, "Multiway
cuts in directed and node weighted graphs", Proc. 21st ICALP, Lecture Notes in Computer Science
820 (1994), 487-498, doi:10.1007/3-540-58201-0_92; journal version: "Multiway cuts in node
weighted graphs", Journal of Algorithms 50 (2004), 49-61, doi:10.1016/S0196-6774(03)00111-1;
M. Johnson, B. Martin, S. Pandey, D. Paulusma, S. Smith and E. J. van Leeuwen, "Edge Multiway
Cut and Node Multiway Cut are hard for planar subcubic graphs", Algorithmica 88 (2026),
article 66, doi:10.1007/s00453-026-01412-5 (NODE MULTIWAY CUT, the special case in which the
pairs are all pairs of a terminal set `T`, every weight is `1` and `C ⊆ V \ T`, is NP-complete,
even for planar graphs of maximum degree 3; NP-completeness for `|T| = 3` is credited there to
Garg, Vazirani and Yannakakis).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.VertexKCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VertexKCut

/-!
# VERTEX K-CUT is NP-complete

INSTANCE: a graph `G = (V, E)`, a set `S = {s₁, t₁, …, s_k, t_k}` of special vertices, a weight
function `w : V - S → ℕ`, and a positive integer `K`.
QUESTION: is there a vertex k-cut, i.e. a subset `C ⊆ V - S` of vertices whose deletion from `G`
disconnects each `sᵢ` from `tᵢ` for `1 ≤ i ≤ k`, of weight `∑_{v ∈ C} w(v)` at most `K`?

The pairs `(sᵢ, tᵢ)` are given as a list, so `k` is its length and `S` is the set of all their
entries. The weights are a list indexed by vertex; the entries at special vertices are never used,
because a cut contains no special vertex. Deleting `C` is Mathlib's induced subgraph
`SimpleGraph.induce` on the complement of `C`, and disconnection is the negation of
`SimpleGraph.Reachable` there; since `C` contains no special vertex, both `sᵢ` and `tᵢ` survive the
deletion. A pair `(v, v)` can never be disconnected, and neither can a pair of adjacent vertices,
so an instance containing one is a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **VERTEX K-CUT is NP-complete.** Source: Crescenzi and Kann, MINIMUM VERTEX K-CUT, citing Garg,
Vazirani and Yannakakis (1994); NP-complete already for NODE MULTIWAY CUT with unit weights,
Johnson, Martin, Pandey, Paulusma, Smith and van Leeuwen (2026). -/
public theorem_wanted vertexKCut_npComplete :
    vertexKCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L vertexKCutDec

end MetaMathlibExt.Complexity.NPComplete.VertexKCut
