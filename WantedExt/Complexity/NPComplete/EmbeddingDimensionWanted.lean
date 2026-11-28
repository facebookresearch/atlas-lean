/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EMBEDDING DIMENSION is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
89-99, doi:10.1016/0196-6774(82)90011-6, problem [4] EMBEDDING DIMENSION (reference: Dewdney;
transformation from VERTEX COVER);
A. K. Dewdney, "The embedding dimension of a graph", Report No. 52, Department of Computer
Science, University of Western Ontario, London, Ontario (1979), as cited by the column
(Dewdney's report was not available; the column records the result and its attribution).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EmbeddingDimensionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EmbeddingDimension

open NesetrilRodlDimension (NesetrilRodlDimensionInstance Graph)

/-!
# EMBEDDING DIMENSION is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`.
QUESTION: does `G` have embedding dimension `K` or less, i.e., is there a one-to-one function
`f : V → {0, 1, 2}^K` such that, for all `u, v ∈ V`, `{u, v} ∈ E` if and only if `f(u)` and
`f(v)` differ by at most `1` in every component?

The column reads the question as asking whether `G` is an induced subgraph of the graph on
`{0, 1, 2}^K` that joins two distinct tuples whose component-wise differences are all at most
`1` (`Host K` below). The question is therefore the existence of a Mathlib graph embedding
`Graph i ↪g Host K` (`SimpleGraph.Embedding`: an injective map with `Host K` adjacency of the
images equivalent to adjacency in `G`). The equivalence is read for distinct `u` and `v`, where
both sides are false for `u = v`: the clause read literally for `u = v` too would make every graph
with a vertex a no-instance, since `f(u)` agrees with itself while `{u, u}` is not an edge.

The instance has the shape of NESETRIL-RODL DIMENSION
(`WantedExt.Complexity.NPComplete.NesetrilRodlDimensionWanted`), whose instance type and
`Graph` are reused (the column calls the similarity of the two problems only superficial): the
number of vertices `n = |V|` in unary, as the length of a list `[true, ..., true]`, a simple edge
list on `Fin n`, and `K`. A graph is given with its vertex set; a binary `n` would make the
problem succinct, since isolated vertices would cost no input while `f` must give each of them a
tuple. A `K`-tuple over `{0, 1, 2}` is a function `Fin K → Fin 3`.

Membership in NP: for `K ≥ |V|` the answer is yes, since the column notes that a graph with `n`
vertices has embedding dimension at most `n` (put `f(u)_w = 0` if `u = w`, `1` if `u` and `w`
are adjacent, `2` otherwise, and `0` in any further component); for `K < |V|` the certificate
`f` has `|V| · K < |V|²` components.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **EMBEDDING DIMENSION is NP-complete.** Source: Johnson, NP-completeness column (1982),
problem [4]; Dewdney (1979). -/
public theorem_wanted embeddingDimension_npComplete :
    embeddingDimensionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L embeddingDimensionDec

end MetaMathlibExt.Complexity.NPComplete.EmbeddingDimension
