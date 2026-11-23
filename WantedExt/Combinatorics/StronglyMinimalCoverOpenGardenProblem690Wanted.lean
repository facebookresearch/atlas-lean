/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Strongly minimal covers of hypergraphs with bounded edges (Open Problem Garden 690)

Open Problem Garden, Strong matchings and covers (R. Aharoni): a strongly minimal cover of a
hypergraph `H` is a (vertex) cover `X ⊆ V(H)` with `|X' \ X| ≥ |X \ X'|` for every cover `X'`.
Conjecture: if `H` is a (possibly infinite) hypergraph in which all edges have size at most `k` for
some integer `k`, then `H` has a strongly maximal matching and a strongly minimal cover.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

namespace MathlibExt.Combinatorics.StronglyMinimalCoverOpenGardenProblem690Wanted

/-!
Source: Open Problem Garden, Strong matchings and covers (node 690; R. Aharoni),
http://www.openproblemgarden.org/op/strong_matchings_and_covers. UnsolvedMath record UM-00003304
(`OPG-690`), dataset ulamai/UnsolvedMath v1.8.0.

This module states the cover part of the conjecture. Its matching part is the statement
`boundedEdgesStronglyMaximalMatching` of
`WantedExt/Combinatorics/StronglyMaximalMatchingAMR29Problem0084Wanted.lean` (EGRES list), refuted
by Hollom and Randall Shaw, Theorem 1.2; the page's second conjecture (the hypergraph of independent
sets of a graph, meant as covering the vertex set by independent sets, i.e. strongly minimal
colourings, refuted by their Theorem 1.5) is not formalized. The hypergraph is encoded as in that
module: a set `E` of finite edges `Finset V`, with `V` and `E` possibly infinite; cardinalities are
compared as cardinals. Edges are required to be nonempty: an empty edge meets no set, so a
hypergraph with an empty edge has no cover at all.
-/

/-- **Vertex cover of a hypergraph.** Let $E$ be a set of finite subsets of a type $V$, the edges
of a hypergraph. A set $X \subseteq V$ is a (vertex) cover of $E$ if it meets every edge: every
$e \in E$ contains some $v \in X$. -/
def IsVertexCover {V : Type} (E : Set (Finset V)) (X : Set V) : Prop :=
  ∀ e ∈ E, ∃ v ∈ e, v ∈ X

/-- **Strongly minimal cover.** Let $E$ be a set of finite subsets of a type $V$, the edges of a
hypergraph. A set $X \subseteq V$ is a strongly minimal cover of $E$ (Aharoni) if $X$ is a cover of
$E$, that is, it meets every edge in $E$, and $|X \setminus X'| \le |X' \setminus X|$, as cardinals,
for every cover $X'$ of $E$. -/
def IsStronglyMinimalCover {V : Type} (E : Set (Finset V)) (X : Set V) : Prop :=
  IsVertexCover E X ∧ ∀ X', IsVertexCover E X' → Cardinal.mk ↥(X \ X') ≤ Cardinal.mk ↥(X' \ X)

/-- **Aharoni's strongly minimal cover conjecture.** The statement that for every type $V$, every
set $E$ of finite subsets of $V$ (the edges of a hypergraph, possibly infinitely many) and every
natural number $k$ such that each edge in $E$ is nonempty and has at most $k$ elements, the
hypergraph with edge set $E$ has a strongly minimal cover. -/
def boundedEdgesStronglyMinimalCover : Prop :=
  ∀ (V : Type) (E : Set (Finset V)) (k : ℕ), (∀ e ∈ E, e.Nonempty ∧ e.card ≤ k) →
    ∃ X, IsStronglyMinimalCover E X

/--
**Aharoni's strongly minimal cover conjecture is false.** There are a type $V$, a set $E$ of
finite subsets of $V$ (the edges of a hypergraph) and a natural number $k$ such that every edge in
$E$ is nonempty and has at most $k$ elements, but no strongly minimal cover of $E$ exists. Here a
cover of $E$ is a set $X \subseteq V$ that meets every edge in $E$, and a cover $X$ is strongly
minimal if $|X \setminus X'| \le |X' \setminus X|$, as cardinals, for every cover $X'$ of $E$.

Hollom and Randall Shaw (Section 3.4) show that the graph on $\mathbb{N}$ whose edges are the
pairs $\{u, v\}$ with $2u \le v$ has no strongly minimal vertex cover, so already hypergraphs with
all edges of size $2$ need not have a strongly minimal cover.

Source: Open Problem Garden, Strong
matchings and covers (node 690; R. Aharoni),
http://www.openproblemgarden.org/op/strong_matchings_and_covers; resolution: L. Hollom and B.
Randall Shaw, Counterexamples to conjectures on strong maximality and minimality, Electron. J.
Combin. 33(2) (2026), #P2.11, doi:10.37236/14948; arXiv:2511.13709, Section 3.4 (Strongly minimal
vertex-covers): the graph G on N with edges {u, v} such that 2u ≤ v has no strongly minimal
vertex-cover; the introduction defines strongly minimal vertex-covers by |C \ C'| ≤ |C' \ C| for
every vertex-cover C', https://doi.org/10.37236/14948.
-/
public theorem_wanted boundedEdgesStronglyMinimalCover_refuted : ¬ boundedEdgesStronglyMinimalCover

end MathlibExt.Combinatorics.StronglyMinimalCoverOpenGardenProblem690Wanted
