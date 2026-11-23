/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ramsey numbers of trees with bipartition classes `k` and `2k` (Erdős Problem 549)

Erdős Problem 549: if `T` is a tree which is a bipartite graph with `k` vertices in one class and
`2k` vertices in the other class, then `R(T) = 4k - 1`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.GraphTheory.TreeRamseyBipartitionErdosProblem549Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #549, https://www.erdosproblems.com/549 (status
DISPROVED). UnsolvedMath record UM-30006929 (`EP-549`), dataset ulamai/UnsolvedMath v1.8.0.

`R(G)` is the two-colour Ramsey number, MathlibExt's `SimpleGraph.diagonalGraphRamsey`: the least
`N` such that for every graph `R` on `Fin N` (the red edges; the blue edges form the complement
`Rᶜ`) the graph `G` is a subgraph, not necessarily induced, of `R` or of `Rᶜ`. A tree with classes
of sizes `k` and `2k` is a tree on `Fin k ⊕ Fin (2k)` with no edge inside either summand (the
bipartition of a tree is unique); the claim is for every `k` (`k = 0` is vacuous, a tree being
nonempty). Compared with the formal-conjectures statement `ErdosProblems/549.lean`
(formal-conjectures also assumes `2 ≤ k`; no code imported).
-/

/-- Erdős Problem 549: every tree `T` whose bipartition classes have `k` and `2k` vertices (vertex
type `Fin k ⊕ Fin (2k)`, no edge inside either summand) has `R(T) = 4k - 1`. -/
def treeRamseyBipartitionFourKMinusOne : Prop :=
  ∀ (k : ℕ) (T : SimpleGraph (Fin k ⊕ Fin (2 * k))), T.IsTree →
    (∀ x y, ¬ T.Adj (Sum.inl x) (Sum.inl y)) → (∀ x y, ¬ T.Adj (Sum.inr x) (Sum.inr y)) →
      SimpleGraph.diagonalGraphRamsey T = 4 * k - 1

/--
Resolved false: Norin, Sun and Zhao proved that the tree obtained by joining the centres of two
stars on `k` and `2k` vertices by an edge (a tree with bipartition classes of sizes `k` and `2k`)
has `R(T) ≥ (4.2 - o(1)) k`, so `R(T) > 4k - 1` for large `k`; erdosproblems.com/549 lists the
problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #549,
https://www.erdosproblems.com/549 (status DISPROVED); resolution: S. Norin, Y. R. Sun and Y. Zhao,
Asymptotics of Ramsey numbers of double stars, arXiv:1605.03612 (2016), erdosproblems.com/549: the
tree joining the centres of stars on k and 2k vertices has R(T) ≥ (4.2 - o(1)) k; abstract: the
Grossman-Harary-Klawe conjecture fails for 7m/4 + o(m) ≤ n ≤ 105m/41 - o(m), which also answers a
question of Erdős, Faudree, Rousseau and Schelp (1982) negatively, https://arxiv.org/abs/1605.03612.
-/
public theorem_wanted treeRamseyBipartitionFourKMinusOne_refuted :
    ¬ treeRamseyBipartitionFourKMinusOne

end MathlibExt.GraphTheory.TreeRamseyBipartitionErdosProblem549Wanted
