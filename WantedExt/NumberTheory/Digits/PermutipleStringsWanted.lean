/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Digits.PermutipleStrings
public import WantedExt.NumberTheory.Digits.PermutipleWanted
public import MathlibExt.NumberTheory.Digits.PermutipleStringsExistsIsPermutipleStringOfHasEulerianCircuitFromZero
public import MathlibExt.NumberTheory.Digits.PermutipleStringsPermutipleEdgeResidueLe
public import MathlibExt.NumberTheory.Digits.PermutipleStringsExistsCarriesOfIsMotherGraphEdge

/-!
# A multigraph characterization of permutiple strings (Holt)

Further statements from Benjamin V. Holt, *A Multigraph Characterization of Permutiple
Strings*, INTEGERS 25 (2025), Article A111 (arXiv:2505.11414).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Edges of a permutiple's graph lie on cycles of the mother graph.** Let $n \ge 1$, $b$ and $k$
be natural numbers, let $\sigma$ be a permutation of $\{0, \dots, k\}$ and let
$(d_k, \dots, d_0)_b$ be an $(n, b, \sigma)$-permutiple, that is, $d_i < b$ for all $i$ and
$(d_k, \dots, d_0)_b = n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$. Its graph has the edges
$(d_i, d_{\sigma(i)})$ for $0 \le i \le k$. Then for every $0 \le j \le k$, the pair
$(d_j, d_{\sigma(j)})$ is an edge of the $(n, b)$-mother graph, and $d_j$ is reachable from
$d_{\sigma(j)}$ along edges of the graph of the permutiple (in zero steps when they are equal),
so the edge $(d_j, d_{\sigma(j)})$ lies on a directed cycle of that graph.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 4 (`integers-2025-A111-thm-4`), quoting Holt,
*Finding Permutiples of a Known Base and Multiplier*. -/
public theorem_wanted permutiple_graph_isUnion_motherGraphCycles (n b : ℕ) (hn : 1 ≤ n) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (j : Fin (k + 1)) :
    IsMotherGraphEdge n b (d j) (d (σ j)) ∧
      Relation.ReflTransGen (fun u v => ∃ i, d i = u ∧ d (σ i) = v) (d (σ j)) (d j)

/-- **$L$-Eulerian criterion for permutiple strings.** Let $1 < n < b$ and let $I$ be a
multiset of cycles of the $(n, b)$-mother graph, with multiset union of cycle edges $C_I$
and multi-image union $\Delta_I$. Then $\Delta_I$ is $L$-Eulerian if and only if there is
an $(n, b)$-permutiple string $s$ whose multiset of entries is $C_I$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Corollary 2 (`integers-2025-A111-cor-2`). -/
public theorem_wanted exists_isPermutipleString_iff_isLEulerian (n b : ℕ) (hn : 1 < n) (hnb : n < b)
    (cs : Multiset (List ℕ)) (hcs : ∀ vs ∈ cs, IsMotherGraphCycle n b vs) :
    (∃ s : List (ℕ × ℕ), (s : Multiset (ℕ × ℕ)) = cycleUnion cs ∧ IsPermutipleString n b s) ↔
      IsLEulerian (multiImageUnion n b cs)

end

end MetaMathlibExt
