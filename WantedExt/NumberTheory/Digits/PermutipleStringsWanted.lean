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

/-!
# A multigraph characterization of permutiple strings (Holt)

Further statements from Benjamin V. Holt, *A Multigraph Characterization of Permutiple
Strings*, INTEGERS 25 (2025), Article A111 (arXiv:2505.11414).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Edge condition for permutiples.** Let $n \ge 1$, $b$ and $k$ be natural numbers, let $\sigma$
be a permutation of $\{0, \dots, k\}$ and let $(d_k, \dots, d_0)_b$ be an
$(n, b, \sigma)$-permutiple, that is, $d_i < b$ for all $i$ and
$(d_k, \dots, d_0)_b = n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$. Then for every
$0 \le j \le k$, $\lambda(d_j + (b - n) d_{\sigma(j)}) \le n - 1$, where $\lambda$ is the least
non-negative residue modulo $b$ and $b - n$ is computed in the integers, so it may be negative.

The hypothesis $n \ge 1$ is needed: for $n = 0$ the only permutiples have all digits zero and the
bound would read $0 \le -1$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 3 (`integers-2025-A111-thm-3`), quoting Holt,
*Finding Permutiples of a Known Base and Multiplier*. -/
public theorem_wanted permutiple_edge_residue_le (n b : ℕ) (hn : 1 ≤ n) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (j : Fin (k + 1)) :
    ((d j : ℤ) + ((b : ℤ) - n) * d (σ j)) % b ≤ (n : ℤ) - 1

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

/-- **Every mother-graph edge induces a carry transition.** Let $n$ and $b$ be natural
numbers. If $(d_1, d_2)$ is an edge of the $(n, b)$-mother graph, then there are natural
numbers $c_1$ and $c_2$ with $c_1 \le n - 1$ and $c_2 \le n - 1$ such that
$b c_2 - c_1 = n d_2 - d_1$ as integers.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 6 (`integers-2025-A111-thm-6`). -/
public theorem_wanted exists_carries_of_isMotherGraphEdge (n b d₁ d₂ : ℕ)
    (h : IsMotherGraphEdge n b d₁ d₂) :
    ∃ c₁ c₂ : ℕ, c₁ ≤ n - 1 ∧ c₂ ≤ n - 1 ∧ (b : ℤ) * c₂ - c₁ = (n : ℤ) * d₂ - d₁

/-- **Eulerian circuits through zero yield permutiple strings.** Let $1 < n < b$ and let $I$
be a multiset of cycles of the $(n, b)$-mother graph, with multiset union of cycle edges
$C_I$ and multi-image union $\Delta_I$. If $\Delta_I$ has an Eulerian circuit beginning
and ending at the zero state, then there is an $(n, b)$-permutiple string $s$ whose
multiset of entries is $C_I$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 7 (`integers-2025-A111-thm-7`). -/
public theorem_wanted exists_isPermutipleString_of_hasEulerianCircuitFromZero (n b : ℕ) (hn : 1 < n)
    (hnb : n < b) (cs : Multiset (List ℕ)) (hcs : ∀ vs ∈ cs, IsMotherGraphCycle n b vs)
    (h : HasEulerianCircuitFromZero (multiImageUnion n b cs)) :
    ∃ s : List (ℕ × ℕ), (s : Multiset (ℕ × ℕ)) = cycleUnion cs ∧ IsPermutipleString n b s

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
