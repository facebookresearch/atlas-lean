/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Relation
public import MathlibExt.NumberTheory.Digits.PermutipleStringsPermutipleEdgeResidueLe
import Mathlib.GroupTheory.Perm.Finite

/-! # Cycles of a permutiple's digit graph

Each indexed digit pair is an edge of the mother graph. The digit permutation gives a
return path through the edges of the permutiple itself.

## References

- Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
  INTEGERS 25 (2025), Article A111, pp. 1–19, Theorem 4 and Theorem 3.
- Benjamin V. Holt, *Finding Permutiples of a Known Base and Multiplier*,
  INTEGERS 25 (2025), Article A13, pp. 1–23, Theorem 6 (the original cycle result),
  Theorem 3 (the residue bound), and Definition 4 (the mother graph).
- Benjamin V. Holt, *A Method for Finding All Permutiples with a Fixed Set of Digits from a
  Single Known Example*, INTEGERS 24 (2024), Article A88, pp. 1–13, Theorem 3
  (the more general residue bound cited in Article A13).
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
public theorem permutiple_graph_isUnion_motherGraphCycles (n b : ℕ) (hn : 1 ≤ n) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (j : Fin (k + 1)) :
    IsMotherGraphEdge n b (d j) (d (σ j)) ∧
      Relation.ReflTransGen (fun u v => ∃ i, d i = u ∧ d (σ i) = v) (d (σ j)) (d j) := by
  refine ⟨⟨hp.1 j, hp.1 (σ j), permutiple_edge_residue_le n b hn d σ hp j⟩, ?_⟩
  -- Reachability on digit positions is closed under σ, hence also under its inverse.
  let reachable (i : Fin (k + 1)) :=
    Relation.ReflTransGen (fun u v => ∃ a, d a = u ∧ d (σ a) = v) (d (σ j)) (d i)
  have forward (i : Fin (k + 1)) (hi : reachable i) : reachable (σ i) :=
    hi.tail ⟨i, rfl, rfl⟩
  have start : reachable (σ j) := .refl
  simpa only [Equiv.symm_apply_apply] using
    Equiv.Perm.perm_symm_on_of_perm_on_finite forward start

end

end MetaMathlibExt
