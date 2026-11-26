/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.Permutiple

/-!
# A multigraph characterization of permutiple strings (Holt)

Further statements from Benjamin V. Holt, *A Multigraph Characterization of Permutiple
Strings*, INTEGERS 25 (2025), Article A111 (arXiv:2505.11414).

This module proves the edge condition for permutiples
(`MetaMathlibExt.permutiple_edge_residue_le`).
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
public theorem permutiple_edge_residue_le (n b : ℕ) (hn : 1 ≤ n) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (j : Fin (k + 1)) :
    ((d j : ℤ) + ((b : ℤ) - n) * d (σ j)) % b ≤ (n : ℤ) - 1 := by
  by_cases hb : 2 ≤ b
  · simpa using permutiple_basePerm_residue_le n b hn hb d σ 1 σ hp hp j
  · have hb01 : b = 0 ∨ b = 1 := by omega
    rcases hb01 with rfl | rfl
    · exfalso
      have h0 := hp.1 j
      omega
    · have hj : d j = 0 := by
        have h := hp.1 j
        omega
      have hσ : d (σ j) = 0 := by
        have h := hp.1 (σ j)
        omega
      rw [hj, hσ]
      simp
      omega

end

end MetaMathlibExt
