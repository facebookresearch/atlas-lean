/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Logic.Equiv.Fin.Rotate
public import MathlibExt.NumberTheory.Digits.HoeySloaneCycles
public import MathlibExt.NumberTheory.Digits.Permutiple
public import MathlibExt.NumberTheory.Digits.PermutiplePermutipleGraphEdgesUnionCycles

/-!
# Permutiples with a fixed set of digits (Holt)

Statements from B. V. Holt, *A Method for Finding All Permutiples with a Fixed
Set of Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88
(arXiv:2312.02056).

A `(k+1)`-digit base-`b` numeral `(d_k, …, d_0)_b` is a digit function
`d : Fin (k + 1) → ℕ` (digit `d j` has weight `b ^ j`); for a permutation `π`,
the numeral `(d_{π(k)}, …, d_{π(0)})_b` is `d ∘ π`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Carry bound for permutiples.** Let $n$ and $b \ge 2$ be natural numbers, let $\sigma$
be a permutation of $\{0, \dots, k\}$, and let $(d_k, \dots, d_0)_b$ be an
$(n, b, \sigma)$-permutiple, where $(e_k, \dots, e_0)_b$ denotes the base-$b$ numeral
$\sum_{j=0}^{k} e_j b^j$. Let $c_0, c_1, \dots$ be the carries of the multiplication
$n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$. Then for every $0 \le j \le k$ we have
$c_j \le n - 1$ if $n \ge 1$, and $c_j = 0$ if $n = 0$.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Theorem 2
(`integers-2024-A88-thm-2`), quoting Holt's earlier paper; restated as Theorem 2
of Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025),
Article A13 (`integers-2025-A13-thm-2`). -/
public theorem_wanted permutipleCarry_le (n b : ℕ) (hb : 2 ≤ b) {k : ℕ} (d : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) (j : Fin (k + 1)) :
    permutipleCarry n b d σ j ≤ n - 1

/-- **Every permutiple has a cycle-preserving digit permutation.** Let $n$, $b$ and
$d_0, \dots, d_k$ be natural numbers and let $\sigma$ be a permutation of $\{0, \dots, k\}$ such
that $(d_k, \dots, d_0)_b$ is an $(n, b, \sigma)$-permutiple. Then there is a permutation
$\hat\sigma$ of $\{0, \dots, k\}$ such that $(d_k, \dots, d_0)_b$ is also an
$(n, b, \hat\sigma)$-permutiple and the digits along each cycle of $\hat\sigma$ are distinct:
for all $j \in \{0, \dots, k\}$ and all $i \ge 0$, if $d_{\hat\sigma^i(j)} = d_j$ then
$\hat\sigma^i(j) = j$.

Unlike the paper, no assumption $1 < n < b$ is made.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Theorem 5 (`integers-2025-A13-thm-5`), with Definition 5
(cycle-preserving permutations). -/
public theorem_wanted exists_cyclePreserving_permutiple (n b : ℕ) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) :
    ∃ σ' : Equiv.Perm (Fin (k + 1)), IsPermutiple n b d σ' ∧
      ∀ (j : Fin (k + 1)) (i : ℕ), d ((σ' ^ i) j) = d j → (σ' ^ i) j = j


end

end MetaMathlibExt
