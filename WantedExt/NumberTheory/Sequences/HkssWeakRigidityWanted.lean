/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Real.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Hinman–Kuca–Schlesinger–Sheydvasser weak rigidity theorem for Ulam sequences.** There
exist sequences of integers $(a_k)$, $(b_k)$, $(c_k)$, $(d_k)$ indexed by $k \in \mathbb{N}$ with
the following property. For every real $C > 0$ there is a natural number $N > 0$ such that for
every natural number $n \ge N$ with $n > 1$, and every sequence of natural numbers
$u_0, u_1, u_2, \dots$ with $u_0 = 1$ and $u_1 = n$ that is strictly increasing and in which, for
every $t \ge 2$, $u_t$ is the least natural number $m > u_{t-1}$ for which there is exactly one
pair of indices $(i, j)$ with $i < j < t$ and $u_i + u_j = m$, the following holds: for every
natural number $x$ with $1 \le x \le Cn$, $x$ is a term of the sequence $u$ if and only if
$a_k n + b_k \le x \le c_k n + d_k$ for some $k \in \mathbb{N}$.

Source: Weak Rigidity Theorem, Theorem 1.1 of HKSS_2019_1, as stated in Sheydvasser, JIS VOL24,
lines 150-155.

Source identifiers (stable):
- canonical_name: Hinman-Kuca-Schlesinger-Sheydvasser weak rigidity theorem for Ulam sequences
- concept_id: jis_dep_b6bd02b67460015658284d14
- grounded_candidate_id: jis_grounded_4a3f4c32b68e2308906fe08d
- source_url: https://cs.uwaterloo.ca/journals/JIS/VOL24/Sheydvasser/sheyd3.tex
- source lines: 150-155
- source_sha256: ee0e4d944870bbfc4ebf49a21dc3a129f9857c6c19b0fffc73a7c923d4baed68
- source_text_sha256: 03e5dd3a6e1e0d117dd2ca2e2724758fc7ee26ac232c48855b404c8ff267e4fe
- label: Weak Rigidity Theorem; cite: Theorem 1.1 of HKSS_2019_1
- corrected mentions/papers/proof-uses: 6/1/1
-/
theorem_wanted hinman_kuca_schlesinger_sheydvasser_weak_rigidity : ∃ a b c d : ℕ → ℤ, ∀ C : ℝ, 0 <
  C → ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → 1 < n → ∀ u : ℕ → ℕ, u 0 = 1 → u 1 = n → StrictMono u →
  (∀ t : ℕ, 2 ≤ t → IsLeast
  {m : ℕ | u (t - 1) < m ∧ ∃! ij : Fin t × Fin t, (ij.1 : ℕ) < (ij.2 : ℕ) ∧ u ij.1 + u ij.2 = m}
  (u t)) → ∀ x : ℕ, 1 ≤ x → (x : ℝ) ≤ C * n →
  (x ∈ Set.range u ↔ ∃ i : ℕ, a i * (n : ℤ) + b i ≤ (x : ℤ) ∧ (x : ℤ) ≤ c i * (n : ℤ) + d i)

end MetaMathlibExt
