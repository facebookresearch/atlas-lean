/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.Words.UlamWords

/-!
# Ulam words — wishlist

Statements from Paul Adutwum, Hopper Clark, Ro Emerson, Alexandra (Sasha) Sheydvasser,
Arseniy (Senia) Sheydvasser, and Axelle Tougouma, *Distributions of Ulam Words up to Length
30*, INTEGERS 25 (2025), Article A102 (arXiv:2410.01217v2).

Words over `{0, 1}` are `List Bool` with `false = 0`, `true = 1`. Following Bade, Cui,
Labelle, and Li (as quoted in Section 1 of the paper), `0` and `1` are Ulam, and a word
`w ≠ 0, 1` is Ulam iff there is exactly one pair of Ulam words `u₁ ≠ u₂` with `w = u₁ u₂`.
The integer `π(w)` of a word is its binary value, most significant letter first, written
`Nat.ofDigits 2 (w.reverse.map Bool.toNat)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Square of the Ulam word count is at most a block sum.** For every natural number $n$,
$(\#U_n)^2 \le \sum_{i=n}^{2n} \#U_i$, where $\#U_i$ is the number of Ulam words of length $i$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Lemma 2. -/
public theorem_wanted ulamWordCount_sq_le_sum (n : ℕ) :
    ulamWordCount n ^ 2 ≤ ∑ i ∈ Finset.Icc n (2 * n), ulamWordCount i

/-- **Exponential lower bound for Ulam word counts along a subsequence.** Let $\#U_n$ be the
number of Ulam words of length $n$ and $\alpha_0 = (\#U_{30} / (2 \cdot 31))^{1/30}$. For every
real $\alpha$ with $1 < \alpha < \alpha_0$, every real $C$ and every natural number $N$, there
is some $n \ge N$ with $C \alpha^n \le \#U_n$; that is,
$\limsup_{n \to \infty} \#U_n / \alpha^n = \infty$.

Here $\alpha_0$ is the constant from the paper's proof, with $n_1 = 30$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 2. -/
public theorem_wanted ulamWordCount_limsup_div_pow_eq_top (α : ℝ) (hα : 1 < α)
    (hα₀ : α < ((ulamWordCount 30 : ℝ) / (2 * 31)) ^ ((1 : ℝ) / 30)) (C : ℝ) (N : ℕ) :
    ∃ n ≥ N, C * α ^ n ≤ ulamWordCount n

/-- **Ulam words with one 101 block.** For natural numbers $a$ and $b$ with $a + b \ge 2$, the
binary word $0^a 101 0^b$ ($a$ zeros, then the letters $1, 0, 1$, then $b$ zeros) is an Ulam word
if and only if $a + b$ is odd.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 7
(Theorem 3.6 of Bade, Cui, Labelle, and Li). -/
public theorem_wanted isUlamWord_zeros_one_zero_one_zeros_iff (a b : ℕ) (hab : 2 ≤ a + b) :
    IsUlamWord (List.replicate a false ++ [true, false, true] ++ List.replicate b false) ↔
      (a + b) % 2 = 1

/-- **Ulam words made of ones followed by zeros.** For natural numbers $x$ and $y$ with
$1 \le y \le x$, the word $1^y 0^{x-y}$ ($y$ ones followed by $x - y$ zeros) is an Ulam word if
and only if $(x, y) = (1, 1)$ or $(x, y)$ belongs to the discrete Sierpiński triangle
$\mathcal{S}$.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 9
(precise form of Theorem 3). -/
public theorem_wanted isUlamWord_ones_zeros_iff_mem_discreteSierpinski (x y : ℕ) (hy : 1 ≤ y)
    (hyx : y ≤ x) :
    IsUlamWord (List.replicate y true ++ List.replicate (x - y) false) ↔
      (x, y) = (1, 1) ∨ (x, y) ∈ discreteSierpinski

/-- **Padding the word 10101 with zeros.** For natural numbers $a$ and $b$ with $a + b \ge 1$, the
word $0^a 10101 0^b$ ($a$ zeros, then $10101$, then $b$ zeros) is an Ulam word if and only if $a$
and $b$ are both even and at least one of $a$ and $b$ is zero.

Source: Adutwum, Clark, Emerson, A. Sheydvasser, A. Sheydvasser, and Tougouma,
*Distributions of Ulam Words up to Length 30*, INTEGERS 25 (2025), Article A102, Theorem 10. -/
public theorem_wanted isUlamWord_zeros_10101_zeros_iff (a b : ℕ) (hab : 1 ≤ a + b) :
    IsUlamWord (List.replicate a false ++ [true, false, true, false, true] ++
        List.replicate b false) ↔
      Even a ∧ Even b ∧ (a = 0 ∨ b = 0)

end

end MetaMathlibExt
