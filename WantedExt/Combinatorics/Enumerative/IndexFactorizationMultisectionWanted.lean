/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import MathlibExt.Analysis.SpecialFunctions.LambertSeries
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer

/-!
# Multisection identities by index factorization (statements)

Statement-only targets from Vignat and Milgram, *Curious Multisection Identities by
Index Factorization*. Every positive integer is written uniquely as
`m = (2n - 1) 2^j` (more generally `m = (bn - k) b^j` with `1 ≤ k < b`), and the
paper's identities regroup a sum or product over `m` along this factorization.

Conventions: a sequence `b₁, b₂, …` is a function `b : ℕ → ℂ` whose value at `0`
is unused; the paper's index `n ≥ 1` becomes `n + 1` (or `2n + 1`, `2n + 2`) with
`n : ℕ`. Product identities over an arbitrary sequence are stated in the paper's
sum form (Section 1 of the paper: each structural product identity "translates into
a sum form"). The paper's "such that the sums exist" is read as summability (absolute
convergence) of each family that the identity regroups.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Parametric two-adic multisection.** Let $q \in \mathbb{C}$ and let $b : \mathbb{N} \to
\mathbb{C}$ be a sequence (its value at $0$ is not used). Suppose that the families
$(q^j b_{(2n-1) 2^j})$ and $(q^j (q - 1) b_{2n \cdot 2^j})$, indexed by the pairs $(j, n)$ of
natural numbers with $n \ge 1$, are summable. Then
$$\sum_{j \ge 0,\ n \ge 1} \left(q^j b_{(2n-1) 2^j} - q^j (q - 1) b_{2n \cdot 2^j}\right)
= \sum_{m \ge 1} b_m.$$

The two summability hypotheses imply that $(b_m)_{m \ge 1}$ is summable.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 1, series version (`jis-2024-24.5.5-prop-1`). -/
public theorem_wanted tsum_twoAdic_parametric_multisection (q : ℂ) (b : ℕ → ℂ)
    (hodd : Summable fun x : ℕ × ℕ => q ^ x.1 * b ((2 * x.2 + 1) * 2 ^ x.1))
    (heven : Summable fun x : ℕ × ℕ => q ^ x.1 * (q - 1) * b ((2 * x.2 + 2) * 2 ^ x.1)) :
    ∑' x : ℕ × ℕ, (q ^ x.1 * b ((2 * x.2 + 1) * 2 ^ x.1)
        - q ^ x.1 * (q - 1) * b ((2 * x.2 + 2) * 2 ^ x.1))
      = ∑' m : ℕ, b (m + 1)

/-- **Parametric 3-adic multisection of a series.** Let $q$ be a complex number and let
$(b_m)_{m \ge 1}$ be a sequence of complex numbers such that the three families
$q^j b_{(3n-1) 3^j}$, $q^j b_{(3n-2) 3^j}$ and $q^j (q - 1) b_{3n \cdot 3^j}$, each indexed by
the pairs $(j, n)$ with $j \ge 0$ and $n \ge 1$, are summable. Then
$$\sum_{j \ge 0,\, n \ge 1} \Bigl( q^j \bigl( b_{(3n-1) 3^j} + b_{(3n-2) 3^j} \bigr) -
q^j (q - 1) b_{3n \cdot 3^j} \Bigr) = \sum_{m \ge 1} b_m.$$

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 6, first display in sum form (`jis-2024-24.5.5-cor-6`). -/
public theorem_wanted tsum_threeAdic_parametric_multisection (q : ℂ) (b : ℕ → ℂ)
    (h₂ : Summable fun x : ℕ × ℕ => q ^ x.1 * b ((3 * x.2 + 2) * 3 ^ x.1))
    (h₁ : Summable fun x : ℕ × ℕ => q ^ x.1 * b ((3 * x.2 + 1) * 3 ^ x.1))
    (h₃ : Summable fun x : ℕ × ℕ => q ^ x.1 * (q - 1) * b ((3 * x.2 + 3) * 3 ^ x.1)) :
    ∑' x : ℕ × ℕ, (q ^ x.1 * (b ((3 * x.2 + 2) * 3 ^ x.1) + b ((3 * x.2 + 1) * 3 ^ x.1))
        - q ^ x.1 * (q - 1) * b ((3 * x.2 + 3) * 3 ^ x.1))
      = ∑' m : ℕ, b (m + 1)

/-- **Regrouping the multiples of 3 by their 3-adic factorization.** Let $(b_m)_{m \ge 1}$ be a
sequence of complex numbers such that the family $(b_{3m})_{m \ge 1}$ is summable. Then
$$\sum_{j \ge 1,\, n \ge 1} \bigl( b_{(3n-1) 3^j} + b_{(3n-2) 3^j} \bigr) =
\sum_{m \ge 1} b_{3m},$$
where the sum on the left is an unconditional sum over the pairs $(j, n)$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 6, deduced identity in sum form (`jis-2024-24.5.5-cor-6`). -/
public theorem_wanted tsum_threeAdic_multiples_regroup (b : ℕ → ℂ)
    (hb : Summable fun m : ℕ => b (3 * (m + 1))) :
    ∑' x : ℕ × ℕ, (b ((3 * x.2 + 2) * 3 ^ (x.1 + 1)) + b ((3 * x.2 + 1) * 3 ^ (x.1 + 1)))
      = ∑' m : ℕ, b (3 * (m + 1))

/-- **Parametric base-B multisection of a series.** Let $B \ge 2$ be a natural number, let $q$
be a complex number and let $(c_m)_{m \ge 1}$ be a sequence of complex numbers. Suppose that the
family $q^j c_{(Bn-k) B^j}$ indexed by the triples $(j, n, k)$ with $j \ge 0$, $n \ge 1$ and
$1 \le k \le B - 1$ is summable, and that the family $q^j (q - 1) c_{Bn \cdot B^j}$ indexed by
the pairs $(j, n)$ with $j \ge 0$ and $n \ge 1$ is summable. Then
$$\sum_{j \ge 0,\, n \ge 1} \Bigl( q^j \sum_{k=1}^{B-1} c_{(Bn-k) B^j} -
q^j (q - 1) c_{Bn \cdot B^j} \Bigr) = \sum_{m \ge 1} c_m.$$

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 7, first display in sum form (`jis-2024-24.5.5-prop-7`). -/
public theorem_wanted tsum_baseAdic_parametric_multisection (B : ℕ) (hB : 2 ≤ B) (q : ℂ)
    (c : ℕ → ℂ)
    (hlow : Summable fun x : ℕ × ℕ × Fin (B - 1) =>
      q ^ x.1 * c ((B * (x.2.1 + 1) - (x.2.2 + 1)) * B ^ x.1))
    (htop : Summable fun x : ℕ × ℕ => q ^ x.1 * (q - 1) * c (B * (x.2 + 1) * B ^ x.1)) :
    ∑' x : ℕ × ℕ, (q ^ x.1 * ∑ i : Fin (B - 1), c ((B * (x.2 + 1) - (i + 1)) * B ^ x.1)
        - q ^ x.1 * (q - 1) * c (B * (x.2 + 1) * B ^ x.1))
      = ∑' m : ℕ, c (m + 1)

/-- **Regrouping the multiples of B by their B-adic factorization.** Let $B \ge 2$ be a natural
number and let $(c_m)_{m \ge 1}$ be a sequence of complex numbers such that the family
$(c_{Bm})_{m \ge 1}$ is summable. Then
$$\sum_{j \ge 1,\, n \ge 1} \sum_{k=1}^{B-1} c_{(Bn-k) B^j} = \sum_{m \ge 1} c_{Bm},$$
where the outer sum on the left is an unconditional sum over the pairs $(j, n)$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 7, deduced identity in sum form (`jis-2024-24.5.5-prop-7`). -/
public theorem_wanted tsum_baseAdic_multiples_regroup (B : ℕ) (hB : 2 ≤ B) (c : ℕ → ℂ)
    (hc : Summable fun m : ℕ => c (B * (m + 1))) :
    ∑' x : ℕ × ℕ, ∑ i : Fin (B - 1), c ((B * (x.2 + 1) - (i + 1)) * B ^ (x.1 + 1))
      = ∑' m : ℕ, c (B * (m + 1))

/-- **Weighted base-B multisection of a series.** Let $B \ge 2$ be a natural number, let
$\varphi, \chi : \mathbb{N} \to \mathbb{C}$ be weights and let $(c_m)_{m \ge 1}$ be a sequence
of complex numbers, and for $m \ge 1$ let $\nu_B(m)$ be the largest $k$ with $B^k \mid m$.
Suppose that the family $\varphi(j) c_{(Bn-k) B^j}$ indexed by the triples $(j, n, k)$ with
$j \ge 0$, $n \ge 1$ and $1 \le k \le B - 1$ is summable, and that the family
$\chi(j) c_{Bn \cdot B^j}$ indexed by the pairs $(j, n)$ with $j \ge 0$ and $n \ge 1$ is
summable. Then
$$\sum_{j \ge 0,\, n \ge 1} \Bigl( \sum_{k=1}^{B-1} \varphi(j) c_{(Bn-k) B^j} +
\chi(j) c_{Bn \cdot B^j} \Bigr) = \sum_{m \ge 1} \Bigl( \varphi(\nu_B(m)) +
\sum_{k < \nu_B(m)} \chi(k) \Bigr) c_m.$$

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 8, base-`b` sum form (`jis-2024-24.5.5-prop-8`). -/
public theorem_wanted tsum_baseAdic_weighted_multisection (B : ℕ) (hB : 2 ≤ B)
    (φ χ c : ℕ → ℂ)
    (hlow : Summable fun x : ℕ × ℕ × Fin (B - 1) =>
      φ x.1 * c ((B * (x.2.1 + 1) - (x.2.2 + 1)) * B ^ x.1))
    (htop : Summable fun x : ℕ × ℕ => χ x.1 * c (B * (x.2 + 1) * B ^ x.1)) :
    ∑' x : ℕ × ℕ, (∑ i : Fin (B - 1), φ x.1 * c ((B * (x.2 + 1) - (i + 1)) * B ^ x.1)
        + χ x.1 * c (B * (x.2 + 1) * B ^ x.1))
      = ∑' m : ℕ, (φ (padicValNat B (m + 1))
          + ∑ k ∈ Finset.range (padicValNat B (m + 1)), χ k) * c (m + 1)

/-- **Truncated two-adic regrouping.** For every natural number $J$ and all sequences
$\varphi, c : \mathbb{N} \to \mathbb{C}$,
$$\sum_{j \ge J,\ n \ge 1} \varphi(j) c_{(2n-1) 2^j}
= \sum_{p \ge 1} \varphi(J + \nu_2(p)) c_{p 2^J},$$
where $\nu_2(p)$ is the exponent of the largest power of $2$ dividing $p$, the left side runs over
the pairs $(j, n)$ of natural numbers with $j \ge J$ and $n \ge 1$, the right side runs over the
positive integers $p$, and each side is an unconditional sum, taken to be $0$ when its family is
not summable.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 13, in sum form (`jis-2024-24.5.5-prop-13`). -/
public theorem_wanted tsum_twoAdic_truncated_regroup (J : ℕ) (φ c : ℕ → ℂ) :
    ∑' x : ℕ × ℕ, φ (x.1 + J) * c ((2 * x.2 + 1) * 2 ^ (x.1 + J))
      = ∑' p : ℕ, φ (J + padicValNat 2 (p + 1)) * c ((p + 1) * 2 ^ J)

/-- **Regrouping the multiples of a power of 2 by their 2-adic factorization.** For every
natural number $J$ and every sequence $(c_m)_{m \ge 1}$ of complex numbers,
$$\sum_{j \ge J,\, n \ge 1} c_{(2n-1) 2^j} = \sum_{p \ge 1} c_{p 2^J},$$
where the left side is an unconditional sum over the pairs $(j, n)$. No summability is assumed:
$(j, n) \mapsto (2n-1) 2^{j-J}$ is a bijection onto the positive integers, so the two families
are summable together or not at all, and a non-summable family has sum $0$ by convention.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 14, first display in sum form (`jis-2024-24.5.5-cor-14`). -/
public theorem_wanted tsum_twoAdic_high_regroup (J : ℕ) (c : ℕ → ℂ) :
    ∑' x : ℕ × ℕ, c ((2 * x.2 + 1) * 2 ^ (x.1 + J)) = ∑' p : ℕ, c ((p + 1) * 2 ^ J)

/-- **Two-adic regrouping of the non-multiples of a power of two.** For every natural number $J$
and every sequence $c : \mathbb{N} \to \mathbb{C}$,
$$\sum_{0 \le j < J,\ n \ge 1} c_{(2n-1) 2^j} = \sum_{p \ge 1,\ 2^J \nmid p} c_p,$$
where the left side runs over the pairs $(j, n)$ of natural numbers with $j < J$ and $n \ge 1$,
the right side runs over the positive integers $p$ not divisible by $2^J$, and each side is an
unconditional sum, taken to be $0$ when its family is not summable.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 14, second display in sum form (`jis-2024-24.5.5-cor-14`). -/
public theorem_wanted tsum_twoAdic_low_regroup (J : ℕ) (c : ℕ → ℂ) :
    ∑' x : Fin J × ℕ, c ((2 * x.2 + 1) * 2 ^ (x.1 : ℕ))
      = ∑' p : {p : ℕ // 0 < p ∧ ¬ 2 ^ J ∣ p}, c p

/-- **Double 2-adic multisection of a double series.** Let $(b_{p,q})_{p, q \ge 1}$ be a double
sequence of complex numbers such that each of the four families
$2^{j+k} b_{(2n-1) 2^j, (2m-1) 2^k}$, $2^{j+k} b_{(2n) 2^j, (2m) 2^k}$,
$2^{j+k} b_{(2n) 2^j, (2m-1) 2^k}$ and $2^{j+k} b_{(2n-1) 2^j, (2m) 2^k}$, indexed by the
quadruples $(j, k, n, m)$ with $j, k \ge 0$ and $n, m \ge 1$, is summable. Then
$$\sum_{p, q \ge 1} b_{p,q} = \sum_{j, k \ge 0,\ n, m \ge 1} 2^{j+k} \bigl(
b_{(2n-1) 2^j, (2m-1) 2^k} + b_{(2n) 2^j, (2m) 2^k} -
b_{(2n) 2^j, (2m-1) 2^k} - b_{(2n-1) 2^j, (2m) 2^k} \bigr),$$
where both sides are unconditional sums, over the pairs $(p, q)$ and the quadruples
$(j, k, n, m)$ respectively.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 15, sum version (`jis-2024-24.5.5-prop-15`). -/
public theorem_wanted tsum_twoAdic_double_multisection (b : ℕ → ℕ → ℂ)
    (h₁ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2))
    (h₂ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2))
    (h₃ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2))
    (h₄ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2)) :
    ∑' p : ℕ × ℕ, b (p.1 + 1) (p.2 + 1)
      = ∑' x : (ℕ × ℕ) × (ℕ × ℕ), (2 : ℂ) ^ (x.1.1 + x.1.2)
          * (b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2)
            + b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2)
            - b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2)
            - b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2))

/-- **$2$-adic expansion of the weighted Lambert series $f$.** For every complex number $q$ with
$|q| < 1$, the weighted Lambert series $f(q) = \sum_{n \ge 1} n q^n / (1 - q^n)$ and
$g(q) = \sum_{n \ge 1} n q^n / (1 + q^n)$ satisfy
$f(q) = \sum_{j, k \ge 0} 2^{2j+k} \bigl(g(q^{2^{j+k}}) - 4 g(q^{2^{j+k+1}})\bigr)$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 16 (`jis-2024-24.5.5-cor-16`). -/
public theorem_wanted lambert_sigma_eq_tsum_twoAdic (q : ℂ) (hq : ‖q‖ < 1) :
    lambertF ⟨q, hq⟩
      = ∑' x : ℕ × ℕ, (2 : ℂ) ^ (2 * x.1 + x.2)
          * (lambertG ⟨q ^ 2 ^ (x.1 + x.2),
              (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))⟩
            - 4 * lambertG ⟨q ^ 2 ^ (x.1 + x.2 + 1),
              (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))⟩)

/-- **2-adic dissection of the Euler function.** For every complex number $q$ with $|q| < 1$,
with the infinite q-Pochhammer symbol $(a; r)_\infty = \prod_{k \ge 0} (1 - a r^k)$, the
unconditional infinite product over $j \ge 0$ satisfies
$$\prod_{j \ge 0} \left( \frac{(q^{2^j}; q^{2^{j+1}})_\infty}
{(q^{2^{j+1}}; q^{2^{j+1}})_\infty} \right)^{2^j} = (q; q)_\infty.$$

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, first display (`jis-2024-24.5.5-prop-19`). -/
public theorem_wanted tprod_qPochhammer_twoAdic (q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, (QPochhammer.qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
        / QPochhammer.qPochhammerInf (q ^ 2 ^ (j + 1)) (q ^ 2 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))) ^ 2 ^ j
      = QPochhammer.qPochhammerInf q q hq

/-- **Parametric 2-adic dissection of the Euler function for real q.** Let $q$ and $p$ be real
numbers with $0 < q < 1$, and write $(a; r)_\infty = \prod_{k \ge 0} (1 - a r^k)$ for real $a$
and $r$ (an unconditional infinite product). Then, with real exponents $p - 1$ and $p^j$,
$$\prod_{j \ge 0} \left( \frac{(q^{2^j}; q^{2^{j+1}})_\infty}
{(q^{2^{j+1}}; q^{2^{j+1}})_\infty^{\,p-1}} \right)^{p^j} = (q; q)_\infty.$$

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, second display, real case (`jis-2024-24.5.5-prop-19`). -/
public theorem_wanted tprod_qPochhammer_twoAdic_parametric (q p : ℝ) (hq₀ : 0 < q)
    (hq₁ : q < 1) :
    ∏' j : ℕ, ((∏' k : ℕ, (1 - q ^ 2 ^ j * (q ^ 2 ^ (j + 1)) ^ k))
        / (∏' k : ℕ, (1 - q ^ 2 ^ (j + 1) * (q ^ 2 ^ (j + 1)) ^ k)) ^ (p - 1)) ^ (p ^ j)
      = ∏' k : ℕ, (1 - q * q ^ k)

/-- **Parametric $3$-adic dissection of the Euler function.** For real numbers $x$ and $y$ with
$0 < y < 1$ write $(x; y)_\infty = \prod_{k \ge 0} (1 - x y^k)$. For all real numbers $q$ and $p$
with $0 < q < 1$,
$\prod_{j \ge 0} \bigl((q^{3^j}; q^{3^{j+1}})_\infty\, (q^{2 \cdot 3^j}; q^{3^{j+1}})_\infty /
(q^{3^{j+1}}; q^{3^{j+1}})_\infty^{\,p - 1}\bigr)^{p^j} = (q; q)_\infty$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, third display, real case (`jis-2024-24.5.5-prop-19`). -/
public theorem_wanted tprod_qPochhammer_threeAdic_parametric (q p : ℝ) (hq₀ : 0 < q)
    (hq₁ : q < 1) :
    ∏' j : ℕ, ((∏' k : ℕ, (1 - q ^ 3 ^ j * (q ^ 3 ^ (j + 1)) ^ k))
        * (∏' k : ℕ, (1 - q ^ (2 * 3 ^ j) * (q ^ 3 ^ (j + 1)) ^ k))
        / (∏' k : ℕ, (1 - q ^ 3 ^ (j + 1) * (q ^ 3 ^ (j + 1)) ^ k)) ^ (p - 1)) ^ (p ^ j)
      = ∏' k : ℕ, (1 - q * q ^ k)

/-- **2-adic product factorization of the Euler function.** For every complex number $q$ with
$|q| < 1$, with the infinite q-Pochhammer symbol $(a; r)_\infty = \prod_{k \ge 0} (1 - a r^k)$,
the unconditional infinite product over $j \ge 0$ satisfies
$\prod_{j \ge 0} (q^{2^j}; q^{2^{j+1}})_\infty = (q; q)_\infty$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, case `p = 1`, base 2 (`jis-2024-24.5.5-prop-19`). -/
public theorem_wanted tprod_qPochhammer_twoAdic_factorization (q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, QPochhammer.qPochhammerInf (q ^ 2 ^ j) (q ^ 2 ^ (j + 1))
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
      = QPochhammer.qPochhammerInf q q hq

/-- **$3$-adic factorization of the Euler function.** Write
$(x; y)_\infty = \prod_{k \ge 0} (1 - x y^k)$ for the infinite $q$-Pochhammer symbol, where $x$
and $y$ are complex and $|y| < 1$. For every complex number $q$ with $|q| < 1$,
$\prod_{j \ge 0} (q^{3^j}; q^{3^{j+1}})_\infty\, (q^{2 \cdot 3^j}; q^{3^{j+1}})_\infty =
(q; q)_\infty$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 19, case `p = 1`, base 3 (`jis-2024-24.5.5-prop-19`). -/
public theorem_wanted tprod_qPochhammer_threeAdic_factorization (q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, (QPochhammer.qPochhammerInf (q ^ 3 ^ j) (q ^ 3 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
        * QPochhammer.qPochhammerInf (q ^ (2 * 3 ^ j)) (q ^ 3 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity)))
      = QPochhammer.qPochhammerInf q q hq

/-- **$2$-adic multisection of the infinite $q$-Pochhammer symbol.** Write
$(x; y)_\infty = \prod_{k \ge 0} (1 - x y^k)$ for the infinite $q$-Pochhammer symbol, where $x$
and $y$ are complex and $|y| < 1$. For complex numbers $a$ and $q$ with $|q| < 1$,
$\prod_{j \ge 0} \bigl((a q^{2^j - 1}; q^{2^{j+1}})_\infty /
(a q^{2^{j+1} - 1}; q^{2^{j+1}})_\infty\bigr)^{2^j} = (a; q)_\infty$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 20 (`jis-2024-24.5.5-prop-20`). -/
public theorem_wanted tprod_qPochhammer_shifted_twoAdic (a q : ℂ) (hq : ‖q‖ < 1) :
    ∏' j : ℕ, (QPochhammer.qPochhammerInf (a * q ^ (2 ^ j - 1)) (q ^ 2 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))
        / QPochhammer.qPochhammerInf (a * q ^ (2 ^ (j + 1) - 1)) (q ^ 2 ^ (j + 1))
          (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))) ^ 2 ^ j
      = QPochhammer.qPochhammerInf a q hq

/-- **$2$-adic dissection of a ratio of Gamma functions.** For complex numbers $a$ and $z$ write
$f(a, z) = \Gamma(a + 1)^2 / \bigl(\Gamma(a + 1 - iz)\, \Gamma(a + 1 + iz)\bigr)$. If $a$ is not a
negative integer, then for every complex number $z$,
$f(a, z) = \prod_{j \ge 0} f(a / 2^{j+1} - 1/2,\ z / 2^{j+1})$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 22 (`jis-2024-24.5.5-prop-22`). -/
public theorem_wanted gamma_ratio_eq_tprod_twoAdic (a z : ℂ)
    (ha : ∀ n : ℕ, a ≠ -((n : ℂ) + 1)) :
    Complex.Gamma (a + 1) ^ 2
        / (Complex.Gamma (a + 1 - Complex.I * z) * Complex.Gamma (a + 1 + Complex.I * z))
      = ∏' j : ℕ, Complex.Gamma (a / 2 ^ (j + 1) + 1 / 2) ^ 2
          / (Complex.Gamma (a / 2 ^ (j + 1) + 1 / 2 - Complex.I * (z / 2 ^ (j + 1)))
            * Complex.Gamma (a / 2 ^ (j + 1) + 1 / 2 + Complex.I * (z / 2 ^ (j + 1))))


/-- **Two-adic multisection of the power-weighted Lambert series.** For every integer $\mu \ge 1$
and every complex number $q$ with $|q| < 1$, the power-weighted Lambert series
$f_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 - q^n)$ and
$g_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 + q^n)$ satisfy
$$
f_\mu(q) = \sum_{j, k \ge 0} 2^{(\mu+1)j+k}
\left(g_\mu\left(q^{2^{j+k}}\right) - 2^{\mu+1} g_\mu\left(q^{2^{j+k+1}}\right)\right),
$$
the sum running over all pairs $(j, k)$ of natural numbers.

The paper prints the weight $2^{2j+k}$, its value for $\mu = 1$ (Corollary 16), which is false
for $\mu \ge 2$: for $\mu = 2$ the coefficient of $q^2$ is $\sigma_2(2) = 1^2 + 2^2 = 5$ on the
left and $1$ on the right. The weight $2^{(\mu+1)j+k}$ is what the paper's proof of Corollary 16
gives with $n^\mu$ in place of $n$: there $2^{2j+k} = 2^{j+k} \cdot 2^j$, where $2^j$ is the
factor of the index $(2n-1) 2^j$ in the summand $n$, which becomes $2^{\mu j}$ for $n^\mu$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Corollary 17 (`jis-2024-24.5.5-cor-17`). -/
public theorem_wanted lambertMu_sigma_eq_tsum_twoAdic (μ : {μ : ℕ // 1 ≤ μ}) (q : ℂ)
    (hq : ‖q‖ < 1) :
    lambertFMu ⟨q, hq⟩ μ
      = ∑' x : ℕ × ℕ, (2 : ℂ) ^ (((μ : ℕ) + 1) * x.1 + x.2)
          * (lambertGMu ⟨q ^ 2 ^ (x.1 + x.2),
              (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))⟩ μ
            - 2 ^ ((μ : ℕ) + 1) * lambertGMu ⟨q ^ 2 ^ (x.1 + x.2 + 1),
              (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by positivity))⟩ μ)

/-- **Borwein's eta–Lambert correspondence.** Let $(a_n)$ and $(b_n)$ be sequences of complex
numbers and let $C$ and $K$ be real numbers with $|a_n| \le C n^K$ and $|b_n| \le C n^K$ for every
$n \ge 1$. Let $\eta(s) = \sum_{n \ge 1} (-1)^{n-1} n^{-s}$ be the Dirichlet eta function. Then
$\eta(s) \sum_{n \ge 1} a_n n^{-s} = \sum_{n \ge 1} b_n n^{-s}$ for every real number
$s > \max(K + 2, 1)$ if and only if $\sum_{n \ge 1} a_n x^n / (1 + x^n) = \sum_{n \ge 1} b_n x^n$
for every real number $x$ with $0 < x < 1$.

The source quotes the correspondence from Borwein and Borwein without growth hypotheses or
ranges for $s$ and $x$; the growth bound and the ranges above make all the series involved converge
absolutely.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Proposition 18 (`jis-2024-24.5.5-prop-18`). -/
public theorem_wanted eta_mul_LSeries_iff_lambert (a b : ℕ → ℂ) (C K : ℝ)
    (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ K)
    (hb : ∀ n : ℕ, 1 ≤ n → ‖b n‖ ≤ C * (n : ℝ) ^ K) :
    (∀ s : ℝ, max (K + 2) 1 < s →
      LSeries (fun n : ℕ => (-1 : ℂ) ^ (n + 1)) s * LSeries a s = LSeries b s) ↔
    ∀ x : ℝ, 0 < x → x < 1 →
      ∑' n : ℕ, a (n + 1) * (x : ℂ) ^ (n + 1) / (1 + (x : ℂ) ^ (n + 1)) =
        ∑' n : ℕ, b (n + 1) * (x : ℂ) ^ (n + 1)

/-- **The Gamma quadratic ratio.** For complex numbers $a$, $b$ and $z$, the Gamma quadratic ratio
is $g(a, b, z) = \dfrac{b}{b - z} \cdot
\dfrac{\Gamma(a - \sqrt{a^2 - b})\, \Gamma(a + \sqrt{a^2 - b})}
{\Gamma(a - \sqrt{a^2 - b + z})\, \Gamma(a + \sqrt{a^2 - b + z})}$, where $\sqrt{\cdot}$ is the
principal complex square root (the value does not depend on the choice of root).

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Proposition 23. -/
public noncomputable def gammaQuadraticRatio (a b z : ℂ) : ℂ :=
  b / (b - z) * (Complex.Gamma (a - (a ^ 2 - b) ^ (1 / 2 : ℂ))
      * Complex.Gamma (a + (a ^ 2 - b) ^ (1 / 2 : ℂ)))
    / (Complex.Gamma (a - (a ^ 2 - b + z) ^ (1 / 2 : ℂ))
      * Complex.Gamma (a + (a ^ 2 - b + z) ^ (1 / 2 : ℂ)))

/-- **The Gamma quadratic ratio at $z = 0$.** Let $a$ and $b$ be complex numbers with $b \ne 0$
and $\Gamma(a - \sqrt{a^2 - b})\, \Gamma(a + \sqrt{a^2 - b}) \ne 0$, where $\sqrt{\cdot}$ denotes
the principal complex square root. Then the Gamma quadratic ratio $g$ satisfies $g(a, b, 0) = 1$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Proposition 23. -/
public theorem gammaQuadraticRatio_zero_right (a b : ℂ) (hb : b ≠ 0)
    (hΓ : Complex.Gamma (a - (a ^ 2 - b) ^ (1 / 2 : ℂ))
      * Complex.Gamma (a + (a ^ 2 - b) ^ (1 / 2 : ℂ)) ≠ 0) :
    gammaQuadraticRatio a b 0 = 1 := by
  simp only [gammaQuadraticRatio, sub_zero, add_zero]
  rw [div_self hb, one_mul, div_self hΓ]

/-- **$2$-adic dissection of the Gamma quadratic ratio.** Let $a, b, z$ be complex numbers such
that $m^2 + 2am + b \ne 0$ and $m^2 + 2am + b - z \ne 0$ for every integer $m$ that is nonnegative
or of the form $m = -2^j$ with $j \ge 0$ an integer. For $j \ge 0$ put $a_j = a / 2^{j+1} - 1/2$
and $b_j = 1/4 - a / 2^{j+1} + b / 2^{2j+2}$. Then the Gamma quadratic ratio $g$ satisfies
$g(a, b, z) = \prod_{j \ge 0} g(a_j, b_j, z / 2^{2j+2})$.

The source prints the parameters $a / 2^j - 1$ and $1 - a / 2^{j+1} + b / 2^{2j+2}$, which make
the identity false: for $a = 3/10$, $b = -2$, $z = 7/10$ the left side is about $1.6283$ and the
printed product about $6.18 \cdot 10^4$, while the product above matches. The parameters $a_j$,
$b_j$ come from the penultimate line of the source's proof, which writes
$m^2 + 2am + b = 2^{2j+2}(n^2 + 2 a_j n + b_j)$ for $m = (2n - 1) 2^j$. The hypotheses, absent
from the source, exclude the poles of every Gamma factor on both sides and the vanishing of $b$
and $b - z$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5, Proposition 23 (`jis-2024-24.5.5-prop-23`). -/
public theorem_wanted gammaQuadraticRatio_eq_tprod_twoAdic (a b z : ℂ)
    (hb : ∀ m : ℤ, (0 ≤ m ∨ ∃ j : ℕ, m = -2 ^ j) → (m : ℂ) ^ 2 + 2 * a * m + b ≠ 0)
    (hz : ∀ m : ℤ, (0 ≤ m ∨ ∃ j : ℕ, m = -2 ^ j) → (m : ℂ) ^ 2 + 2 * a * m + b - z ≠ 0) :
    gammaQuadraticRatio a b z
      = ∏' j : ℕ, gammaQuadraticRatio (a / 2 ^ (j + 1) - 1 / 2)
          (1 / 4 - a / 2 ^ (j + 1) + b / 2 ^ (2 * j + 2)) (z / 2 ^ (2 * j + 2))

end

end MetaMathlibExt
