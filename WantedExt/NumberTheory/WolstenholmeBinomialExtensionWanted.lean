/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Binomial
public import MathlibExt.NumberTheory.HigherOrderHarmonic

/-!
# Extensions of Wolstenholme's theorem by binomial coefficients

Statements from Kehila's INTEGERS paper on `binom(np, kp)` modulo powers of `p`.
A rational congruence `x ≡ y (mod p^s)` (both sides `p`-integral) is written
`x - y = 0 ∨ s ≤ padicValRat p (x - y)`. The generalized harmonic numbers
`H_{p-1}(s) = ∑_{j=1}^{p-1} j^{-s}` are `higherHarmonic (p - 1) s`, and the
multiple harmonic sum `H_{p-1}(1, 1) = ∑_{1 ≤ i < j ≤ p-1} 1 / (i j)` is written
out with a strict inner range. Where the modulus is `p^{s + v_p(B)}` with an integer
`B`, the congruence is `X = 0 ∨ (B ≠ 0 ∧ s + padicValRat p B ≤ padicValRat p X)`, so
`B = 0` (`v_p(B) = ∞`) demands equality. The higher `p`-adic mean value theorem is stated
over `K = ℚ_p` for an ultrametric normed `ℚ_p`-space `B`.
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- Lemma 2: the coefficient of `x^{kp}` in `(x + 1)^{jp} (x^p + 1)^{n-j}` is
`c_j(n, k) = ∑_{s=0}^{j} binom(jp, sp) binom(n - j, k - s)`, where
`binom(n - j, k - s) = 0` for `s > k`. Stated for every `p > 0` (the paper takes
`p` prime) and every `j` (for `j > n` the truncated `n - j = 0` keeps it true).

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 2
(`integers-2026-A32-lem-2`). -/
public theorem_wanted coeff_add_one_pow_mul_X_pow_add_one_pow (p n j k : ℕ) (hp : 0 < p) :
    ((X + 1 : ℕ[X]) ^ (j * p) * (X ^ p + 1) ^ (n - j)).coeff (k * p) =
      ∑ s ∈ Finset.range (j + 1),
        if s ≤ k then (j * p).choose (s * p) * (n - j).choose (k - s) else 0

/-- Lemma 5: for `n ∈ ℕ` and `k ≥ 1`,
`binom(-np, kp) = (-1)^{kp} (n / k) binom((n + k)p - 1, kp - 1)
= (-1)^{kp} (n / (n + k)) binom((n + k)p, kp)`, with the negative upper index
read through `Ring.choose` on `ℤ`. Stated for every `p > 0` (the paper takes `p`
prime).

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 5
(`integers-2026-A32-lem-5`). -/
public theorem_wanted ringChoose_neg_mul_mul_eq (p n k : ℕ) (hp : 0 < p) (hk : 1 ≤ k) :
    ((Ring.choose (-((n * p : ℕ) : ℤ)) (k * p) : ℤ) : ℚ) =
        (-1) ^ (k * p) * ((n : ℚ) / k) * (((n + k) * p - 1).choose (k * p - 1) : ℚ) ∧
      ((Ring.choose (-((n * p : ℕ) : ℤ)) (k * p) : ℤ) : ℚ) =
        (-1) ^ (k * p) * ((n : ℚ) / (n + k)) * (((n + k) * p).choose (k * p) : ℚ)

/-- Theorem 10: for a prime `p ≥ 11` and `t ∈ ℕ`,
`binom(tp, p) ≡ t + (-t^5 + 2t^4 - t^2) p H_{p-1}(1) + t^3 (t - 1)^2 p^2 H_{p-1}(1, 1)
(mod p^7)`,
`binom(tp, p) ≡ t + (-t^5 + 2t^4 - t^2) p H_{p-1}(1) - (t^3 (t - 1)^2 / 2) p^2 H_{p-1}(2)
(mod p^6)`, and
`binom(tp, p) ≡ t + t^2 (t - 1) p H_{p-1}(1) (mod p^5)`.
`H_{p-1}(1, 1)` is the strict sum `∑_{i < j}` (the reading under which the first two
congruences agree modulo `p^6`).

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 10
(`integers-2026-A32-thm-10`). -/
public theorem_wanted choose_mul_prime_prime_harmonic_congr (p t : ℕ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let H1 : ℚ := higherHarmonic (p - 1) 1
    let H2 : ℚ := higherHarmonic (p - 1) 2
    let H11 : ℚ := ∑ j ∈ Finset.Icc 1 (p - 1), ∑ i ∈ Finset.Ico 1 j, 1 / ((i : ℚ) * j)
    let T : ℚ := t
    let B : ℚ := ((t * p).choose p : ℚ)
    (B - (T + (-T ^ 5 + 2 * T ^ 4 - T ^ 2) * p * H1 + T ^ 3 * (T - 1) ^ 2 * p ^ 2 * H11) = 0 ∨
        7 ≤ padicValRat p
          (B - (T + (-T ^ 5 + 2 * T ^ 4 - T ^ 2) * p * H1 + T ^ 3 * (T - 1) ^ 2 * p ^ 2 * H11))) ∧
      (B - (T + (-T ^ 5 + 2 * T ^ 4 - T ^ 2) * p * H1 - T ^ 3 * (T - 1) ^ 2 / 2 * p ^ 2 * H2) = 0 ∨
        6 ≤ padicValRat p
          (B - (T + (-T ^ 5 + 2 * T ^ 4 - T ^ 2) * p * H1 - T ^ 3 * (T - 1) ^ 2 / 2 * p ^ 2 * H2))) ∧
      (B - (T + T ^ 2 * (T - 1) * p * H1) = 0 ∨
        5 ≤ padicValRat p (B - (T + T ^ 2 * (T - 1) * p * H1)))

/-- Theorem 13: for a prime `p ≥ 11` and `α ∈ ℤ`,
`binom(αp - 1, p - 1) binom((α + 1)p - 1, p - 1)
≡ 1 - (αp)^2 H_{p-1}(2) + ((αp)^4 / 2) (H_{p-1}(2)^2 - H_{p-1}(4)) (mod p^7)`, and
`binom(2p - 1, p - 1)^{-1} ≡ 1 + p^2 H_{p-1}(2) + (p^4 / 2) (H_{p-1}(2)^2 + H_{p-1}(4))
(mod p^7)`. The paper takes `α ∈ ℤ_p`; this states the integer case, with negative
upper indices read through `Ring.choose`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 13
(`integers-2026-A32-thm-13`). -/
public theorem_wanted ringChoose_mul_prime_sub_one_mul_congr (p : ℕ) (α : ℤ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let H2 : ℚ := higherHarmonic (p - 1) 2
    let H4 : ℚ := higherHarmonic (p - 1) 4
    let A : ℚ := α * p
    let L : ℚ := ((Ring.choose (α * p - 1) (p - 1) : ℤ) : ℚ) *
      ((Ring.choose ((α + 1) * p - 1) (p - 1) : ℤ) : ℚ)
    let R : ℚ := ((2 * p - 1).choose (p - 1) : ℚ)⁻¹
    (L - (1 - A ^ 2 * H2 + A ^ 4 / 2 * (H2 ^ 2 - H4)) = 0 ∨
        7 ≤ padicValRat p (L - (1 - A ^ 2 * H2 + A ^ 4 / 2 * (H2 ^ 2 - H4)))) ∧
      (R - (1 + (p : ℚ) ^ 2 * H2 + (p : ℚ) ^ 4 / 2 * (H2 ^ 2 + H4)) = 0 ∨
        7 ≤ padicValRat p (R - (1 + (p : ℚ) ^ 2 * H2 + (p : ℚ) ^ 4 / 2 * (H2 ^ 2 + H4))))

/-! ### Higher `p`-adic mean value theorem -/

/-- Lemma 1: on the Tate algebra `B{t}` over an ultrametric Banach space `B` with the
sup norm, `‖D^n / n!‖ ≤ 1`; coefficientwise, every coefficient
`binom(k + n, n) a_{k+n}` of `D^n f / n!` has norm at most any bound `C` of the
coefficient norms of `f = ∑ a_k t^k`. Stated over `K = ℚ_p` (the paper allows any
`K` between `ℚ_p` and `ℂ_p`) and for every coefficient sequence (the decay
`a_k → 0` and completeness of `B` are not needed for the bound).

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 1
(`integers-2026-A32-lem-1`). -/
public theorem_wanted norm_choose_nsmul_coeff_le {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (a : ℕ → B) (C : ℝ)
    (hC : ∀ k, ‖a k‖ ≤ C) (n k : ℕ) :
    ‖(k + n).choose n • a (k + n)‖ ≤ C

/-- Theorem 1 (higher `p`-adic mean value theorem): for a polynomial
`f(t) = ∑_{j < N} a_j t^j` with coefficients in an ultrametric normed space `B` over
`ℚ_p`, `|t| ≤ 1`, and `1 ≤ m ≤ p`,
`‖f(t + h) - ∑_{q < m} f^{(q)}(t) h^q / q!‖ ≤ |h^m / m| ‖f^{(m)}‖`
provided `|h| ≤ |p|^{1/(p-m)}` when `m < p` and `|h| ≤ |p|^{1/p}` when `m = p`.
Here `f^{(q)}(t) / q! = ∑_j binom(j, q) t^{j-q} a_j`, `‖f^{(m)}‖` is the sup of the
norms of the coefficients `j (j - 1) ⋯ (j - m + 1) a_j` (any nonnegative upper bound `C` of
them is allowed), and `|p| = p⁻¹`. Stated over `K = ℚ_p` (the paper allows any `K`
between `ℚ_p` and `ℂ_p`); completeness of `B` is not needed for polynomials.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 1
(`integers-2026-A32-thm-1`). -/
public theorem_wanted norm_sub_taylor_le_of_norm_le {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (N m : ℕ) (a : ℕ → B)
    (t h : ℚ_[p]) (C : ℝ) (ht : ‖t‖ ≤ 1) (hm : 1 ≤ m) (hmp : m ≤ p)
    (hh₁ : m < p → ‖h‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - m))))
    (hh₂ : m = p → ‖h‖ ≤ (p : ℝ) ^ (-(1 / (p : ℝ))))
    (hC₀ : 0 ≤ C) (hC : ∀ j ∈ Finset.range N, ‖j.descFactorial m • a j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, (t + h) ^ j • a j -
        ∑ q ∈ Finset.range m, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j‖ ≤
      ‖h ^ m / (m : ℚ_[p])‖ * C

/-- Theorem 2 (congruence form of Theorem 1): with `f`, `t`, `m` as in Theorem 1 and
`v_p(‖f^{(m)}‖) ≥ w` (every coefficient `j (j - 1) ⋯ (j - m + 1) a_j` has norm at most
`p^{-w}`),
`f(t + h) ≡ ∑_{q < m} f^{(q)}(t) h^q / q! (mod p^{m v_p(h) + w})` when `m < p` and
`v_p(h) ≥ 1 / (p - m)`, and modulo `p^{p v_p(h) + w - 1}` when `m = p` and
`v_p(h) ≥ 1 / p`; a congruence modulo `p^v` in `B` means norm at most `p^{-v}`.
Stated over `K = ℚ_p`, where `v_p(h)` is `Padic.valuation h`. Mathlib sets
`Padic.valuation 0 = 0` rather than `∞`, so the case `h = 0` (where both congruences hold
because the remainder vanishes) is the separate third conjunct.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 2
(`integers-2026-A32-thm-2`). -/
public theorem_wanted norm_sub_taylor_le_zpow_valuation {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (N m : ℕ) (a : ℕ → B)
    (t h : ℚ_[p]) (w : ℝ) (ht : ‖t‖ ≤ 1) (hm : 1 ≤ m) (hmp : m ≤ p)
    (hC : ∀ j ∈ Finset.range N, ‖j.descFactorial m • a j‖ ≤ (p : ℝ) ^ (-w)) :
    let R : ℝ := ‖∑ j ∈ Finset.range N, (t + h) ^ j • a j -
        ∑ q ∈ Finset.range m, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j‖
    (m < p → 1 / ((p : ℝ) - m) ≤ h.valuation →
        R ≤ (p : ℝ) ^ (-((m : ℝ) * h.valuation + w))) ∧
      (m = p → 1 / (p : ℝ) ≤ h.valuation →
        R ≤ (p : ℝ) ^ (-((p : ℝ) * h.valuation + w - 1))) ∧
      (h = 0 → R = 0)

/-! ### The general congruence for `binom(np, kp)` -/

/-- Lemma 3: for `m, n, k ∈ ℕ` and `0 ≤ j ≤ m`,
`∑_{s=j}^{m} (-1)^{s-j} binom(n, s) binom(s, j) = (-1)^{m-j} binom(n, j) binom(n - j - 1, m - j)
= binom(n, j) binom(m - n, m - j)`,
`∑_{j=0}^{m} (-1)^{m-j} binom(n, j) binom(n - j - 1, m - j) binom(n - j, k) = binom(n, k) binom(m - k, m)`,
`∑_{j=0}^{m} (-1)^{m-j} binom(n, j) binom(n - j - 1, m - j) binom(n - j, k - j)
= binom(n, k) binom(k + m - n, m)`,
with integer upper indices read through `Ring.choose` and `binom(x, k - j) = 0` for `j > k`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 3
(`integers-2026-A32-lem-3`). -/
public theorem_wanted alternating_choose_sum_identities (m n k : ℕ) :
    let C : ℤ → ℕ → ℤ := fun x r => Ring.choose x r
    (∀ j ≤ m, ∑ s ∈ Finset.Icc j m, (-1 : ℤ) ^ (s - j) * C n s * C s j =
          (-1) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) ∧
        (-1 : ℤ) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) =
          C n j * C ((m : ℤ) - n) (m - j)) ∧
      ∑ j ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) * C ((n : ℤ) - j) k =
        C n k * C ((m : ℤ) - k) m ∧
      ∑ j ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) *
            (if j ≤ k then C ((n : ℤ) - j) (k - j) else 0) =
        C n k * C ((k : ℤ) + m - n) m

/-- Theorem 3: for a prime `p`, `m, k ∈ ℕ` with `m + 1 < p` (the paper's setting: the mean value
theorem is applied with order `m + 1 < p`) and `n ∈ ℤ`, with
`c_j(n, k) = ∑_{s=0}^{j} binom(jp, sp) binom(n - j, k - s)` (Lemma 2) and
`d(l, n, k) = binom(n, l) ∑_{j=0}^{l} (-1)^{l-j} binom(l, j) c_j(n, k)`,
`binom(np, kp) - binom(n, k) ≡ d(1, n, k) + ⋯ + d(m, n, k) (mod p^{m+1+v_p(binom(n, m+1))})`.
Negative upper indices are read through `Ring.choose`. The congruence is written
`X = 0 ∨ (binom(n, m+1) ≠ 0 ∧ m + 1 + v_p(binom(n, m+1)) ≤ v_p(X))`, so
`binom(n, m+1) = 0` (`v_p = ∞`) demands equality.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 3
(`integers-2026-A32-thm-3`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_sum_d (p m k : ℕ) (n : ℤ) (hp : p.Prime)
    (hmp : m + 1 < p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let c : ℕ → ℚ := fun j => ∑ s ∈ Finset.range (j + 1),
      if s ≤ k then C ((j * p : ℕ) : ℤ) (s * p) * C (n - j) (k - s) else 0
    let d : ℕ → ℚ := fun l =>
      C n l * ∑ j ∈ Finset.range (l + 1), (-1) ^ (l - j) * (l.choose j : ℚ) * c j
    let X : ℚ := C (n * p) (k * p) - C n k - ∑ l ∈ Finset.Icc 1 m, d l
    X = 0 ∨ (C n (m + 1) ≠ 0 ∧
      ((m + 1 : ℕ) : ℤ) + padicValRat p (C n (m + 1)) ≤ padicValRat p X)

/-- Lemma 4: for a prime `p`, `m, k ∈ ℕ` with `m + 1 < p` and `n ∈ ℤ`,
`binom(np, kp) - binom(n, k) ≡ C̄_{00}(m, n, k) + ∑_{1 ≤ i < j ≤ m} C̄_{ji}(m, n, k) binom(jp, ip)
(mod p^{m+1+v_p(binom(n, m+1))})`, where
`C̄_{00} = (binom(m - k, m) + binom(k + m - n, m) + (-1)^{m+1} binom(n - 1, m) - 1) binom(n, k)`
and `C̄_{ji} = binom(n, j) binom(m - n, m - j) binom(n - j, k - i)`. The paper takes
`n ∈ ℤ_p`; this states the integer case, with the congruence read as in
`ringChoose_mul_prime_sub_congr_sum_d`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 4
(`integers-2026-A32-lem-4`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_cbar (p m k : ℕ) (n : ℤ) (hp : p.Prime)
    (hmp : m + 1 < p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let C00 : ℚ :=
      (C ((m : ℤ) - k) m + C ((k : ℤ) + m - n) m + (-1) ^ (m + 1) * C (n - 1) m - 1) * C n k
    let Cbar : ℕ → ℕ → ℚ := fun j i =>
      C n j * C ((m : ℤ) - n) (m - j) * (if i ≤ k then C (n - j) (k - i) else 0)
    let X : ℚ := C (n * p) (k * p) - C n k -
      (C00 + ∑ j ∈ Finset.Icc 1 m, ∑ i ∈ Finset.Ico 1 j, Cbar j i * C ((j * p : ℕ) : ℤ) (i * p))
    X = 0 ∨ (C n (m + 1) ≠ 0 ∧
      ((m + 1 : ℕ) : ℤ) + padicValRat p (C n (m + 1)) ≤ padicValRat p X)

/-- Theorem 4: for a prime `p`, `m, k ∈ ℕ` with `m + 1 < p` and `n ∈ ℤ`,
`binom(np, kp) - binom(n, k) ≡ C'_{00}(m, n, k)
+ ∑_{2 ≤ j ≤ m, 1 ≤ i ≤ ⌊j/2⌋} C'_{ji}(m, n, k) binom(jp, ip) (mod p^{m+1+v_p(binom(n, m+1))})`,
where `C'_{00} = C̄_{00}` (Lemma 4) and
`C'_{ji} = ((n - k)_{j-i} (k)_i + (n - k)_i (k)_{j-i}) / j! · binom(m - n, m - j) binom(n, k)`,
halved when `j = 2i`; `(x)_i = x (x - 1) ⋯ (x - i + 1)` is the falling factorial. The
paper takes `n ∈ ℤ_p`; this states the integer case, with the congruence read as in
`ringChoose_mul_prime_sub_congr_sum_d`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 4
(`integers-2026-A32-thm-4`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_cprime (p m k : ℕ) (n : ℤ) (hp : p.Prime)
    (hmp : m + 1 < p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let ff : ℚ → ℕ → ℚ := fun x i => ∏ t ∈ Finset.range i, (x - t)
    let C00 : ℚ :=
      (C ((m : ℤ) - k) m + C ((k : ℤ) + m - n) m + (-1) ^ (m + 1) * C (n - 1) m - 1) * C n k
    let Cp : ℕ → ℕ → ℚ := fun j i =>
      (if j = 2 * i then (1 / 2 : ℚ) else 1) *
        ((ff ((n : ℚ) - k) (j - i) * ff k i + ff ((n : ℚ) - k) i * ff k (j - i)) / j.factorial *
          C ((m : ℤ) - n) (m - j) * C n k)
    let X : ℚ := C (n * p) (k * p) - C n k -
      (C00 + ∑ j ∈ Finset.Icc 2 m, ∑ i ∈ Finset.Icc 1 (j / 2), Cp j i * C ((j * p : ℕ) : ℤ) (i * p))
    X = 0 ∨ (C n (m + 1) ≠ 0 ∧
      ((m + 1 : ℕ) : ℤ) + padicValRat p (C n (m + 1)) ≤ padicValRat p X)

/-- Proposition 1: for `m ∈ ℕ` and `n ∈ ℤ`, the polynomial part
`binom(m - k, m) + binom(k + m - n, m) + (-1)^{m+1} binom(n - 1, m) - 1` of `C'_{00}(m, n, k)`
is divisible by `k (n - k) / 2` in `ℚ[k]`, and so is the polynomial part
`((n - k)_{j-i} (k)_i + (n - k)_i (k)_{j-i}) / j! · binom(m - n, m - j)` of `C'_{ji}(m, n, k)`
for `1 ≤ i < j` (the halving at `j = 2i` does not affect divisibility). Divisibility is
stated as agreement with `k (n - k) / 2 · Q(k)` at every `k ∈ ℕ`, which determines the
polynomial identity.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 1
(`integers-2026-A32-prop-1`). -/
public theorem_wanted exists_polynomial_part_eq_mul_half_mul (m : ℕ) (n : ℤ) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let ff : ℚ → ℕ → ℚ := fun x i => ∏ t ∈ Finset.range i, (x - t)
    (∃ Q : ℚ[X], ∀ k : ℕ,
        C ((m : ℤ) - k) m + C ((k : ℤ) + m - n) m + (-1) ^ (m + 1) * C (n - 1) m - 1 =
          (k : ℚ) * (n - k) / 2 * Q.eval (k : ℚ)) ∧
      ∀ j i : ℕ, 1 ≤ i → i < j → ∃ Q : ℚ[X], ∀ k : ℕ,
        (ff ((n : ℚ) - k) (j - i) * ff k i + ff ((n : ℚ) - k) i * ff k (j - i)) / j.factorial *
            C ((m : ℤ) - n) (m - j) =
          (k : ℚ) * (n - k) / 2 * Q.eval (k : ℚ)

/-! ### Explicit congruences modulo `p^3`, ..., `p^7` -/

/-- Proposition 2: for a prime `p ≥ 5`, `n ∈ ℤ` and `k ∈ ℕ`,
`binom(np, kp) - binom(n, k) ≡ (k (n - k) / 2) binom(n, k) (binom(2p, p) - 2)
(mod p^{3+v_p(binom(n, 3))})`. The paper takes `n ∈ ℤ_p`; integer case, congruence read
as in `ringChoose_mul_prime_sub_congr_sum_d`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 2
(`integers-2026-A32-prop-2`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_three (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let X : ℚ := C (n * p) (k * p) - C n k -
      (k : ℚ) * (n - k) / 2 * C n k * (((2 * p).choose p : ℚ) - 2)
    X = 0 ∨ (C n 3 ≠ 0 ∧ 3 + padicValRat p (C n 3) ≤ padicValRat p X)

/-- Corollary 2: for a prime `p ≥ 5` and `n, k ∈ ℕ`, the congruences
`binom(2p, p) ≡ 2`, `binom(np, p) ≡ n` and `binom(np, kp) ≡ binom(n, k)` modulo `p^3` are
equivalent. (By Wolstenholme's theorem all three hold for every such `p`.)

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Corollary 2
(`integers-2026-A32-cor-2`). -/
public theorem_wanted choose_two_mul_prime_congr_iff_pow_three (p n k : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    ((p : ℤ) ^ 3 ∣ ((2 * p).choose p : ℤ) - 2 ↔ (p : ℤ) ^ 3 ∣ ((n * p).choose p : ℤ) - n) ∧
      ((p : ℤ) ^ 3 ∣ ((n * p).choose p : ℤ) - n ↔
        (p : ℤ) ^ 3 ∣ ((n * p).choose (k * p) : ℤ) - n.choose k)

/-- Proposition 3: for a prime `p ≥ 7`, `n ∈ ℤ` and `k ∈ ℕ`,
`binom(np, kp) - binom(n, k) ≡ (k (n - k) / 2) binom(n, k)
((n - 4) + (3 - n) binom(2p, p) + ((n - 2) / 3) binom(3p, p)) (mod p^{4+v_p(binom(n, 4))})`.
The paper takes `n ∈ ℤ_p`; integer case, congruence read as in
`ringChoose_mul_prime_sub_congr_sum_d`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 3
(`integers-2026-A32-prop-3`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_four (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp7 : 7 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let N : ℚ := n
    let X : ℚ := C (n * p) (k * p) - C n k -
      (k : ℚ) * (N - k) / 2 * C n k *
        ((N - 4) + (3 - N) * ((2 * p).choose p : ℚ) + (N - 2) / 3 * ((3 * p).choose p : ℚ))
    X = 0 ∨ (C n 4 ≠ 0 ∧ 4 + padicValRat p (C n 4) ≤ padicValRat p X)

/-- Theorem 6: for a prime `p ≥ 7`, `n ∈ ℤ` and `k ∈ ℕ`,
`binom(np, kp) - binom(n, k) ≡ (n k (n - k) / 4) binom(n, k) (binom(2p, p) - 2)
(mod p^{4+v_p(binom(n, 4))})`. The paper takes `n ∈ ℤ_p`; integer case. The exponent uses
Lean's `padicValRat p 0 = 0`, so for `binom(n, 4) = 0` (`n ∈ {0, 1, 2, 3}`) this reads
modulo `p^4`: the exact-equality reading `v_p(0) = ∞` fails at `p = 7`, `n = 3`, `k = 1`,
where the difference is `100842 = 6 · 7^5`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 6
(`integers-2026-A32-thm-6`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_four_two_mul (p k : ℕ) (n : ℤ)
    (hp : p.Prime) (hp7 : 7 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let X : ℚ := C (n * p) (k * p) - C n k -
      (n : ℚ) * k * (n - k) / 4 * C n k * (((2 * p).choose p : ℚ) - 2)
    X = 0 ∨ 4 + padicValRat p (C n 4) ≤ padicValRat p X

/-- Proposition 4: for a prime `p ≥ 11`, `n ∈ ℤ` and `k ∈ ℕ`,
`binom(np, kp) - binom(n, k) ≡ (k (n - k) / 2) binom(n, k) (C_{00} + C_{21} binom(2p, p)
+ C_{31} binom(3p, p) + C_{41} binom(4p, p) + C_{42} binom(4p, 2p)) (mod p^{5+v_p(binom(n, 5))})`
with `C_{00} = -(k^2 - kn + 2n^2 - 15n + 35)/6`, `C_{21} = (n - 4)(n - 3)/2`,
`C_{31} = (n - 2)(4 - n)/3`, `C_{41} = (2k^2 - 2kn + n^2 - 3n + 4)/12`,
`C_{42} = (n - k - 1)(k - 1)/12`. The paper takes `n ∈ ℤ_p`; integer case, congruence read
as in `ringChoose_mul_prime_sub_congr_sum_d`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 4
(`integers-2026-A32-prop-4`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_five (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let b : ℕ → ℕ → ℚ := fun j i => ((j * p).choose (i * p) : ℚ)
    let N : ℚ := n
    let K : ℚ := k
    let X : ℚ := C (n * p) (k * p) - C n k -
      K * (N - K) / 2 * C n k *
        (-(K ^ 2 - K * N + 2 * N ^ 2 - 15 * N + 35) / 6 + (N - 4) * (N - 3) / 2 * b 2 1 +
          (N - 2) * (4 - N) / 3 * b 3 1 + (2 * K ^ 2 - 2 * K * N + N ^ 2 - 3 * N + 4) / 12 * b 4 1 +
          (N - K - 1) * (K - 1) / 12 * b 4 2)
    X = 0 ∨ (C n 5 ≠ 0 ∧ 5 + padicValRat p (C n 5) ≤ padicValRat p X)

/-- Proposition 5: for a prime `p ≥ 11`, `n ∈ ℤ` and `k ∈ ℕ`,
`binom(np, kp) - binom(n, k) ≡ (k (n - k) / 2) binom(n, k)
(C_{00} + ∑_{2 ≤ j ≤ 5, 1 ≤ i ≤ ⌊j/2⌋} C_{ji} binom(jp, ip)) (mod p^{6+v_p(binom(n, 6))})`
with the paper's displayed `C_{ji}(5, n, k)`. The paper takes `n ∈ ℤ_p`; integer case,
congruence read as in `ringChoose_mul_prime_sub_congr_sum_d`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 5
(`integers-2026-A32-prop-5`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_six (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let b : ℕ → ℕ → ℚ := fun j i => ((j * p).choose (i * p) : ℚ)
    let N : ℚ := n
    let K : ℚ := k
    let X : ℚ := C (n * p) (k * p) - C n k -
      K * (N - K) / 2 * C n k *
        ((N - 6) * (N ^ 2 - N * K - 6 * N + K ^ 2 + 15) / 12 +
          (5 - N) * (4 - N) * (3 - N) / 6 * b 2 1 + (N - 2) * (N - 5) * (N - 4) / 6 * b 3 1 +
          (2 * K ^ 2 - 2 * K * N + N ^ 2 - 3 * N + 4) * (5 - N) / 12 * b 4 1 +
          (K + 1 - N) * (K - 1) * (N - 5) / 12 * b 4 2 +
          (N - 4) * (3 * K ^ 2 - 3 * K * N + N ^ 2 - 2 * N + 3) / 60 * b 5 1 +
          (N - K - 1) * (K - 1) * (N - 4) / 60 * b 5 2)
    X = 0 ∨ (C n 6 ≠ 0 ∧ 6 + padicValRat p (C n 6) ≤ padicValRat p X)

/-- Proposition 6: for a prime `p ≥ 11`, `n ∈ ℤ` and `k ∈ ℕ`,
`binom(np, kp) - binom(n, k) ≡ (k (n - k) / 2) binom(n, k)
(C_{00} + ∑_{2 ≤ j ≤ 6, 1 ≤ i ≤ ⌊j/2⌋} C_{ji} binom(jp, ip)) (mod p^{7+v_p(binom(n, 7))})`.
Two printed coefficients are corrected to the values that Definition 1 and Theorem 4 of
the paper give: `C_{00}(6, n, k)` has prefactor `-1/360` (printed `-1/720`), and
`C_{63}(6, n, k) = (n - k - 1)(n - k - 2)(k - 1)(k - 2)/360` (printed with
`(k - n - 1)(k - n - 2)`). As printed the congruence fails already modulo `p`
(`p = 11`, `n = 7`, `k = 1`: the difference is a `p`-adic unit). The other eight
coefficients are as printed. The paper takes `n ∈ ℤ_p`; integer case, congruence read
as in `ringChoose_mul_prime_sub_congr_sum_d`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 6
(`integers-2026-A32-prop-6`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_seven (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let b : ℕ → ℕ → ℚ := fun j i => ((j * p).choose (i * p) : ℚ)
    let N : ℚ := n
    let K : ℚ := k
    let X : ℚ := C (n * p) (k * p) - C n k -
      K * (N - K) / 2 * C n k *
        (-(2 * K ^ 4 - 4 * K ^ 3 * N + 11 * K ^ 2 * N ^ 2 - 9 * K * N ^ 3 + 6 * N ^ 4 -
              105 * K ^ 2 * N + 105 * K * N ^ 2 - 105 * N ^ 3 + 350 * K ^ 2 - 350 * N * K +
              700 * N ^ 2 - 2205 * N + 3248) / 360 +
          (6 - N) * (5 - N) * (4 - N) * (3 - N) / 24 * b 2 1 +
          (N - 2) * (6 - N) * (5 - N) * (4 - N) / 18 * b 3 1 +
          (6 - N) * (5 - N) * (2 * K ^ 2 - 2 * K * N + N ^ 2 - 3 * N + 4) / 24 * b 4 1 +
          (N - K - 1) * (K - 1) * (6 - N) * (5 - N) / 24 * b 4 2 +
          (4 - N) * (N - 6) * (3 * K ^ 2 - 3 * K * N + N ^ 2 - 2 * N + 3) / 60 * b 5 1 +
          (-N + K + 1) * (K - 1) * (N - 4) * (N - 6) / 60 * b 5 2 +
          (2 * K ^ 4 - 4 * K ^ 3 * N + 6 * K ^ 2 * N ^ 2 - 4 * K * N ^ 3 + N ^ 4 -
              30 * K ^ 2 * N + 30 * K * N ^ 2 - 10 * N ^ 3 + 70 * K ^ 2 - 70 * K * N +
              35 * N ^ 2 - 50 * N + 48) / 360 * b 6 1 +
          (N - K - 1) * (K - 1) * (2 * K ^ 2 - 2 * K * N + N ^ 2 - 5 * N + 12) / 360 * b 6 2 +
          (N - K - 1) * (N - K - 2) * (K - 1) * (K - 2) / 360 * b 6 3)
    X = 0 ∨ (C n 7 ≠ 0 ∧ 7 + padicValRat p (C n 7) ≤ padicValRat p X)

/-- Lemma 6: for a prime `p` and `1 ≤ m ≤ n`,
`binom(np, mp) = binom(n, m) ∏_{j<m} binom((n - m + j + 1)p - 1, p - 1) / ∏_{j<m} binom((j + 1)p - 1, p - 1)
= ∏_{j<m} binom((n - m + j + 1)p, p) / ∏_{j<m} binom((j + 1)p, p)`.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 6
(`integers-2026-A32-lem-6`). -/
public theorem_wanted choose_mul_prime_eq_prod_div_prod (p m n : ℕ) (hp : p.Prime) (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    ((n * p).choose (m * p) : ℚ) =
        (n.choose m : ℚ) * (∏ j ∈ Finset.range m, (((n - m + j + 1) * p - 1).choose (p - 1) : ℚ)) /
          ∏ j ∈ Finset.range m, (((j + 1) * p - 1).choose (p - 1) : ℚ) ∧
      ((n * p).choose (m * p) : ℚ) =
        (∏ j ∈ Finset.range m, (((n - m + j + 1) * p).choose p : ℚ)) /
          ∏ j ∈ Finset.range m, (((j + 1) * p).choose p : ℚ)

end

end MetaMathlibExt
