/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting

/-! # Explicit prime bounds from the refinements of Mandl's inequality

Statement-only requests for the explicit lemmas, propositions, corollaries and Theorem 1 of
Zhang and Xiong. The source's one-indexed `pₙ` is `Nat.nth Nat.Prime (n - 1)` and `π(x)` is
`Nat.primeCounting ⌊x⌋₊`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The Rosser–Schoenfeld lower bound $x / \log x$ for the prime-counting function.** For every
real number $x \ge 17$, the number $\pi(x)$ of primes at most $x$ satisfies
$x / \log x < \pi(x)$.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 2 (`integers-2025-A58-lem-2`). -/
public theorem_wanted primeCounting_gt_div_log_of_seventeen_le (x : ℝ) (hx : 17 ≤ x) :
    x / Real.log x < (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- **For $n \ge 7$, the $n$th prime is less than $n$ times its logarithm.** For every integer
$n \ge 7$, the $n$th prime $p_n$ (counting from $p_1 = 2$) satisfies $p_n < n \log p_n$.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 2, inequality (2) (`integers-2025-A58-lem-2`). -/
public theorem_wanted nthPrime_lt_mul_log_nthPrime (n : ℕ) (hn : 7 ≤ n) :
    (Nat.nth Nat.Prime (n - 1) : ℝ) < n * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ)

/-- **Dusart's upper bound $x / (\log x - 1.1)$ for the prime-counting function.** For every
real number $x \ge 60184$, the number $\pi(x)$ of primes at most $x$ satisfies
$\pi(x) < x / (\log x - 1.1)$.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 3 (`integers-2025-A58-lem-3`). -/
public theorem_wanted primeCounting_lt_div_log_sub_eleven_tenths (x : ℝ) (hx : 60184 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) < x / (Real.log x - 1.1)

/-- **An upper bound for the $n$-th prime in terms of its logarithm.** Let $p_n$ denote the
$n$-th prime, so that $p_1 = 2$. For every integer $n \ge 711$, $p_n < n(\log p_n - 1)$.

Here $711 = \pi(5393)$, where $\pi(x)$ denotes the number of primes at most $x$. The paper's
companion inequality (3) is not included: it fails at $n = 6076$, where $p_{6076} = 60169$ and
$6076(\log 60169 - 1.1) \approx 60182.2$.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 3, inequality (4) (`integers-2025-A58-lem-3`). -/
public theorem_wanted nthPrime_lt_mul_log_nthPrime_sub_one (n : ℕ) (hn : 711 ≤ n) :
    (Nat.nth Nat.Prime (n - 1) : ℝ) < n * (Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) - 1)

/-- **Lower bound $x / (\log x - 1 - 1 / \log x)$ for the prime-counting function.** For every
real number $x \ge 468049$, the number $\pi(x)$ of primes at most $x$ satisfies
$\pi(x) > x / (\log x - 1 - 1 / \log x)$.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 4 (`integers-2025-A58-lem-4`). -/
public theorem_wanted primeCounting_gt_div_log_sub_one_sub_inv_log (x : ℝ) (hx : 468049 ≤ x) :
    x / (Real.log x - 1 - 1 / Real.log x) < (Nat.primeCounting ⌊x⌋₊ : ℝ)

/-- **A second-order upper bound for the $n$-th prime in terms of its logarithm.** Let $p_n$
denote the $n$-th prime, so that $p_1 = 2$. For every integer $n \ge 39071$,
$$p_n < n\left(\log p_n - 1 - \frac{1}{\log p_n}\right).$$

Here $39071 = \pi(468049)$, where $\pi(x)$ denotes the number of primes at most $x$.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 4, inequality (5) (`integers-2025-A58-lem-4`). -/
public theorem_wanted nthPrime_lt_mul_log_nthPrime_sub_one_sub_inv_log (n : ℕ) (hn : 39071 ≤ n) :
    (Nat.nth Nat.Prime (n - 1) : ℝ) <
      n * (Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) - 1 -
        1 / Real.log (Nat.nth Nat.Prime (n - 1) : ℝ))

/-- **Lower bound for $\log n$ in terms of the logarithm of the $n$-th prime.** Let $p_n$ denote
the $n$-th prime, so that $p_1 = 2$. For every integer $n \ge 234057667276344608$,
$\log n \ge 0.914 \log p_n$.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 6, inequality (15) (`integers-2025-A58-lem-6`). -/
public theorem_wanted mul_log_nthPrime_le_log (n : ℕ) (hn : 234057667276344608 ≤ n) :
    0.914 * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) ≤ Real.log n

/-- **An explicit inequality between $n$ and the $n$th prime.** For every integer $n \ge 1$, the
$n$th prime $p_n$ (counting from $p_1 = 2$) satisfies
$$118.676119576 \, n^2 (\log p_n)^3 + 709.7856 \, n \, p_n (\log p_n)^2
< 937.5 \, p_n^2 \log p_n + 5674.5 \, p_n^2.$$

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Proposition 1 (`integers-2025-A58-prop-1`). -/
public theorem_wanted nthPrime_sq_log_bound (n : ℕ) (hn : 1 ≤ n) :
    118.676119576 * (n : ℝ) ^ 2 * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 3 +
        709.7856 * n * (Nat.nth Nat.Prime (n - 1) : ℝ) *
          Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 2 <
      937.5 * (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 2 * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) +
        5674.5 * (Nat.nth Nat.Prime (n - 1) : ℝ) ^ 2

/-- **An auxiliary inequality in $\log n$ and $\log\log n$.** For every integer $n \ge 2$, with
$L = \log n$,
$$\frac{4.151332(\log L - 2)}{L} + \frac{3.151332(\log L - 1)}{L} +
\frac{3.151332(\log L - 2)}{L^2} \le 1.$$

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Proposition 3, inequality (25) (`integers-2025-A58-prop-3`). -/
public theorem_wanted loglog_ratio_sum_le_one (n : ℕ) (hn : 2 ≤ n) :
    4.151332 * (Real.log (Real.log n) - 2) / Real.log n +
        3.151332 * (Real.log (Real.log n) - 1) / Real.log n +
        3.151332 * (Real.log (Real.log n) - 2) / Real.log n ^ 2 ≤ 1

/-- **Lower bounds for the $n$-th prime in terms of its logarithm.** Let $p_n$ denote the $n$-th
prime, so that $p_1 = 2$, and put $L = \log p_n$. Then
$p_n > n\left(L - 1 - \frac{1.109}{L}\right)$ for every integer $n \ge 2621506158680$,
$p_n > n\left(L - 1 - \frac{1}{L} - \frac{3.48}{L^2}\right)$ for every integer
$n \ge 4605081012945$,
$p_n > n\left(L - 1 - \frac{1}{L} - \frac{3.024334}{L^2} - \frac{14.893}{L^3}\right)$ for every
integer $n \ge 4514634967572$, and
$p_n > n\left(L - 1 - \frac{1}{L} - \frac{3.024334}{L^2} - \frac{12.975666}{L^3} -
\frac{79.962}{L^4}\right)$ for every integer $n \ge 8$.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Corollary 1 (`integers-2025-A58-cor-1`). -/
public theorem_wanted nthPrime_gt_mul_log_sub_corollary_one :
    (∀ n : ℕ, 2621506158680 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      n * (Real.log p - 1 - 1.109 / Real.log p) < p) ∧
    (∀ n : ℕ, 4605081012945 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      n * (Real.log p - 1 - 1 / Real.log p - 3.48 / Real.log p ^ 2) < p) ∧
    (∀ n : ℕ, 4514634967572 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      n * (Real.log p - 1 - 1 / Real.log p - 3.024334 / Real.log p ^ 2 -
        14.893 / Real.log p ^ 3) < p) ∧
    (∀ n : ℕ, 8 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      n * (Real.log p - 1 - 1 / Real.log p - 3.024334 / Real.log p ^ 2 -
        12.975666 / Real.log p ^ 3 - 79.962 / Real.log p ^ 4) < p)

/-- **Zhang–Xiong upper bounds for the $n$th prime.** Let $p_n$ be the $n$th prime (counting from
$p_1 = 2$) and $L = \log p_n$. Set $c_2 = 2.975666$, $c_3 = 13.024334$, $c_4 = 70.951332$,
$c_5 = 460.634397856444$ and $c_6 = 3444.031844143556$, and set $N_2 = 3278841$,
$N_3 = 355193892$, $N_4 = 6226419706$, $N_5 = 38900733192$ and $N_6 = 64497259289$.
Then for each $k \in \{2, 3, 4, 5, 6\}$ and every integer $n \ge N_k$,
$$
p_n < n \left(L - 1 - \frac{1}{L} - \sum_{j=2}^{k} \frac{c_j}{L^j}\right).
$$

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Corollary 2 (`integers-2025-A58-cor-2`). -/
public theorem_wanted nthPrime_lt_mul_log_sub_corollary_two :
    (∀ n : ℕ, 3278841 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      p < n * (Real.log p - 1 - 1 / Real.log p - 2.975666 / Real.log p ^ 2)) ∧
    (∀ n : ℕ, 355193892 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      p < n * (Real.log p - 1 - 1 / Real.log p - 2.975666 / Real.log p ^ 2 -
        13.024334 / Real.log p ^ 3)) ∧
    (∀ n : ℕ, 6226419706 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      p < n * (Real.log p - 1 - 1 / Real.log p - 2.975666 / Real.log p ^ 2 -
        13.024334 / Real.log p ^ 3 - 70.951332 / Real.log p ^ 4)) ∧
    (∀ n : ℕ, 38900733192 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      p < n * (Real.log p - 1 - 1 / Real.log p - 2.975666 / Real.log p ^ 2 -
        13.024334 / Real.log p ^ 3 - 70.951332 / Real.log p ^ 4 -
        460.634397856444 / Real.log p ^ 5)) ∧
    (∀ n : ℕ, 64497259289 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      p < n * (Real.log p - 1 - 1 / Real.log p - 2.975666 / Real.log p ^ 2 -
        13.024334 / Real.log p ^ 3 - 70.951332 / Real.log p ^ 4 -
        460.634397856444 / Real.log p ^ 5 - 3444.031844143556 / Real.log p ^ 6))

/-- **Lower bound for the logarithm of the $n$-th prime.** Let $p_n$ denote the $n$-th prime, so
that $p_1 = 2$. For every integer $n \ge 3$,
$$\log p_n \ge \log n + \log\log n + \log\left(1 + \frac{\log\log n - 1}{\log n}\right).$$

The paper states this for all positive integers $n$; the right side is undefined at $n = 1$
(where $\log\log 1$ appears) and at $n = 2$ (where the last logarithm's argument is about
$-0.9715$), so $n \ge 3$ is assumed.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 8, inequality (17) (`integers-2025-A58-lem-8`). -/
public theorem_wanted log_nthPrime_ge_log_add_loglog (n : ℕ) (hn : 3 ≤ n) :
    Real.log n + Real.log (Real.log n) +
        Real.log (1 + (Real.log (Real.log n) - 1) / Real.log n) ≤
      Real.log (Nat.nth Nat.Prime (n - 1) : ℝ)

/-- **Bounds for $n$ times the $n$-th prime minus the sum of the first $n$ primes.** Let $p_k$
denote the $k$-th prime, so that $p_1 = 2$, and for $n \ge 1$ put $L = \log p_n$ and
$S(n) = n p_n - \sum_{k=1}^{n} p_k$. For every integer $n \ge 440200309$,
$$S(n) \ge p_n^2\left(\frac{1}{2L} + \frac{3}{4L^2} + \frac{7}{4L^3} + \frac{44.4}{8L^4} +
\frac{92.1}{4L^5} + \frac{937.5}{8L^6} + \frac{5674.5}{8L^7} + \frac{79789.5}{16L^8}\right),$$
and for every integer $n \ge 1$,
$$S(n) \le p_n^2\left(\frac{1}{2L} + \frac{3}{4L^2} + \frac{7}{4L^3} + \frac{45.6}{8L^4} +
\frac{93.9}{4L^5} + \frac{952.5}{8L^6} + \frac{5755.5}{8L^7} + \frac{116371}{16L^8}\right).$$

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Lemma 9 (`integers-2025-A58-lem-9`). -/
public theorem_wanted mul_nthPrime_sub_sum_primes_bounds :
    (∀ n : ℕ, 440200309 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      let L : ℝ := Real.log p
      p ^ 2 / (2 * L) + 3 * p ^ 2 / (4 * L ^ 2) + 7 * p ^ 2 / (4 * L ^ 3) +
          44.4 * p ^ 2 / (8 * L ^ 4) + 92.1 * p ^ 2 / (4 * L ^ 5) + 937.5 * p ^ 2 / (8 * L ^ 6) +
          5674.5 * p ^ 2 / (8 * L ^ 7) + 79789.5 * p ^ 2 / (16 * L ^ 8) ≤
        n * p - ∑ k ∈ Finset.range n, (Nat.nth Nat.Prime k : ℝ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      let p : ℝ := Nat.nth Nat.Prime (n - 1)
      let L : ℝ := Real.log p
      n * p - ∑ k ∈ Finset.range n, (Nat.nth Nat.Prime k : ℝ) ≤
        p ^ 2 / (2 * L) + 3 * p ^ 2 / (4 * L ^ 2) + 7 * p ^ 2 / (4 * L ^ 3) +
          45.6 * p ^ 2 / (8 * L ^ 4) + 93.9 * p ^ 2 / (4 * L ^ 5) + 952.5 * p ^ 2 / (8 * L ^ 6) +
          5755.5 * p ^ 2 / (8 * L ^ 7) + 116371 * p ^ 2 / (16 * L ^ 8))

/-- **Explicit lower bound in Mandl's inequality.** Let $p_k$ denote the $k$-th prime, so that
$p_1 = 2$. For every integer $n \ge 4605081012945$, put $\ell = \log n$, $L = \log p_n$,
$M(n) = \frac{n p_n}{2} - \sum_{k=1}^{n} p_k$ and
$$\omega(n) = \frac{3.151332\,\ell^2}{4L^2} + \frac{\ell^2}{4L} + \frac{16.7\,\ell^2}{4L^3} -
\frac{\ell}{4} + \frac{\log \ell}{4}.$$
Then
$$M(n) > \frac{n^2}{4} + \frac{n^2}{4\ell} - \frac{n^2 \log \ell}{4\ell^2} +
\frac{\omega(n)\, n^2}{\ell^2}.$$

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Proposition 2 (`integers-2025-A58-prop-2`). -/
public theorem_wanted mandl_sum_gt_omega_bound (n : ℕ) (hn : 4605081012945 ≤ n) :
    let p : ℝ := Nat.nth Nat.Prime (n - 1)
    let l : ℝ := Real.log n
    let L : ℝ := Real.log p
    let ω : ℝ := 3.151332 * l ^ 2 / (4 * L ^ 2) + l ^ 2 / (4 * L) + 16.7 * l ^ 2 / (4 * L ^ 3) -
      l / 4 + Real.log l / 4
    (n : ℝ) ^ 2 / 4 + (n : ℝ) ^ 2 / (4 * l) - (n : ℝ) ^ 2 * Real.log l / (4 * l ^ 2) +
        ω * (n : ℝ) ^ 2 / l ^ 2 <
      n * p / 2 - ∑ k ∈ Finset.range n, (Nat.nth Nat.Prime k : ℝ)

/-- **Explicit upper bound in Mandl's inequality.** Let $p_k$ denote the $k$-th prime, so that
$p_1 = 2$. For every integer $n \ge 64497259289$, put $\ell = \log n$, $L = \log p_n$,
$M(n) = \frac{n p_n}{2} - \sum_{k=1}^{n} p_k$,
$$\tau = 34.6L^3 + 205.592008L^2 + 1420.426661948448L + 28890.293784512888$$
and
$$\Omega(n) = \frac{\ell^2}{4L} + \frac{3.848668\,\ell^2}{4L^2} - \frac{\ell}{4} +
\frac{\log \ell}{4} + \frac{\tau\,\ell^2}{8L^6}.$$
Then
$$M(n) < \frac{n^2}{4} + \frac{n^2}{4\ell} - \frac{n^2 \log \ell}{4\ell^2} +
\frac{\Omega(n)\, n^2}{\ell^2}.$$

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Proposition 4 (`integers-2025-A58-prop-4`). -/
public theorem_wanted mandl_sum_lt_Omega_bound (n : ℕ) (hn : 64497259289 ≤ n) :
    let p : ℝ := Nat.nth Nat.Prime (n - 1)
    let l : ℝ := Real.log n
    let L : ℝ := Real.log p
    let τ : ℝ := 34.6 * L ^ 3 + 205.592008 * L ^ 2 + 1420.426661948448 * L +
      28890.293784512888
    let Ω : ℝ := l ^ 2 / (4 * L) + 3.848668 * l ^ 2 / (4 * L ^ 2) - l / 4 + Real.log l / 4 +
      τ * l ^ 2 / (8 * L ^ 6)
    n * p / 2 - ∑ k ∈ Finset.range n, (Nat.nth Nat.Prime k : ℝ) <
      (n : ℝ) ^ 2 / 4 + (n : ℝ) ^ 2 / (4 * l) - (n : ℝ) ^ 2 * Real.log l / (4 * l ^ 2) +
        Ω * (n : ℝ) ^ 2 / l ^ 2

/-- **Zhang–Xiong refinement of Mandl's inequality.** Let $p_k$ denote the $k$-th prime, so that
$p_1 = 2$, and let $M(n) = \frac{n p_n}{2} - \sum_{k=1}^{n} p_k$. For real $\eta$ let
$$B_\eta(n) = \frac{n^2}{4}\left(1 + \frac{1}{\log n} -
\frac{\log\log n - \eta}{(\log n)^2}\right).$$
With $\alpha = 3.151332$ and $\beta = 4.168668$, we have $B_\alpha(n) < M(n)$ for every integer
$n \ge 234057667276344608$, and $M(n) < B_\beta(n)$ for every integer $n \ge 64497259289$.

Source: Qianxi Zhang and Xinhua Xiong, *New Refinements of Mandl's Inequality*,
INTEGERS 25 (2025), Article A58, Theorem 1 (`integers-2025-A58-thm-1`). -/
public theorem_wanted mandl_sum_between_B_alpha_B_beta :
    let M : ℕ → ℝ := fun n =>
      n * (Nat.nth Nat.Prime (n - 1) : ℝ) / 2 - ∑ k ∈ Finset.range n, (Nat.nth Nat.Prime k : ℝ)
    let B : ℝ → ℕ → ℝ := fun η n =>
      (n : ℝ) ^ 2 / 4 *
        (1 + 1 / Real.log n - (Real.log (Real.log n) - η) / Real.log n ^ 2)
    (∀ n : ℕ, 234057667276344608 ≤ n → B 3.151332 n < M n) ∧
    (∀ n : ℕ, 64497259289 ≤ n → M n < B 4.168668 n)

end

end MetaMathlibExt
