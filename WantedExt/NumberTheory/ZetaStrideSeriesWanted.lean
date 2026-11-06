/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MetaMathlibExt

open Filter Topology

@[expose] public section

/-- **Alternating stride sum.** For natural numbers $q$, $t$ and $n$, let
$K = \lfloor (n + q - 1)/q \rfloor$ if $q \ge 1$ and $K = 0$ if $q = 0$. The alternating stride
sum is the real number
$$
S_{q,t}(n) = \sum_{i=0}^{K-1} \frac{(-1)^i}{(n - qi)^t}.
$$
For $q \ge 1$ this is the alternating sum of $m^{-t}$ over $m = n, n - q, n - 2q, \dots$ with
$m \ge 1$; with $j = i + 1$ it reads $\sum_{j=1}^{K} (-1)^{j+1}/(n + q - qj)^t$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 1,
equation (9). -/
public noncomputable def strideAlternatingSum (q t n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ((n + q - 1) / q), (-1 : ℝ) ^ i / ((n - q * i : ℕ) : ℝ) ^ t

/-- **Signed stride sum.** For natural numbers $q$, $t$ and $n$, let
$K = \lfloor (n + q - 1)/q \rfloor$ if $q \ge 1$ and $K = 0$ if $q = 0$. The signed stride sum is
the real number
$$
T_{q,t}(n) = \sum_{i=0}^{K-1} \frac{(-1)^{(q+1)i}}{(n - qi)^t}.
$$
With $j = i + 1$ it reads $\sum_{j=1}^{K} (-1)^{(q+1)(j+1)}/(n + q - qj)^t$. For odd $q$ every
sign is $+$, and for even $q$ the signs alternate.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 2,
equation (25). -/
public noncomputable def strideSignedSum (q t n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range ((n + q - 1) / q), (-1 : ℝ) ^ ((q + 1) * i) / ((n - q * i : ℕ) : ℝ) ^ t

private theorem div_eq_one_of_le {q n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    (n + q - 1) / q = 1 :=
  Nat.div_eq_of_lt_le (by omega) (by omega)

private theorem div_add_eq {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    (n + q + q - 1) / q = (n + q - 1) / q + 1 := by
  rw [show n + q + q - 1 = n + q - 1 + q by omega, Nat.add_div_right _ hq]

/-- **Alternating stride sum with a single term.** For natural numbers $q$, $t$ and $n$ with
$1 \le n \le q$, the alternating stride sum satisfies $S_{q,t}(n) = 1/n^t$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (9). -/
public theorem strideAlternatingSum_of_le {q t n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    strideAlternatingSum q t n = 1 / (n : ℝ) ^ t := by
  simp [strideAlternatingSum, div_eq_one_of_le hn hnq]

/-- **Signed stride sum with a single term.** For natural numbers $q$, $t$ and $n$ with
$1 \le n \le q$, the signed stride sum satisfies $T_{q,t}(n) = 1/n^t$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (25). -/
public theorem strideSignedSum_of_le {q t n : ℕ} (hn : 0 < n) (hnq : n ≤ q) :
    strideSignedSum q t n = 1 / (n : ℝ) ^ t := by
  simp [strideSignedSum, div_eq_one_of_le hn hnq]

/-- **Recurrence for the alternating stride sum.** Let $q \ge 1$, $n \ge 1$ and $t \ge 0$ be
integers and let $S_{q,t}$ denote the alternating stride sum. Then
$S_{q,t}(n + q) = 1/(n + q)^t - S_{q,t}(n)$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (9). -/
public theorem strideAlternatingSum_add {q t n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    strideAlternatingSum q t (n + q) = 1 / ((n + q : ℕ) : ℝ) ^ t - strideAlternatingSum q t n := by
  rw [strideAlternatingSum, div_add_eq hq hn, Finset.sum_range_succ', strideAlternatingSum,
    sub_eq_neg_add, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show n + q - q * (i + 1) = n - q * i by rw [Nat.mul_succ]; omega, pow_succ]
    ring

/-- **Recurrence for the signed stride sum.** Let $q \ge 1$, $n \ge 1$ and $t \ge 0$ be integers
and let $T_{q,t}$ denote the signed stride sum. Then
$T_{q,t}(n + q) = 1/(n + q)^t + (-1)^{q+1} T_{q,t}(n)$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, equation (25). -/
public theorem strideSignedSum_add {q t n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    strideSignedSum q t (n + q) =
      1 / ((n + q : ℕ) : ℝ) ^ t + (-1 : ℝ) ^ (q + 1) * strideSignedSum q t n := by
  rw [strideSignedSum, div_add_eq hq hn, Finset.sum_range_succ', strideSignedSum,
    Finset.mul_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show n + q - q * (i + 1) = n - q * i by rw [Nat.mul_succ]; omega, mul_add, mul_one,
      pow_add]
    ring

/-- **Alternating stride sum series for $\zeta(t + 1)$.** Let $q \ge 1$ and $t \ge 1$ be integers
and let $S_{q,t}$ denote the alternating stride sum. Then the partial sums
$$
\sum_{n=1}^{N} \frac{2n + q}{n(n + q)} \, S_{q,t}(n)
$$
converge to $\zeta(t + 1)$ as $N \to \infty$, where $\zeta$ is the Riemann zeta function.

The series converges only conditionally, since $S_{q,t}(n)$ does not tend to $0$, which is why
it is stated through its partial sums. The second expression in equation (9) and the general
identity (8) use a quantity $A^{(t)}$ that the record does not define and are not stated here.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 1,
equation (9). -/
public theorem_wanted tendsto_strideAlternatingSum_riemannZeta (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) *
          strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 (riemannZeta ((t : ℂ) + 1)))

/-- **Digamma series for the signed stride sum.** Let $q \ge 1$ and $t \ge 1$ be integers, let
$a$ be a real number with $-1 \le a < 1$, let $T_{q,t}$ denote the signed stride sum and $\psi$
the digamma function. As $N \to \infty$, the partial sums
$$
\sum_{n=1}^{N} (-1)^{n+1} \frac{2n + q}{(n + a + 1)(n - a - 1 + q)} \, T_{q,t}(n)
$$
converge to
$$
\frac{1}{2q} \sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n^t}
\left[\psi\left(\frac{n+a+1+q}{2q}\right) - \psi\left(\frac{n+a+1}{2q}\right)\right] +
\frac{1}{2q} \sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n^t}
\left[\psi\left(\frac{n-a-1+2q}{2q}\right) - \psi\left(\frac{n-a-1+q}{2q}\right)\right].
$$

The first series converges only conditionally, while the two digamma series converge
absolutely.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 2,
equation (24). -/
public theorem_wanted tendsto_strideSignedSum_digamma (q t : ℕ) (hq : 0 < q) (ht : 0 < t)
    (a : ℝ) (ha : -1 ≤ a) (ha' : a < 1) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + q) /
          (((n : ℝ) + 1 + a + 1) * ((n : ℝ) + 1 - a - 1 + q)) *
            strideSignedSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 ((∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ t *
          (Complex.digamma (((n : ℂ) + 1 + a + 1 + q) / (2 * q)) -
            Complex.digamma (((n : ℂ) + 1 + a + 1) / (2 * q)))) / (2 * q) +
        (∑' n : ℕ, (-1 : ℂ) ^ n / ((n : ℂ) + 1) ^ t *
          (Complex.digamma (((n : ℂ) + 1 - a - 1 + 2 * q) / (2 * q)) -
            Complex.digamma (((n : ℂ) + 1 - a - 1 + q) / (2 * q)))) / (2 * q)))

/-- **Stride series for the Dirichlet eta function.** Let $q, t \ge 1$ be integers and let
$T_{q,t}(n)$ denote the signed stride sum. Then the partial sums
$$\sum_{n=1}^{N} (-1)^{n+1} \frac{2n+q}{n(n+q)} T_{q,t}(n)$$
converge, as $N \to \infty$, to $\eta(t+1)$, where $\eta(s) = \sum_{n \ge 1} (-1)^{n+1} n^{-s}$ is
the Dirichlet eta function.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 2,
equation (25). -/
public theorem_wanted tendsto_strideSignedSum_dirichletEta (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) *
          strideSignedSum q t (n + 1))
      atTop (𝓝 (∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ (t + 1)))

/-- **Digamma identity for stride sums over odd indices.** Let $q, t \ge 1$ be integers, let
$a$ be a real number with $-1 \le a < 1$, let $S_{q,t}(n)$ denote the alternating stride sum and
$T_{q,t}(n)$ the signed stride sum, and let $\psi$ be the digamma function. Then the partial sums
$$\sum_{n=1}^{N} \frac{2n+q}{2(n+a+1)(n-a-1+q)} \bigl(S_{q,t}(n) + (-1)^{n+1} T_{q,t}(n)\bigr)$$
converge, as $N \to \infty$, to
$$\frac{1}{2q} \sum_{n \ge 1} \frac{1}{(2n-1)^t}
\Bigl[\psi\Bigl(\frac{2n+a+q}{2q}\Bigr) - \psi\Bigl(\frac{2n+a}{2q}\Bigr)\Bigr] +
\frac{1}{2q} \sum_{n \ge 1} \frac{1}{(2n-1)^t}
\Bigl[\psi\Bigl(\frac{2n-a-2+2q}{2q}\Bigr) - \psi\Bigl(\frac{2n-a-2+q}{2q}\Bigr)\Bigr].$$

Deviation: the paper prints the factor $2$ where this statement has $1/2$; as printed the
series sums to four times this limit (for $q = t = 1$ and $a = -1$: $4\lambda(2) \approx 4.935$
against $\lambda(2) = \pi^2/8 \approx 1.234$, where $\lambda(s) = \sum_{n \ge 0} (2n+1)^{-s}$
is the Dirichlet lambda function). With $1/2$ the identity checks numerically for several
$(a, q, t)$, and at $a = -1$ it is the stride series for $\lambda(t+1)$, half the sum of the
paper's series (9) for $\zeta(t+1)$ and (25) for $\eta(t+1)$.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 3,
equation (27) (`integers-2024-A45-thm-3`). -/
public theorem_wanted tendsto_strideSums_digamma_odd (q t : ℕ) (hq : 0 < q) (ht : 0 < t)
    (a : ℝ) (ha : -1 ≤ a) (ha' : a < 1) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) /
          (2 * (((n : ℝ) + 1 + a + 1) * ((n : ℝ) + 1 - a - 1 + q))) *
            (strideAlternatingSum q t (n + 1) + (-1 : ℝ) ^ n * strideSignedSum q t (n + 1)) :
          ℝ) : ℂ))
      atTop (𝓝 ((∑' n : ℕ, 1 / (2 * ((n : ℂ) + 1) - 1) ^ t *
          (Complex.digamma ((2 * ((n : ℂ) + 1) + a + q) / (2 * q)) -
            Complex.digamma ((2 * ((n : ℂ) + 1) + a) / (2 * q)))) / (2 * q) +
        (∑' n : ℕ, 1 / (2 * ((n : ℂ) + 1) - 1) ^ t *
          (Complex.digamma ((2 * ((n : ℂ) + 1) - a - 2 + 2 * q) / (2 * q)) -
            Complex.digamma ((2 * ((n : ℂ) + 1) - a - 2 + q) / (2 * q)))) / (2 * q)))

/-- **Stride series for the Dirichlet lambda function.** Let $q, t \ge 1$ be integers, and let
$S_{q,t}(n)$ denote the alternating stride sum and $T_{q,t}(n)$ the signed stride sum. Then the
partial sums
$$\sum_{n=1}^{N} \frac{2n+q}{2n(n+q)} \bigl(S_{q,t}(n) + (-1)^{n+1} T_{q,t}(n)\bigr)$$
converge, as $N \to \infty$, to $\lambda(t+1)$, where $\lambda(s) = \sum_{n \ge 0} (2n+1)^{-s}$ is
the Dirichlet lambda function. The series is half the sum of the paper's series (9) for
$\zeta(t+1)$ and (25) for $\eta(t+1)$.

Deviation: the paper prints the factor $2$ where this statement has $1/2$; as printed the
series sums to $4\lambda(t+1)$ (for $q = t = 1$: about $4.935$ against
$\lambda(2) = \pi^2/8 \approx 1.234$).

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 3,
equation (28) (`integers-2024-A45-thm-3`). -/
public theorem_wanted tendsto_strideSums_dirichletLambda (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) / (2 * (((n : ℝ) + 1) * ((n : ℝ) + 1 + q))) *
          (strideAlternatingSum q t (n + 1) + (-1 : ℝ) ^ n * strideSignedSum q t (n + 1)))
      atTop (𝓝 (∑' n : ℕ, 1 / (2 * (n : ℝ) + 1) ^ (t + 1)))

/-- **Alternating stride sum series for $\zeta(p + t + 1)$.** Let $q \ge 1$ and $t \ge 1$ be
integers, let $p \ge 0$ be an even integer and let $S_{q,t}$ denote the alternating stride sum.
Then the partial sums
$$
\sum_{n=1}^{N} \frac{n^{p+1} + (n + q)^{p+1}}{(n(n + q))^{p+1}} \, S_{q,t}(n)
$$
converge to $\zeta(p + t + 1)$ as $N \to \infty$, where $\zeta$ is the Riemann zeta function.

Only the first equality of equation (32) is stated; its second expression uses a quantity
$A^{(t)}$ that the record does not define.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 4,
equation (32). -/
public theorem_wanted tendsto_strideAlternatingSum_riemannZeta_add (q t p : ℕ) (hq : 0 < q)
    (ht : 0 < t) (hp : Even p) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (((n : ℝ) + 1) ^ (p + 1) + ((n : ℝ) + 1 + q) ^ (p + 1)) /
          (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) ^ (p + 1) *
            strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 (riemannZeta ((p : ℂ) + t + 1)))

/-- **Higher-power stride series for the Dirichlet eta function.** Let $q, t \ge 1$ be integers,
let $p \ge 0$ be an even integer, and let $T_{q,t}(n)$ denote the signed stride sum. Then the
partial sums
$$\sum_{n=1}^{N} (-1)^{n+1} \frac{n^{p+1} + (n+q)^{p+1}}{(n(n+q))^{p+1}} T_{q,t}(n)$$
converge, as $N \to \infty$, to $\eta(p+t+1)$, where $\eta(s) = \sum_{n \ge 1} (-1)^{n+1} n^{-s}$
is the Dirichlet eta function.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Theorem 5,
equation (40). -/
public theorem_wanted tendsto_strideSignedSum_dirichletEta_add (q t p : ℕ) (hq : 0 < q)
    (ht : 0 < t) (hp : Even p) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n * (((n : ℝ) + 1) ^ (p + 1) + ((n : ℝ) + 1 + q) ^ (p + 1)) /
          (((n : ℝ) + 1) * ((n : ℝ) + 1 + q)) ^ (p + 1) * strideSignedSum q t (n + 1))
      atTop (𝓝 (∑' n : ℕ, (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ (p + t + 1)))

/-- **Digamma series for the alternating stride sum.** Let $q \ge 1$ and $t \ge 1$ be integers,
let $S_{q,t}$ denote the alternating stride sum and $\psi$ the digamma function. As
$N \to \infty$, the partial sums
$$
\sum_{n=1}^{N} \frac{2n + q}{(n + \frac12)(n - \frac12 + q)} \, S_{q,t}(n)
$$
converge to
$$
\frac{1}{2q} \sum_{n=1}^{\infty} \frac{1}{n^t}
\left[\psi\left(\frac{n+\frac12+q}{2q}\right) - \psi\left(\frac{n+\frac12}{2q}\right)\right] +
\frac{1}{2q} \sum_{n=1}^{\infty} \frac{1}{n^t}
\left[\psi\left(\frac{n-\frac12+2q}{2q}\right) - \psi\left(\frac{n-\frac12+q}{2q}\right)\right].
$$

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Corollary 1,
equation (20). -/
public theorem_wanted tendsto_strideAlternatingSum_digamma_half (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) :
    Tendsto (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (2 * ((n : ℝ) + 1) + q) / (((n : ℝ) + 1 + 1 / 2) * ((n : ℝ) + 1 - 1 / 2 + q)) *
          strideAlternatingSum q t (n + 1) : ℝ) : ℂ))
      atTop (𝓝 ((∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ t *
          (Complex.digamma (((n : ℂ) + 1 + 1 / 2 + q) / (2 * q)) -
            Complex.digamma (((n : ℂ) + 1 + 1 / 2) / (2 * q)))) / (2 * q) +
        (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ t *
          (Complex.digamma (((n : ℂ) + 1 - 1 / 2 + 2 * q) / (2 * q)) -
            Complex.digamma (((n : ℂ) + 1 - 1 / 2 + q) / (2 * q)))) / (2 * q)))

/-- **Closed form of $\sum_{n \ge 1} 1/(n^t(2n-1))$.** For every integer $t \ge 1$,
$$\sum_{n \ge 1} \frac{1}{n^t (2n-1)} = 2^t \log 2 - \sum_{j=1}^{t-1} 2^{t-1-j} \zeta(j+1),$$
where $\zeta$ is the Riemann zeta function.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Corollary 1,
equation (22). -/
public theorem_wanted tsum_inv_pow_mul_two_mul_sub_one (t : ℕ) (ht : 0 < t) :
    ((∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ t * (2 * ((n : ℝ) + 1) - 1)) : ℝ) : ℂ) =
      2 ^ t * Real.log 2 -
        ∑ j ∈ Finset.Icc 1 (t - 1), (2 : ℂ) ^ (t - 1 - j) * riemannZeta ((j : ℂ) + 1)

end

end MetaMathlibExt
