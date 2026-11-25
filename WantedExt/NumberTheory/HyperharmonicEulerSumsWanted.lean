/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import MathlibExt.NumberTheory.HyperharmonicEulerSums

namespace MetaMathlibExt

@[expose] public section

open Real

/-- **Beta-function evaluation of hyperharmonic Euler sums.** Let $k, p \ge 0$ be integers and
let $r, a$ be complex numbers with $\operatorname{Re}(r) < p + 1$ and $\operatorname{Re}(a) > -k$,
such that $r$ is not a positive integer and $a$ is not a nonpositive integer. Write
$H_n^{[r]}(k)$ for the generalized hyperharmonic number and let
$S(k, r; p + 1; a) = \sum_{n \ge k} H_n^{[r]}(k) / (n + a)^{p+1}$. Then

$$p! \, k! \, S(k, r; p + 1; a) = (-1)^p D_a^p D_r^k B(a, 1 - r),$$

where $B(a, 1 - r) = \Gamma(a) \Gamma(1 - r) \cdot (1/\Gamma)(a + 1 - r)$, with $1/\Gamma$ the
entire reciprocal of the Gamma function (zero at the poles of $\Gamma$), and $D_a^p D_r^k$ means
the $k$-th complex derivative in $r$ followed by the $p$-th complex derivative in $a$.

The source also states the identity at positive integers $r$, after removing the singularity of
$\Gamma(1 - r)$, and at nonpositive integers $a$, and extends it by analytic continuation; those
cases are not included here.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Theorem 1 (`integers-2026-A81-thm-1`). -/
public theorem_wanted hyperharmonicEulerSum_eq_iteratedDeriv_beta (k p : ℕ) (r a : ℂ)
    (hr : r.re < p + 1) (ha : -(k : ℝ) < a.re) (hr' : ∀ m : ℕ, r ≠ m + 1)
    (ha' : ∀ m : ℕ, a ≠ -m) :
    (p.factorial * k.factorial : ℂ) * hyperharmonicEulerSum k r (p + 1) a =
      (-1) ^ p * iteratedDeriv p (fun b => iteratedDeriv k
        (fun s => Complex.Gamma b * Complex.Gamma (1 - s) * (Complex.Gamma (b + 1 - s))⁻¹) r) a

/-- **Polygamma structure of hyperharmonic Euler sums.** Let $k \ge 0$, $r$ and $p$ be integers
with $1 \le r \le p$, and let $a \in \mathbb{C} \setminus \mathbb{Z}$. Write $H_n^{[r]}(k)$ for
the generalized hyperharmonic number. Then the series
$S(k, r; p + 1; a) = \sum_{n \ge k} H_n^{[r]}(k) / (n + a)^{p+1}$ converges absolutely, and its
sum lies in the algebra generated over the field $\mathbb{Q}(a)$ by $\psi(a) + \gamma$, the
derivatives $\psi^{(j)}(a)$ for $j \ge 1$ and the zeta values $\zeta(j)$ for $j \ge 2$, where
$\psi$ is the digamma function and $\gamma$ is the Euler–Mascheroni constant.

The source also extends the result by continuity to integers $a > -k$; that case is not included
here.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Theorem 2 (`integers-2026-A81-thm-2`). -/
public theorem_wanted hyperharmonicEulerSum_mem_adjoin_digamma (k p r : ℕ) (hr : 1 ≤ r)
    (hrp : r ≤ p) (a : ℂ) (ha : ∀ m : ℤ, a ≠ m) :
    Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + a) ^ ((p : ℤ) + 1)) ∧
      hyperharmonicEulerSum k r (p + 1) a ∈
        Algebra.adjoin (IntermediateField.adjoin ℚ {a})
          ({Complex.digamma a + Real.eulerMascheroniConstant} ∪
            Set.range (fun j : ℕ => iteratedDeriv (j + 1) Complex.digamma a) ∪
            Set.range fun j : ℕ => riemannZeta (j + 2))

/-- **Hyperharmonic Euler sums with rational parameters.** Let $a$ and $r$ be rational numbers
that are not integers, with $a - r \in \mathbb{Z}$, let $N \ge 1$ be an integer with
$N a \in \mathbb{Z}$, and let $k \ge 0$ and $p > r$ be integers. Put $M = \mathrm{lcm}(2N, 4)$
and $\omega = e^{2 \pi i / M}$, a primitive $M$-th root of unity. Write $H_n^{[r]}(k)$ for the
generalized hyperharmonic numbers. Then the generalized hyperharmonic Euler sum
$S(k, r; p; a) = \sum_{n \ge k} H_n^{[r]}(k) / (n + a)^p$ converges, and $S(k, r; p; a) = \pi x$
for some $x$ in the algebra generated over the field $\mathbb{Q}(\omega + \omega^{-1})$ by
$\psi(a) + \gamma$, the derivatives $\psi^{(j)}(a)$ for $j \ge 1$, $\pi^2$ and the odd zeta
values $\zeta(3), \zeta(5), \dots$, where $\psi$ is the digamma function and $\gamma$ is the
Euler–Mascheroni constant.

The field $\mathbb{Q}(\omega + \omega^{-1})$ does not depend on which primitive $M$-th root of
unity $\omega$ is chosen.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Theorem 3 (`integers-2026-A81-thm-3`). -/
public theorem_wanted hyperharmonicEulerSum_rat_mem_pi_mul_adjoin (a r : ℚ)
    (ha : ∀ m : ℤ, a ≠ m) (hr : ∀ m : ℤ, r ≠ m) (N : ℕ) (hN : 0 < N)
    (hNa : ∃ m : ℤ, N * a = m) (har : ∃ m : ℤ, a - r = m) (k : ℕ) (p : ℤ) (hp : r < p) :
    let ζ : ℂ := Complex.exp (2 * π * Complex.I / (Nat.lcm (2 * N) 4 : ℂ))
    Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + a) ^ p) ∧
      ∃ x ∈ Algebra.adjoin (IntermediateField.adjoin ℚ {ζ + ζ⁻¹})
          ({Complex.digamma a + Real.eulerMascheroniConstant} ∪
            Set.range (fun j : ℕ => iteratedDeriv (j + 1) Complex.digamma a) ∪
            {(π : ℂ) ^ 2} ∪ Set.range fun j : ℕ => riemannZeta (2 * j + 3)),
        hyperharmonicEulerSum k r p a = π * x

/-- **Hyperharmonic Euler sums with integer parameter and half-integer shift.** Let $k \ge 0$, $r$
and $p$ be integers with $1 \le r < p$, and let $a \in \frac{1}{2} + \mathbb{Z}$. Write
$H_n^{[r]}(k)$ for the generalized hyperharmonic number. Then the series
$S(k, r; p; a) = \sum_{n \ge k} H_n^{[r]}(k) / (n + a)^p$ converges absolutely, and its sum lies
in the $\mathbb{Q}$-subalgebra $\mathbb{Q}[\log 2, \pi^2, \zeta(2j+1)_{j \ge 1}]$ of $\mathbb{C}$
generated by $\log 2$, $\pi^2$ and the odd zeta values.

The source prints $1 \le r \le p$, but at $r = p$ the series can diverge (for $k = 0$,
$r = p = 1$ and $a = 1/2$ it is $\sum_{n \ge 0} 1/(n + 1/2)$), and the source's Theorem 2 has
exponent $p + 1$ for $r \le p$; so $r < p$ is assumed.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 2, first part (`integers-2026-A81-cor-2`). -/
public theorem_wanted hyperharmonicEulerSum_half_mem_eulerSumPeriodAlgebra (k p r : ℕ)
    (hr : 1 ≤ r) (hrp : r < p) (c : ℤ) :
    Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + (c + 1 / 2)) ^ (p : ℤ)) ∧
      hyperharmonicEulerSum k r p (c + 1 / 2) ∈ eulerSumPeriodAlgebra

/-- **Odd harmonic central binomial sums at integer shifts.** Let $k \ge 0$ and $p > 0$ be
integers, let $a$ be an integer with $a > -k$, and let $O_n(k)$ denote the depth-$k$ odd harmonic
number. Then the series of real numbers
$$\sum_{n \ge 0} \frac{\binom{2n}{n} O_n(k)}{4^n (n + a)^p}$$
converges, and its sum lies in the algebra $\mathbb{Q}[\log 2, \pi^2, \zeta(3), \zeta(5), \dots]$
viewed inside $\mathbb{C}$. The terms with $n < k$ are $0$, since $O_n(k) = 0$ for $n < k$, so
this is also the sum over $n \ge k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 2, second part (`integers-2026-A81-cor-2`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_sum_mem_eulerSumPeriodAlgebra
    (k p : ℕ) (hp : 0 < p) (a : ℤ) (ha : -(k : ℤ) < a) :
    Summable (fun n : ℕ =>
        ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n / (4 ^ n * ((n : ℝ) + a) ^ p)) ∧
      ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + a) ^ p) : ℝ) : ℂ) ∈ eulerSumPeriodAlgebra

/-- **Central binomial odd harmonic sum with denominator $4^n (n + 1)^2$.** For every integer
$k \ge 0$, with $O_n(k)$ the depth-$k$ odd harmonic number,
$$\sum_{n \ge 0} \frac{\binom{2n}{n} O_n(k)}{4^n (n + 1)^2} =
2^{k+2} (k + 1 - \log 2) - \sum_{j=1}^{k} (2^{k+2} - 2^j) \zeta(k + 2 - j).$$

The terms with $n < k$ vanish, since $O_n(k) = 0$ for $n < k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 3 (`integers-2026-A81-cor-3`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_div_succ_sq_tsum (k : ℕ) :
    ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) =
      2 ^ (k + 2) * (k + 1 - Real.log 2) -
        ∑ j ∈ Finset.Icc 1 k, (2 ^ (k + 2) - 2 ^ j) * riemannZeta ((k + 2 - j : ℕ) : ℂ)

/-- **Odd harmonic central binomial sums with weight $\binom{n}{m}$ at integer shifts.** Let
$k, m \ge 0$ and $p > m$ be integers, let $a$ be an integer with $a > -k$, and let $O_n(k)$
denote the depth-$k$ odd harmonic number. Then the series of real numbers
$$\sum_{n \ge 0} \binom{n}{m} \frac{\binom{2n}{n} O_n(k)}{4^n (n + a)^p}$$
converges, and its sum lies in the algebra $\mathbb{Q}[\log 2, \pi^2, \zeta(3), \zeta(5), \dots]$
viewed inside $\mathbb{C}$. The terms with $n < k$ are $0$, since $O_n(k) = 0$ for $n < k$, so
this is also the sum over $n \ge k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 4, first part (`integers-2026-A81-cor-4`). -/
public theorem_wanted choose_centralBinom_oddMultipleHarmonic_sum_mem_eulerSumPeriodAlgebra
    (k p m : ℕ) (hmp : m < p) (a : ℤ) (ha : -(k : ℤ) < a) :
    Summable (fun n : ℕ => (n.choose m : ℝ) * ((2 * n).choose n : ℝ) *
        oddMultipleHarmonic k n / (4 ^ n * ((n : ℝ) + a) ^ p)) ∧
      ((∑' n : ℕ, (n.choose m : ℝ) * ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + a) ^ p) : ℝ) : ℂ) ∈ eulerSumPeriodAlgebra

/-- **Central binomial odd harmonic sums over $\binom{n+m}{m}$ lie in the period algebra.** Let
$O_n(k)$ denote the depth-$k$ odd harmonic number and let
$A = \mathbb{Q}[\log 2, \pi^2, \zeta(3), \zeta(5), \ldots] \subseteq \mathbb{C}$ be the Euler sum
period algebra. For integers $k \ge 0$, $p \ge 1$, $m \ge 1$ and $a > -k$, the series
$$\sum_{n \ge 0} \frac{\binom{2n}{n} O_n(k)}{4^n \binom{n+m}{m} (n + a)^p}$$
converges and its sum lies in $A$.

The terms with $n < k$ are $0$ because $O_n(k) = 0$ there; this includes the term with
$n + a = 0$ when $a \le 0$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 4, second part (`integers-2026-A81-cor-4`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_div_choose_sum_mem_eulerSumPeriodAlgebra
    (k p m : ℕ) (hp : 0 < p) (hm : 0 < m) (a : ℤ) (ha : -(k : ℤ) < a) :
    Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + a) ^ p)) ∧
      ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + a) ^ p) : ℝ) : ℂ) ∈
        eulerSumPeriodAlgebra

/-- **Catalan–odd harmonic sum with denominator $4^n n$.** Let $k \ge 1$ be an integer, let $C_n$
denote the $n$-th Catalan number and $O_n(k)$ the depth-$k$ odd harmonic number. Then
$$\sum_{n \ge 1} \frac{C_n O_n(k)}{4^n n} = (2^{k+1} - 1) \zeta(k + 1) - 2^{k+1}.$$

Since $O_n(k) = 0$ for $n < k$, the sum can equally be taken over $n \ge k$.

Source: the denominator $4^n n$ is read from the record's two-row layout ($C_n O_n(k)$ over
$4^n n$).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 5 (`integers-2026-A81-cor-5`). -/
public theorem_wanted catalan_oddMultipleHarmonic_div_tsum (k : ℕ) (hk : 0 < k) :
    ((∑' n : ℕ, (catalan n : ℝ) * oddMultipleHarmonic k n / (4 ^ n * n) : ℝ) : ℂ) =
      (2 ^ (k + 1) - 1) * riemannZeta (k + 1) - 2 ^ (k + 1)

/-- **Quarter-shift hyperharmonic Euler sums.** Let $k \ge 0$ and $0 \le r < p$ be integers, and
let $a$ be a complex number with $a \in \tfrac14 + \mathbb{Z}$ or $a \in \tfrac34 + \mathbb{Z}$.
Write $H_n^{[r]}(k)$ for the generalized hyperharmonic numbers. Then the generalized
hyperharmonic Euler sum $S(k, r; p; a) = \sum_{n \ge k} H_n^{[r]}(k) / (n + a)^p$ converges, and
its value lies in the $\mathbb{Q}$-algebra
$\mathbb{Q}[\log 2, \pi, \zeta(3), \zeta(5), \dots, \beta(2), \beta(4), \dots]$ of complex
numbers, where $\beta(s) = \sum_{n \ge 0} (-1)^n / (2n+1)^s$ is the Dirichlet beta function.

The source prints $0 \le r \le p$; at $r = p \ge 1$ the series diverges (for $k = 0$ and
$r = p = 1$ it is $\sum_{n \ge 0} 1 / (n + a)$), so $r < p$ is used.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 6 (`integers-2026-A81-cor-6`). -/
public theorem_wanted hyperharmonicEulerSum_quarter_mem_eulerSumBetaPeriodAlgebra
    (k p r : ℕ) (hrp : r < p) (a : ℂ) (ha : ∃ c : ℤ, a = c + 1 / 4 ∨ a = c + 3 / 4) :
    Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + a) ^ (p : ℤ)) ∧
      hyperharmonicEulerSum k r p a ∈ eulerSumBetaPeriodAlgebra

/-- **Hyperharmonic Euler sums with half-integer parameter and shift.** Let $k \ge 0$ be an
integer, let $r, a \in \frac{1}{2} + \mathbb{Z}$, and let $p$ be an integer with $p > r$. Write
$H_n^{[r]}(k)$ for the generalized hyperharmonic number. Then the series
$S(k, r; p; a) = \sum_{n \ge k} H_n^{[r]}(k) / (n + a)^p$ converges absolutely, and its sum
equals $\pi x$ for some $x$ in the $\mathbb{Q}$-subalgebra $\mathbb{Q}[\log 2, \pi^2,
\zeta(2j+1)_{j \ge 1}]$ of $\mathbb{C}$ generated by $\log 2$, $\pi^2$ and the odd zeta values.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 7, first part (`integers-2026-A81-cor-7`). -/
public theorem_wanted hyperharmonicEulerSum_half_half_mem_pi_mul (k : ℕ) (c d p : ℤ)
    (hp : c < p) :
    Summable (fun n : ℕ => generalizedHyperharmonic (n + k) k (c + 1 / 2) /
        (((n + k : ℕ) : ℂ) + (d + 1 / 2)) ^ p) ∧
      ∃ x ∈ eulerSumPeriodAlgebra,
        hyperharmonicEulerSum k (c + 1 / 2) p (d + 1 / 2) = π * x

/-- **Odd harmonic central binomial sums with weight $\binom{n}{m}$ at half-integer shifts.**
Let $k, m \ge 0$ and $p > m$ be integers, let $a = d + 1/2$ with $d$ an integer, and let $O_n(k)$
denote the depth-$k$ odd harmonic number. Then the series of real numbers
$$\sum_{n \ge 0} \binom{n}{m} \frac{\binom{2n}{n} O_n(k)}{4^n (n + a)^p}$$
converges, and its sum equals $\pi x$ for some $x$ in the algebra
$\mathbb{Q}[\log 2, \pi^2, \zeta(3), \zeta(5), \dots] \subseteq \mathbb{C}$. The terms with $n < k$
are $0$, since $O_n(k) = 0$ for $n < k$, so this is also the sum over $n \ge k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 7, second part (`integers-2026-A81-cor-7`). -/
public theorem_wanted choose_centralBinom_oddMultipleHarmonic_half_sum_mem_pi_mul
    (k p m : ℕ) (hmp : m < p) (d : ℤ) :
    Summable (fun n : ℕ => (n.choose m : ℝ) * ((2 * n).choose n : ℝ) *
        oddMultipleHarmonic k n / (4 ^ n * ((n : ℝ) + (d + 1 / 2)) ^ p)) ∧
      ∃ x ∈ eulerSumPeriodAlgebra,
        ((∑' n : ℕ, (n.choose m : ℝ) * ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + (d + 1 / 2)) ^ p) : ℝ) : ℂ) = π * x

/-- **Central binomial odd harmonic sums over $\binom{n+m}{m}$ at half-integer shifts.** Let
$O_n(k)$ denote the depth-$k$ odd harmonic number and let
$A = \mathbb{Q}[\log 2, \pi^2, \zeta(3), \zeta(5), \ldots] \subseteq \mathbb{C}$ be the Euler sum
period algebra. For integers $k \ge 0$, $p \ge 1$, $m \ge 1$ and $d$, put $a = d + 1/2$. Then the
series
$$\sum_{n \ge 0} \frac{\binom{2n}{n} O_n(k)}{4^n \binom{n+m}{m} (n + a)^p}$$
converges, and its sum equals $q + \pi x$ for some rational number $q$ and some $x \in A$.

The terms with $n < k$ vanish, since $O_n(k) = 0$ for $n < k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 7, third part (`integers-2026-A81-cor-7`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_div_choose_half_sum_mem
    (k p m : ℕ) (hp : 0 < p) (hm : 0 < m) (d : ℤ) :
    Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + (d + 1 / 2)) ^ p)) ∧
      ∃ q : ℚ, ∃ x ∈ eulerSumPeriodAlgebra,
        ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + (d + 1 / 2)) ^ p) : ℝ) : ℂ) =
          q + π * x

/-- **Catalan–odd harmonic sums at the shift $1/2$.** Let $k \ge 0$ and $p \ge 1$ be integers,
let $C_n$ denote the $n$-th Catalan number and $O_n(k)$ the depth-$k$ odd harmonic number, and
let $A = \mathbb{Q}[\log 2, \pi^2, \zeta(3), \zeta(5), \ldots] \subseteq \mathbb{C}$ be the Euler
sum period algebra. Then the series
$$S = \sum_{n \ge 0} \frac{C_n O_n(k)}{4^n (n + 1/2)^p}$$
converges, and $S - (-2)^p 2^{k+1} = \pi x$ for some $x \in A$.

The terms with $n < k$ vanish, since $O_n(k) = 0$ for $n < k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 8 (`integers-2026-A81-cor-8`). -/
public theorem_wanted catalan_oddMultipleHarmonic_half_sum_sub_mem_pi_mul (k p : ℕ)
    (hp : 0 < p) :
    Summable (fun n : ℕ => (catalan n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n : ℝ) + 1 / 2) ^ p)) ∧
      ∃ x ∈ eulerSumPeriodAlgebra,
        ((∑' n : ℕ, (catalan n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + 1 / 2) ^ p) : ℝ) : ℂ) - (-2) ^ p * 2 ^ (k + 1) = π * x

/-- **Central binomial sum over $\binom{n+m}{m} (n + 1/2)^2$.** Let $m \ge 1$ be an integer and
write $O_m = O_m(1) = \sum_{i=1}^{m} 1/(i - 1/2)$ for the depth-one odd harmonic number. Then
$$\sum_{n \ge 0} \frac{\binom{2n}{n}}{4^n \binom{n+m}{m} (n + 1/2)^2} =
\frac{4^m \pi}{\binom{2m}{m}} \bigl(2 \log 2 - O_m\bigr) -
\sum_{q=1}^{m} \frac{(-4)^q \binom{m}{q}}{\binom{2q}{q} (q - 1/2)^2}.$$

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 9, first identity (`integers-2026-A81-cor-9`). -/
public theorem_wanted centralBinom_div_choose_half_sq_tsum (m : ℕ) (hm : 0 < m) :
    ∑' n : ℕ, ((2 * n).choose n : ℝ) / (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 1 / 2) ^ 2) =
      4 ^ m * π / ((2 * m).choose m : ℝ) * (2 * Real.log 2 - oddMultipleHarmonic 1 m) -
        ∑ q ∈ Finset.Icc 1 m,
          (-4 : ℝ) ^ q * (m.choose q : ℝ) / (((2 * q).choose q : ℝ) * ((q : ℝ) - 1 / 2) ^ 2)

/-- **Odd harmonic central binomial sum over $\binom{n+m}{m} (n + 1/2)^2$.** Let $m \ge 1$ be an
integer and write $O_j = O_j(1) = \sum_{i=1}^{j} 1/(i - 1/2)$ for the depth-one odd harmonic
number. Then
$$\sum_{n \ge 0} \frac{\binom{2n}{n} (O_n - O_m)}{4^n \binom{n+m}{m} (n + 1/2)^2} =
\frac{4^m \pi}{\binom{2m}{m}} \Bigl(\bigl(O_m - 2 \log 2\bigr)^2 - \frac{\pi^2}{6}\Bigr) +
\sum_{q=1}^{m} \frac{(-4)^q \binom{m}{q} (O_m - O_q)}{\binom{2q}{q} (q - 1/2)^2}.$$

Here $\pi^2 / 6 = \zeta(2)$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 9, second identity (`integers-2026-A81-cor-9`). -/
public theorem_wanted centralBinom_oddHarmonic_sub_div_choose_half_sq_tsum (m : ℕ)
    (hm : 0 < m) :
    ∑' n : ℕ, ((2 * n).choose n : ℝ) * (oddMultipleHarmonic 1 n - oddMultipleHarmonic 1 m) /
        (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 1 / 2) ^ 2) =
      4 ^ m * π / ((2 * m).choose m : ℝ) *
          ((oddMultipleHarmonic 1 m - 2 * Real.log 2) ^ 2 - π ^ 2 / 6) +
        ∑ q ∈ Finset.Icc 1 m,
          (-4 : ℝ) ^ q * (m.choose q : ℝ) * (oddMultipleHarmonic 1 m - oddMultipleHarmonic 1 q) /
            (((2 * q).choose q : ℝ) * ((q : ℝ) - 1 / 2) ^ 2)

/-- **Products of quarter-shift hyperharmonic Euler sums.** Let $k_1, k_2 \ge 0$ be integers,
let $r_1, r_2 \in \tfrac12 + \mathbb{Z}$, $a \in \tfrac14 + \mathbb{Z}$ and
$b \in \tfrac34 + \mathbb{Z}$, and let $p_1, p_2$ be integers with $p_1 > r_1$ and $p_2 > r_2$.
Write $H_n^{[r]}(k)$ for the generalized hyperharmonic numbers and
$S(k, r; p; a) = \sum_{n \ge k} H_n^{[r]}(k) / (n + a)^p$ for the generalized hyperharmonic
Euler sum. Then the series $S(k_1, r_1; p_1; a)$ and $S(k_2, r_2; p_2; b)$ converge, and
$S(k_1, r_1; p_1; a) \, S(k_2, r_2; p_2; b) = \pi x$ for some $x$ in the $\mathbb{Q}$-algebra
$\mathbb{Q}[\log 2, \pi, \zeta(3), \zeta(5), \dots, \beta(2), \beta(4), \dots]$ of complex
numbers, where $\beta(s) = \sum_{n \ge 0} (-1)^n / (2n+1)^s$ is the Dirichlet beta function.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 11, first part (`integers-2026-A81-cor-11`). -/
public theorem_wanted hyperharmonicEulerSum_quarter_mul_mem_pi_mul (k₁ k₂ : ℕ)
    (c₁ c₂ d e p₁ p₂ : ℤ) (h₁ : c₁ < p₁) (h₂ : c₂ < p₂) :
    Summable (fun n : ℕ => generalizedHyperharmonic (n + k₁) k₁ (c₁ + 1 / 2) /
        (((n + k₁ : ℕ) : ℂ) + (d + 1 / 4)) ^ p₁) ∧
      Summable (fun n : ℕ => generalizedHyperharmonic (n + k₂) k₂ (c₂ + 1 / 2) /
        (((n + k₂ : ℕ) : ℂ) + (e + 3 / 4)) ^ p₂) ∧
      ∃ x ∈ eulerSumBetaPeriodAlgebra,
        hyperharmonicEulerSum k₁ (c₁ + 1 / 2) p₁ (d + 1 / 4) *
          hyperharmonicEulerSum k₂ (c₂ + 1 / 2) p₂ (e + 3 / 4) = π * x

/-- **Products of quarter-shift central binomial odd harmonic sums.** Let $O_n(k)$ denote the
depth-$k$ odd harmonic number, let $\beta(s) = \sum_{n \ge 0} (-1)^n / (2n+1)^s$ be the Dirichlet
beta function, and let
$B = \mathbb{Q}[\log 2, \pi, \zeta(3), \zeta(5), \ldots, \beta(2), \beta(4), \ldots] \subseteq
\mathbb{C}$. For integers $k_1, k_2 \ge 0$ and $p_1, p_2 \ge 1$, the series
$$S_1 = \sum_{n \ge 0} \frac{\binom{2n}{n} O_n(k_1)}{4^n (n + 1/4)^{p_1}}, \qquad
S_2 = \sum_{n \ge 0} \frac{\binom{2n}{n} O_n(k_2)}{4^n (n + 3/4)^{p_2}}$$
both converge, and $S_1 S_2 = \pi x$ for some $x \in B$.

The terms with $n < k_i$ vanish, since $O_n(k_i) = 0$ for $n < k_i$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 11, second part (`integers-2026-A81-cor-11`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_quarter_mul_mem_pi_mul
    (k₁ k₂ p₁ p₂ : ℕ) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) :
    Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k₁ n /
        (4 ^ n * ((n : ℝ) + 1 / 4) ^ p₁)) ∧
      Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k₂ n /
        (4 ^ n * ((n : ℝ) + 3 / 4) ^ p₂)) ∧
      ∃ x ∈ eulerSumBetaPeriodAlgebra,
        ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k₁ n /
            (4 ^ n * ((n : ℝ) + 1 / 4) ^ p₁) : ℝ) : ℂ) *
          ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k₂ n /
            (4 ^ n * ((n : ℝ) + 3 / 4) ^ p₂) : ℝ) : ℂ) = π * x

/-- **Odd harmonic central binomial sums with weight $\binom{n}{m}$ at shift $1/4$.** Let
$k, m \ge 0$ and $p > m$ be integers, let $O_n(k)$ denote the depth-$k$ odd harmonic number, let
$\beta$ be the Dirichlet beta function, and let
$$\varpi = 2 \int_0^1 \frac{dt}{\sqrt{1 - t^4}}$$
be the lemniscate constant. Then the series of real numbers
$$\sum_{n \ge 0} \binom{n}{m} \frac{\binom{2n}{n} O_n(k)}{4^n (n + 1/4)^p}$$
converges, and its sum equals $\varpi x$ for some $x$ in the algebra
$\mathbb{Q}[\log 2, \pi, \zeta(2j+1)_{j \ge 1}, \beta(2j)_{j \ge 1}] \subseteq \mathbb{C}$. The
terms with $n < k$ are $0$, since $O_n(k) = 0$ for $n < k$, so this is also the sum over $n \ge k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 10, first statement (`integers-2026-A81-cor-10`). -/
public theorem_wanted choose_centralBinom_oddMultipleHarmonic_quarter_sum_mem
    (k p m : ℕ) (hmp : m < p) :
    Summable (fun n : ℕ => (n.choose m : ℝ) * ((2 * n).choose n : ℝ) *
        oddMultipleHarmonic k n / (4 ^ n * ((n : ℝ) + 1 / 4) ^ p)) ∧
      ∃ x ∈ eulerSumBetaPeriodAlgebra,
        ((∑' n : ℕ, (n.choose m : ℝ) * ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + 1 / 4) ^ p) : ℝ) : ℂ) =
          (((2 * ∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t ^ 4))⁻¹) : ℝ) : ℂ) * x

/-- **Odd harmonic central binomial sums with weight $\binom{n}{m}$ at shift $3/4$.** Let
$k, m \ge 0$ and $p > m$ be integers, let $O_n(k)$ denote the depth-$k$ odd harmonic number, let
$\beta$ be the Dirichlet beta function, and let
$$\varpi = 2 \int_0^1 \frac{dt}{\sqrt{1 - t^4}}$$
be the lemniscate constant. Then the series of real numbers
$$\sum_{n \ge 0} \binom{n}{m} \frac{\binom{2n}{n} O_n(k)}{4^n (n + 3/4)^p}$$
converges, and its sum equals $(\pi / \varpi) x$ for some $x$ in the algebra
$\mathbb{Q}[\log 2, \pi, \zeta(2j+1)_{j \ge 1}, \beta(2j)_{j \ge 1}] \subseteq \mathbb{C}$. The
terms with $n < k$ are $0$, since $O_n(k) = 0$ for $n < k$, so this is also the sum over $n \ge k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 10, second statement (`integers-2026-A81-cor-10`). -/
public theorem_wanted choose_centralBinom_oddMultipleHarmonic_three_quarter_sum_mem
    (k p m : ℕ) (hmp : m < p) :
    Summable (fun n : ℕ => (n.choose m : ℝ) * ((2 * n).choose n : ℝ) *
        oddMultipleHarmonic k n / (4 ^ n * ((n : ℝ) + 3 / 4) ^ p)) ∧
      ∃ x ∈ eulerSumBetaPeriodAlgebra,
        ((∑' n : ℕ, (n.choose m : ℝ) * ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + 3 / 4) ^ p) : ℝ) : ℂ) =
          ((π / (2 * ∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t ^ 4))⁻¹) : ℝ) : ℂ) * x

/-- **Central binomial odd harmonic sums over $\binom{n+m}{m}$ at the shift $1/4$.** Let $O_n(k)$
denote the depth-$k$ odd harmonic number, let $\beta(s) = \sum_{n \ge 0} (-1)^n / (2n+1)^s$ be the
Dirichlet beta function, let
$B = \mathbb{Q}[\log 2, \pi, \zeta(3), \zeta(5), \ldots, \beta(2), \beta(4), \ldots] \subseteq
\mathbb{C}$, and let $\varpi = 2 \int_0^1 dt / \sqrt{1 - t^4}$ be the lemniscate constant. For
integers $k \ge 0$, $p \ge 1$ and $m \ge 1$, the series
$$\sum_{n \ge 0} \frac{\binom{2n}{n} O_n(k)}{4^n \binom{n+m}{m} (n + 1/4)^p}$$
converges, and its sum equals $q + \varpi x$ for some rational number $q$ and some $x \in B$.

The terms with $n < k$ vanish, since $O_n(k) = 0$ for $n < k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 10, third statement (`integers-2026-A81-cor-10`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_div_choose_quarter_sum_mem
    (k p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 1 / 4) ^ p)) ∧
      ∃ q : ℚ, ∃ x ∈ eulerSumBetaPeriodAlgebra,
        ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 1 / 4) ^ p) : ℝ) : ℂ) =
          q + (((2 * ∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t ^ 4))⁻¹) : ℝ) : ℂ) * x

/-- **Central binomial odd harmonic sums over $\binom{n+m}{m}$ at the shift $3/4$.** Let $O_n(k)$
denote the depth-$k$ odd harmonic number, let $\beta(s) = \sum_{n \ge 0} (-1)^n / (2n+1)^s$ be the
Dirichlet beta function, let
$B = \mathbb{Q}[\log 2, \pi, \zeta(3), \zeta(5), \ldots, \beta(2), \beta(4), \ldots] \subseteq
\mathbb{C}$, and let $\varpi = 2 \int_0^1 dt / \sqrt{1 - t^4}$ be the lemniscate constant. For
integers $k \ge 0$, $p \ge 1$ and $m \ge 1$, the series
$$\sum_{n \ge 0} \frac{\binom{2n}{n} O_n(k)}{4^n \binom{n+m}{m} (n + 3/4)^p}$$
converges, and its sum equals $q + (\pi / \varpi) x$ for some rational number $q$ and some
$x \in B$.

The terms with $n < k$ vanish, since $O_n(k) = 0$ for $n < k$.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 10, fourth statement (`integers-2026-A81-cor-10`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_div_choose_three_quarter_sum_mem
    (k p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 3 / 4) ^ p)) ∧
      ∃ q : ℚ, ∃ x ∈ eulerSumBetaPeriodAlgebra,
        ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 3 / 4) ^ p) : ℝ) : ℂ) =
          q + ((π / (2 * ∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t ^ 4))⁻¹) : ℝ) : ℂ) * x

end

end MetaMathlibExt
