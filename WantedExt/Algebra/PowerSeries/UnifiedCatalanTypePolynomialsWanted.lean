/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Unified Catalan-type polynomials

Statements from M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105.

Every family in the paper is defined by a generating function of the shape
`numerator(t) / (c - α t + β t^m)^λ` with a real exponent `λ`. The denominator factor
`(c - α t + β t^m)^(-λ)` is `trinomialNegPowSeries λ c α β m`, built from Mathlib's binomial
series; the paper's polynomials are coefficients of products of power series in `t`, with
all variables `x, y, z` fixed real numbers. The paper's `P^λ_{r,m}(z)` and `h^λ_{r,m}(z)`
in Theorems 2 and 3 are read as the coefficients of `(1 - m t + z t^m)^(-λ)` and
`(1 - m z t + t^m)^(-λ)` (Definition 5 with `A = 0`), as in the proof of Theorem 2.
The paper's Hermite polynomials `H_n(x)` have the generating function `e^(2xt - t²)`
(Section 1), and `H_n(x, y)` are the Kampé de Fériet polynomials `H^2_n(x, y)` of
Equation (2).
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Negative real power of a trinomial as a power series.** For real numbers $\lambda$, $c$,
$\alpha$, $\beta$ and a natural number $m$, this is the formal power series in $t$ with real
coefficients
$$c^{-\lambda} \sum_{n \ge 0} \binom{-\lambda}{n} u^n, \qquad u = \frac{-\alpha t + \beta t^m}{c},$$
that is, the real power $c^{-\lambda}$ times the binomial series
$(1 + t)^{-\lambda} = \sum_{n \ge 0} \binom{-\lambda}{n} t^n$ with $u$ substituted for $t$ (for
$c = 0$ the division is read as $0$, so $u = 0$). The substitution is meaningful when $u$ has
zero constant term, which holds for $m \ge 1$; for $c > 0$ and $m \ge 1$ the series is the
expansion of $(c - \alpha t + \beta t^m)^{-\lambda}$ in powers of $t$.

For $c > 0$ and $m \ge 1$ this is the denominator factor of every generating function in Pathan
and Usman's paper; Section 2 takes $c = 1$, $\alpha = m$ and $\beta = x$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equations (6), (12)
and (15). -/
noncomputable def trinomialNegPowSeries (lam c α β : ℝ) (m : ℕ) : PowerSeries ℝ :=
  C (c ^ (-lam)) *
    (binomialSeries ℝ (-lam)).subst (C (-α / c) * X + C (β / c) * X ^ m : PowerSeries ℝ)

/-- **Constant term of the trinomial series.** For all real numbers $\lambda, c, \alpha, \beta$
and every natural number $m \ne 0$, the negative real power of the trinomial
$c - \alpha t + \beta t^m$ with exponent $\lambda$ as a power series in $t$, that is, the real
power $c^{-\lambda}$ times the binomial series $(1 + u)^{-\lambda}$ with
$u = (-\alpha t + \beta t^m)/c$ substituted (where $u = 0$ when $c = 0$), has constant term
$c^{-\lambda}$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (6). -/
theorem constantCoeff_trinomialNegPowSeries (lam c α β : ℝ) {m : ℕ} (hm : m ≠ 0) :
    constantCoeff (trinomialNegPowSeries lam c α β m) = c ^ (-lam) := by
  set u : PowerSeries ℝ := C (-α / c) * X + C (β / c) * X ^ m with hu_def
  have hu0 : constantCoeff u = 0 := by simp [u, hm]
  have hu : HasSubst u := HasSubst.of_constantCoeff_zero' hu0
  have hone : subst u (1 : PowerSeries ℝ) = 1 := by
    rw [← coe_substAlgHom hu, map_one]
  set b := binomialSeries ℝ (-lam) with hb_def
  have hb0 : constantCoeff (b - 1) = 0 := by simp [b]
  have hsub0 : constantCoeff ((b - 1).subst u) = 0 :=
    constantCoeff_subst_eq_zero hu0 (b - 1) hb0
  have hb : b = 1 + (b - 1) := by ring
  unfold trinomialNegPowSeries
  rw [← hu_def, ← hb_def, map_mul, hb, subst_add hu, map_add, hone, hsub0]
  simp

/-- **The trinomial series at exponent one.** For all real numbers $\alpha, \beta$ and every
natural number $m \ne 0$, the formal expansion of $(1 - \alpha t + \beta t^m)^{-\lambda}$ in
powers of $t$ at $\lambda = -1$ is the polynomial $1 - \alpha t + \beta t^m$ itself.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (6). -/
theorem trinomialNegPowSeries_neg_one (α β : ℝ) {m : ℕ} (hm : m ≠ 0) :
    trinomialNegPowSeries (-1) 1 α β m = 1 - C α * X + C β * X ^ m := by
  set u : PowerSeries ℝ := C (-α / 1) * X + C (β / 1) * X ^ m with hu_def
  have hu0 : constantCoeff u = 0 := by simp [u, hm]
  have hu : HasSubst u := HasSubst.of_constantCoeff_zero' hu0
  have hone : subst u (1 : PowerSeries ℝ) = 1 := by
    rw [← coe_substAlgHom hu, map_one]
  have h1 : (-(-1 : ℝ)) = ((1 : ℕ) : ℝ) := by norm_num
  unfold trinomialNegPowSeries
  rw [← hu_def, h1, binomialSeries_nat, pow_one, subst_add hu, subst_X hu, hone]
  simp [u, map_neg]
  ring

/-- **Kampé de Fériet polynomials.** For natural numbers $m, n$ and elements $x, y$ of a
commutative $\mathbb{R}$-algebra, the Kampé de Fériet (two-variable Hermite) polynomial is

$$H^m_n(x, y) = \sum_{r=0}^{q} \frac{n!}{r!\,(n - m r)!}\, y^r x^{n - m r},$$

where $q = \lfloor n / m \rfloor$, read as $q = 0$ when $m = 0$. The paper writes $H_n(x, y)$
for $H^2_n(x, y)$; taking values in an algebra lets $H_k(x + 2yt, y)$ be formed as a formal
power series in $t$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (2). -/
noncomputable def kampeDeFerietHermite {A : Type*} [CommRing A] [Algebra ℝ A] (m n : ℕ)
    (x y : A) : A :=
  ∑ r ∈ Finset.range (n / m + 1),
    ((n.factorial : ℝ) / ((r.factorial : ℝ) * ((n - m * r).factorial : ℝ))) •
      (y ^ r * x ^ (n - m * r))

/-- **The zeroth Kampé de Fériet polynomial.** For every natural number $m$ and all elements
$x, y$ of a commutative $\mathbb{R}$-algebra, $H^m_0(x, y) = 1$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (2). -/
theorem kampeDeFerietHermite_zero {A : Type*} [CommRing A] [Algebra ℝ A] (m : ℕ) (x y : A) :
    kampeDeFerietHermite m 0 x y = 1 := by
  simp [kampeDeFerietHermite]

/-- **The second Kampé de Fériet polynomial.** For all real numbers $x$ and $y$,
$H^2_2(x, y) = x^2 + 2y$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Equation (2). -/
theorem kampeDeFerietHermite_two_two (x y : ℝ) :
    kampeDeFerietHermite 2 2 x y = x ^ 2 + 2 * y := by
  simp [kampeDeFerietHermite, Finset.sum_range_succ, Nat.factorial]

/-- **Hermite-shifted Catalan-type polynomials as convolutions.** Write $H_n(x, y) = H^2_n(x, y)$
for the Kampé de Fériet polynomials. For a natural number $m$ and real numbers $\lambda, z$,
write $(1 - m t + z t^m)^{-\lambda}$ and $(1 - m z t + t^m)^{-\lambda}$ for the negative real
powers of the trinomials $1 - m t + z t^m$ and $1 - m z t + t^m$ with exponent $\lambda$ as
power series in $t$ (for $m \ge 1$ these are their expansions in powers of $t$), and let
$P^\lambda_{r,m}(z)$ and $h^\lambda_{r,m}(z)$ be their coefficients of $t^r$. For all natural
numbers $k, m, n$ and real numbers $\lambda, x, y, z$, as formal power series in $t$ (with
$e^{xt + yt^2}$ the exponential series and $H_k(x + 2yt, y)$ evaluated in power series), the
coefficient of $t^n$ in $e^{xt + yt^2} H_k(x + 2yt, y) (1 - m t + z t^m)^{-\lambda}$ is
$\sum_{r=0}^{n} H_{n-r+k}(x, y) P^\lambda_{r,m}(z) / (n - r)!$, and the coefficient of $t^n$
in $e^{xt + yt^2} H_k(x + 2yt, y) (1 - m z t + t^m)^{-\lambda}$ is
$\sum_{r=0}^{n} H_{n-r+k}(x, y) h^\lambda_{r,m}(z) / (n - r)!$.

These coefficients are the paper's $H^{k;\lambda}_{n,m}(x, y, z)$ and
$h^{k;\lambda}_{n,m}(x, y, z)$ (Definition 3, Equations (8) and (9)).

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 2
(`integers-2026-A105-thm-2`). -/
public theorem_wanted coeff_hermiteShift_mul_trinomialNegPowSeries (k m n : ℕ)
    (lam x y z : ℝ) :
    let G : PowerSeries ℝ := ((exp ℝ).subst (C x * X + C y * X ^ 2 : PowerSeries ℝ) :
        PowerSeries ℝ) * kampeDeFerietHermite 2 k (C x + C (2 * y) * X) (C y)
    coeff n (G * trinomialNegPowSeries lam 1 m z m) =
        ∑ r ∈ Finset.range (n + 1), kampeDeFerietHermite 2 (n - r + k) x y /
          ((n - r).factorial : ℝ) * coeff r (trinomialNegPowSeries lam 1 m z m) ∧
      coeff n (G * trinomialNegPowSeries lam 1 (m * z) 1 m) =
        ∑ r ∈ Finset.range (n + 1), kampeDeFerietHermite 2 (n - r + k) x y /
          ((n - r).factorial : ℝ) * coeff r (trinomialNegPowSeries lam 1 (m * z) 1 m)

/-- **Nieto–Hermite Catalan-type polynomials as convolutions.** Let $j, k, m, r$ be natural
numbers with $k \le r$ and let $\lambda, x, y$ be real numbers. Let $E(t) = e^{2yt - t^2}$ be the
exponential series, so that its coefficient of $t^n$ is $H_n(y) / n!$ with $H_n$ the Hermite
polynomials, and let $F(t)$ be the power series whose coefficient of $t^n$ is $H_n(y) / n!$ when
$n \ge k$ and $j \mid n - k$, and $0$ otherwise (for $j \ge 1$ this is the series
$F(j, k, y, t) = \sum_n H_{jn+k}(y) t^{jn+k} / (jn + k)!$ of Equation (1)). Write
$(1 - m t + x t^m)^{-\lambda}$ and $(1 - m x t + t^m)^{-\lambda}$ for the negative real powers
of the trinomials $1 - m t + x t^m$ and $1 - m x t + t^m$ with exponent $\lambda$ as power
series in $t$ (for $m \ge 1$ these are their expansions in powers of $t$), let
$P^\lambda_{s,m}(x)$ and $h^\lambda_{s,m}(x)$ be their coefficients of $t^s$, and let
$q = \lfloor (r - k) / j \rfloor$, read as $q = 0$ when $j = 0$. Then the coefficient of
$t^r$ in $F(t) (1 - m t + x t^m)^{-\lambda}$ is
$\sum_{n=0}^{q} H_{jn+k}(y) P^\lambda_{r-jn-k,m}(x) / (jn + k)!$, and the coefficient of $t^r$
in $F(t) (1 - m x t + t^m)^{-\lambda}$ is the same sum with $h^\lambda_{r-jn-k,m}(x)$ in place
of $P^\lambda_{r-jn-k,m}(x)$.

These are the paper's $F^{j.k;\lambda}_{r,m}(x, y)$ and $f^{j.k;\lambda}_{r,m}(x, y)$
(Equations (10) and (11)). The paper takes $j, m \ge 1$; for $r < k$ its sum is empty.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 3
(`integers-2026-A105-thm-3`). -/
public theorem_wanted coeff_nietoHermiteSeries_mul_trinomialNegPowSeries (j k m r : ℕ)
    (lam x y : ℝ) (hkr : k ≤ r) :
    let E : PowerSeries ℝ :=
      ((exp ℝ).subst (C (2 * y) * X - X ^ 2 : PowerSeries ℝ) : PowerSeries ℝ)
    let F : PowerSeries ℝ := PowerSeries.mk fun n ↦ if k ≤ n ∧ j ∣ n - k then coeff n E else 0
    coeff r (F * trinomialNegPowSeries lam 1 m x m) =
        ∑ n ∈ Finset.range ((r - k) / j + 1),
          coeff (j * n + k) E * coeff (r - j * n - k) (trinomialNegPowSeries lam 1 m x m) ∧
      coeff r (F * trinomialNegPowSeries lam 1 (m * x) 1 m) =
        ∑ n ∈ Finset.range ((r - k) / j + 1),
          coeff (j * n + k) E * coeff (r - j * n - k) (trinomialNegPowSeries lam 1 (m * x) 1 m)

/-- **Splitting the numerator of a unified Catalan-type generating function.** Let
$j, k, m, d, n$ be natural numbers, let $a, b, c, \lambda, x, y$ be real numbers and let $A$ be
a polynomial with integer coefficients. Let $K(t)$ be the negative real power of the trinomial
$c - a x t + b (2x - 1)^d t^m$ with exponent $\lambda$ as a power series in $t$ (for $c > 0$ and
$m \ge 1$ this is the expansion of $(c - a x t + b (2x - 1)^d t^m)^{-\lambda}$ in powers of $t$),
and let $S(t) = \sum_i y^i t^i / i!$, the sum running over the natural numbers $i \ge k$ with
$j \mid i - k$ (for $j \ge 1$ this is the pseudo-Bessel function $S(j, k, yt)$ of Equation (5)).
Then the coefficient of $t^n$ in $(S(t) + A(x)\, t)\, K(t)$ equals the coefficient of $t^n$ in
$S(t) K(t)$, plus the coefficient of $t^n$ in $(1 + A(x)\, t)\, K(t)$, minus the coefficient of
$t^n$ in $K(t)$.

In the paper's notation this is
$P^{j.k;\lambda,A}_{n,m}(x, y) = P^{j.k;\lambda,0}_{n,m}(x, y) + P^{1.0;\lambda,A}_{n,m}(x) -
P^{1.0;\lambda,0}_{n,m}(x)$; the kernel is the paper's for $c > 0$.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 6
(`integers-2026-A105-thm-6`). -/
public theorem_wanted coeff_catalanTypeKernel_decomposition (j k m d n : ℕ)
    (a b c lam x y : ℝ) (A : Polynomial ℤ) :
    let K : PowerSeries ℝ := trinomialNegPowSeries lam c (a * x) (b * (2 * x - 1) ^ d) m
    let S : PowerSeries ℝ :=
      PowerSeries.mk fun i ↦ if k ≤ i ∧ j ∣ i - k then y ^ i / (i.factorial : ℝ) else 0
    let At : PowerSeries ℝ := C (Polynomial.aeval x A) * X
    coeff n ((S + At) * K) = coeff n (S * K) + coeff n ((1 + At) * K) - coeff n K

/-- **Determinant of the lower-triangular Catalan-type matrix.** Let $m, N$ be natural numbers,
let $\lambda, x$ be real numbers, let $A$ be a polynomial with integer coefficients, and let
$P_n$ be the coefficient of $t^n$ in $(1 + A(x)\, t)(1 - m t + x t^m)^{-\lambda}$, where
$(1 - m t + x t^m)^{-\lambda}$ denotes the negative real power of the trinomial
$1 - m t + x t^m$ with exponent $\lambda$ as a power series in $t$ (for $m \ge 1$, its expansion
in powers of $t$). Then the $(N + 1) \times (N + 1)$ matrix whose $(i, j)$ entry, for
$0 \le i, j \le N$, is $P_{i-j}$ when $j \le i$ and $0$ otherwise has determinant $P_0^{N+1}$.

In the paper's notation $P_n = P^{\lambda,A}_{n,m}(x)$ (Definition 6 at $y = 0$) and the matrix
is $P_N^{(m,\lambda,A)}(x)$ of Equation (18). The paper's proviso $P_0 \ne 0$ is dropped.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 7
(`integers-2026-A105-thm-7`). -/
public theorem_wanted det_catalanTypeLowerTriangular (m N : ℕ) (lam x : ℝ)
    (A : Polynomial ℤ) :
    let P : ℕ → ℝ := fun n ↦
      coeff n ((1 + C (Polynomial.aeval x A) * X) * trinomialNegPowSeries lam 1 m x m)
    (Matrix.of fun i j : Fin (N + 1) ↦ if j ≤ i then P (i - j) else 0).det = P 0 ^ (N + 1)

/-- **Hankel determinants of recurrent Catalan-type sequences vanish.** Let $m, N, r$ be natural
numbers with $r \le N$, let $\lambda, x$ be real numbers, let $A$ be a polynomial with integer
coefficients, and let $P_n$ be the coefficient of $t^n$ in
$(1 + A(x)\, t)(1 - m t + x t^m)^{-\lambda}$, where $(1 - m t + x t^m)^{-\lambda}$ denotes the
negative real power of the trinomial $1 - m t + x t^m$ with exponent $\lambda$ as a power series
in $t$ (for $m \ge 1$, its expansion in powers of $t$). Suppose real numbers $c_0, \dots, c_r$,
not all zero, satisfy $\sum_{k=0}^{r} c_k P_{n-k} = 0$ for every $n \ge r$. Then the
$(N + 1) \times (N + 1)$ Hankel matrix with $(i, j)$ entry $P_{i+j}$ for $0 \le i, j \le N$ has
determinant $0$.

In the paper's notation $P_n = P^{\lambda,A}_{n,m}(x)$, the recurrence is Equation (22) and the
Hankel matrix is $H_N^{(m,\lambda,A)}(x)$ of Equation (20). The paper's assumption $1 \le r$ is
dropped.

Source: M. A. Pathan and T. Usman, *Unified Catalan-Type Polynomials with Matrix
Formulations and Applications*, INTEGERS 26 (2026), Article A105, Theorem 8
(`integers-2026-A105-thm-8`). -/
public theorem_wanted det_catalanTypeHankel_eq_zero (m N r : ℕ) (lam x : ℝ)
    (A : Polynomial ℤ) (cs : ℕ → ℝ) :
    let P : ℕ → ℝ := fun n ↦
      coeff n ((1 + C (Polynomial.aeval x A) * X) * trinomialNegPowSeries lam 1 m x m)
    r ≤ N → (∃ k ≤ r, cs k ≠ 0) →
      (∀ n, r ≤ n → ∑ k ∈ Finset.range (r + 1), cs k * P (n - k) = 0) →
      (Matrix.of fun i j : Fin (N + 1) ↦ P (i + j)).det = 0

end

end MetaMathlibExt
