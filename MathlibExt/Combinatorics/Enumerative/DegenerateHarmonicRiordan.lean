/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.HsuShiueGeneralizedStirlingNumber
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Generalized degenerate harmonic numbers and Riordan arrays

This file defines the sequences used by Duran, Ömür and Koparal in their study of generalized
degenerate harmonic numbers. At `α = 1`, Pascal's identity expresses the partial harmonic sum
in terms of a single binomial coefficient. The Chu–Vandermonde identity then evaluates its
alternating binomial transform. A differential equation for the generating series of the harmonic
terms gives the shifted alternating exponential sum for every positive scale parameter.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Degenerate harmonic terms.** For real numbers $\lambda$ and $\alpha$ and a natural number
$n$, the degenerate harmonic term is $0$ when $n = 0$ and
$(-1)^{n-1} \binom{\lambda}{n} / (\lambda \alpha^n)$ when $n \ge 1$, where
$\binom{\lambda}{n} = \lambda(\lambda - 1)\cdots(\lambda - n + 1)/n!$.

These are the coefficients of $t^n$ in $-\log_\lambda(1 - t/\alpha)$, where
$\log_\lambda(1 + t) = \sum_{n \ge 1} \binom{\lambda}{n} t^n / \lambda$; the series has no constant
term. For $n \ge 1$ the term is the paper's $H^0_{n,\lambda}(\alpha)$; at $n = 0$ the value $0$
follows the paper's convention $H^r_{0,\lambda}(\alpha) = 0$ and the generating function.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1
(`H⁰_{n,λ}(α)` and Equation (2)). -/
noncomputable def degenerateHarmonicTerm (lam α : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (-1) ^ (n - 1) * Ring.choose lam n / (lam * α ^ n)

/-- **Degenerate harmonic term of index zero.** For all real $\lambda$ and $\alpha$, the
degenerate harmonic term of index $0$, $H^0_{0,\lambda}(\alpha)$, is $0$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem degenerateHarmonicTerm_zero (lam α : ℝ) : degenerateHarmonicTerm lam α 0 = 0 := by
  simp [degenerateHarmonicTerm]

/-- **Degenerate harmonic term of index one.** For every real $\lambda \ne 0$ and every real
$\alpha$, the degenerate harmonic term of index $1$,
$H^0_{1,\lambda}(\alpha) = \binom{\lambda}{1} / (\lambda \alpha)$, equals $1/\alpha$.

At $\alpha = 0$ both sides are $0$, under the convention that a quotient by $0$ is $0$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem degenerateHarmonicTerm_one {lam : ℝ} (hlam : lam ≠ 0) (α : ℝ) :
    degenerateHarmonicTerm lam α 1 = 1 / α := by
  simp [degenerateHarmonicTerm]
  field_simp

/-- **Generalized degenerate harmonic numbers.** For real numbers $\lambda$ and $\alpha$ and a
natural number $n$, Dağlı's generalized degenerate harmonic number is
$$
H_{n,\lambda}(\alpha) = \sum_{k=1}^{n} \frac{(-1)^{k-1} \binom{\lambda}{k}}{\lambda\, \alpha^k},
$$
where $\binom{\lambda}{k} = \lambda(\lambda - 1)\cdots(\lambda - k + 1)/k!$; in particular
$H_{0,\lambda}(\alpha) = 0$. At $\alpha = 1$ these are the degenerate harmonic numbers
$H_{n,\lambda}$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
noncomputable def generalizedDegenerateHarmonic (lam α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (-1) ^ (k - 1) * Ring.choose lam k / (lam * α ^ k)

/-- **The zeroth generalized degenerate harmonic number.** For all real numbers $\lambda$ and
$\alpha$, the generalized degenerate harmonic number $H_{0,\lambda}(\alpha)$ is $0$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem generalizedDegenerateHarmonic_zero (lam α : ℝ) :
    generalizedDegenerateHarmonic lam α 0 = 0 := by
  simp [generalizedDegenerateHarmonic]

/-- **Recurrence for generalized degenerate harmonic numbers.** For all real numbers $\lambda$ and
$\alpha$ and every natural number $n$, the generalized degenerate harmonic numbers satisfy
$$
H_{n+1,\lambda}(\alpha) = H_{n,\lambda}(\alpha) +
\frac{(-1)^n \binom{\lambda}{n+1}}{\lambda\, \alpha^{n+1}},
$$
where $\binom{\lambda}{n+1} = \lambda(\lambda - 1)\cdots(\lambda - n)/(n+1)!$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem generalizedDegenerateHarmonic_succ (lam α : ℝ) (n : ℕ) :
    generalizedDegenerateHarmonic lam α (n + 1) =
      generalizedDegenerateHarmonic lam α n +
        (-1) ^ n * Ring.choose lam (n + 1) / (lam * α ^ (n + 1)) := by
  simp [generalizedDegenerateHarmonic, Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]

/-- **Generalized degenerate hyperharmonic numbers.** For real numbers $\lambda$ and $\alpha$,
the generalized degenerate hyperharmonic numbers $H^r_{n,\lambda}(\alpha)$, indexed by natural
numbers $r$ (the order) and $n$, are defined by recursion on $r$. At order $0$ they are the
degenerate harmonic terms: $H^0_{0,\lambda}(\alpha) = 0$ and
$H^0_{n,\lambda}(\alpha) = (-1)^{n-1} \binom{\lambda}{n} / (\lambda \alpha^n)$ for $n \ge 1$,
where $\binom{\lambda}{n}$ is the generalized binomial coefficient. For every order $r$,
$H^{r+1}_{n,\lambda}(\alpha) = \sum_{k=1}^{n} H^r_{k,\lambda}(\alpha)$.

In particular $H^r_{0,\lambda}(\alpha) = 0$ for $r \ge 1$, and $H^1_{n,\lambda}(\alpha)$ is the
generalized degenerate harmonic number
$H_{n,\lambda}(\alpha) = \sum_{k=1}^{n} (-1)^{k-1} \binom{\lambda}{k} / (\lambda \alpha^k)$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
noncomputable def generalizedDegenerateHyperharmonic (lam α : ℝ) : ℕ → ℕ → ℝ
  | 0, n => degenerateHarmonicTerm lam α n
  | r + 1, n => ∑ k ∈ Finset.Icc 1 n, generalizedDegenerateHyperharmonic lam α r k

/-- **Generalized degenerate hyperharmonic numbers of positive order vanish at zero.** For all
real numbers $\lambda$ and $\alpha$ and every natural number $r$, the generalized degenerate
hyperharmonic number of order $r + 1$ at index $0$ is zero: $H^{r+1}_{0,\lambda}(\alpha) = 0$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem generalizedDegenerateHyperharmonic_succ_zero (lam α : ℝ) (r : ℕ) :
    generalizedDegenerateHyperharmonic lam α (r + 1) 0 = 0 := by
  simp [generalizedDegenerateHyperharmonic]

/-- **Generalized degenerate hyperharmonic numbers of order one.** For all real numbers
$\lambda$ and $\alpha$ and every natural number $n$, the generalized degenerate hyperharmonic
number of order $1$ equals the generalized degenerate harmonic number:
$H^1_{n,\lambda}(\alpha) = H_{n,\lambda}(\alpha)$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem generalizedDegenerateHyperharmonic_one (lam α : ℝ) (n : ℕ) :
    generalizedDegenerateHyperharmonic lam α 1 n = generalizedDegenerateHarmonic lam α n := by
  simp only [generalizedDegenerateHyperharmonic, generalizedDegenerateHarmonic]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
  simp [degenerateHarmonicTerm, hk0]

/-- **Generalized degenerate harmonic numbers of a given rank.** For real $\lambda$ and $\alpha$,
let $\ell_0 = 0$ and $\ell_m = (-1)^{m-1} \binom{\lambda}{m} / (\lambda \alpha^m)$ for $m \ge 1$,
where $\binom{\lambda}{m}$ is the generalized binomial coefficient and a quotient by $0$ is read
as $0$, and let $L(t) = \sum_{m \ge 0} \ell_m t^m$ as a formal power series. For
$\lambda, \alpha > 0$ this is the expansion of $-\log_\lambda(1 - t/\alpha)$, where
$\log_\lambda(1 + t) = ((1 + t)^\lambda - 1)/\lambda$ is the degenerate logarithm. For natural
numbers $n$ and $r$, the generalized degenerate harmonic number of rank $r$, written
$H_\lambda(n, r, \alpha)$, is the sum of the coefficients of $t^0, t^1, \dots, t^n$ in
$L(t)^{r+1}$. Equivalently, $\sum_{n \ge 0} H_\lambda(n, r, \alpha) t^n = L(t)^{r+1} / (1 - t)$.

Expanding the power, $H_\lambda(n, r, \alpha)$ is the sum of $\ell_{k_0} \cdots \ell_{k_r}$ over
all $k_0, \dots, k_r \ge 1$ with $k_0 + \cdots + k_r \le n$, which is the explicit definition in
the source.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1,
Equation (5). -/
noncomputable def degenerateHarmonicRank (lam α : ℝ) (n r : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1),
    PowerSeries.coeff m (PowerSeries.mk (degenerateHarmonicTerm lam α) ^ (r + 1))

/-- **Degenerate harmonic numbers of rank vanish at index zero.** For all real $\lambda$ and
$\alpha$ and every natural number $r$, the generalized degenerate harmonic number of rank $r$
satisfies $H_\lambda(0, r, \alpha) = 0$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem degenerateHarmonicRank_zero_left (lam α : ℝ) (r : ℕ) :
    degenerateHarmonicRank lam α 0 r = 0 := by
  simp [degenerateHarmonicRank, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
    degenerateHarmonicTerm_zero]

/-- **Degenerate harmonic numbers of rank zero.** For all real $\lambda$ and $\alpha$ and every
natural number $n$, the generalized degenerate harmonic number of rank $0$ equals the generalized
degenerate harmonic number: $H_\lambda(n, 0, \alpha) = H_{n,\lambda}(\alpha)$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Section 1. -/
theorem degenerateHarmonicRank_zero_right (lam α : ℝ) (n : ℕ) :
    degenerateHarmonicRank lam α n 0 = generalizedDegenerateHarmonic lam α n := by
  induction n with
  | zero => simp [degenerateHarmonicRank_zero_left, generalizedDegenerateHarmonic_zero]
  | succ n ih =>
    rw [generalizedDegenerateHarmonic_succ, ← ih]
    simp [degenerateHarmonicRank, Finset.sum_range_succ _ (n + 1), degenerateHarmonicTerm]

/-- **Degenerate exponential series.** For a real number $\lambda$, the degenerate exponential
series is the formal power series $e_\lambda(t) = \sum_{n \ge 0} (1)_{n,\lambda} \, t^n / n!$
over $\mathbb{R}$, where $(1)_{0,\lambda} = 1$ and, for $n \ge 1$,
$(1)_{n,\lambda} = 1 \cdot (1 - \lambda) \cdots (1 - (n - 1)\lambda)$ is the generalized falling
factorial of $1$ with increment $\lambda$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (1) at
`x = 1`. -/
noncomputable def degenerateExpSeries (lam : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => generalizedFallingFactorial 1 lam n / n.factorial

/-- **Constant term of the degenerate exponential series.** For every real number $\lambda$, the
constant term of the degenerate exponential series $e_\lambda(t)$ is $1$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (1). -/
theorem constantCoeff_degenerateExpSeries (lam : ℝ) :
    PowerSeries.constantCoeff (degenerateExpSeries lam) = 1 := by
  simp [degenerateExpSeries, generalizedFallingFactorial]

/-- **Degenerate Bernoulli numbers.** For a real number $\lambda$, let $(1)_{0,\lambda} = 1$ and
$(1)_{m,\lambda} = 1 \cdot (1 - \lambda) \cdots (1 - (m - 1)\lambda)$ for $m \ge 1$ (the
generalized falling factorial of $1$ with increment $\lambda$). For $n \in \mathbb{N}$, the
degenerate Bernoulli number $\beta_{n,\lambda}$ is $n!$ times the coefficient of $t^n$ in the
inverse of the formal power series $\sum_{m \ge 0} (1)_{m+1,\lambda} \, t^m / (m + 1)!$ over
$\mathbb{R}$, whose constant term is $1$.

Since this power series is $(e_\lambda(t) - 1) / t$ for the degenerate exponential series
$e_\lambda(t)$, the numbers $\beta_{n,\lambda}$ satisfy
$t / (e_\lambda(t) - 1) = \sum_{n \ge 0} \beta_{n,\lambda} \, t^n / n!$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (6). -/
noncomputable def degenerateBernoulli (lam : ℝ) (n : ℕ) : ℝ :=
  n.factorial * PowerSeries.coeff n
    (PowerSeries.mk fun m => generalizedFallingFactorial 1 lam (m + 1) / (m + 1).factorial)⁻¹

/-- **The zeroth degenerate Bernoulli number.** For every real number $\lambda$, the degenerate
Bernoulli number $\beta_{0,\lambda}$ equals $1$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (6). -/
theorem degenerateBernoulli_zero (lam : ℝ) : degenerateBernoulli lam 0 = 1 := by
  simp [degenerateBernoulli, PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.constantCoeff_inv, generalizedFallingFactorial]

/-- **Degenerate Euler numbers.** For a real number $\lambda$ and $n \in \mathbb{N}$, the
degenerate Euler number $\varepsilon_{n,\lambda}$ is $n!$ times the coefficient of $t^n$ in the
formal power series $2 / (e_\lambda(t) + 1)$ over $\mathbb{R}$, where $e_\lambda(t)$ is the
degenerate exponential series; that is,
$2 / (e_\lambda(t) + 1) = \sum_{n \ge 0} \varepsilon_{n,\lambda} \, t^n / n!$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (7). -/
noncomputable def degenerateEuler (lam : ℝ) (n : ℕ) : ℝ :=
  n.factorial * PowerSeries.coeff n (PowerSeries.C (2 : ℝ) * (degenerateExpSeries lam + 1)⁻¹)

/-- **The zeroth degenerate Euler number.** For every real number $\lambda$, the degenerate Euler
number $\varepsilon_{0,\lambda}$ equals $1$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (7). -/
theorem degenerateEuler_zero (lam : ℝ) : degenerateEuler lam 0 = 1 := by
  simp [degenerateEuler, PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_inv,
    constantCoeff_degenerateExpSeries]
  norm_num

/-- **Degenerate Stirling numbers of the first kind.** For a real number $\lambda$, let
$\log_\lambda(1 + t)$ be the formal power series $\sum_{m \ge 1} \binom{\lambda}{m} t^m / \lambda$,
where $\binom{\lambda}{m} = \lambda(\lambda - 1)\cdots(\lambda - m + 1)/m!$. For natural numbers
$n$ and $k$, the degenerate Stirling number of the first kind $S_{1,\lambda}(n, k)$ is $n!/k!$
times the coefficient of $t^n$ in $(\log_\lambda(1 + t))^k$. Equivalently,
$(\log_\lambda(1 + t))^k / k! = \sum_{n \ge k} S_{1,\lambda}(n, k) t^n / n!$, and
$S_{1,\lambda}(n, k) = 0$ for $n < k$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equations (2) and (8). -/
noncomputable def degenerateStirlingFirst (lam : ℝ) (n k : ℕ) : ℝ :=
  n.factorial / k.factorial * PowerSeries.coeff n
    ((PowerSeries.mk fun m => if m = 0 then 0 else Ring.choose lam m / lam) ^ k)

/-- **Degenerate Stirling numbers of the first kind in column zero.** For every real number
$\lambda$ and every natural number $n$, the degenerate Stirling number of the first kind
$S_{1,\lambda}(n, 0)$ equals $1$ if $n = 0$ and $0$ otherwise.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (8). -/
theorem degenerateStirlingFirst_zero_right (lam : ℝ) (n : ℕ) :
    degenerateStirlingFirst lam n 0 = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0 <;> simp [degenerateStirlingFirst, PowerSeries.coeff_one, hn]

/-- **Degenerate Stirling numbers of the second kind.** For a real number $\lambda$, let
$e_\lambda(t) = \sum_{n \ge 0} (1)_{n,\lambda} t^n / n!$ be the degenerate exponential series,
where $(1)_{0,\lambda} = 1$ and $(1)_{n,\lambda} = 1 (1 - \lambda) \cdots (1 - (n - 1)\lambda)$.
For natural numbers $n$ and $k$, the degenerate Stirling number of the second kind
$S_{2,\lambda}(n, k)$ is $n!/k!$ times the coefficient of $t^n$ in $(e_\lambda(t) - 1)^k$.
Equivalently, $(e_\lambda(t) - 1)^k / k! = \sum_{n \ge k} S_{2,\lambda}(n, k) t^n / n!$, and
$S_{2,\lambda}(n, k) = 0$ for $n < k$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (8). -/
noncomputable def degenerateStirlingSecond (lam : ℝ) (n k : ℕ) : ℝ :=
  n.factorial / k.factorial * PowerSeries.coeff n ((degenerateExpSeries lam - 1) ^ k)

/-- **Degenerate Stirling numbers of the second kind in column zero.** For every real number
$\lambda$ and every natural number $n$, the degenerate Stirling number of the second kind
$S_{2,\lambda}(n, 0)$ equals $1$ if $n = 0$ and $0$ otherwise.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (8). -/
theorem degenerateStirlingSecond_zero_right (lam : ℝ) (n : ℕ) :
    degenerateStirlingSecond lam n 0 = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0 <;> simp [degenerateStirlingSecond, PowerSeries.coeff_one, hn]

/-- **Degenerate Daehee numbers.** For a real number $\lambda$ and $n \in \mathbb{N}$, the
degenerate Daehee number is $D_{n,\lambda} = n! \binom{\lambda}{n+1} / \lambda$, where
$\binom{\lambda}{k} = \lambda (\lambda - 1) \cdots (\lambda - k + 1) / k!$ is the generalized
binomial coefficient (for $\lambda = 0$ the value is $0$, by the convention $x / 0 = 0$).

For $\lambda \ne 0$ the degenerate logarithm $\log_\lambda(1 + t) = ((1 + t)^\lambda - 1) / \lambda$
satisfies $\log_\lambda(1 + t) / t = \sum_{n \ge 0} \binom{\lambda}{n+1} t^n / \lambda$, so the
numbers $D_{n,\lambda}$ are given by
$\log_\lambda(1 + t) / t = \sum_{n \ge 0} D_{n,\lambda} \, t^n / n!$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equations (2)
and (9). -/
noncomputable def degenerateDaehee (lam : ℝ) (n : ℕ) : ℝ :=
  n.factorial * Ring.choose lam (n + 1) / lam

/-- **The zeroth degenerate Daehee number.** For every real number $\lambda \ne 0$, the degenerate
Daehee number $D_{0,\lambda}$ equals $1$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Equation (9). -/
theorem degenerateDaehee_zero {lam : ℝ} (hlam : lam ≠ 0) : degenerateDaehee lam 0 = 1 := by
  simp [degenerateDaehee, hlam]

/-- **Alternating binomial sum of degenerate harmonic numbers.** Let $\lambda > 0$ be real and let
$H_{k,\lambda} = H_{k,\lambda}(1)$ be the degenerate harmonic numbers, that is, the generalized
degenerate harmonic numbers at $\alpha = 1$. Then for every integer $n \ge 1$,
$\sum_{k=0}^{n} (-1)^{k+1} \binom{n}{k} H_{k,\lambda} = \binom{n + \lambda - 1}{n} / \lambda$,
where $\binom{n + \lambda - 1}{n}$ is the generalized binomial coefficient.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 2
(`integers-2024-A41-thm-2`). -/
theorem degenerateHarmonic_alternating_binomial_sum {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (k + 1) * (n.choose k : ℝ) * generalizedDegenerateHarmonic lam 1 k =
      Ring.choose ((n : ℝ) + lam - 1) n / lam := by
  have scaled (k : ℕ) : generalizedDegenerateHarmonic lam 1 k * lam =
      1 - (-1) ^ k * Ring.choose (lam - 1) k := by
    induction k with
    | zero => simp [generalizedDegenerateHarmonic_zero]
    | succ k ih =>
      have pascal := Ring.choose_succ_succ (lam - 1) k
      rw [sub_add_cancel] at pascal
      rw [generalizedDegenerateHarmonic_succ, one_pow, mul_one, add_mul, ih,
        div_mul_cancel₀ _ hlam.ne', pascal, pow_succ]
      ring
  have cancel : ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) = 0 := by
    exact_mod_cast Int.alternating_sum_range_choose_of_ne (n := n) (by omega)
  apply (eq_div_iff hlam.ne').2
  rw [Finset.sum_mul]
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
          (Ring.choose (lam - 1) k * (n.choose k : ℝ) - (-1) ^ k * (n.choose k : ℝ)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc _ (generalizedDegenerateHarmonic lam 1 k) lam, scaled, pow_succ]
      have hs : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by simp [← mul_pow]
      linear_combination Ring.choose (lam - 1) k * (n.choose k : ℝ) * hs
    _ = _ := by
      rw [Finset.sum_sub_distrib, cancel, sub_zero,
        show (n : ℝ) + lam - 1 = (lam - 1) + n by ring,
        Ring.add_choose_eq n (Commute.all _ _), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Ring.choose_natCast, Nat.choose_symm (Finset.mem_range_succ_iff.mp hk)]

set_option linter.unusedVariables false in
/-- **Partial sums of degenerate harmonic numbers of rank as a convolution.** Let $\lambda > 0$
and $\alpha > 0$ be real and let $n$ and $r$ be natural numbers. Write $H_\lambda(k, r, \alpha)$
for the generalized degenerate harmonic numbers of rank $r$ and $H_{m,\lambda}(\alpha)$ for the
generalized degenerate harmonic numbers. Then
$$\sum_{k=0}^{n} H_\lambda(k, r+1, \alpha) =
\sum_{k=0}^{n} H_{n-k,\lambda}(\alpha) \, H_\lambda(k, r, \alpha).$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 4
(`integers-2024-A41-thm-4`). -/
theorem degenerateHarmonicRank_succ_partial_sum {lam α : ℝ}
    (hlam : 0 < lam) (hα : 0 < α) (n r : ℕ) :
    ∑ k ∈ Finset.range (n + 1), degenerateHarmonicRank lam α k (r + 1) =
      ∑ k ∈ Finset.range (n + 1),
        generalizedDegenerateHarmonic lam α (n - k) * degenerateHarmonicRank lam α k r := by
  let L := PowerSeries.mk (degenerateHarmonicTerm lam α)
  let G : PowerSeries ℝ := PowerSeries.mk fun _ => 1
  have partialSum (f : PowerSeries ℝ) (m : ℕ) :
      PowerSeries.coeff m (f * G) = ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k f := by
    simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, G]
  have rank (m s : ℕ) : degenerateHarmonicRank lam α m s =
      PowerSeries.coeff m (L ^ (s + 1) * G) := (partialSum _ _).symm
  have product : (L ^ (r + 1) * G) * (L * G) = (L ^ (r + 1 + 1) * G) * G := by
    rw [pow_succ L (r + 1)]
    ac_rfl
  calc
    _ = PowerSeries.coeff n ((L ^ (r + 1 + 1) * G) * G) := by
      simp_rw [rank, partialSum (L ^ (r + 1 + 1) * G)]
    _ = _ := by
      rw [← product, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [← degenerateHarmonicRank_zero_right lam α, rank, Nat.zero_add, pow_one]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _

open PowerSeries

namespace degenerateHarmonicRank_shifted_exp_weighted_sum

private noncomputable abbrev logSeries (lam α : ℝ) := PowerSeries.mk (degenerateHarmonicTerm lam α)

-- The binomial coefficient recurrence gives the differential equation for the harmonic terms.
private lemma logSeries_derivative {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α) :
    (C α - X) * derivative (logSeries lam α) = 1 - C lam * logSeries lam α := by
  ext n
  rw [sub_mul, map_sub, map_sub, coeff_C_mul, coeff_C_mul, coeff_derivative]
  cases n with
  | zero =>
    simp [logSeries, coeff_zero_X_mul, degenerateHarmonicTerm_zero,
      degenerateHarmonicTerm_one hlam.ne', hα.ne']
  | succ n =>
    have h := Ring.choose_smul_choose lam (n := n + 1 + 1) (k := n + 1) (Nat.le_succ _)
    simp only [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right,
      nsmul_eq_mul, Nat.cast_succ] at h
    rw [coeff_succ_X_mul, coeff_derivative]
    simp only [logSeries, coeff_mk, degenerateHarmonicTerm, Nat.add_one_ne_zero, ite_false,
      Nat.add_sub_cancel, coeff_one, Nat.cast_succ, zero_sub]
    rw [pow_succ (-1 : ℝ), pow_succ α (n + 1)]
    field_simp
    linear_combination -h

private noncomputable abbrev weight (lam : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * generalizedFallingFactorial 1 lam (k + 1) / (k + 1).factorial

private lemma weight_succ (lam : ℝ) (k : ℕ) :
    (↑(k + 1 + 1) : ℝ) * weight lam (k + 1) =
      ((k + 1 : ℝ) * lam - 1) * weight lam k := by
  unfold weight
  rw [generalizedFallingFactorial]
  simp only [Nat.factorial_succ (k + 1), pow_succ (-1 : ℝ) k, Nat.cast_mul, Nat.cast_succ]
  field_simp
  ring

private lemma weighted_derivative {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α) (k : ℕ) :
    (C α - X) * derivative (C (weight lam k) * logSeries lam α ^ (k + 1)) +
        C (weight lam k) * logSeries lam α ^ (k + 1) =
      C ((k + 1 : ℝ) * weight lam k) * logSeries lam α ^ k -
        C ((↑(k + 1 + 1) : ℝ) * weight lam (k + 1)) * logSeries lam α ^ (k + 1) := by
  rw [weight_succ, Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul,
    derivative_pow, Nat.add_sub_cancel, pow_succ (logSeries lam α) k]
  simp only [map_sub, map_mul, map_one, map_add, map_natCast, Nat.cast_succ]
  linear_combination
    C (weight lam k) * ((k : PowerSeries ℝ) + 1) * logSeries lam α ^ k *
      logSeries_derivative hlam hα

private lemma coeff_X_derivative (f : PowerSeries ℝ) (m : ℕ) :
    coeff m (X * derivative f) = m * coeff m f := by
  cases m with
  | zero => simp [coeff_zero_X_mul]
  | succ m => rw [coeff_succ_X_mul, coeff_derivative, Nat.cast_succ, mul_comm]

end degenerateHarmonicRank_shifted_exp_weighted_sum

open degenerateHarmonicRank_shifted_exp_weighted_sum in
/-- **Shifted alternating degenerate exponential sum of degenerate harmonic numbers of rank.**
Let $\lambda > 0$ and $\alpha > 0$ be real and let $n$ be a natural number. Write
$(1)_{k,\lambda} = 1 \cdot (1 - \lambda) \cdots (1 - (k-1)\lambda)$ for the generalized falling
factorial and $H_\lambda(m, r, \alpha)$ for the generalized degenerate harmonic numbers of rank $r$.
Then
$$\sum_{k=0}^{n} (-1)^k \frac{(1)_{k+1,\lambda}}{(k+1)!} H_\lambda(n+1, k, \alpha) =
\frac{1}{\alpha}.$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 5
(`integers-2024-A41-thm-5`). -/
theorem degenerateHarmonicRank_shifted_exp_weighted_sum {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * generalizedFallingFactorial 1 lam (k + 1) / (k + 1).factorial *
          degenerateHarmonicRank lam α (n + 1) k =
      1 / α := by
  let P : PowerSeries ℝ :=
    ∑ k ∈ Finset.range (n + 1), C (weight lam k) * logSeries lam α ^ (k + 1)
  let boundary (k : ℕ) := C (↑(k + 1) * weight lam k) * logSeries lam α ^ k
  have telescope : (C α - X) * derivative P + P = 1 - boundary (n + 1) := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), (boundary k - boundary (k + 1)) := by
        simp only [P, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simpa only [boundary, Nat.cast_succ] using weighted_derivative hlam hα k
      _ = _ := by
        rw [Finset.sum_range_sub']
        simp [boundary, weight, generalizedFallingFactorial]
  -- Subtract the linear solution. The remaining differential equation has zero
  -- right-hand coefficients through degree n because logSeries has zero constant term.
  let R := P - C α⁻¹ * X
  have equation : (C α - X) * derivative R + R = -boundary (n + 1) := by
    dsimp only [R]
    rw [map_sub, derivative_C_mul_X, mul_sub, sub_mul (C α) X (C α⁻¹), ← map_mul,
      mul_inv_cancel₀ hα.ne', map_one]
    linear_combination telescope
  have vanish (m : ℕ) (hm : m ≤ n + 1) : coeff m R = 0 := by
    induction m with
    | zero =>
      simp [R, P, coeff_zero_eq_constantCoeff, logSeries, degenerateHarmonicTerm_zero]
    | succ m ih =>
      have hL : constantCoeff (logSeries lam α) = 0 := by
        simp [logSeries, degenerateHarmonicTerm_zero]
      have hpow := nat_le_order_iff.mp (le_order_pow_of_constantCoeff_eq_zero (n + 1) hL) m
        (by omega)
      have hb : coeff m (boundary (n + 1)) = 0 := by
        simp only [boundary, coeff_C_mul, hpow, mul_zero]
      have h := congrArg (coeff m) equation
      simpa [hb, sub_mul, coeff_C_mul, coeff_derivative, coeff_X_derivative,
        ih (by omega), hα.ne', show (m : ℝ) + 1 ≠ 0 by positivity] using h
  calc
    _ = ∑ m ∈ Finset.range (n + 1 + 1), coeff m P := by
      simp only [P, map_sum, coeff_C_mul, degenerateHarmonicRank, weight, Finset.mul_sum, logSeries]
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.range (n + 1 + 1), coeff m (C α⁻¹ * X) := by
      refine Finset.sum_congr rfl fun m hm => sub_eq_zero.mp ?_
      simpa only [R, map_sub] using vanish m (Finset.mem_range_succ_iff.mp hm)
    _ = _ := by simp [coeff_C_mul, coeff_X]

end

end MetaMathlibExt
