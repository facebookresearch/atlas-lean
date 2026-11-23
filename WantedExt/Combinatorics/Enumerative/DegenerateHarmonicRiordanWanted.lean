/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalized degenerate harmonic numbers and Riordan arrays

Statements from Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic
Numbers and Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41.

Throughout, `λ > 0` and `α > 0` are real, `(x)_{n,λ} = x(x - λ)⋯(x - (n - 1)λ)` is the existing
`MetaMathlibExt.generalizedFallingFactorial x λ n` (over `ℝ`), the degenerate
exponential is `e_λ(t) = ∑ (1)_{n,λ} tⁿ / n!`, and `-log_λ(1 - t/α) = ∑_{k ≥ 1} (-1)^{k-1}
binom(λ, k) tᵏ / (λ αᵏ)` (paper, Equations (1) and (2)). The degenerate Bernoulli, Euler, Stirling
and Daehee numbers are defined through the generating functions (6)-(9) of the paper, as power
series coefficients.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.HsuShiueGeneralizedStirlingNumber

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

/-- **Alternating and binomial sums of degenerate hyperharmonic numbers.** Let $\lambda > 0$ and
$\alpha > 0$ be real numbers and let $n$ be a natural number. Write $H_{m,\lambda}(\alpha)$ for the
generalized degenerate harmonic numbers, $H^s_{m,\lambda}(\alpha)$ for the generalized degenerate
hyperharmonic numbers of order $s$, and $D_{n,\lambda}$ for the degenerate Daehee numbers. Then
$$
\sum_{k=0}^{n} (-1)^k H^{k+1}_{n-k+1,\lambda}(\alpha) =
\frac{(-1)^n D_{n,\lambda}}{\alpha^{n+1}\, n!},
$$
and for every natural number $r$,
$$
\sum_{k=0}^{n} \binom{k+r}{r} H_{n-k+1,\lambda}(\alpha) = H^{r+2}_{n+1,\lambda}(\alpha).
$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 1
(`integers-2024-A41-thm-1`). -/
public theorem_wanted degenerateHyperharmonic_alternating_and_binomial_sums {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * generalizedDegenerateHyperharmonic lam α (k + 1) (n - k + 1) =
      (-1) ^ n * degenerateDaehee lam n / (α ^ (n + 1) * n.factorial) ∧
    ∀ r : ℕ, ∑ k ∈ Finset.range (n + 1),
        ((k + r).choose r : ℝ) * generalizedDegenerateHarmonic lam α (n - k + 1) =
      generalizedDegenerateHyperharmonic lam α (r + 2) (n + 1)

/-- **Alternating binomial sum of degenerate harmonic numbers.** Let $\lambda > 0$ be real and let
$H_{k,\lambda} = H_{k,\lambda}(1)$ be the degenerate harmonic numbers, that is, the generalized
degenerate harmonic numbers at $\alpha = 1$. Then for every integer $n \ge 1$,
$\sum_{k=0}^{n} (-1)^{k+1} \binom{n}{k} H_{k,\lambda} = \binom{n + \lambda - 1}{n} / \lambda$,
where $\binom{n + \lambda - 1}{n}$ is the generalized binomial coefficient.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 2
(`integers-2024-A41-thm-2`). -/
public theorem_wanted degenerateHarmonic_alternating_binomial_sum {lam : ℝ} (hlam : 0 < lam) {n : ℕ}
    (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (k + 1) * (n.choose k : ℝ) * generalizedDegenerateHarmonic lam 1 k =
      Ring.choose ((n : ℝ) + lam - 1) n / lam

/-- **Alternating degenerate exponential sum of degenerate harmonic numbers of rank.** Let
$\lambda > 0$ and $\alpha > 0$ be real and let $n$ be a natural number. Write
$(1)_{k,\lambda} = 1 \cdot (1 - \lambda) \cdots (1 - (k-1)\lambda)$ for the generalized falling
factorial (so $(1)_{0,\lambda} = 1$), $H_\lambda(m, r, \alpha)$ for the generalized degenerate
harmonic numbers of rank $r$, and $H_{m,\lambda}(\alpha)$ for the generalized degenerate harmonic
numbers. Then
$$\sum_{k=0}^{n} (-1)^k \frac{(1)_{k,\lambda}}{k!} H_\lambda(n+1, k, \alpha) =
H_{n+1,\lambda}(\alpha) - \frac{H_{n,\lambda}(\alpha)}{\alpha}.$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 3
(`integers-2024-A41-thm-3`). -/
public theorem_wanted degenerateHarmonicRank_exp_weighted_sum {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α)
    (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * generalizedFallingFactorial 1 lam k / k.factorial *
          degenerateHarmonicRank lam α (n + 1) k =
      generalizedDegenerateHarmonic lam α (n + 1) - generalizedDegenerateHarmonic lam α n / α

/-- **Partial sums of degenerate harmonic numbers of rank as a convolution.** Let $\lambda > 0$
and $\alpha > 0$ be real and let $n$ and $r$ be natural numbers. Write $H_\lambda(k, r, \alpha)$
for the generalized degenerate harmonic numbers of rank $r$ and $H_{m,\lambda}(\alpha)$ for the
generalized degenerate harmonic numbers. Then
$$\sum_{k=0}^{n} H_\lambda(k, r+1, \alpha) =
\sum_{k=0}^{n} H_{n-k,\lambda}(\alpha) \, H_\lambda(k, r, \alpha).$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 4
(`integers-2024-A41-thm-4`). -/
public theorem_wanted degenerateHarmonicRank_succ_partial_sum {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α)
    (n r : ℕ) :
    ∑ k ∈ Finset.range (n + 1), degenerateHarmonicRank lam α k (r + 1) =
      ∑ k ∈ Finset.range (n + 1),
        generalizedDegenerateHarmonic lam α (n - k) * degenerateHarmonicRank lam α k r

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
public theorem_wanted degenerateHarmonicRank_shifted_exp_weighted_sum {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * generalizedFallingFactorial 1 lam (k + 1) / (k + 1).factorial *
          degenerateHarmonicRank lam α (n + 1) k =
      1 / α

/-- **A binomial sum equal to a degenerate hyperharmonic number.** Let $\lambda > 0$ and
$\alpha > 0$ be real numbers and let $r \le n$ be natural numbers. Write
$\binom{\lambda}{j} = \lambda(\lambda - 1)\cdots(\lambda - j + 1)/j!$ and $H^s_{m,\lambda}(\alpha)$
for the generalized degenerate hyperharmonic numbers of order $s$. Then
$$
\sum_{k=r}^{n} (-1)^{n-k} \frac{\binom{\lambda}{n-k+1}}{\lambda\, \alpha^{n-k+1}} \binom{k}{r} =
H^{r+1}_{n-r+1,\lambda}(\alpha).
$$

The hypothesis $r \le n$ makes the summation range $r \le k \le n$ nonempty, as in the paper.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 6
(`integers-2024-A41-thm-6`). -/
public theorem_wanted degenerateHyperharmonic_eq_binomial_sum {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α)
    {n r : ℕ} (hrn : r ≤ n) :
    ∑ k ∈ Finset.Icc r n,
        (-1 : ℝ) ^ (n - k) * Ring.choose lam (n - k + 1) / (lam * α ^ (n - k + 1)) *
          (k.choose r : ℝ) =
      generalizedDegenerateHyperharmonic lam α (r + 1) (n - r + 1)

/-- **Degenerate harmonic numbers of rank and degenerate Stirling numbers of the first kind.** Let
$\lambda > 0$ and $\alpha > 0$ be real and let $n \ge 1$ be a natural number. Write
$(1)_{k,\lambda} = 1 \cdot (1 - \lambda) \cdots (1 - (k-1)\lambda)$ for the generalized falling
factorial, $H_\lambda(m, r, \alpha)$ for the generalized degenerate harmonic numbers of rank $r$,
and $S_{1,\lambda}(k, i)$ for the degenerate Stirling numbers of the first kind. Then
$$\sum_{k=1}^{n} \frac{(1)_{k,\lambda}}{k!} H_\lambda(n, k-1, \alpha) =
\sum_{k=1}^{n} \sum_{i=1}^{k} \frac{(-1)^{k+i} (1)_{i,\lambda} S_{1,\lambda}(k, i)}{\alpha^k k!}.$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 7
(`integers-2024-A41-thm-7`). -/
public theorem_wanted degenerateHarmonicRank_exp_sum_eq_stirlingFirst {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n,
        generalizedFallingFactorial 1 lam k / k.factorial * degenerateHarmonicRank lam α n (k - 1) =
      ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 k,
        (-1 : ℝ) ^ (k + i) * generalizedFallingFactorial 1 lam i * degenerateStirlingFirst lam k i /
          (α ^ k * k.factorial)

/-- **Degenerate Bernoulli and Euler sums of higher-rank degenerate harmonic numbers.** Let
$\lambda > 0$ and $\alpha > 0$ be real and let $n \ge 1$ be an integer. Write $\beta_{k,\lambda}$
and $\varepsilon_{k,\lambda}$ for the degenerate Bernoulli and Euler numbers,
$H_{m,\lambda}(\alpha)$ for the generalized degenerate harmonic numbers, and
$H_\lambda(m, r, \alpha)$ for the generalized degenerate harmonic numbers of rank $r$. Then
$\sum_{k=1}^{n} (-1)^k \beta_{k,\lambda} H_\lambda(n, k - 1, \alpha) / k! =
\alpha H_{n+1,\lambda}(\alpha) - 1$, and if moreover $\alpha \ne 1/2$, then
$\sum_{k=1}^{n} (-1)^{k+1} \varepsilon_{k,\lambda} H_\lambda(n, k - 1, \alpha) / k! =
((2\alpha)^{-n} - 1) / (2\alpha - 1)$.

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 8
(`integers-2024-A41-thm-8`). -/
public theorem_wanted degenerateHarmonicRank_bernoulli_euler_sums {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℝ) ^ k * degenerateBernoulli lam k * degenerateHarmonicRank lam α n (k - 1) /
          k.factorial =
      α * generalizedDegenerateHarmonic lam α (n + 1) - 1 ∧
    (α ≠ 1 / 2 →
      ∑ k ∈ Finset.Icc 1 n,
          (-1 : ℝ) ^ (k + 1) * degenerateEuler lam k / k.factorial *
            degenerateHarmonicRank lam α n (k - 1) =
        (((2 * α) ^ n)⁻¹ - 1) / (2 * α - 1))

/-- **Degenerate harmonic numbers of rank and degenerate Stirling numbers of the second kind.**
Let $\lambda > 0$ and $\alpha > 0$ be real and let $m$ and $n$ be natural numbers with
$1 \le m \le n$. Write $S_{2,\lambda}(k, m)$ for the degenerate Stirling numbers of the second kind
and $H_\lambda(n, r, \alpha)$ for the generalized degenerate harmonic numbers of rank $r$. Then
$$\sum_{k=m}^{n} \frac{(-1)^k S_{2,\lambda}(k, m) H_\lambda(n, k-1, \alpha)}{k!} =
\frac{(-1)^m}{m! \, \alpha^m}.$$

Source: Ömer Duran, Neşe Ömür and Sibel Koparal, *Generalized Degenerate Harmonic Numbers and
Their Applications with Riordan Arrays*, INTEGERS 24 (2024), Article A41, Theorem 9
(`integers-2024-A41-thm-9`). -/
public theorem_wanted degenerateHarmonicRank_stirlingSecond_sum {lam α : ℝ} (hlam : 0 < lam)
    (hα : 0 < α) {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∑ k ∈ Finset.Icc m n,
        (-1 : ℝ) ^ k * degenerateStirlingSecond lam k m * degenerateHarmonicRank lam α n (k - 1) /
          k.factorial =
      (-1) ^ m / (m.factorial * α ^ m)

end

end MetaMathlibExt
