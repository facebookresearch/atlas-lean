/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.Combinatorics.AssociatedStirlingEulerian

/-!
# Generalized Eulerian polynomials with a nonnegative gamma vector

Statements from Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5.

The paper treats `q, t, x, y` as indeterminates over `ℚ`; here they are rational numbers
(a polynomial identity over `ℚ` is equivalent to the identity at all rational points), and
the generating function `((x - y) / (x e^(yz) - y e^(xz)))^q e^((x+y)qtz)` is formed for
`x ≠ y`, where its denominator has nonzero constant term. Permutations of `Fin n` are
zero-indexed; excedances `w(i) > i` are `MetaMathlibExt.excedanceCount`, and the
`n`-cycles (all points in one cycle, so the identity of `Fin 1` counts) are those counted by
`MetaMathlibExt.circularEulerian`. The cycle count `cyc(w)` (fixed points included) is
`MetaMathlibExt.cycleQuotientCount` and `fix(w)` is `Fintype.card (Function.fixedPoints w)`.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Number of double excedances.** For a permutation $w$ of $\{0, 1, \dots, n-1\}$, a double
excedance of $w$ is a point $i$ with $w^{-1}(i) < i < w(i)$, and $\mathrm{dexc}(w)$ is the
number of double excedances of $w$.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Section 4. -/
def doubleExcedanceCount {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i ↦ w⁻¹ i < i ∧ i < w i).card

/-- **The identity has no double excedances.** For every $n$, the identity permutation of
$\{0, 1, \dots, n-1\}$ has no double excedances.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Section 4. -/
theorem doubleExcedanceCount_one (n : ℕ) :
    doubleExcedanceCount (1 : Equiv.Perm (Fin n)) = 0 := by
  simp [doubleExcedanceCount]

/-- **Generating function of the generalized Eulerian polynomials.** For rational numbers
$q$, $t$, $x$, $y$ with $x \ne y$, this is the formal power series in $z$ over $\mathbb{Q}$
$$\mathcal{P}(q, t; x, y; z) = \left(\frac{x - y}{x e^{yz} - y e^{xz}}\right)^q e^{(x+y)qtz}.$$
Here the base has constant term $1$, and its $q$-th power is the binomial series
$(1 + u)^q = \sum_{n \ge 0} \binom{q}{n} u^n$ with $u$ the base minus $1$. For $x = y$ the
denominator is zero and the formula above does not apply.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5,
Equation (2). -/
noncomputable def generalizedEulerianSeries (q t x y : ℚ) : PowerSeries ℚ :=
  (binomialSeries ℚ q).subst
      (C (x - y) * (C x * rescale y (exp ℚ) - C y * rescale x (exp ℚ))⁻¹ - 1) *
    rescale ((x + y) * q * t) (exp ℚ)

/-- **Generalized Eulerian polynomials.** For rational numbers $q, t, x, y$ and $n \ge 0$, the
generalized Eulerian polynomial $P_n(q, t; x, y)$ is $n!$ times the coefficient of $z^n$ in the
formal power series over $\mathbb{Q}$
$$\mathcal{P}(q, t; x, y; z) = \left(\frac{x - y}{x e^{yz} - y e^{xz}}\right)^q e^{(x + y) q t z},$$
where the $q$-th power is the binomial series $(1 + u)^q = \sum_{k \ge 0} \binom{q}{k} u^k$
applied to $u = \frac{x - y}{x e^{yz} - y e^{xz}} - 1$. When $x \ne y$ the quotient has constant
term $1$, so $u$ has constant term $0$; for $x = y$ the formula is degenerate and the value of
$P_n$ is a formal convention.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5,
Equation (3). -/
noncomputable def generalizedEulerianP (q t x y : ℚ) (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * coeff n (generalizedEulerianSeries q t x y)

/-- **Generalized Eulerian polynomials with zero cycle weight.** For all rational numbers
$t, x, y$ and every $n \ge 0$, the generalized Eulerian polynomial satisfies
$P_0(0, t; x, y) = 1$ and $P_n(0, t; x, y) = 0$ for $n \ge 1$.

Indeed, for $q = 0$ the generating function of the polynomials $P_n(0, t; x, y)$ is $1$.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5,
Equation (2). -/
theorem generalizedEulerianP_zero_left (t x y : ℚ) (n : ℕ) :
    generalizedEulerianP 0 t x y n = if n = 0 then 1 else 0 := by
  have hb : binomialSeries ℚ (0 : ℚ) = 1 := by
    simp
  have hs : ∀ u : PowerSeries ℚ, (1 : PowerSeries ℚ).subst u = 1 := by
    intro u
    ext n
    simp [PowerSeries.subst, MvPowerSeries.subst, MvPowerSeries.eval₂]
  unfold generalizedEulerianP generalizedEulerianSeries
  rw [hb, hs, mul_zero, zero_mul, rescale_zero_apply]
  rcases n with _ | n <;> simp [coeff_one]

/-- **Exponential generating function of excedances over cyclic permutations.** Let $x \ne 1$ be
a rational number. For $n \ge 1$ let $C_n(x) = \sum_{m=0}^{n} C_{n,m} x^m$, where the circular
Eulerian number $C_{n,m}$ is the number of permutations $w$ of $\{0, 1, \dots, n-1\}$ whose points
all lie in a single cycle and which have exactly $m$ excedances, that is, points $i$ with
$w(i) > i$. Then, as formal power series in $z$ over $\mathbb{Q}$,
$$\sum_{n \ge 1} C_n(x) \frac{z^n}{n!} = z + \log \frac{x - 1}{x e^z - e^{xz}},$$
where the quotient has constant term $1$ and $\log$ is the formal logarithm of a power series
with constant term $1$.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Proposition 1 (`jis-2024-24.1.5-prop-1`). -/
public theorem_wanted cyclicExcedanceEGF_eq (x : ℚ) (hx : x ≠ 1) :
    PowerSeries.mk (fun n ↦ if n = 0 then 0 else
        (∑ m ∈ Finset.range (n + 1), (circularEulerian n m : ℚ) * x ^ m) / (n.factorial : ℚ)) =
      X + logOf (C (x - 1) * (C x * exp ℚ - rescale x (exp ℚ))⁻¹)

/-- **Permutation expansion of the generalized Eulerian polynomials.** Let $P_n(q, t; x, y)$ be
the generalized Eulerian polynomial and let $S_n$ be the set of permutations of
$\{0, 1, \dots, n-1\}$. For $w \in S_n$ write $\mathrm{cyc}(w)$ for the number of cycles of $w$
(fixed points counted as cycles), $\mathrm{fix}(w)$ for the number of fixed points of $w$, and
$\mathrm{exc}(w)$ for the number of excedances of $w$, the points $i$ with $w(i) > i$. Then for
all rational numbers $q, t, x, y$ with $x \ne y$ and every $n \ge 0$,
$$
P_n(q, t; x, y) = \sum_{w \in S_n} q^{\mathrm{cyc}(w)} t^{\mathrm{fix}(w)} x^{\mathrm{exc}(w)}
y^{\mathrm{exc}(w^{-1})} (x + y)^{\mathrm{fix}(w)}.
$$

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 2 (`jis-2024-24.1.5-thm-2`). -/
public theorem_wanted generalizedEulerianP_eq_sum_perm (q t x y : ℚ) (hxy : x ≠ y) (n : ℕ) :
    generalizedEulerianP q t x y n =
      ∑ w : Equiv.Perm (Fin n),
        q ^ cycleQuotientCount w * t ^ Fintype.card (Function.fixedPoints w) *
          x ^ excedanceCount n w * y ^ excedanceCount n w⁻¹ *
          (x + y) ^ Fintype.card (Function.fixedPoints w)

/-- **The gamma coefficients of the generalized Eulerian polynomials have nonnegative integer
coefficients.** Fix $n \ge 0$ and let $P_n(q, t; x, y)$ be the generalized Eulerian polynomial.
There are natural numbers $c_{k,i,j}$, for $k, i, j \ge 0$, such that, writing
$\gamma_{n,k}(q, t) = \sum_{i=0}^{n} \sum_{j=0}^{n} c_{k,i,j} q^i t^j$, for all rational numbers
$q, t, x, y$ with $x \ne y$,
$$
P_n(q, t; x, y) = \sum_{k=0}^{\lfloor n/2 \rfloor} \gamma_{n,k}(q, t) x^k y^k (x + y)^{n - 2k}.
$$
That is, the gamma coefficients $\gamma_{n,k}$ are polynomials in $q$ and $t$ with nonnegative
integer coefficients.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 4 (`jis-2024-24.1.5-thm-4`). -/
public theorem_wanted generalizedEulerianP_gamma_nonneg (n : ℕ) :
    ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ q t x y : ℚ, x ≠ y →
      generalizedEulerianP q t x y n =
        ∑ k ∈ Finset.range (n / 2 + 1),
          (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (c k i j : ℚ) * q ^ i * t ^ j) * x ^ k * y ^ k * (x + y) ^ (n - 2 * k)

/-- **Unimodality of the generalized Eulerian polynomials.** Let $P_n(q, t; x, y)$ be the
generalized Eulerian polynomial. For all natural numbers $q$, $t$ and $n$ there are a polynomial
$p$ with rational coefficients $p_0, p_1, p_2, \dots$ and an index $m$ such that
$p(x) = P_n(q, t; x, 1)$ for every rational $x \ne 1$, $p_i \le p_{i+1}$ for every $i < m$, and
$p_{i+1} \le p_i$ for every $i \ge m$. That is, $P_n(q, t; x, 1)$ is a unimodal polynomial in $x$.

Only unimodality is asserted, not symmetry of the coefficients.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Corollary 5 (`jis-2024-24.1.5-cor-5`). -/
public theorem_wanted generalizedEulerianP_unimodal (q t n : ℕ) :
    ∃ p : Polynomial ℚ, (∀ x : ℚ, x ≠ 1 → p.eval x = generalizedEulerianP q t x 1 n) ∧
      ∃ m : ℕ, (∀ i < m, p.coeff i ≤ p.coeff (i + 1)) ∧
        ∀ i, m ≤ i → p.coeff (i + 1) ≤ p.coeff i

/-- **The gamma coefficients of the generalized Eulerian polynomials count permutations.** Fix
$n \ge 0$ and let $P_n(q, t; x, y)$ be the generalized Eulerian polynomial. For a permutation $w$
of $\{0, 1, \dots, n-1\}$ write $\mathrm{cyc}(w)$ for its number of cycles (fixed points counted
as cycles), $\mathrm{fix}(w)$ for its number of fixed points, $\mathrm{exc}(w)$ for its number of
excedances (points $i$ with $w(i) > i$) and $\mathrm{dexc}(w)$ for its number of double
excedances. For $k \ge 0$ and rational $q, t$ let $\gamma_{n,k}(q, t)$ be the sum of
$q^{\mathrm{cyc}(w)} t^{\mathrm{fix}(w)}$ over the permutations $w$ of $\{0, 1, \dots, n-1\}$
with $\mathrm{exc}(w) = k$ and $\mathrm{dexc}(w) = 0$. Then for all rational $q, t, x, y$ with
$x \ne y$,
$$
P_n(q, t; x, y) = \sum_{k=0}^{\lfloor n/2 \rfloor} \gamma_{n,k}(q, t) x^k y^k (x + y)^{n - 2k},
$$
and for every $k \ge 0$ and all rational $q, t$,
$\gamma_{n,k}(q, t) = \sum_{i=0}^{n} \sum_{j=0}^{n} \gamma_{n,k,i,j} q^i t^j$, where
$\gamma_{n,k,i,j}$ is the number of permutations $w$ of $\{0, 1, \dots, n-1\}$ with
$\mathrm{exc}(w) = k$, $\mathrm{dexc}(w) = 0$, $\mathrm{cyc}(w) = i$ and $\mathrm{fix}(w) = j$.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 7 (`jis-2024-24.1.5-thm-7`). -/
public theorem_wanted generalizedEulerianP_gamma_eq (n : ℕ) :
    (∀ q t x y : ℚ, x ≠ y →
      generalizedEulerianP q t x y n =
        ∑ k ∈ Finset.range (n / 2 + 1),
          (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) ↦
              excedanceCount n w = k ∧ doubleExcedanceCount w = 0),
            q ^ cycleQuotientCount w * t ^ Fintype.card (Function.fixedPoints w)) *
          x ^ k * y ^ k * (x + y) ^ (n - 2 * k)) ∧
    ∀ (k : ℕ) (q t : ℚ),
      ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) ↦
          excedanceCount n w = k ∧ doubleExcedanceCount w = 0),
        q ^ cycleQuotientCount w * t ^ Fintype.card (Function.fixedPoints w) =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        ((Finset.univ.filter (fun w : Equiv.Perm (Fin n) ↦ excedanceCount n w = k ∧
            doubleExcedanceCount w = 0 ∧
              cycleQuotientCount w = i ∧ Fintype.card (Function.fixedPoints w) = j)).card : ℚ) *
          q ^ i * t ^ j

/-- **Generalized Eulerian polynomials at $x = -1$, $y = 1$.** Let $P_m(q, t; x, y)$ be the
generalized Eulerian polynomial. For a permutation $w$ write $\mathrm{cyc}(w)$ for its number of
cycles (fixed points counted as cycles), $\mathrm{exc}(w)$ for its number of excedances (points
$i$ with $w(i) > i$) and $\mathrm{dexc}(w)$ for its number of double excedances, and let $D_{2n}$
be the set of derangements (permutations without fixed points) of $\{0, 1, \dots, 2n-1\}$. Then
for all rational numbers $q, t$ and every $n \ge 0$, $P_{2n+1}(q, t; -1, 1) = 0$ and
$$
(-1)^n P_{2n}(q, t; -1, 1) = \sum_{w \in D_{2n}} q^{\mathrm{cyc}(w)} (-1)^{n - \mathrm{exc}(w)}
= \sum_{w \in D_{2n},\ \mathrm{exc}(w) = n,\ \mathrm{dexc}(w) = 0} q^{\mathrm{cyc}(w)},
$$
where the exponent $n - \mathrm{exc}(w)$ is an integer, possibly negative.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Corollary 8 (`jis-2024-24.1.5-cor-8`). -/
public theorem_wanted generalizedEulerianP_neg_one (q t : ℚ) (n : ℕ) :
    generalizedEulerianP q t (-1) 1 (2 * n + 1) = 0 ∧
      (-1) ^ n * generalizedEulerianP q t (-1) 1 (2 * n) =
        ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin (2 * n)) ↦
            Fintype.card (Function.fixedPoints w) = 0),
          q ^ cycleQuotientCount w * (-1 : ℚ) ^ ((n : ℤ) - excedanceCount (2 * n) w) ∧
      ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin (2 * n)) ↦
          Fintype.card (Function.fixedPoints w) = 0),
          q ^ cycleQuotientCount w * (-1 : ℚ) ^ ((n : ℤ) - excedanceCount (2 * n) w) =
        ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin (2 * n)) ↦
            Fintype.card (Function.fixedPoints w) = 0 ∧ excedanceCount (2 * n) w = n ∧
              doubleExcedanceCount w = 0), q ^ cycleQuotientCount w

end

end MetaMathlibExt
