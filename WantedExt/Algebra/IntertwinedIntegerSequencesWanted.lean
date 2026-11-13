/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Pairs of intertwined integer sequences (Kassel–Reutenauer)

Statements from C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer
Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.4
(arXiv:2507.15780).

Notation used throughout:

* `Polynomial.Chebyshev.C ℤ k` is the paper's monic Chebyshev polynomial
  `T̄_k(X)` (`T̄_k(q + q⁻¹) = q^k + q^{-k}`, `T̄_0 = 2`, `T̄_1 = X`).
* `chebyshevCPartialSum n` is the paper's `F_n(X) = 1 + ∑_{k=1}^n T̄_k(X)`.
* `kasselReutenauerPoly n` is the paper's `P̄_n(X)`, with
  `P̄_n(q + q⁻¹) = P_n(q) / q^{n-1}`; in the ring `ℤ[T;T⁻¹]` of Laurent
  polynomials in `q = T 1`, the Laurent polynomial `P_n(q) / q^{n-1}` is
  `aeval (T 1 + T (-1)) (kasselReutenauerPoly n)` and, by the paper's relation
  `C_n(q) / q^n = q⁻¹ (q - 1)² P_n(q) / q^{n-1}`, the Laurent polynomial
  `C_n(q) / q^n` is `(T 1 - 2 + T (-1)) * aeval (T 1 + T (-1)) (kasselReutenauerPoly n)`.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- **The Kassel–Reutenauer coefficients $a_{n,i}$.** For natural numbers $n$ and $i$, $a_{n,i}$ is
the number of positive divisors $d$ of $n$ with
$$\frac{i + \sqrt{2n + i^2}}{2} < d \le i + \sqrt{2n + i^2},$$
equivalently with $d(d - 2i) \le 2n$ and $n < 2d(d - i)$. For $n = 0$ the set of divisors is
taken to be empty, so $a_{0,i} = 0$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, display (2.3), quoting
their earlier Theorem 1.3 of *Complete determination of the zeta function of the
Hilbert scheme of n points on a two-dimensional torus*. -/
public def kasselReutenauerCoeff (n i : ℕ) : ℕ :=
  ((Nat.divisors n).filter fun d => d * (d - 2 * i) ≤ 2 * n ∧ n < 2 * d * (d - i)).card

/-- **Kassel–Reutenauer polynomial.** For a natural number $n$, the Kassel–Reutenauer polynomial
$\bar P_n(X) \in \mathbb{Z}[X]$ is defined by
$$
\bar P_n(X) = a_{n,0} + \sum_{i=1}^{n-1} a_{n,i} \, \bar T_i(X),
$$
where $a_{n,i}$ is the number of divisors $d$ of $n$ with $d(d - 2i) \le 2n$ and
$n < 2d(d - i)$ (equivalently, $(i + \sqrt{2n + i^2})/2 < d \le i + \sqrt{2n + i^2}$), and
$\bar T_i$ is the monic Chebyshev polynomial: $\bar T_0 = 2$, $\bar T_1 = X$ and
$\bar T_{i+2} = X \bar T_{i+1} - \bar T_i$. For $n = 0$ the sum is empty and the set of divisors
of $0$ is taken to be empty, so $\bar P_0 = 0$.

In the paper, $\bar P_n$ is characterized for $n \ge 1$ by
$\bar P_n(q + q^{-1}) = P_n(q)/q^{n-1}$, where $(q - 1)^2 P_n(q)$ is the number of ideals of
codimension $n$ of $\mathbb{F}_q[x, y, x^{-1}, y^{-1}]$; the definition here uses the explicit
expansion (2.4) of the paper instead.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (2.1)–(2.4) and Table 2. -/
public noncomputable def kasselReutenauerPoly (n : ℕ) : ℤ[X] :=
  (kasselReutenauerCoeff n 0 : ℤ[X]) +
    ∑ i ∈ Finset.Icc 1 (n - 1), (kasselReutenauerCoeff n i : ℤ[X]) * Chebyshev.C ℤ i

/-- **Partial sums of the monic Chebyshev polynomials.** For $n \ge 0$, $F_n(X)$ is the
polynomial with integer coefficients
$$F_n(X) = 1 + \sum_{k=1}^{n} \bar T_k(X),$$
where $\bar T_k \in \mathbb{Z}[X]$ is the monic Chebyshev polynomial of the source, that is, the
polynomial with $\bar T_k(q + q^{-1}) = q^k + q^{-k}$; equivalently $\bar T_0 = 2$,
$\bar T_1 = X$ and $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$. Thus $F_0 = 1$ and
$F_n = F_{n-1} + \bar T_n$ for $n \ge 1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (3.6)–(3.7). -/
public noncomputable def chebyshevCPartialSum (n : ℕ) : ℤ[X] :=
  1 + ∑ k ∈ Finset.Icc 1 n, Chebyshev.C ℤ k

/-- **Small values of the coefficients $a_{n,i}$.** The Kassel–Reutenauer coefficients satisfy
$a_{1,0} = 1$, $a_{2,0} = a_{2,1} = 1$, $a_{3,0} = 0$ and $a_{3,1} = a_{3,2} = 1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (2.3) and Table 2. -/
public theorem kasselReutenauerCoeff_small :
    kasselReutenauerCoeff 1 0 = 1 ∧ kasselReutenauerCoeff 2 0 = 1 ∧
      kasselReutenauerCoeff 2 1 = 1 ∧ kasselReutenauerCoeff 3 0 = 0 ∧
      kasselReutenauerCoeff 3 1 = 1 ∧ kasselReutenauerCoeff 3 2 = 1 := by
  decide

/-- **The first Kassel–Reutenauer polynomial.** The Kassel–Reutenauer polynomial $\bar P_1$ is the
constant polynomial $1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Table 2. -/
public theorem kasselReutenauerPoly_one : kasselReutenauerPoly 1 = 1 := by
  have h : kasselReutenauerCoeff 1 0 = 1 := by decide
  simp [kasselReutenauerPoly, h]

/-- **The Kassel–Reutenauer polynomial $\bar P_2$.** The Kassel–Reutenauer polynomial
$\bar P_2(X) \in \mathbb{Z}[X]$ equals $X + 1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Table 2. -/
public theorem kasselReutenauerPoly_two : kasselReutenauerPoly 2 = X + 1 := by
  have h0 : kasselReutenauerCoeff 2 0 = 1 := by decide
  have h1 : kasselReutenauerCoeff 2 1 = 1 := by decide
  simp [kasselReutenauerPoly, h0, h1, add_comm]

/-- **The third Kassel–Reutenauer polynomial.** The Kassel–Reutenauer polynomial $\bar P_3$ is
$X^2 + X - 2$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Table 2. -/
public theorem kasselReutenauerPoly_three : kasselReutenauerPoly 3 = X ^ 2 + X - 2 := by
  have h0 : kasselReutenauerCoeff 3 0 = 0 := by decide
  have h1 : kasselReutenauerCoeff 3 1 = 1 := by decide
  have h2 : kasselReutenauerCoeff 3 2 = 1 := by decide
  have hI : Finset.Icc 1 (3 - 1) = {1, 2} := by decide
  rw [kasselReutenauerPoly, hI, Finset.sum_pair (by decide), h0, h1, h2]
  simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, one_mul, zero_add]
  rw [Chebyshev.C_one, Chebyshev.C_two]
  ring

/-- **Zeroth partial sum of the Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
Then $F_0 = 1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (3.6). -/
public theorem chebyshevCPartialSum_zero : chebyshevCPartialSum 0 = 1 := by
  simp [chebyshevCPartialSum]

/-- **Successive partial sums of the Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every natural number $n$, $F_{n+1} = F_n + \bar T_{n+1}$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (3.6). -/
public theorem chebyshevCPartialSum_succ (n : ℕ) :
    chebyshevCPartialSum (n + 1) = chebyshevCPartialSum n + Chebyshev.C ℤ (n + 1 : ℕ) := by
  simp only [chebyshevCPartialSum, Finset.sum_Icc_succ_top (Nat.le_add_left 1 n), add_assoc]

/-- **First and second partial sums of the Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
Then $F_1 = X + 1$ and $F_2 = X^2 + X - 1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Table 4. -/
public theorem chebyshevCPartialSum_one_two :
    chebyshevCPartialSum 1 = X + 1 ∧ chebyshevCPartialSum 2 = X ^ 2 + X - 1 := by
  have h1 : chebyshevCPartialSum 1 = X + 1 := by
    rw [chebyshevCPartialSum_succ, chebyshevCPartialSum_zero]
    simp [add_comm]
  refine ⟨h1, ?_⟩
  rw [chebyshevCPartialSum_succ, h1]
  have hc : Chebyshev.C ℤ ((1 + 1 : ℕ) : ℤ) = X ^ 2 - 2 := by
    simpa using Chebyshev.C_two (R := ℤ)
  rw [hc]
  ring

/-- **Positivity of the Kassel–Reutenauer polynomials at integers $N \ge 2$.** For every $n \ge 1$
and every integer $N \ge 2$, the Kassel–Reutenauer polynomial $\bar P_n$ satisfies
$\bar P_n(N) > 0$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 2.1
(`jis-2026-26.4.4-prop-1`). -/
public theorem_wanted kasselReutenauerPoly_eval_pos (n : ℕ) (hn : 1 ≤ n) (N : ℤ) (hN : 2 ≤ N) :
    0 < (kasselReutenauerPoly n).eval N

/-- **Multiplicativity at roots of unity of order at most 4.** Let $q \in \mathbb{C}$ be a primitive
$d$-th root of unity with $d \in \{1, 2, 3, 4\}$, and let $\bar P_n$ be the Kassel–Reutenauer
polynomials. Then for all coprime integers $m, n \ge 1$,
$$
|\bar P_{mn}(q + q^{-1})| = |\bar P_m(q + q^{-1})| \, |\bar P_n(q + q^{-1})|.
$$

Since $|q| = 1$, $|\bar P_n(q + q^{-1})|$ is the absolute value $|P_n(q)|$ of the paper's
polynomial $P_n(q) = q^{n-1} \bar P_n(q + q^{-1})$, so $n \mapsto |P_n(q)|$ is multiplicative.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 2.2
(`jis-2026-26.4.4-prop-2`). -/
public theorem_wanted kasselReutenauerPoly_norm_multiplicative_rootOfUnity (q : ℂ) (d : ℕ)
    (hd : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4) (hq : IsPrimitiveRoot q d) (m n : ℕ) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hmn : m.Coprime n) :
    ‖aeval (q + q⁻¹) (kasselReutenauerPoly (m * n))‖ =
      ‖aeval (q + q⁻¹) (kasselReutenauerPoly m)‖ * ‖aeval (q + q⁻¹) (kasselReutenauerPoly n)‖

/-- **Almost multiplicativity at a primitive sixth root of unity.** Let $\omega \in \mathbb{C}$ be a
primitive sixth root of unity, and for $n \ge 1$ let $v_n = |\bar P_n(\omega + \omega^{-1})|$,
where $\bar P_n$ is the Kassel–Reutenauer polynomial. Let $m, n \ge 1$ be coprime. Then
$v_m v_n = v_{mn}$ if $(m \bmod 3, n \bmod 3)$ is $(0, 1)$, $(1, 1)$ or $(1, 2)$;
$v_m v_n = 2 v_{mn}$ if $(m \bmod 3, n \bmod 3) = (0, 2)$; and $v_m v_n = 4 v_{mn}$ if
$(m \bmod 3, n \bmod 3) = (2, 2)$. The residue pairs are ordered: nothing is claimed for the
swapped pairs.

Since $|\omega| = 1$, $v_n$ is the absolute value $|P_n(\omega)|$ of the paper's polynomial
$P_n(q) = q^{n-1} \bar P_n(q + q^{-1})$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 2.3
(`jis-2026-26.4.4-prop-3`). -/
public theorem_wanted kasselReutenauerPoly_norm_almost_multiplicative_sixth (ω : ℂ)
    (hω : IsPrimitiveRoot ω 6) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m.Coprime n) :
    ((m % 3 = 0 ∧ n % 3 = 1 ∨ m % 3 = 1 ∧ n % 3 = 1 ∨ m % 3 = 1 ∧ n % 3 = 2) →
        ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly m)‖ * ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly n)‖ =
          ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly (m * n))‖) ∧
      (m % 3 = 0 ∧ n % 3 = 2 →
        ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly m)‖ * ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly n)‖ =
          2 * ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly (m * n))‖) ∧
      (m % 3 = 2 ∧ n % 3 = 2 →
        ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly m)‖ * ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly n)‖ =
          4 * ‖aeval (ω + ω⁻¹) (kasselReutenauerPoly (m * n))‖)

/-- **Multiplicativity of $\bar P_n^2$ modulo $X (X + 1) (X^2 - 4)$.** Let $\bar P_n$ be the
Kassel–Reutenauer polynomials. For coprime integers $m, n \ge 1$, the polynomial
$\bar P_{mn}(X)^2 - \bar P_m(X)^2 \bar P_n(X)^2$ is divisible in $\mathbb{Z}[X]$ by
$X (X + 1) (X^2 - 4)$; if moreover $(m \bmod 3, n \bmod 3)$ is $(0, 1)$, $(1, 1)$ or $(1, 2)$,
it is divisible by $X (X + 1) (X^2 - 4) (X - 1)$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 2.4
(`jis-2026-26.4.4-cor-4`). -/
public theorem_wanted kasselReutenauerPoly_sq_sub_dvd (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : m.Coprime n) :
    X * (X + 1) * (X ^ 2 - 4) ∣
        kasselReutenauerPoly (m * n) ^ 2 - kasselReutenauerPoly m ^ 2 * kasselReutenauerPoly n ^ 2 ∧
      ((m % 3 = 0 ∧ n % 3 = 1 ∨ m % 3 = 1 ∧ n % 3 = 1 ∨ m % 3 = 1 ∧ n % 3 = 2) →
        X * (X + 1) * (X ^ 2 - 4) * (X - 1) ∣
          kasselReutenauerPoly (m * n) ^ 2 - kasselReutenauerPoly m ^ 2 * kasselReutenauerPoly n ^ 2)

/-- **Integers at which $|\bar P_n|$ is multiplicative.** Let $\bar P_n$ be the
Kassel–Reutenauer polynomial and let $N$ be an integer. Then
$|\bar P_{mn}(N)| = |\bar P_m(N)|\,|\bar P_n(N)|$ for all coprime positive integers $m$ and $n$
if and only if $N \in \{-2, -1, 0, 2\}$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 2.5
(`jis-2026-26.4.4-prop-5`). -/
public theorem_wanted kasselReutenauerPoly_abs_eval_multiplicative_iff (N : ℤ) :
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → m.Coprime n →
        |(kasselReutenauerPoly (m * n)).eval N| =
          |(kasselReutenauerPoly m).eval N| * |(kasselReutenauerPoly n).eval N|) ↔
      N = -2 ∨ N = -1 ∨ N = 0 ∨ N = 2

/-- **Positivity of the monic Chebyshev polynomials.** Let $\bar T_k \in \mathbb{R}[X]$ be the
monic Chebyshev polynomials, given by $\bar T_0 = 2$, $\bar T_1 = X$ and
$\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$. Then $\bar T_k(x) > 0$ for every natural number $k$
and every real number $x \ge 2$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.1
(`jis-2026-26.4.4-prop-6`). -/
public theorem_wanted chebyshevC_eval_pos_of_two_le (k : ℕ) (x : ℝ) (hx : 2 ≤ x) :
    0 < (Chebyshev.C ℝ k).eval x

/-- **Trace formula for the monic Chebyshev polynomials.** Let $\bar T_k \in \mathbb{Z}[X]$ be
the monic Chebyshev polynomials, given by $\bar T_0 = 2$, $\bar T_1 = X$ and
$\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$, and let $M$ be the $2 \times 2$ matrix over
$\mathbb{Z}[X]$ with rows $(X, -1)$ and $(1, 0)$. Then $\bar T_k = \operatorname{tr}(M^k)$ for
every natural number $k$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.2
(`jis-2026-26.4.4-prop-7`). -/
public theorem_wanted chebyshevC_eq_trace_pow (k : ℕ) :
    Chebyshev.C ℤ k = Matrix.trace ((!![X, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ[X]) ^ k)

/-- **Generating function of the partial sums of Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
In the ring $\mathbb{Z}[X][[t]]$ of formal power series in $t$ over $\mathbb{Z}[X]$,
$$(1 - X t + t^2) \sum_{n \ge 0} F_n t^n = 1 + t.$$

Since $1 - X t + t^2$ is a unit in $\mathbb{Z}[X][[t]]$, this is equivalent to
$\sum_{n \ge 0} F_n t^n = (1 + t)/(1 - X t + t^2)$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.3
(`jis-2026-26.4.4-prop-8`). -/
public theorem_wanted chebyshevCPartialSum_generatingFunction :
    (1 - PowerSeries.C X * PowerSeries.X + PowerSeries.X ^ 2) *
        PowerSeries.mk (fun n => chebyshevCPartialSum n) =
      (1 + PowerSeries.X : PowerSeries ℤ[X])

/-- **Binomial expansion of the partial sums of Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every $n \ge 1$,
$$F_n = \sum_{m=0}^{\lfloor n/2 \rfloor} (-1)^m \binom{n-m}{m} X^{n-2m} +
\sum_{m=0}^{\lfloor (n-1)/2 \rfloor} (-1)^m \binom{n-m-1}{m} X^{n-2m-1}.$$

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.4
(`jis-2026-26.4.4-prop-9`). -/
public theorem_wanted chebyshevCPartialSum_eq_binomial_sum (n : ℕ) (hn : 1 ≤ n) :
    chebyshevCPartialSum n =
      ∑ m ∈ Finset.range (n / 2 + 1), (-1 : ℤ[X]) ^ m * ((n - m).choose m : ℤ[X]) * X ^ (n - 2 * m) +
        ∑ m ∈ Finset.range ((n - 1) / 2 + 1),
          (-1 : ℤ[X]) ^ m * ((n - m - 1).choose m : ℤ[X]) * X ^ (n - 2 * m - 1)

/-- **Leading coefficients of the partial sums of Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every $n \ge 5$, the polynomial
$$F_n - \Big(X^n + X^{n-1} - (n-1) X^{n-2} - (n-2) X^{n-3} + \binom{n-2}{2} X^{n-4} +
\binom{n-3}{2} X^{n-5}\Big)$$
is either zero or has degree less than $n - 5$.

Here $\binom{n-2}{2} = (n-2)(n-3)/2$ and $\binom{n-3}{2} = (n-3)(n-4)/2$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 3.5
(`jis-2026-26.4.4-cor-10`). -/
public theorem_wanted chebyshevCPartialSum_top_coeffs (n : ℕ) (hn : 5 ≤ n) :
    (chebyshevCPartialSum n -
        (X ^ n + X ^ (n - 1) - ((n - 1 : ℕ) : ℤ[X]) * X ^ (n - 2) - ((n - 2 : ℕ) : ℤ[X]) * X ^ (n - 3) +
          ((n - 2).choose 2 : ℤ[X]) * X ^ (n - 4) + ((n - 3).choose 2 : ℤ[X]) * X ^ (n - 5))).degree <
      ((n - 5 : ℕ) : WithBot ℕ)

/-- **Three-term recurrence for the partial sums of Chebyshev polynomials.** Let
$F_n = 1 + \sum_{k=1}^{n} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every $k \ge 1$, $F_{k+1} = X F_k - F_{k-1}$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.6
(`jis-2026-26.4.4-prop-11`). -/
public theorem_wanted chebyshevCPartialSum_recurrence (k : ℕ) (hk : 1 ≤ k) :
    chebyshevCPartialSum (k + 1) = X * chebyshevCPartialSum k - chebyshevCPartialSum (k - 1)

/-- **Approximation of $\bar P_n$ by $F_{n-1}$.** Let $\bar P_n$ be the Kassel–Reutenauer
polynomials, and for $r \ge 0$ let $F_r(X) = 1 + \sum_{j=1}^{r} \bar T_j(X)$ be the partial sum
of the monic Chebyshev polynomials $\bar T_j$. For $n \ge 2$, every nonzero coefficient of
$\bar P_n(X) - F_{n-1}(X)$ sits in a degree $k$ with $2k + 2 < n$; that is, the difference has
degree less than $n/2 - 1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Theorem 4.1
(`jis-2026-26.4.4-thm-12`). -/
public theorem_wanted kasselReutenauerPoly_sub_chebyshevCPartialSum_coeff (n : ℕ) (hn : 2 ≤ n)
    (k : ℕ) (hk : (kasselReutenauerPoly n - chebyshevCPartialSum (n - 1)).coeff k ≠ 0) :
    2 * k + 2 < n

/-- **Top coefficients of the Kassel–Reutenauer polynomials.** For $n \ge 10$, the polynomial
$$
\bar P_n(X) - \Bigl(X^{n-1} + X^{n-2} - (n-2) X^{n-3} - (n-3) X^{n-4} +
\tbinom{n-3}{2} X^{n-5} + \tbinom{n-4}{2} X^{n-6}\Bigr)
$$
has degree less than $n - 6$, where $\bar P_n$ is the Kassel–Reutenauer polynomial. That is, up
to terms of degree at most $n - 7$, $\bar P_n(X)$ equals
$X^{n-1} + X^{n-2} - (n-2) X^{n-3} - (n-3) X^{n-4} + \frac{(n-3)(n-4)}{2} X^{n-5} +
\frac{(n-4)(n-5)}{2} X^{n-6}$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 4.2
(`jis-2026-26.4.4-cor-13`). -/
public theorem_wanted kasselReutenauerPoly_top_coeffs (n : ℕ) (hn : 10 ≤ n) :
    (kasselReutenauerPoly n -
        (X ^ (n - 1) + X ^ (n - 2) - ((n - 2 : ℕ) : ℤ[X]) * X ^ (n - 3) -
          ((n - 3 : ℕ) : ℤ[X]) * X ^ (n - 4) + ((n - 3).choose 2 : ℤ[X]) * X ^ (n - 5) +
          ((n - 4).choose 2 : ℤ[X]) * X ^ (n - 6))).degree <
      ((n - 6 : ℕ) : WithBot ℕ)

/-- **The top coefficients $a_{n,i}$ equal $1$.** Let $n \ge 1$ and let $i$ be a natural number
with $n \le 2i + 2$ and $i \le n - 1$; equivalently $n/2 - 1 \le i \le n - 1$, where $n/2$ is
the rational number, not the integer quotient. Then the Kassel–Reutenauer coefficient $a_{n,i}$
equals $1$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Lemma 4.3
(`jis-2026-26.4.4-lem-14`). -/
public theorem_wanted kasselReutenauerCoeff_eq_one (n i : ℕ) (hn : 1 ≤ n) (hi : n ≤ 2 * i + 2)
    (hi' : i ≤ n - 1) : kasselReutenauerCoeff n i = 1

/-- **Odd-divisor formula for the Kassel–Reutenauer polynomials.** Let $n \ge 1$, and for each
odd divisor $d$ of $n$ put $r_n(d) = n/d - (d+1)/2$, an integer. Then the Kassel–Reutenauer
polynomial $\bar P_n$ satisfies
$$
\bar P_n(X) = \sum_{d \mid n,\ d \text{ odd},\ r_n(d) \ge 0} F_{r_n(d)}(X) -
\sum_{d \mid n,\ d \text{ odd},\ r_n(d) < 0} F_{-r_n(d)-1}(X),
$$
where $F_r(X) = 1 + \sum_{k=1}^{r} \bar T_k(X)$ is the partial sum of the monic Chebyshev
polynomials $\bar T_k$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Theorem 4.4
(`jis-2026-26.4.4-thm-16`). -/
public theorem_wanted kasselReutenauerPoly_eq_oddDivisor_sum (n : ℕ) (hn : 1 ≤ n) :
    kasselReutenauerPoly n =
      ∑ d ∈ (Nat.divisors n).filter (fun d => Odd d ∧ 0 ≤ ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)),
          chebyshevCPartialSum (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)).toNat -
        ∑ d ∈ (Nat.divisors n).filter (fun d => Odd d ∧ ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) < 0),
          chebyshevCPartialSum (-(((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)) - 1).toNat

/-- **$\bar P_n$ equals $F_{n-1}$ exactly for powers of two.** Let $n \ge 1$, let $\bar P_n$ be the
Kassel–Reutenauer polynomial, and let $F_{n-1} = 1 + \sum_{k=1}^{n-1} \bar T_k$ be the partial
sum of the monic Chebyshev polynomials. Then $\bar P_n = F_{n-1}$ if and only if $n = 2^k$ for
some natural number $k$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 4.5
(`jis-2026-26.4.4-cor-17`). -/
public theorem_wanted kasselReutenauerPoly_eq_chebyshevCPartialSum_iff (n : ℕ) (hn : 1 ≤ n) :
    kasselReutenauerPoly n = chebyshevCPartialSum (n - 1) ↔ ∃ k : ℕ, n = 2 ^ k

/-- **$C_n(q)/q^n$ as a sum over the solutions of $h(h + 1 + 2a) = 2n$.** Let $n \ge 1$, let
$\bar P_n$ be the Kassel–Reutenauer polynomial, and write $C_n(q)/q^n$ for the Laurent polynomial
$(q - 2 + q^{-1})\,\bar P_n(q + q^{-1})$ in $\mathbb{Z}[q, q^{-1}]$. Then
$$\frac{C_n(q)}{q^n} = \sum_{(h, a)} (-1)^h \left(q^a + q^{-a}\right),$$
where the sum runs over the pairs of integers $(h, a)$ with $1 \le h \le 2n$, $-n \le a \le n$
and $h(h + 1 + 2a) = 2n$. Moreover, if $h, h'$ are positive integers and $a, a'$ are
integers with $h(h + 1 + 2a) = 2n$, $h'(h' + 1 + 2a') = 2n$ and $|a| = |a'|$, then $h = h'$
and $a = a'$.

Every pair of integers $(h, a)$ with $h \ge 1$ and $h(h + 1 + 2a) = 2n$ satisfies $h \le 2n$
and $|a| \le n$, so the sum runs over all such pairs.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Lemma 5.2
(`jis-2026-26.4.4-lem-22`). -/
public theorem_wanted kasselReutenauer_C_div_pow_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    (LaurentPolynomial.T 1 - 2 + LaurentPolynomial.T (-1)) *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (kasselReutenauerPoly n) =
      ∑ p ∈ (Finset.Icc 1 (2 * n) ×ˢ Finset.Icc (-(n : ℤ)) n).filter
          (fun p : ℕ × ℤ => (p.1 : ℤ) * (p.1 + 1 + 2 * p.2) = 2 * n),
        (-1) ^ p.1 * (LaurentPolynomial.T p.2 + LaurentPolynomial.T (-p.2)) ∧
    ∀ h h' : ℕ, ∀ a a' : ℤ, 1 ≤ h → 1 ≤ h' → (h : ℤ) * (h + 1 + 2 * a) = 2 * n →
      (h' : ℤ) * (h' + 1 + 2 * a') = 2 * n → |a| = |a'| → h = h' ∧ a = a'

/-- **Increasing-sequence and odd-divisor formulas for $C_n(q)/q^n$.** Let $n \ge 1$, let
$\bar P_n$ be the Kassel–Reutenauer polynomial, and write $C_n(q)/q^n$ for the Laurent polynomial
$(q - 2 + q^{-1})\,\bar P_n(q + q^{-1})$ in $\mathbb{Z}[q, q^{-1}]$. For integers $h \ge 1$ and
$a$ let $IS(a, h) = \{a + 1, \dots, a + h\}$.

(i) We have
$$\frac{C_n(q)}{q^n} = \sum_{(h, a)} (-1)^h \left(q^a + q^{-a}\right),$$
where the sum runs over the pairs of integers $(h, a)$ with $1 \le h \le 2n$ and $-n \le a \le n$
such that the elements of $IS(a, h)$ sum to $n$. Moreover, if $h, h' \ge 1$ and $a, a'$ are
integers such that the elements of $IS(a, h)$ and those of $IS(a', h')$ both sum to $n$, and
$|a| = |a'|$, then $h = h'$ and $a = a'$.

(ii) For an odd divisor $d$ of $n$ put $u_d = n/d - (d - 1)/2$ and $v_d = n/d - (d + 1)/2$. Then
$$\frac{C_n(q)}{q^n} = \sum_{d \mid n,\ d \text{ odd}} (q^{u_d} + q^{-u_d} - q^{v_d} - q^{-v_d}),$$
and in the list of the exponents $u_d, -u_d, v_d, -v_d$ over all odd divisors $d$ of $n$, the
nonzero entries are pairwise distinct.

Every pair $(h, a)$ with $h \ge 1$ such that the elements of $IS(a, h)$ sum to $n$ satisfies
$h \le 2n$ and $|a| \le n$, so the sum in (i) runs over all such sequences.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Theorem 5.3
(`jis-2026-26.4.4-thm-23`). -/
public theorem_wanted kasselReutenauer_C_div_pow_increasingSequences (n : ℕ) (hn : 1 ≤ n) :
    ((LaurentPolynomial.T 1 - 2 + LaurentPolynomial.T (-1)) *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (kasselReutenauerPoly n) =
      ∑ p ∈ (Finset.Icc 1 (2 * n) ×ˢ Finset.Icc (-(n : ℤ)) n).filter
          (fun p : ℕ × ℤ => ∑ j ∈ Finset.Icc (p.2 + 1) (p.2 + p.1), j = n),
        (-1) ^ p.1 * (LaurentPolynomial.T p.2 + LaurentPolynomial.T (-p.2))) ∧
    (∀ h h' : ℕ, ∀ a a' : ℤ, 1 ≤ h → 1 ≤ h' → ∑ j ∈ Finset.Icc (a + 1) (a + h), j = n →
      ∑ j ∈ Finset.Icc (a' + 1) (a' + h'), j = n → |a| = |a'| → h = h' ∧ a = a') ∧
    ((LaurentPolynomial.T 1 - 2 + LaurentPolynomial.T (-1)) *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (kasselReutenauerPoly n) =
      ∑ d ∈ (Nat.divisors n).filter Odd,
        (LaurentPolynomial.T (((n / d : ℕ) : ℤ) - ((d - 1) / 2 : ℕ)) +
          LaurentPolynomial.T (-((n / d : ℕ) : ℤ) + ((d - 1) / 2 : ℕ)) -
          LaurentPolynomial.T (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)) -
          LaurentPolynomial.T (-((n / d : ℕ) : ℤ) + ((d + 1) / 2 : ℕ)))) ∧
    ((((Nat.divisors n).filter Odd).val.bind (fun d =>
        ({((n / d : ℕ) : ℤ) - ((d - 1) / 2 : ℕ), -((n / d : ℕ) : ℤ) + ((d - 1) / 2 : ℕ),
          ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ), -((n / d : ℕ) : ℤ) + ((d + 1) / 2 : ℕ)} :
          Multiset ℤ))).filter (· ≠ 0)).Nodup

/-- **The absolute coefficient sum of $C_n$ counts odd divisors.** Let $n \ge 1$, let $\bar P_n$ be
the Kassel–Reutenauer polynomial, and write $C_n(q)/q^n$ for the Laurent polynomial
$(q - 2 + q^{-1})\,\bar P_n(q + q^{-1})$ in $\mathbb{Z}[q, q^{-1}]$. Then the sum of the absolute
values of the coefficients of $C_n(q)/q^n$ equals four times the number of odd divisors of $n$.

Multiplying by $q^n$ does not change the coefficients, so this is the source's statement about
the polynomial $C_n(q)$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 5.4
(`jis-2026-26.4.4-cor-24`). -/
public theorem_wanted kasselReutenauer_C_abs_coeff_sum (n : ℕ) (hn : 1 ≤ n) :
    ((LaurentPolynomial.T 1 - 2 + LaurentPolynomial.T (-1)) *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (kasselReutenauerPoly n)).coeff.sum (fun _ c => |c|) =
      4 * (((Nat.divisors n).filter Odd).card : ℤ)

/-- **Laurent polynomial identity for the partial sums of Chebyshev polynomials.** Let
$F_r = 1 + \sum_{k=1}^{r} \bar T_k \in \mathbb{Z}[X]$ be the partial sums of the monic Chebyshev
polynomials $\bar T_k$ ($\bar T_0 = 2$, $\bar T_1 = X$, $\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$).
For every natural number $r$, in the ring $\mathbb{Z}[q, q^{-1}]$ of Laurent polynomials,
$$q^{r+1} + q^{-r-1} - q^r - q^{-r} = q^{-1} (q - 1)^2 F_r(q + q^{-1}).$$

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Lemma 6.1
(`jis-2026-26.4.4-lem-26`). -/
public theorem_wanted chebyshevCPartialSum_laurent_identity (r : ℕ) :
    (LaurentPolynomial.T ((r : ℤ) + 1) + LaurentPolynomial.T (-(r : ℤ) - 1) -
        LaurentPolynomial.T (r : ℤ) - LaurentPolynomial.T (-(r : ℤ)) : LaurentPolynomial ℤ) =
      LaurentPolynomial.T (-1) * (LaurentPolynomial.T 1 - 1) ^ 2 *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (chebyshevCPartialSum r)

/-- **Increasing-sequence formula for the Kassel–Reutenauer polynomials.** Let $n \ge 1$ and
work in the ring $\mathbb{Z}[q, q^{-1}]$ of Laurent polynomials. For integers $a$ and $h$ let
$IS(a, h) = \{a+1, \dots, a+h\}$. For an odd divisor $d$ of $n$ put $r_n(d) = n/d - (d+1)/2$,
$A_d = IS(r_n(d), d)$ and $\check A_d = IS(-r_n(d) - 1, 2n/d)$. Then the Kassel–Reutenauer
polynomial $\bar P_n$ satisfies
$$
\bar P_n(q + q^{-1}) = \sum_{d \mid n,\ d \text{ odd},\ r_n(d) \ge 0}\
\sum_{i \in \check A_d \setminus A_d} q^i -
\sum_{d \mid n,\ d \text{ odd},\ r_n(d) < 0}\ \sum_{i \in A_d \setminus \check A_d} q^i.
$$

The left-hand side is the paper's $P_n(q)/q^{n-1}$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 6.2
(`jis-2026-26.4.4-prop-27`). -/
public theorem_wanted kasselReutenauerPoly_laurent_increasingSequences (n : ℕ) (hn : 1 ≤ n) :
    aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
        (kasselReutenauerPoly n) =
      ∑ d ∈ (Nat.divisors n).filter (fun d => Odd d ∧ 0 ≤ ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)),
          ∑ i ∈ Finset.Icc (-(((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)))
                (-(((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)) - 1 + ((2 * n / d : ℕ) : ℤ)) \
              Finset.Icc (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) + 1)
                (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) + d),
            LaurentPolynomial.T i -
        ∑ d ∈ (Nat.divisors n).filter (fun d => Odd d ∧ ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) < 0),
          ∑ i ∈ Finset.Icc (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) + 1)
                (((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ) + d) \
              Finset.Icc (-(((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)))
                (-(((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)) - 1 + ((2 * n / d : ℕ) : ℤ)),
            LaurentPolynomial.T i

/-- **Zeta function of the Hilbert scheme of points on the two-dimensional torus.** Let $p$ be a
prime, $k \ge 1$, $q = p^k$ and $n \ge 1$. For $m \ge 1$ let $\mathbb{F}_{q^m}$ be the field with
$q^m$ elements and let $N_m$ be the number of ideals $I$ of the Laurent polynomial ring
$\mathbb{F}_{q^m}[x^{\pm 1}, y^{\pm 1}]$ (the group algebra of $\mathbb{Z} \times \mathbb{Z}$)
such that the quotient by $I$ has dimension $n$ over $\mathbb{F}_{q^m}$; this is the number of
$\mathbb{F}_{q^m}$-points of the Hilbert scheme $H^n$ of $n$ points on the torus. For an odd
divisor $d$ of $n$ put $r_n(d) = n/d - (d + 1)/2$, $a_d = n + r_n(d)$ and $b_d = n - r_n(d)$.
Then the zeta function $Z(t) = \exp\big(\sum_{m \ge 1} N_m t^m / m\big)$, a formal power series
with rational coefficients, is
$$Z(t) = \prod_{d} \frac{(1-q^{a_d}t)(1-q^{b_d}t)}{(1-q^{a_d+1}t)(1-q^{b_d-1}t)},$$
the product running over the odd divisors $d$ of $n$.

The exponents $a_d$, $b_d$, $a_d + 1$ and $b_d - 1$ are nonnegative integers.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of
Integer Sequences 29 (2026), Article 26.4.4, Proposition 5.5 (`jis-2026-26.4.4-prop-25`). -/
public theorem_wanted hilbertSchemeTorus_zeta_eq_prod (p k n : ℕ) [Fact p.Prime] (hk : 0 < k)
    (hn : 1 ≤ n) :
    let q : ℚ := (p : ℚ) ^ k
    let N : ℕ → ℕ := fun m =>
      Nat.card {I : Ideal (AddMonoidAlgebra (GaloisField p (k * m)) (ℤ × ℤ)) //
        Module.finrank (GaloisField p (k * m))
          (AddMonoidAlgebra (GaloisField p (k * m)) (ℤ × ℤ) ⧸ I) = n}
    let r : ℕ → ℤ := fun d => ((n / d : ℕ) : ℤ) - ((d + 1) / 2 : ℕ)
    PowerSeries.subst (PowerSeries.mk fun m : ℕ => if m = 0 then (0 : ℚ) else (N m : ℚ) / m)
        (PowerSeries.exp ℚ) =
      ∏ d ∈ n.divisors.filter Odd,
        (1 - PowerSeries.C (q ^ ((n : ℤ) + r d)) * PowerSeries.X) *
          (1 - PowerSeries.C (q ^ ((n : ℤ) - r d)) * PowerSeries.X) *
          ((1 - PowerSeries.C (q ^ ((n : ℤ) + r d + 1)) * PowerSeries.X) *
            (1 - PowerSeries.C (q ^ ((n : ℤ) - r d - 1)) * PowerSeries.X))⁻¹

end

end MetaMathlibExt
