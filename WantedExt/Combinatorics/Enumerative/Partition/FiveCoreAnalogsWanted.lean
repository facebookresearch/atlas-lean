/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import MathlibExt.Data.Set.Density
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Arithmetic identities for analogs of the 5-core partition function

Statements from Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for
Some Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5 (arXiv:2409.02034).

Notation (Section 1 of the paper): `f(a, b) = ∑_{n ∈ ℤ} a^{n(n+1)/2} b^{n(n-1)/2}` is Ramanujan's
general theta function, `φ(q) = f(q, q)`, `ψ(q) = f(q, q^3)`, `f(-q) = f_1` and
`f_k = (q^k; q^k)_∞ = qEulerProduct k`; the substitution `q ↦ -q` is `PowerSeries.rescale (-1)`
and `q ↦ q^k` is `PowerSeries.expand k`. The paper's sequences are defined by their generating
functions `∑ c_5(n) q^n = f_5^5 / f_1`, `∑ ā_5(n) q^n = φ^5(-q^5) / φ(-q)` and
`∑ b̄_5(n) q^n = ψ^5(-q^5) / ψ(-q)`. Identities between quotients of power series are stated
with denominators cleared.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Ramanujan's general theta function at powers of q.** For positive integers $i$ and $j$,
$f(q^i, q^j)$ is the integer power series $\sum_{n \in \mathbb{Z}} q^{i n(n+1)/2 + j n(n-1)/2}$,
that is, Ramanujan's $f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ at $a = q^i$
and $b = q^j$.

Since $i, j \ge 1$, only integers $n$ with $|n| \le m$ contribute to the coefficient of $q^m$, so
each coefficient is a finite count.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1 (definition of `f(a, b)`). -/
def ramanujanThetaPow (i j : ℕ+) : ℤ⟦X⟧ :=
  mk fun m => (((Finset.Icc (-(m : ℤ)) m).filter fun n =>
    ((i : ℕ) : ℤ) * (n * (n + 1) / 2) + ((j : ℕ) : ℤ) * (n * (n - 1) / 2) = m).card : ℤ)

/-- **The 5-core counts.** For a natural number $n$, $c_5(n)$ is the coefficient of $q^n$ in the
integer power series $f_5^5 / f_1$, where $f_k = \prod_{m \ge 1} (1 - q^{km})$ is the Euler
product. The series $f_5^5 / f_1$ is the generating function of 5-core partitions.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation for `∑ c_t(n) q^n` with `t = 5` (OEIS A053723). -/
noncomputable def fiveCoreCount (n : ℕ) : ℤ :=
  coeff n (qEulerProduct 5 ^ 5 * invOfUnit (pentagonalSeries ℤ) 1)

/-- **The φ-analog of the 5-core partition function.** Let
$\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ be Ramanujan's theta function. For a natural
number $n$, $\bar a_5(n)$ is the coefficient of $q^n$ in the integer power series
$\varphi^5(-q^5)/\varphi(-q)$ (the denominator has constant term $1$, so the quotient is a power
series).

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (at) (OEIS A368490). -/
noncomputable def phiFiveCoreAnalog (n : ℕ) : ℤ :=
  coeff n (expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 1)) ^ 5 *
    invOfUnit (rescale (-1) (ramanujanThetaPow 1 1)) 1)

/-- **The ψ-analog of the 5-core partition function.** Let
$\psi(q) = \sum_{n \in \mathbb{Z}} q^{2n^2 - n} = \sum_{n \ge 0} q^{n(n+1)/2}$ be Ramanujan's theta
function. For a natural number $n$, $\bar b_5(n)$ is the coefficient of $q^n$ in the integer
power series $\psi^5(-q^5)/\psi(-q)$ (the denominator has constant term $1$, so the quotient is
a power series).

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (bt) (OEIS A368495). -/
noncomputable def psiFiveCoreAnalog (n : ℕ) : ℤ :=
  coeff n (expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 3)) ^ 5 *
    invOfUnit (rescale (-1) (ramanujanThetaPow 1 3)) 1)

/-- **Constant term of Ramanujan's theta function.** For all positive integers $i$ and $j$, the
integer power series $f(q^i, q^j) = \sum_{n \in \mathbb{Z}} q^{i n(n+1)/2 + j n(n-1)/2}$ has
constant term $1$: only $n = 0$ contributes to $q^0$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1. -/
theorem constantCoeff_ramanujanThetaPow (i j : ℕ+) : constantCoeff (ramanujanThetaPow i j) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ramanujanThetaPow, coeff_mk]
  simp [Finset.filter_singleton]

/-- **Generating function of the 5-core counts.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ and
let $c_5(n)$ be the coefficient of $q^n$ in $f_5^5 / f_1$. Then, as integer power series,
$\left(\sum_{n \ge 0} c_5(n) q^n\right) f_1 = f_5^5$, where $f_1$ is written as the pentagonal
series $\sum_{j \in \mathbb{Z}} (-1)^j q^{j(3j-1)/2}$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1. -/
theorem mk_fiveCoreCount_mul : mk fiveCoreCount * pentagonalSeries ℤ = qEulerProduct 5 ^ 5 := by
  have h0 : constantCoeff (pentagonalSeries ℤ) = ((1 : ℤˣ) : ℤ) := by
    have := coeff_pentagonalSeries_pentagonal (R := ℤ) 0
    rw [show pentagonal 0 = 0 by simp [pentagonal_def], coeff_zero_eq_constantCoeff_apply] at this
    simpa using this
  have hmk : mk fiveCoreCount = qEulerProduct 5 ^ 5 * invOfUnit (pentagonalSeries ℤ) 1 := by
    ext n; simp [fiveCoreCount]
  rw [hmk, mul_assoc, invOfUnit_mul _ _ h0, mul_one]

/-- **Generating function of the $\varphi$-analog of the 5-core counts.** Let
$\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ and let $\bar a_5(n)$ be the coefficient of $q^n$
in $\varphi(-q^5)^5 / \varphi(-q)$. Then, as integer power series,
$\left(\sum_{n \ge 0} \bar a_5(n) q^n\right) \varphi(-q) = \varphi(-q^5)^5$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (at). -/
theorem mk_phiFiveCoreAnalog_mul :
    mk phiFiveCoreAnalog * rescale (-1) (ramanujanThetaPow 1 1) =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 1)) ^ 5 := by
  have h0 : constantCoeff (rescale (-1) (ramanujanThetaPow 1 1)) = ((1 : ℤˣ) : ℤ) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_ramanujanThetaPow]
    simp
  have hmk : mk phiFiveCoreAnalog =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 1)) ^ 5 *
      invOfUnit (rescale (-1) (ramanujanThetaPow 1 1)) 1 := by
    ext n; simp [phiFiveCoreAnalog]
  rw [hmk, mul_assoc, invOfUnit_mul _ _ h0, mul_one]

/-- **Generating function of the $\psi$-analog of the 5-core counts.** Let
$\psi(q) = \sum_{n \in \mathbb{Z}} q^{n(2n-1)}$ and let $\bar b_5(n)$ be the coefficient of $q^n$
in $\psi(-q^5)^5 / \psi(-q)$. Then, as integer power series,
$\left(\sum_{n \ge 0} \bar b_5(n) q^n\right) \psi(-q) = \psi(-q^5)^5$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Section 1, equation (bt). -/
theorem mk_psiFiveCoreAnalog_mul :
    mk psiFiveCoreAnalog * rescale (-1) (ramanujanThetaPow 1 3) =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 3)) ^ 5 := by
  have h0 : constantCoeff (rescale (-1) (ramanujanThetaPow 1 3)) = ((1 : ℤˣ) : ℤ) := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_ramanujanThetaPow]
    simp
  have hmk : mk psiFiveCoreAnalog =
      expand 5 (by norm_num) (rescale (-1) (ramanujanThetaPow 1 3)) ^ 5 *
      invOfUnit (rescale (-1) (ramanujanThetaPow 1 3)) 1 := by
    ext n; simp [psiFiveCoreAnalog]
  rw [hmk, mul_assoc, invOfUnit_mul _ _ h0, mul_one]


local notation "𝔣" => qEulerProduct
local notation "Φ" => ramanujanThetaPow 1 1
local notation "Ψ" => ramanujanThetaPow 1 3

/-- **The $\varphi$-analog of the 5-core counts in terms of the 5-core counts.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, let $c_5(n)$ be the coefficient of $q^n$ in $f_5^5 / f_1$,
let $\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ and let $\bar a_5(n)$ be the coefficient of
$q^n$ in $\varphi(-q^5)^5 / \varphi(-q)$. For every natural number $n$,
$\bar a_5(5n+2) = 4\, c_5(5n+1)$, $\bar a_5(5n+3) = 4\, c_5(5n+2)$,
$\bar a_5(10n+1) = 2\, c_5(10n)$, $\bar a_5(10n+9) = 2\, c_5(10n+8)$,
$\bar a_5(20n+6) = 10\, c_5(10n+2)$ and $\bar a_5(20n+14) = 10\, c_5(10n+6)$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 2 (`jis-2024-24.4.5-thm-2`). -/
public theorem_wanted phiFiveCoreAnalog_eq_fiveCoreCount (n : ℕ) :
    phiFiveCoreAnalog (5 * n + 2) = 4 * fiveCoreCount (5 * n + 1) ∧
      phiFiveCoreAnalog (5 * n + 3) = 4 * fiveCoreCount (5 * n + 2) ∧
      phiFiveCoreAnalog (10 * n + 1) = 2 * fiveCoreCount (10 * n) ∧
      phiFiveCoreAnalog (10 * n + 9) = 2 * fiveCoreCount (10 * n + 8) ∧
      phiFiveCoreAnalog (20 * n + 6) = 10 * fiveCoreCount (10 * n + 2) ∧
      phiFiveCoreAnalog (20 * n + 14) = 10 * fiveCoreCount (10 * n + 6)

/-- **Recurrence for the $\varphi$-analog of the 5-core counts along powers of 5.** Let
$\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ and let $\bar a_5(n)$ be the coefficient of $q^n$
in $\varphi(-q^5)^5 / \varphi(-q)$. For every natural number $k \ge 2$ and every natural number
$n$, $\bar a_5(5^k n) = \frac{5^k - 1}{4}\, \bar a_5(5n) - \frac{5^k - 5}{4}\, \bar a_5(n)$.
Both quotients are integers.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 2 (`jis-2024-24.4.5-thm-2`). -/
public theorem_wanted phiFiveCoreAnalog_five_pow_mul {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    phiFiveCoreAnalog (5 ^ k * n) =
      ((5 ^ k - 1) / 4 : ℤ) * phiFiveCoreAnalog (5 * n) -
        ((5 ^ k - 5) / 4 : ℤ) * phiFiveCoreAnalog n

/-- **Congruences for the $\varphi$-analog of the 5-core counts.** Let
$\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ and let $\bar a_5(n)$ be the coefficient of $q^n$
in $\varphi(-q^5)^5 / \varphi(-q)$. For every natural number $k \ge 2$ and every natural number
$n$, $\bar a_5(20n+6) \equiv 0 \pmod{10}$, $\bar a_5(20n+14) \equiv 0 \pmod{10}$ and
$4\, \bar a_5(5^k n) \equiv 5\, \bar a_5(n) - \bar a_5(5n) \pmod{5^k}$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Corollary 3 (`jis-2024-24.4.5-cor-3`). -/
public theorem_wanted phiFiveCoreAnalog_congruences {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    phiFiveCoreAnalog (20 * n + 6) ≡ 0 [ZMOD 10] ∧
      phiFiveCoreAnalog (20 * n + 14) ≡ 0 [ZMOD 10] ∧
      4 * phiFiveCoreAnalog (5 ^ k * n) ≡ 5 * phiFiveCoreAnalog n - phiFiveCoreAnalog (5 * n)
        [ZMOD 5 ^ k]

/-- **A doubling identity for the ψ-analog of the 5-core partition function.** Let
$\bar b_5(n)$ be the coefficient of $q^n$ in $\psi^5(-q^5)/\psi(-q)$, where
$\psi(q) = \sum_{n \ge 0} q^{n(n+1)/2}$. For every natural number $n$,
$\bar b_5(4n+3) = 2 \bar b_5(2n)$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 4 (`jis-2024-24.4.5-thm-4`). -/
public theorem_wanted psiFiveCoreAnalog_four_mul_add_three (n : ℕ) :
    psiFiveCoreAnalog (4 * n + 3) = 2 * psiFiveCoreAnalog (2 * n)

/-- **A recurrence for the ψ-analog of the 5-core partition function along powers of 5.** Let
$\bar b_5(n)$ be the coefficient of $q^n$ in $\psi^5(-q^5)/\psi(-q)$, where
$\psi(q) = \sum_{n \ge 0} q^{n(n+1)/2}$. For every integer $k \ge 2$ and every natural number
$n$, $\bar b_5(5^k(n+3) - 3) = \frac{5^k - 1}{4} \bar b_5(5n+12) - \frac{5^k - 5}{4} \bar b_5(n)$;
both quotients are integers.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 4 (`jis-2024-24.4.5-thm-4`). -/
public theorem_wanted psiFiveCoreAnalog_five_pow_mul {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    psiFiveCoreAnalog (5 ^ k * (n + 3) - 3) =
      ((5 ^ k - 1) / 4 : ℤ) * psiFiveCoreAnalog (5 * n + 12) -
        ((5 ^ k - 5) / 4 : ℤ) * psiFiveCoreAnalog n

/-- **Identities relating the ψ-analog to the 5-core counts and the φ-analog.** Let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, $\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ and
$\psi(q) = \sum_{n \ge 0} q^{n(n+1)/2}$, and let $c_5(n)$, $\bar a_5(n)$ and $\bar b_5(n)$ be the
coefficients of $q^n$ in $f_5^5/f_1$, $\varphi^5(-q^5)/\varphi(-q)$ and $\psi^5(-q^5)/\psi(-q)$.
Then for every natural number $n$:
$\bar b_5(4n+1) = c_5(n) - 2 \bar b_5(2n-1)$, where the last term is read as $0$ for $n = 0$;
$2 \bar b_5(10n) = c_5(10n+2)$; $\bar b_5(10n+1) = c_5(5n+1)$;
$4 \bar b_5(10n+2) = \bar a_5(2n+1) + 2 c_5(2n)$; $\bar b_5(10n+3) = c_5(5n+2)$;
$2 \bar b_5(10n+4) = c_5(10n+6)$; $\bar b_5(10n+6) = \bar b_5(10n+8) = 0$;
$\bar b_5(20n+5) = -c_5(5n+1)$; $2 \bar b_5(20n+7) = \bar a_5(2n+1) + 2 c_5(2n)$;
$\bar b_5(20n+9) = -c_5(5n+2)$; and $\bar b_5(20n+15) = \bar b_5(20n+19) = 0$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Theorem 5 (`jis-2024-24.4.5-thm-5`). -/
public theorem_wanted psiFiveCoreAnalog_identities (n : ℕ) :
    psiFiveCoreAnalog (4 * n + 1) =
        fiveCoreCount n - 2 * (if n = 0 then 0 else psiFiveCoreAnalog (2 * n - 1)) ∧
      2 * psiFiveCoreAnalog (10 * n) = fiveCoreCount (10 * n + 2) ∧
      psiFiveCoreAnalog (10 * n + 1) = fiveCoreCount (5 * n + 1) ∧
      4 * psiFiveCoreAnalog (10 * n + 2) =
        phiFiveCoreAnalog (2 * n + 1) + 2 * fiveCoreCount (2 * n) ∧
      psiFiveCoreAnalog (10 * n + 3) = fiveCoreCount (5 * n + 2) ∧
      2 * psiFiveCoreAnalog (10 * n + 4) = fiveCoreCount (10 * n + 6) ∧
      psiFiveCoreAnalog (10 * n + 6) = 0 ∧
      psiFiveCoreAnalog (10 * n + 8) = 0 ∧
      psiFiveCoreAnalog (20 * n + 5) = -fiveCoreCount (5 * n + 1) ∧
      2 * psiFiveCoreAnalog (20 * n + 7) =
        phiFiveCoreAnalog (2 * n + 1) + 2 * fiveCoreCount (2 * n) ∧
      psiFiveCoreAnalog (20 * n + 9) = -fiveCoreCount (5 * n + 2) ∧
      psiFiveCoreAnalog (20 * n + 15) = 0 ∧
      psiFiveCoreAnalog (20 * n + 19) = 0

/-- **Sign densities of the ψ-analog of the 5-core partition function.** Let
$\bar b_5(n)$ be the coefficient of $q^n$ in $\psi^5(-q^5)/\psi(-q)$, where
$\psi(q) = \sum_{n \ge 0} q^{n(n+1)/2}$, and let the lower density of a set $S$ of natural numbers
be $\liminf_{N \to \infty} |S \cap \{0, \dots, N - 1\}|/N$. The set of positive integers $n$ with
$\bar b_5(n) = 0$ has lower density at least $3/10$, the set of positive $n$ with
$\bar b_5(n) > 0$ has lower density at least $52/100$, and the set of positive $n$ with
$\bar b_5(n) < 0$ has lower density at least $1/10$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Corollary 6 (`jis-2024-24.4.5-cor-6`). -/
public theorem_wanted psiFiveCoreAnalog_sign_densities :
    3 / 10 ≤ {n : ℕ | 0 < n ∧ psiFiveCoreAnalog n = 0}.lowerDensity ∧
      52 / 100 ≤ {n : ℕ | 0 < n ∧ 0 < psiFiveCoreAnalog n}.lowerDensity ∧
      1 / 10 ≤ {n : ℕ | 0 < n ∧ psiFiveCoreAnalog n < 0}.lowerDensity

/-- **The $\varphi$-analog in terms of the $\psi$-analog of the 5-core counts.** Let
$\varphi(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$ and $\psi(q) = \sum_{n \in \mathbb{Z}} q^{n(2n-1)}$,
and let $\bar a_5(n)$ and $\bar b_5(n)$ be the coefficients of $q^n$ in
$\varphi(-q^5)^5 / \varphi(-q)$ and $\psi(-q^5)^5 / \psi(-q)$ respectively. For every natural
number $n$, $\bar a_5(20n+6) = 20\, \bar b_5(10n)$ and
$\bar a_5(20n+14) = 20\, \bar b_5(10n+4)$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Corollary 7 (`jis-2024-24.4.5-cor-7`). -/
public theorem_wanted phiFiveCoreAnalog_eq_twenty_mul_psiFiveCoreAnalog (n : ℕ) :
    phiFiveCoreAnalog (20 * n + 6) = 20 * psiFiveCoreAnalog (10 * n) ∧
      phiFiveCoreAnalog (20 * n + 14) = 20 * psiFiveCoreAnalog (10 * n + 4)

/-- **Congruences for the ψ-analog of the 5-core partition function.** Let
$\bar b_5(n)$ be the coefficient of $q^n$ in $\psi^5(-q^5)/\psi(-q)$, where
$\psi(q) = \sum_{n \ge 0} q^{n(n+1)/2}$. For every integer $k \ge 2$ and every natural number
$n$, $4 \bar b_5(5^k(n+3) - 3) \equiv 5 \bar b_5(n) - \bar b_5(5n+12) \pmod{5^k}$, and both
$\bar b_5(5^k(20n+18) - 3)$ and $\bar b_5(5^k(20n+22) - 3)$ are divisible by $(5^k - 1)/4$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Corollary 8 (`jis-2024-24.4.5-cor-8`). -/
public theorem_wanted psiFiveCoreAnalog_congruences {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    4 * psiFiveCoreAnalog (5 ^ k * (n + 3) - 3) ≡
        5 * psiFiveCoreAnalog n - psiFiveCoreAnalog (5 * n + 12) [ZMOD 5 ^ k] ∧
      psiFiveCoreAnalog (5 ^ k * (20 * n + 18) - 3) ≡ 0 [ZMOD (5 ^ k - 1) / 4] ∧
      psiFiveCoreAnalog (5 ^ k * (20 * n + 22) - 3) ≡ 0 [ZMOD (5 ^ k - 1) / 4]

/-- **Theta-function identities of level 5.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$,
$f(q) = \prod_{m \ge 1} (1 - (-q)^m)$ (so that $f(-q) = f_1$),
$\chi(-q) = \prod_{m \ge 0} (1 - q^{2m+1})$ and $\chi(q) = \prod_{m \ge 0} (1 + q^{2m+1})$. Let
$f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's general theta
function, $\varphi(q) = f(q, q)$ and $\psi(q) = f(q, q^3)$. Then, as integer power series in
$q$ (every denominator below has constant term $1$):
$\varphi^5(q^5)/\varphi(q) + 4q f^5(q^5)/f(q) = \varphi(q) \varphi^3(q^5)$;
$\varphi^2(q) - \varphi^2(q^5) = 4q \chi(q) f_5 f_{20}$;
$\psi^5(-q^5)/\psi(-q) - \psi^5(q^5)/\psi(q) = 4q^3 \psi^5(q^{10})/\psi(q^2) + 2q f_{20}^5/f_4$;
$\psi^2(q) - q \psi^2(q^5) = f_5 \varphi(-q^5)/\chi(-q) = f(q, q^4) f(q^2, q^3)$;
$f_5^5/f_1 - 4q^3 f_{20}^5/f_4 = f^5(q^5)/f(q) + 2q f_{10}^5/f_2$; and
$f_2^2/f_1^4 = f_{10}^2/f_5^4 + 4q f_2 f_{10}^5/(f_1^3 f_5^5)$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Lemma 9 (`jis-2024-24.4.5-lem-9`). -/
public theorem_wanted theta_level_five_identities :
    expand 5 (by norm_num) Φ ^ 5 * rescale (-1) (𝔣 1) +
        4 * X * expand 5 (by norm_num) (rescale (-1) (𝔣 1)) ^ 5 * Φ =
      Φ ^ 2 * expand 5 (by norm_num) Φ ^ 3 * rescale (-1) (𝔣 1) ∧
    Φ ^ 2 - expand 5 (by norm_num) Φ ^ 2 =
      4 * X * rescale (-1) (∏' m : ℕ, (1 - X ^ (2 * m + 1)) : ℤ⟦X⟧) * 𝔣 5 * 𝔣 20 ∧
    expand 5 (by norm_num) (rescale (-1) Ψ) ^ 5 * Ψ * expand 2 (by norm_num) Ψ * 𝔣 4 -
        expand 5 (by norm_num) Ψ ^ 5 * rescale (-1) Ψ * expand 2 (by norm_num) Ψ * 𝔣 4 =
      4 * X ^ 3 * expand 10 (by norm_num) Ψ ^ 5 * rescale (-1) Ψ * Ψ * 𝔣 4 +
        2 * X * 𝔣 20 ^ 5 * rescale (-1) Ψ * Ψ * expand 2 (by norm_num) Ψ ∧
    (Ψ ^ 2 - X * expand 5 (by norm_num) Ψ ^ 2) * (∏' m : ℕ, (1 - X ^ (2 * m + 1)) : ℤ⟦X⟧) =
      𝔣 5 * expand 5 (by norm_num) (rescale (-1) Φ) ∧
    Ψ ^ 2 - X * expand 5 (by norm_num) Ψ ^ 2 = ramanujanThetaPow 1 4 * ramanujanThetaPow 2 3 ∧
    𝔣 5 ^ 5 * 𝔣 4 * rescale (-1) (𝔣 1) * 𝔣 2 -
        4 * X ^ 3 * 𝔣 20 ^ 5 * 𝔣 1 * rescale (-1) (𝔣 1) * 𝔣 2 =
      expand 5 (by norm_num) (rescale (-1) (𝔣 1)) ^ 5 * 𝔣 1 * 𝔣 4 * 𝔣 2 +
        2 * X * 𝔣 10 ^ 5 * 𝔣 1 * 𝔣 4 * rescale (-1) (𝔣 1) ∧
    𝔣 2 ^ 2 * 𝔣 5 ^ 5 = 𝔣 10 ^ 2 * 𝔣 5 * 𝔣 1 ^ 4 + 4 * X * 𝔣 2 * 𝔣 10 ^ 5 * 𝔣 1

/-- **5-dissections of Ramanujan's theta functions φ and ψ.** Let
$f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's general theta
function, $\varphi(q) = f(q, q)$ and $\psi(q) = f(q, q^3)$. As integer power series in $q$,
$\varphi(q) = \varphi(q^{25}) + 2q f(q^{15}, q^{35}) + 2q^4 f(q^5, q^{45})$ and
$\psi(q) = f(q^{10}, q^{15}) + q f(q^5, q^{20}) + q^3 \psi(q^{25})$.

Lemma 10 of the source also gives a 5-dissection of $\prod_{m \ge 1} (1 - q^m)^{-1}$ via the
Rogers–Ramanujan continued fraction; that part is not included.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Lemma 10 (`jis-2024-24.4.5-lem-10`). -/
public theorem_wanted theta_five_dissections :
    Φ = expand 25 (by norm_num) Φ + 2 * X * ramanujanThetaPow 15 35 +
        2 * X ^ 4 * ramanujanThetaPow 5 45 ∧
      Ψ = ramanujanThetaPow 10 15 + X * ramanujanThetaPow 5 20 + X ^ 3 * expand 25 (by norm_num) Ψ

/-- **Two identities for the 5-core counts.** Let $f_k = \prod_{m \ge 1} (1 - q^{km})$ and let
$c_5(n)$ be the coefficient of $q^n$ in $f_5^5 / f_1$. For every natural number $n$,
$c_5(4n+1) = c_5(2n)$ and $c_5(5n+4) = 5\, c_5(n)$.

Source: Subhajit Bandyopadhyay and Nayandeep Deka Baruah, *Arithmetic Identities for Some
Analogs of the 5-Core Partition Function*, Journal of Integer Sequences 27 (2024),
Article 24.4.5, Lemma 11 (`jis-2024-24.4.5-lem-11`). -/
public theorem_wanted fiveCoreCount_identities (n : ℕ) :
    fiveCoreCount (4 * n + 1) = fiveCoreCount (2 * n) ∧
      fiveCoreCount (5 * n + 4) = 5 * fiveCoreCount n

end

end MetaMathlibExt
