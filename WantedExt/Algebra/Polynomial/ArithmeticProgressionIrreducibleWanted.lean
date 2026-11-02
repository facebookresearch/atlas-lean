/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Card

/-!
# Irreducibility of polynomials with coefficients in an arithmetic progression

Statements from Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92. For coprime positive integers `a`,
`d` and `m ≥ 2` the paper studies
`A_m(x) = a x^m + (a + d) x^(m-1) + ⋯ + (a + (m-1)d) x + (a + md)`, written inline below as
`∑ i ∈ range (m + 1), C (a + i d) X^(m - i)`. The paper writes `a_n = a + (n - 1)d`, so
`a_0 = a - d`, `a_1 = a`, `a_{m+1} = a + md`, `a_{m+2} = a + (m + 1)d`; `λ` is the positive solution
of equation (3), `a_1 x^{m+2} + a_0 x^{m+1} - a_{m+2} x - a_{m+1} = 0`, written out and passed
as a hypothesis.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- **Perron's irreducibility criterion.** Let $f = x^n + a_{n-1} x^{n-1} + \cdots + a_0$ be a
monic polynomial in $\mathbb{Z}[x]$ of degree $n \ge 1$ with $a_0 \neq 0$ and
$|a_{n-1}| > 1 + \sum_{i=0}^{n-2} |a_i|$. Then $f$ is irreducible in $\mathbb{Z}[x]$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Theorem 1 (Perron's criterion,
quoted from the paper's reference [6]) (`integers-2026-A92-thm-1`). -/
public theorem_wanted perron_irreducible {f : ℤ[X]} (hmonic : f.Monic) (hdeg : 1 ≤ f.natDegree)
    (h0 : f.coeff 0 ≠ 0)
    (hbig : 1 + ∑ i ∈ Finset.range (f.natDegree - 1), |f.coeff i| <
      |f.coeff (f.natDegree - 1)|) :
    Irreducible f

/-- **Irreducibility of polynomials with coefficients in an arithmetic progression.** Let
$m \ge 2$ and let $a$, $d$ be coprime positive integers with $m^2 d^2 < 8a$. Then the polynomial
$a x^m + (a + d) x^{m-1} + \cdots + (a + (m - 1)d) x + (a + md)$ is irreducible in
$\mathbb{Z}[x]$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Theorem 2
(`integers-2026-A92-thm-2`). -/
public theorem_wanted arithProgPoly_irreducible {m a d : ℕ} (hm : 2 ≤ m) (ha : 0 < a)
    (hd : 0 < d) (hcop : Nat.Coprime a d) (hbig : m ^ 2 * d ^ 2 < 8 * a) :
    Irreducible (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i))

/-- **The arithmetic-progression quartic is not a product of two quadratics.** Let $a$, $d$ be
coprime integers with $0 < d \le a$. Then the polynomial
$a x^4 + (a + d) x^3 + (a + 2d) x^2 + (a + 3d) x + (a + 4d)$ is not the product of two
polynomials of degree $2$ in $\mathbb{Z}[x]$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Theorem 4
(`integers-2026-A92-thm-4`). -/
public theorem_wanted arithProgPoly_four_not_mul_quadratics {a d : ℕ} (hd : 0 < d) (had : d ≤ a)
    (hcop : Nat.Coprime a d) :
    ¬ ∃ g h : ℤ[X], g.natDegree = 2 ∧ h.natDegree = 2 ∧
      ∑ i ∈ Finset.range 5, C ((a : ℤ) + i * d) * X ^ (4 - i) = g * h

/-- **Irreducibility when $d$ has a primitive-root prime factor.** Let $m \ge 2$ with $m + 1$
prime, and let $a$, $d$ be coprime positive integers. Suppose $d$ has a prime divisor $p$ that is
not divisible by $m + 1$ and whose residue modulo $m + 1$ has multiplicative order $m$ (that is,
$p$ is a primitive root modulo $m + 1$). Then the polynomial
$a x^m + (a + d) x^{m-1} + \cdots + (a + (m - 1)d) x + (a + md)$ is irreducible in
$\mathbb{Z}[x]$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 6
(`integers-2026-A92-prop-6`). -/
public theorem_wanted arithProgPoly_irreducible_of_primitiveRoot {m a d p : ℕ} (hm : 2 ≤ m)
    (hprime : (m + 1).Prime) (ha : 0 < a) (hd : 0 < d) (hcop : Nat.Coprime a d)
    (hp : p.Prime) (hpd : p ∣ d) (hpm : ¬ (m + 1) ∣ p)
    (hroot : orderOf (p : ZMod (m + 1)) = m) :
    Irreducible (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i))

/-- **The arithmetic-progression polynomial times $(x - 1)^2$.** For all natural numbers $m$, $a$,
$d$, the polynomial $A_m(x) = \sum_{i=0}^{m} (a + id) x^{m-i}$ satisfies, in $\mathbb{Z}[x]$,

$$A_m(x)(x - 1)^2 = a x^{m+2} - (a - d) x^{m+1} - (a + (m + 1)d) x + (a + md).$$

The source assumes $m$, $a$, $d$ positive.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 1 (`integers-2026-A92-lem-1`). -/
public theorem_wanted arithProgPoly_mul_sub_one_sq (m a d : ℕ) :
    (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i)) * (X - 1) ^ 2 =
      C (a : ℤ) * X ^ (m + 2) - C ((a : ℤ) - d) * X ^ (m + 1) -
        C ((a : ℤ) + (m + 1) * d) * X + C ((a : ℤ) + m * d)

/-- **Power identity at the roots of an arithmetic-progression polynomial.** Let $m$ and $a$
be natural numbers, let $d$ be a positive integer, and let
$A_m(x) = a x^m + (a + d) x^{m-1} + \cdots + (a + md)$, that is,
$A_m(x) = \sum_{i=0}^{m} (a + id) x^{m-i} \in \mathbb{Z}[x]$. If $z \in \mathbb{C}$ is a root of
$A_m$ or $z = 1$, then

$$z^{m+1} = \frac{(a + (m + 1)d) z - (a + md)}{a z - (a - d)}.$$

With the paper's notation $a_n = a + (n - 1)d$ this reads
$z^{m+1} = (a_{m+2} z - a_{m+1}) / (a_1 z - a_0)$. The denominator does not vanish at such $z$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 1, equation (2)
(`integers-2026-A92-lem-1`). -/
public theorem_wanted arithProgPoly_root_pow_eq (m a d : ℕ) (hd : 0 < d) (z : ℂ)
    (hz : aeval z (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i)) = 0 ∨ z = 1) :
    z ^ (m + 1) =
      (((a : ℂ) + (m + 1) * d) * z - ((a : ℂ) + m * d)) / ((a : ℂ) * z - ((a : ℂ) - d))

/-- **The auxiliary equation has a unique positive root, which exceeds $1$.** Let $m \ge 2$ and
let $a$, $d$ be integers with $0 < d \le a$. Then the equation
$a x^{m+2} + (a - d) x^{m+1} - (a + (m + 1)d) x - (a + md) = 0$ has exactly one positive real
solution, and every positive real solution $x$ satisfies $x > 1$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 1
(`integers-2026-A92-prop-1`). -/
public theorem_wanted arithProgPoly_eq3_existsUnique_pos {m a d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (hda : d ≤ a) :
    (∃! x : ℝ, 0 < x ∧ (a : ℝ) * x ^ (m + 2) + ((a : ℝ) - d) * x ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * x - ((a : ℝ) + m * d) = 0) ∧
    ∀ x : ℝ, 0 < x → (a : ℝ) * x ^ (m + 2) + ((a : ℝ) - d) * x ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * x - ((a : ℝ) + m * d) = 0 → 1 < x

/-- **Bound on the zeros of the arithmetic-progression polynomial.** Let $m \ge 2$, let $a$, $d$
be integers with $0 < d \le a$, and let $\lambda > 0$ be a real number with
$a \lambda^{m+2} + (a - d) \lambda^{m+1} - (a + (m + 1)d) \lambda - (a + md) = 0$. Then every
complex zero $z$ of $A_m(x) = a x^m + (a + d) x^{m-1} + \cdots + (a + md)$ satisfies
$|z| \le \lambda$, and $|z| = \lambda$ only if $z = -\lambda$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 2
(`integers-2026-A92-prop-2`). -/
public theorem_wanted arithProgPoly_root_norm_le {m a d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (hda : d ≤ a) (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) (z : ℂ)
    (hz : aeval z (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i)) = 0) :
    ‖z‖ ≤ lam ∧ (‖z‖ = lam → z = -(lam : ℂ))

/-- **Lower bound on a power of the auxiliary root.** Let $m \ge 2$, let $a$, $d$ be integers with
$0 < d \le a$, and let $\lambda > 0$ be a real number with
$a \lambda^{m+2} + (a - d) \lambda^{m+1} - (a + (m + 1)d) \lambda - (a + md) = 0$. Then
$a + md < a \lambda^m$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 2 (`integers-2026-A92-lem-2`). -/
public theorem_wanted arithProgPoly_lam_pow_gt {m a d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (hda : d ≤ a) (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) :
    (a : ℝ) + m * d < a * lam ^ m

/-- **A rational lower bound for $(1 + mx)^{1/m}$.** For every natural number $m \ge 2$ and every
real $x > 0$,

$$\frac{2 + (m + 1)x}{2 + (m - 1)x} < (1 + mx)^{1/m}.$$

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 3 (`integers-2026-A92-lem-3`). -/
public theorem_wanted one_add_mul_rpow_inv_gt {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 0 < x) :
    (2 + (m + 1) * x) / (2 + (m - 1) * x) < (1 + m * x) ^ (1 / (m : ℝ))

/-- **Strict upper bound on floors at powers of the auxiliary root.** Let $m \ge 2$, let $a$, $d$
be natural numbers with $d > 0$ and $(m + 1)d < 2a$, and let $\lambda > 0$ be a real number with
$a \lambda^{m+2} + (a - d) \lambda^{m+1} - (a + (m + 1)d) \lambda - (a + md) = 0$. Then
$\lfloor a \lambda^p \rfloor < a + pd$ for every integer $p$ with $1 \le p \le m - 1$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 4
(`integers-2026-A92-prop-4`). -/
public theorem_wanted arithProgPoly_floor_lam_pow_lt {m a d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (had : (m + 1) * d < 2 * a) (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) (p : ℕ) (hp1 : 1 ≤ p)
    (hpm : p ≤ m - 1) :
    ⌊(a : ℝ) * lam ^ p⌋ < (a : ℤ) + p * d

/-- **Exact floor at a power of the auxiliary root (single exponent).** Let $m \ge 2$, let $a$,
$d$ be positive integers, and let $p$ be an integer with $1 \le p \le m - 1$ and
$p(m - p)d^2 < 2a$. If $\lambda > 0$ is a real number with
$a \lambda^{m+2} + (a - d) \lambda^{m+1} - (a + (m + 1)d) \lambda - (a + md) = 0$, then
$\lfloor a \lambda^p \rfloor = a + pd - 1$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 5
(`integers-2026-A92-prop-5`). -/
public theorem_wanted arithProgPoly_floor_lam_pow_eq {m a d : ℕ} (hm : 2 ≤ m) (ha : 0 < a)
    (hd : 0 < d) (p : ℕ) (hp1 : 1 ≤ p) (hpm : p ≤ m - 1) (had : p * (m - p) * d ^ 2 < 2 * a)
    (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) :
    ⌊(a : ℝ) * lam ^ p⌋ = (a : ℤ) + p * d - 1

/-- **Exact floors at powers of the auxiliary root (all exponents).** Let $m \ge 2$, let $a$, $d$
be positive integers with $m^2 d^2 < 8a$, and let $\lambda > 0$ be a real number with
$a \lambda^{m+2} + (a - d) \lambda^{m+1} - (a + (m + 1)d) \lambda - (a + md) = 0$. Then
$\lfloor a \lambda^p \rfloor = a + pd - 1$ for every integer $p$ with $1 \le p \le m - 1$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 5, second statement
(`integers-2026-A92-prop-5`). -/
public theorem_wanted arithProgPoly_floor_lam_pow_eq_of_eight {m a d : ℕ} (hm : 2 ≤ m)
    (ha : 0 < a) (hd : 0 < d) (had : m ^ 2 * d ^ 2 < 8 * a) (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) (p : ℕ) (hp1 : 1 ≤ p)
    (hpm : p ≤ m - 1) :
    ⌊(a : ℝ) * lam ^ p⌋ = (a : ℤ) + p * d - 1

/-- **Reducible quadratics with coefficients in an arithmetic progression.** Let $d \ge 2$ be an
integer and, for a positive integer $a$, let $A_2(x) = ax^2 + (a + d)x + (a + 2d)$ in
$\mathbb{Z}[x]$. There is a positive integer $a$ coprime to $d$ for which $A_2$ is not
irreducible in $\mathbb{Z}[x]$ if and only if every prime divisor of $d$ is congruent to $1$
modulo $3$. In that case the number of positive integers $a$ coprime to $d$ for which $A_2$ is
not irreducible is exactly $2^{n-1}$, where $n$ is the number of distinct prime divisors of $d$.

Both hypotheses matter: without coprimality, $a = d = 7$ gives $A_2(x) = 7(x^2 + 2x + 3)$, which
is not irreducible in $\mathbb{Z}[x]$; and for $d = 1$ the prime condition holds vacuously while
$A_2$ is irreducible for every $a \ge 1$, its discriminant $-3a^2 - 6a + 1$ being negative.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Theorem 3
(`integers-2026-A92-thm-3`). -/
public theorem_wanted arithProgPoly_two_reducible_iff {d : ℕ} (hd : 2 ≤ d) :
    ((∃ a : ℕ, 0 < a ∧ Nat.Coprime a d ∧
        ¬ Irreducible (∑ i ∈ Finset.range 3, C ((a : ℤ) + i * d) * X ^ (2 - i))) ↔
      ∀ p ∈ d.primeFactors, p % 3 = 1) ∧
    ((∀ p ∈ d.primeFactors, p % 3 = 1) →
      {a : ℕ | 0 < a ∧ Nat.Coprime a d ∧
        ¬ Irreducible (∑ i ∈ Finset.range 3, C ((a : ℤ) + i * d) * X ^ (2 - i))}.ncard =
        2 ^ (d.primeFactors.card - 1))

end

end MetaMathlibExt
