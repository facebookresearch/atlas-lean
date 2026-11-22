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

/-- Perron's irreducibility criterion: a monic `f = x^n + a_{n-1} x^{n-1} + ⋯ + a_0 ∈ ℤ[x]`
of degree `n ≥ 1` with `a_0 ≠ 0` and `|a_{n-1}| > 1 + |a_{n-2}| + ⋯ + |a_0|` is irreducible.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Theorem 1 (Perron's criterion,
quoted from the paper's reference [6]) (`integers-2026-A92-thm-1`). -/
public theorem_wanted perron_irreducible {f : ℤ[X]} (hmonic : f.Monic) (hdeg : 1 ≤ f.natDegree)
    (h0 : f.coeff 0 ≠ 0)
    (hbig : 1 + ∑ i ∈ Finset.range (f.natDegree - 1), |f.coeff i| <
      |f.coeff (f.natDegree - 1)|) :
    Irreducible f

/-- Main theorem: for `m ≥ 2` and coprime positive integers `a`, `d` with `8a > m² d²`, the
polynomial `a x^m + (a + d) x^(m-1) + ⋯ + (a + (m-1)d) x + (a + md)` is irreducible over `ℤ`.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Theorem 2
(`integers-2026-A92-thm-2`). -/
public theorem_wanted arithProgPoly_irreducible {m a d : ℕ} (hm : 2 ≤ m) (ha : 0 < a)
    (hd : 0 < d) (hcop : Nat.Coprime a d) (hbig : m ^ 2 * d ^ 2 < 8 * a) :
    Irreducible (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i))

/-- For coprime positive integers `a ≥ d`, the quartic
`A_4(x) = a x^4 + (a + d) x^3 + (a + 2d) x^2 + (a + 3d) x + (a + 4d)` is not a product of two
quadratic polynomials in `ℤ[x]`.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Theorem 4
(`integers-2026-A92-thm-4`). -/
public theorem_wanted arithProgPoly_four_not_mul_quadratics {a d : ℕ} (hd : 0 < d) (had : d ≤ a)
    (hcop : Nat.Coprime a d) :
    ¬ ∃ g h : ℤ[X], g.natDegree = 2 ∧ h.natDegree = 2 ∧
      ∑ i ∈ Finset.range 5, C ((a : ℤ) + i * d) * X ^ (4 - i) = g * h

/-- If `m + 1` is prime and `d` has a prime divisor `p` with `p ≢ 0 (mod m + 1)` that is a
primitive root modulo `m + 1`, then `A_m(x) = a x^m + (a + d) x^(m-1) + ⋯ + (a + md)` is
irreducible over `ℤ` (for coprime positive `a`, `d`, the paper's standing assumption).

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 6
(`integers-2026-A92-prop-6`). -/
public theorem_wanted arithProgPoly_irreducible_of_primitiveRoot {m a d p : ℕ} (hm : 2 ≤ m)
    (hprime : (m + 1).Prime) (ha : 0 < a) (hd : 0 < d) (hcop : Nat.Coprime a d)
    (hp : p.Prime) (hpd : p ∣ d) (hpm : ¬ (m + 1) ∣ p)
    (hroot : orderOf (p : ZMod (m + 1)) = m) :
    Irreducible (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i))

/-- Lemma 1, identity: with `a_n = a + (n - 1)d`,
`A_m(x)(x - 1)² = a_1 x^{m+2} - a_0 x^{m+1} - a_{m+2} x + a_{m+1}`; stated for all `m, a, d ≥ 0`
(the paper says positive).

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 1 (`integers-2026-A92-lem-1`). -/
public theorem_wanted arithProgPoly_mul_sub_one_sq (m a d : ℕ) :
    (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i)) * (X - 1) ^ 2 =
      C (a : ℤ) * X ^ (m + 2) - C ((a : ℤ) - d) * X ^ (m + 1) -
        C ((a : ℤ) + (m + 1) * d) * X + C ((a : ℤ) + m * d)

/-- Lemma 1, equation (2): if `z ∈ ℂ` is a zero of `A_m(x)` or `z = 1`, then
`z^{m+1} = (a_{m+2} z - a_{m+1}) / (a_1 z - a_0)` with `a_n = a + (n - 1)d`; stated for all
`m, a ≥ 0` and `d ≥ 1` (the denominator never vanishes at such `z`).

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 1, equation (2)
(`integers-2026-A92-lem-1`). -/
public theorem_wanted arithProgPoly_root_pow_eq (m a d : ℕ) (hd : 0 < d) (z : ℂ)
    (hz : aeval z (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i)) = 0 ∨ z = 1) :
    z ^ (m + 1) =
      (((a : ℂ) + (m + 1) * d) * z - ((a : ℂ) + m * d)) / ((a : ℂ) * z - ((a : ℂ) - d))

/-- For `m ≥ 2` and positive integers `a ≥ d`, the equation
`a_1 x^{m+2} + a_0 x^{m+1} - a_{m+2} x - a_{m+1} = 0` (`a_n = a + (n - 1)d`), equation (3), has
exactly one positive real solution, and it is larger than `1`.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 1
(`integers-2026-A92-prop-1`). -/
public theorem_wanted arithProgPoly_eq3_existsUnique_pos {m a d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (hda : d ≤ a) :
    (∃! x : ℝ, 0 < x ∧ (a : ℝ) * x ^ (m + 2) + ((a : ℝ) - d) * x ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * x - ((a : ℝ) + m * d) = 0) ∧
    ∀ x : ℝ, 0 < x → (a : ℝ) * x ^ (m + 2) + ((a : ℝ) - d) * x ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * x - ((a : ℝ) + m * d) = 0 → 1 < x

/-- For `m ≥ 2`, positive integers `a ≥ d`, and `λ` the positive solution of equation (3),
every zero `z ∈ ℂ` of `A_m(x)` has `|z| ≤ λ`, with equality only at `z = -λ`.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 2
(`integers-2026-A92-prop-2`). -/
public theorem_wanted arithProgPoly_root_norm_le {m a d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (hda : d ≤ a) (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) (z : ℂ)
    (hz : aeval z (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i)) = 0) :
    ‖z‖ ≤ lam ∧ (‖z‖ = lam → z = -(lam : ℂ))

/-- For `m ≥ 2`, positive integers `a ≥ d`, and `λ` the positive solution of equation (3),
`a λ^m - a_{m+1} > 0`, i.e. `a + md < a λ^m`.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 2 (`integers-2026-A92-lem-2`). -/
public theorem_wanted arithProgPoly_lam_pow_gt {m a d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (hda : d ≤ a) (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) :
    (a : ℝ) + m * d < a * lam ^ m

/-- For real `x > 0` and integer `m ≥ 2`, `(1 + mx)^{1/m} > (2 + (m + 1)x) / (2 + (m - 1)x)`.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Lemma 3 (`integers-2026-A92-lem-3`). -/
public theorem_wanted one_add_mul_rpow_inv_gt {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : 0 < x) :
    (2 + (m + 1) * x) / (2 + (m - 1) * x) < (1 + m * x) ^ (1 / (m : ℝ))

/-- For `m ≥ 2`, positive integers `a`, `d` with `2a > (m + 1)d`, and `λ` the positive solution
of equation (3): `⌊a λ^p⌋ < a_{p+1} = a + pd` for every `1 ≤ p ≤ m - 1`.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 4
(`integers-2026-A92-prop-4`). -/
public theorem_wanted arithProgPoly_floor_lam_pow_lt {m a d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (had : (m + 1) * d < 2 * a) (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) (p : ℕ) (hp1 : 1 ≤ p)
    (hpm : p ≤ m - 1) :
    ⌊(a : ℝ) * lam ^ p⌋ < (a : ℤ) + p * d

/-- For `m ≥ 2`, positive integers `a`, `d`, `1 ≤ p ≤ m - 1` with `2a > p(m - p)d²`, and `λ` the
positive solution of equation (3): `⌊a λ^p⌋ = a_{p+1} - 1 = a + pd - 1`.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 5
(`integers-2026-A92-prop-5`). -/
public theorem_wanted arithProgPoly_floor_lam_pow_eq {m a d : ℕ} (hm : 2 ≤ m) (ha : 0 < a)
    (hd : 0 < d) (p : ℕ) (hp1 : 1 ≤ p) (hpm : p ≤ m - 1) (had : p * (m - p) * d ^ 2 < 2 * a)
    (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) :
    ⌊(a : ℝ) * lam ^ p⌋ = (a : ℤ) + p * d - 1

/-- For `m ≥ 2` and positive integers `a`, `d` with `8a > m²d²`, and `λ` the positive solution
of equation (3): `⌊a λ^p⌋ = a + pd - 1` for every `1 ≤ p ≤ m - 1`.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 5, second statement
(`integers-2026-A92-prop-5`). -/
public theorem_wanted arithProgPoly_floor_lam_pow_eq_of_eight {m a d : ℕ} (hm : 2 ≤ m)
    (ha : 0 < a) (hd : 0 < d) (had : m ^ 2 * d ^ 2 < 8 * a) (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) (p : ℕ) (hp1 : 1 ≤ p)
    (hpm : p ≤ m - 1) :
    ⌊(a : ℝ) * lam ^ p⌋ = (a : ℤ) + p * d - 1

/-- For an integer `d ≥ 2`: some positive integer `a` coprime to `d` makes
`A_2(x) = ax² + (a + d)x + (a + 2d)` reducible over `ℤ` if and only if every prime divisor of
`d` is `≡ 1 (mod 3)`; in that case there are exactly `2^{n-1}` such `a`, where `n` is the number
of distinct prime divisors of `d`. Corrected reading: the record omits the paper's standing
coprimality of `a` and `d` (without it `a = d = 7` gives content `7`) and allows `d = 1`, where
the condition holds vacuously but `A_2` is irreducible for every `a ≥ 1` (discriminant
`-3a² - 6a + 1 < 0`) and `2^{-1}` is not a count; the proof's conjugate-pair count needs
`n ≥ 1`.

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
