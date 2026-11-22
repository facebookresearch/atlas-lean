/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Discriminants of truncated logarithmic polynomials

Statements from Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39 (arXiv:2401.14138).
`F_n(x) = 1 + x + x²/2 + ⋯ + xⁿ/n`, `L_n = lcm(1, …, n)`, `F̃_n = L_n F_n ∈ ℤ[x]`,
and `𝒫_n = ∏ F̃_n(θ)` over the roots `θ` of `F_n' = 1 + x + ⋯ + x^{n-1}` (the
source's Equation (5)), here the resultant `Res(1 + x + ⋯ + x^{n-1}, F̃_n)`; by
`Polynomial.resultant_eq_prod_eval` this is that product, since
`1 + x + ⋯ + x^{n-1}` is monic. The discriminant is Mathlib's
`Polynomial.discr`. "Not in `ℚ^{×2}`" is stated as `¬ IsSquare`; the two agree
because these discriminants are nonzero.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- The truncated logarithmic polynomial `F_n(x) = 1 + x + x²/2 + ⋯ + xⁿ/n`.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public noncomputable def truncatedLogPolynomial (n : ℕ) : ℚ[X] :=
  1 + ∑ j ∈ Finset.Icc 1 n, C ((j : ℚ)⁻¹) * X ^ j

/-- `L_n = lcm(1, 2, …, n)`.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public def truncatedLogLcm (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

/-- `L_4 = 12`.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public theorem truncatedLogLcm_four : truncatedLogLcm 4 = 12 := by
  decide

/-- The integer polynomial `F̃_n = L_n F_n = L_n + ∑_{j=1}^n (L_n / j) x^j`.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public noncomputable def scaledTruncatedLogPolynomial (n : ℕ) : ℤ[X] :=
  C (truncatedLogLcm n : ℤ) + ∑ j ∈ Finset.Icc 1 n, C ((truncatedLogLcm n / j : ℕ) : ℤ) * X ^ j

/-- `F̃_n` maps to `L_n F_n` in `ℚ[x]`.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 1. -/
public theorem map_scaledTruncatedLogPolynomial (n : ℕ) :
    (scaledTruncatedLogPolynomial n).map (Int.castRingHom ℚ) =
      C (truncatedLogLcm n : ℚ) * truncatedLogPolynomial n := by
  simp only [scaledTruncatedLogPolynomial, truncatedLogPolynomial, Polynomial.map_add,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, mul_add, mul_one,
    Finset.mul_sum]
  refine congrArg₂ (· + ·) (by simp) (Finset.sum_congr rfl fun j hj => ?_)
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj0 : (j : ℚ) ≠ 0 := by positivity
  have hdvd : j ∣ truncatedLogLcm n := Finset.dvd_lcm (s := Finset.Icc 1 n) (f := id) hj
  rw [← mul_assoc, ← C_mul]
  congr 2
  simp only [eq_intCast, Int.cast_natCast]
  rw [Nat.cast_div hdvd hj0, div_eq_mul_inv]

/-- `𝒫_n = ∏_{θ : F_n'(θ) = 0} F̃_n(θ)`, as the resultant
`Res(1 + x + ⋯ + x^{n-1}, F̃_n)`.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Equation (5). -/
public noncomputable def truncatedLogResultantProduct (n : ℕ) : ℤ :=
  resultant (∑ k ∈ Finset.range n, (X : ℤ[X]) ^ k) (scaledTruncatedLogPolynomial n)

/-- `X(m) = ∏_{k=1}^{m-1} (1/m + ω^k + ω^{2k}/2 + ⋯ + ω^{(m-1)k}/(m-1))` for a
primitive `m`-th root of unity `ω`, as the resultant of `1 + x + ⋯ + x^{m-1}`
with `1/m + x + x²/2 + ⋯ + x^{m-1}/(m-1)`.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 4. -/
public noncomputable def truncatedLogAuxProduct (m : ℕ) : ℚ :=
  resultant (∑ k ∈ Finset.range m, (X : ℚ[X]) ^ k)
    (C ((m : ℚ)⁻¹) + ∑ j ∈ Finset.Icc 1 (m - 1), C ((j : ℚ)⁻¹) * X ^ j)

/-- `X(1) = 1` (an empty product).

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 4. -/
public theorem truncatedLogAuxProduct_one : truncatedLogAuxProduct 1 = 1 := by
  simp [truncatedLogAuxProduct]

/-- `𝒫_1 = 1` (an empty product).

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Equation (5). -/
public theorem truncatedLogResultantProduct_one : truncatedLogResultantProduct 1 = 1 := by
  simp [truncatedLogResultantProduct]

/-- The exceptional set `E_m`: primes `ℓ` dividing `X(m)` or `Y(m) = H_m` (positive
`ℓ`-adic valuation) with `m ℓ ≡ 1 (mod 4)`. The source's display joins the two
valuation conditions with "and", but its text ("all prime divisors of `X(m)` and
`Y(m)`") and its table (`E_3 = {11}` with `11 ∤ X(3) = 13/36`) use the union.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Section 4. -/
public def truncatedLogExceptionalPrimes (m : ℕ) : Set ℕ :=
  {ℓ | ℓ.Prime ∧ (0 < padicValRat ℓ (truncatedLogAuxProduct m) ∨
    0 < padicValRat ℓ (_root_.harmonic m)) ∧ m * ℓ % 4 = 1}

/-- `𝒫_n` is positive (for `n ≥ 1`).

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Lemma 1
(`integers-2025-A39-lem-1`). -/
public theorem_wanted truncatedLogResultantProduct_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < truncatedLogResultantProduct n

/-- If `n ≡ 0, 2, 3 (mod 4)` (`n ≥ 1`), then `disc(F_n)` is not a rational square.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Proposition 1
(`integers-2025-A39-prop-1`). -/
public theorem_wanted not_isSquare_discr_truncatedLog_of_mod_four {n : ℕ} (hn : 1 ≤ n)
    (h : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3) :
    ¬ IsSquare (truncatedLogPolynomial n).discr

/-- If `n ≡ 0, 2, 3 (mod 4)` (`n ≥ 1`), or `n ≡ 1 (mod 4)` is an odd power of a
prime, then `disc(F_n)` is not a rational square.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 1
(`integers-2025-A39-thm-1`). -/
public theorem_wanted not_isSquare_discr_truncatedLog {n : ℕ} (hn : 1 ≤ n)
    (h : n % 4 = 0 ∨ n % 4 = 2 ∨ n % 4 = 3 ∨
      (n % 4 = 1 ∧ ∃ p e : ℕ, p.Prime ∧ Odd e ∧ n = p ^ e)) :
    ¬ IsSquare (truncatedLogPolynomial n).discr

/-- If `n = p^{2e}` for an odd prime `p` and `e ≥ 1`, then `𝒫_n` is coprime to `p`.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 2
(`integers-2025-A39-thm-2`). -/
public theorem_wanted not_dvd_truncatedLogResultantProduct_of_even_power {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) :
    ¬ (p : ℤ) ∣ truncatedLogResultantProduct (p ^ (2 * e))

/-- For `m ≥ 1`, all but finitely many primes `q` with `m q ≡ 1 (mod 4)` have
`disc(F_{mq})` not a rational square.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 3
(`integers-2025-A39-thm-3`). -/
public theorem_wanted finite_primes_isSquare_discr_truncatedLog {m : ℕ} (hm : 1 ≤ m) :
    {q : ℕ | q.Prime ∧ m * q % 4 = 1 ∧ IsSquare (truncatedLogPolynomial (m * q)).discr}.Finite

/-- If `p ≡ 1 (mod 4)` is prime, `e ≥ 1`, and `n = p^e`, then `𝒫_n` is coprime to `p`.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 4
(`integers-2025-A39-thm-4`). -/
public theorem_wanted not_dvd_truncatedLogResultantProduct_of_prime_power {p e : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (he : 1 ≤ e) :
    ¬ (p : ℤ) ∣ truncatedLogResultantProduct (p ^ e)

/-- If `p ≡ 1 (mod 4)` is prime, `e ≥ 1`, and `n = p^e`: for odd `e`, `disc(F_n)` is not
a rational square; for even `e`, it is not a rational square if and only if `𝒫_n` is
not.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Corollary 1
(`integers-2025-A39-cor-1`). -/
public theorem_wanted discr_truncatedLog_prime_power {p e : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (he : 1 ≤ e) :
    (Odd e → ¬ IsSquare (truncatedLogPolynomial (p ^ e)).discr) ∧
      (Even e → (¬ IsSquare (truncatedLogPolynomial (p ^ e)).discr ↔
        ¬ IsSquare ((truncatedLogResultantProduct (p ^ e) : ℤ) : ℚ)))

/-- For a prime `q ∉ E_m` with `q > m` and `n = m q ≡ 1 (mod 4)`, `disc(F_n)` is not a
rational square.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Theorem 5
(`integers-2025-A39-thm-5`). -/
public theorem_wanted not_isSquare_discr_truncatedLog_mul_prime {m q : ℕ} (hq : q.Prime)
    (hE : q ∉ truncatedLogExceptionalPrimes m) (hmq : m < q) (h4 : m * q % 4 = 1) :
    ¬ IsSquare (truncatedLogPolynomial (m * q)).discr

/-- For every prime `q`, if `n = 3q`, `5q`, or `7q`, then `disc(F_n)` is not a rational
square.

Source: Cullinan and Gajek-Leonard, *On the Discriminants of Truncated
Logarithmic Polynomials*, INTEGERS 25 (2025), Article A39, Proposition 2
(`integers-2025-A39-prop-2`). -/
public theorem_wanted not_isSquare_discr_truncatedLog_three_five_seven_mul {q n : ℕ}
    (hq : q.Prime) (hn : n = 3 * q ∨ n = 5 * q ∨ n = 7 * q) :
    ¬ IsSquare (truncatedLogPolynomial n).discr

end

end MetaMathlibExt
