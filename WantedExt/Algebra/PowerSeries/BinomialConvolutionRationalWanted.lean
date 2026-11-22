/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.RingTheory.PowerSeries.BinomialProduct

/-!
# Binomial convolutions for rational power series

Statements from Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3 (arXiv `2304.10426`).

The binomial product `A ⊙ B` is `binomialProduct A B`
(`MathlibExt.RingTheory.PowerSeries.BinomialProduct`), with `n`-th coefficient
`∑_k binom(n, k) a_k b_{n-k}`; the Hadamard product `A * B` is written out coefficientwise.
The paper works over a field of characteristic `0`; the zeros `αᵢ`, `βⱼ` of the
denominators, which the paper takes in an extension field, are taken here in the coefficient
field `K` itself (map the series to a splitting field to recover the paper's setting).
Resultants are Mathlib's `Polynomial.resultant` with explicit formal degrees.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **Theorem 1.** If a power series `A` with coefficients in a field `F` is a quotient of
polynomials `p / q` with coefficients in an extension field `G`, then `A = P / Q` for
polynomials `P`, `Q` with coefficients in `F`.

The quotients are stated with denominators cleared (`A q = p`, `q ≠ 0`).

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 1 (`jis-2024-24.1.3-thm-1`). -/
public theorem_wanted exists_polynomial_quotient_of_extension {F G : Type*} [Field F] [Field G]
    [Algebra F G] (A : PowerSeries F) (p q : Polynomial G) (hq : q ≠ 0)
    (h : PowerSeries.map (algebraMap F G) A * (q : PowerSeries G) = p) :
    ∃ P Q : Polynomial F, Q ≠ 0 ∧ A * (Q : PowerSeries F) = P

/-- **Lemma 3.** Let `F ⊆ G` be fields and `S ⊆ Fⁿ`. If some nonzero `t ∈ Gⁿ` has `s · t = 0`
for all `s ∈ S`, then some nonzero `u ∈ Fⁿ` has `s · u = 0` for all `s ∈ S`.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Lemma 3 (`jis-2024-24.1.3-lem-3`). -/
public theorem_wanted exists_orthogonal_of_orthogonal_over_extension {F G : Type*} [Field F]
    [Field G] [Algebra F G] {n : ℕ} (S : Set (Fin n → F)) (t : Fin n → G) (ht : t ≠ 0)
    (horth : ∀ s ∈ S, ∑ i, algebraMap F G (s i) * t i = 0) :
    ∃ u : Fin n → F, u ≠ 0 ∧ ∀ s ∈ S, ∑ i, s i * u i = 0

/-- **Lemma 4.** `xʲ / (1 - αx)^{j+1} ⊙ xᵏ / (1 - βx)^{k+1} =
binom(j + k, j) x^{j+k} / (1 - (α + β)x)^{j+k+1}`.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Lemma 4 (`jis-2024-24.1.3-lem-4`). -/
public theorem_wanted binomialProduct_X_pow_mul_inv_pow {K : Type*} [Field K] [CharZero K]
    (j k : ℕ) (α β : K) :
    binomialProduct (X ^ j * ((1 - C α * X)⁻¹) ^ (j + 1))
        (X ^ k * ((1 - C β * X)⁻¹) ^ (k + 1)) =
      ((j + k).choose j : PowerSeries K) * X ^ (j + k) * ((1 - C (α + β) * X)⁻¹) ^ (j + k + 1)

/-- **Corollary 5.** `A(x) ⊙ 1 / (1 - βx) = 1 / (1 - βx) · A(x / (1 - βx))`.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Corollary 5 (`jis-2024-24.1.3-cor-5`). -/
public theorem_wanted binomialProduct_inv_one_sub {K : Type*} [Field K] [CharZero K]
    (A : PowerSeries K) (β : K) :
    binomialProduct A (1 - C β * X)⁻¹ =
      (1 - C β * X)⁻¹ * PowerSeries.subst (X * (1 - C β * X)⁻¹) A

/-- **Theorem 6.** If `A = R / ∏_{i ≤ m} (1 - αᵢx)` with `deg R < m` and
`B = S / ∏_{j ≤ n} (1 - βⱼx)` with `deg S < n` (the `αᵢ`, `βⱼ` need not be distinct nor
nonzero), then `A ⊙ B = T / ∏ᵢ ∏ⱼ (1 - (αᵢ + βⱼ)x)` for a polynomial `T` of degree at most
`mn - 1`.

Denominators are cleared; `deg T < mn` (so `T = 0` when `mn = 0`).

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 6 (`jis-2024-24.1.3-thm-6`). -/
public theorem_wanted binomialProduct_rational {K : Type*} [Field K] [CharZero K] (m n : ℕ)
    (α : Fin m → K) (β : Fin n → K) (R S : Polynomial K) (hR : R.degree < m) (hS : S.degree < n)
    (A B : PowerSeries K) (hA : A * ∏ i, (1 - C (α i) * X) = (R : PowerSeries K))
    (hB : B * ∏ j, (1 - C (β j) * X) = (S : PowerSeries K)) :
    ∃ T : Polynomial K, T.degree < (m * n : ℕ) ∧
      binomialProduct A B * ∏ i, ∏ j, (1 - C (α i + β j) * X) = (T : PowerSeries K)

/-- **Corollary 7.** If `A = R / ∏_{i ≤ m} (1 - αᵢx)` and `B = S / ∏_{j ≤ n} (1 - βⱼx)` with all
`αᵢ`, `βⱼ` nonzero, `u = max(deg R + 1 - m, 0)` and `v = max(deg S + 1 - n, 0)`, then
`A ⊙ B = T / ((∏ᵢ (1 - αᵢx))^v (∏ⱼ (1 - βⱼx))^u ∏ᵢ ∏ⱼ (1 - (αᵢ + βⱼ)x))` for a polynomial `T`
of degree less than `(u + m)(v + n)`.

Denominators are cleared; `u`, `v` use truncated subtraction of `natDegree`.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Corollary 7 (`jis-2024-24.1.3-cor-7`). -/
public theorem_wanted binomialProduct_rational_general {K : Type*} [Field K] [CharZero K]
    (m n : ℕ) (α : Fin m → K) (β : Fin n → K) (hα : ∀ i, α i ≠ 0) (hβ : ∀ j, β j ≠ 0)
    (R S : Polynomial K) (A B : PowerSeries K) (hA : A * ∏ i, (1 - C (α i) * X) = (R : PowerSeries K))
    (hB : B * ∏ j, (1 - C (β j) * X) = (S : PowerSeries K)) :
    ∃ T : Polynomial K, T.degree < (((R.natDegree + 1 - m) + m) * ((S.natDegree + 1 - n) + n) : ℕ) ∧
      binomialProduct A B * ((∏ i, (1 - C (α i) * X)) ^ (S.natDegree + 1 - n) *
        (∏ j, (1 - C (β j) * X)) ^ (R.natDegree + 1 - m) *
        ∏ i, ∏ j, (1 - C (α i + β j) * X)) = (T : PowerSeries K)

/-- **Lemma 8.** `xᵐ ⊙ A(x) = (xᵐ / m!) (d/dx)ᵐ (xᵐ A(x))`.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Lemma 8 (`jis-2024-24.1.3-lem-8`). -/
public theorem_wanted binomialProduct_X_pow {K : Type*} [Field K] [CharZero K] (m : ℕ)
    (A : PowerSeries K) :
    binomialProduct (X ^ m) A =
      C ((m.factorial : K)⁻¹) * X ^ m * (⇑(PowerSeries.derivative (R := K)))^[m] (X ^ m * A)

/-- **Theorem 10.** With `U(x) = ∏_{i ≤ m} (1 - αᵢx)` and `V(x) = ∏_{j ≤ n} (1 - βⱼx)`,
`∏ᵢ ∏ⱼ (1 - (αᵢ + βⱼ)x) = (-1)^{mn} Res((1 - y)^m U(x / (1 - y)), yⁿ V(x / y), y)`.

The two resultant arguments are written expanded as polynomials in `y` over `K[x]`:
`(1 - y)^m U(x / (1 - y)) = ∏ᵢ (1 - y - αᵢx)` and `yⁿ V(x / y) = ∏ⱼ (y - βⱼx)`; the resultant
uses the formal degrees `m` and `n`.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 10 (`jis-2024-24.1.3-thm-10`). -/
public theorem_wanted prod_one_sub_add_eq_resultant {K : Type*} [Field K] [CharZero K] (m n : ℕ)
    (α : Fin m → K) (β : Fin n → K) :
    ∏ i, ∏ j, (1 - Polynomial.C (α i + β j) * Polynomial.X) =
      (-1) ^ (m * n) * Polynomial.resultant
        (∏ i, (1 - Polynomial.X - Polynomial.C (Polynomial.C (α i) * Polynomial.X)))
        (∏ j, (Polynomial.X - Polynomial.C (Polynomial.C (β j) * Polynomial.X))) m n

/-- **Theorem 11.** If `g(x) = ∑ Gₙ xⁿ = (2 - ax) / (1 - ax - bx²)`, then
`g ⊙ g = 2 / (1 - ax) + g(2x)`, so `∑_k binom(n, k) G_k G_{n-k} = 2aⁿ + 2ⁿ Gₙ`.

`g` is given by `g (1 - ax - bx²) = 2 - ax`; `g(2x)` is `PowerSeries.rescale 2 g`.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 11 (`jis-2024-24.1.3-thm-11`). -/
public theorem_wanted binomialProduct_lucasV_generatingFunction {K : Type*} [Field K]
    [CharZero K] (a b : K) (g : PowerSeries K)
    (hg : g * (1 - C a * X - C b * X ^ 2) = 2 - C a * X) :
    binomialProduct g g = 2 * (1 - C a * X)⁻¹ + PowerSeries.rescale 2 g ∧
      ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1),
          (n.choose k : K) * PowerSeries.coeff k g * PowerSeries.coeff (n - k) g =
        2 * a ^ n + 2 ^ n * PowerSeries.coeff n g

/-- **Theorem 12.** Let `r`, `s` be proper rational series with denominator
`D(x) = 1 + Ax + Bx² + Cx³ = ∏_{i ≤ 3} (1 - αᵢx)`, `C ≠ 0`, where `2αᵢ ≠ αⱼ + α_k` for
`i, j, k` not all equal. Then for some polynomials `u`, `v` of degree at most `2`,
`r ⊙ s = u(x) / D(2x) + 1 / (1 + Ax) ⊙ v(x) / D(-x)`.

Corrected reading: the record prints `1 / (1 - Ax)`, which is false. For the tribonacci series
`t = x / (1 - x - x² - x³)` (`A = -1`), the paper's own computation gives
`t ⊙ t = (1 + x + 10x²) / (11 D(2x)) - (1 + x - 8x²) / (11 (1 - 2x + 2x³))` and
`(1 + x - 8x²) / (1 - 2x + 2x³) = 1 / (1 - x) ⊙ (1 + 3x - 6x²) / D(-x)`, i.e. the factor is
`1 / (1 + Ax)`; with `1 / (1 - Ax) = 1 / (1 + x)` the second part `1 / (1 - x) ⊙ (…)` times
`D(-x)` is not a polynomial (exact check: nonzero coefficient of `x⁴`). The hypothesis
"not all equal" is from the paper's statement (the record drops it, which would make the
hypothesis unsatisfiable). The `αᵢ` are taken in `K`.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 12 (`jis-2024-24.1.3-thm-12`). -/
public theorem_wanted binomialProduct_cubic_denominator {K : Type*} [Field K] [CharZero K]
    (A B C' : K) (hC : C' ≠ 0) (α : Fin 3 → K)
    (hD : 1 + C A * X + C B * X ^ 2 + C C' * X ^ 3 = ∏ i, (1 - C (α i) * X))
    (hα : ∀ i j k, ¬(i = j ∧ j = k) → 2 * α i ≠ α j + α k)
    (r s : PowerSeries K) (pr ps : Polynomial K) (hpr : pr.degree < 3) (hps : ps.degree < 3)
    (hr : r * (1 + C A * X + C B * X ^ 2 + C C' * X ^ 3) = (pr : PowerSeries K))
    (hs : s * (1 + C A * X + C B * X ^ 2 + C C' * X ^ 3) = (ps : PowerSeries K)) :
    ∃ u v : Polynomial K, u.natDegree ≤ 2 ∧ v.natDegree ≤ 2 ∧
      binomialProduct r s =
        (u : PowerSeries K) * (1 + C (2 * A) * X + C (4 * B) * X ^ 2 + C (8 * C') * X ^ 3)⁻¹ +
          binomialProduct (1 + C A * X)⁻¹
            ((v : PowerSeries K) * (1 - C A * X + C B * X ^ 2 - C C' * X ^ 3)⁻¹)

/-- **Theorem 13.** If `A` is rational with denominator `∏_{i ≤ m} (1 - αᵢx)` and `B` with
denominator `∏_{j ≤ n} (1 - βⱼx)`, then the Hadamard product `A * B` is rational and may be
written with denominator `∏ᵢ ∏ⱼ (1 - αᵢβⱼx)`; moreover, if `A` and `B` are proper then so is
`A * B`.

Denominators are cleared. Properness is intrinsic: some representation `P / Q` with
`Q(0) ≠ 0` and `deg P < deg Q`.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 13 (`jis-2024-24.1.3-thm-13`). -/
public theorem_wanted hadamardProduct_rational {K : Type*} [Field K] [CharZero K] (m n : ℕ)
    (α : Fin m → K) (β : Fin n → K) (R S : Polynomial K) (A B : PowerSeries K)
    (hA : A * ∏ i, (1 - C (α i) * X) = (R : PowerSeries K)) (hB : B * ∏ j, (1 - C (β j) * X) = (S : PowerSeries K)) :
    (∃ T : Polynomial K, PowerSeries.mk (fun k => PowerSeries.coeff k A * PowerSeries.coeff k B) *
        ∏ i, ∏ j, (1 - C (α i * β j) * X) = (T : PowerSeries K)) ∧
      ((∃ P Q : Polynomial K, Q.coeff 0 ≠ 0 ∧ P.degree < Q.degree ∧ A * (Q : PowerSeries K) = (P : PowerSeries K)) →
        (∃ P Q : Polynomial K, Q.coeff 0 ≠ 0 ∧ P.degree < Q.degree ∧
          B * (Q : PowerSeries K) = (P : PowerSeries K)) →
        ∃ P Q : Polynomial K, Q.coeff 0 ≠ 0 ∧ P.degree < Q.degree ∧
          PowerSeries.mk (fun k => PowerSeries.coeff k A * PowerSeries.coeff k B) *
            (Q : PowerSeries K) = (P : PowerSeries K))

/-- **Theorem 14.** With `U(x) = ∏_{i ≤ m} (1 - αᵢx)` and `V(x) = ∏_{j ≤ n} (1 - βⱼx)`,
`∏ᵢ ∏ⱼ (1 - αᵢβⱼx) = (-1)^{mn} Res(U(y), yⁿ V(x / y), y)`.

The resultant arguments are polynomials in `y` over `K[x]`, with `yⁿ V(x / y)` written
expanded as `∏ⱼ (y - βⱼx)`; the resultant uses the formal degrees `m` and `n`.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 14 (`jis-2024-24.1.3-thm-14`). -/
public theorem_wanted prod_one_sub_mul_eq_resultant {K : Type*} [Field K] [CharZero K] (m n : ℕ)
    (α : Fin m → K) (β : Fin n → K) :
    ∏ i, ∏ j, (1 - Polynomial.C (α i * β j) * Polynomial.X) =
      (-1) ^ (m * n) * Polynomial.resultant
        (∏ i, (1 - Polynomial.C (Polynomial.C (α i)) * Polynomial.X))
        (∏ j, (Polynomial.X - Polynomial.C (Polynomial.C (β j) * Polynomial.X))) m n

end

end MetaMathlibExt
