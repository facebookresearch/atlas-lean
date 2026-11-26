/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.RingTheory.PowerSeries.BinomialProduct
import MathlibExt.Combinatorics.Enumerative.RiordanArraySum
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FieldSimp

/-!
# Binomial products of shifted geometric series

Dividing the coefficient of degree `n` by `n!` turns the binomial product into ordinary
multiplication. Under this transformation, the shifted geometric series with shift `j` and
parameter `α` becomes the product of `X ^ j / j!` and the formal exponential of `α X`.
-/

namespace MetaMathlibExt

open PowerSeries

namespace binomialProduct_X_pow_mul_inv_pow

variable {K : Type*} [Field K]

private noncomputable def egf (A : PowerSeries K) : PowerSeries K :=
  mk fun n ↦ coeff n A / n.factorial

private theorem egf_natCast_mul (m : ℕ) (A : PowerSeries K) :
    egf ((m : PowerSeries K) * A) = C (m : K) * egf A := by
  ext n
  simp [egf, mul_div_assoc]

variable [CharZero K]

private theorem egf_injective : Function.Injective (egf (K := K)) := by
  intro A B h
  ext n
  have hn := congrArg (coeff n) h
  simpa [egf, Nat.factorial_ne_zero] using hn

private theorem egf_binomialProduct (A B : PowerSeries K) :
    egf (binomialProduct A B) = egf A * egf B := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [egf, coeff_mk, coeff_binomialProduct, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_choose K (Finset.mem_range_succ_iff.mp hi)]
  field_simp [Nat.factorial_ne_zero]

private theorem egf_shifted (j : ℕ) (α : K) :
    egf (X ^ j * ((1 - C α * X)⁻¹) ^ (j + 1)) =
      C (j.factorial : K)⁻¹ * (X ^ j * rescale α (exp K)) := by
  have hinv : ((1 - C α * X)⁻¹) ^ (j + 1) =
      rescale α (mk fun n ↦ ((j + n).choose j : K)) := by
    rw [PowerSeries.inv_pow, inv_eq_iff_mul_eq_one (by simp)]
    simpa only [map_mul, map_pow, map_sub, map_one, rescale_X] using
      congrArg (rescale α) (mk_add_choose_mul_one_sub_pow_eq_one K j)
  ext n
  rw [egf, coeff_mk, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul']
  split_ifs with hj
  · rw [hinv, coeff_rescale, coeff_mk, coeff_rescale, coeff_exp, Nat.cast_add_choose K]
    rw [Nat.add_sub_of_le hj]
    simp
    field_simp [Nat.factorial_ne_zero]
  · simp

end binomialProduct_X_pow_mul_inv_pow

open binomialProduct_X_pow_mul_inv_pow

/-- **Binomial product of shifted powers of geometric series.** For every field $K$ of
characteristic $0$, all $j, k \in \mathbb{N}$ and all $\alpha, \beta \in K$,

$$\frac{x^j}{(1 - \alpha x)^{j+1}} \odot \frac{x^k}{(1 - \beta x)^{k+1}} =
\binom{j + k}{j} \frac{x^{j+k}}{(1 - (\alpha + \beta) x)^{j+k+1}},$$

where $\odot$ is the binomial product.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Lemma 4 (`jis-2024-24.1.3-lem-4`). -/
public theorem binomialProduct_X_pow_mul_inv_pow {K : Type*} [Field K] [CharZero K]
    (j k : ℕ) (α β : K) :
    binomialProduct (X ^ j * ((1 - C α * X)⁻¹) ^ (j + 1))
        (X ^ k * ((1 - C β * X)⁻¹) ^ (k + 1)) =
      ((j + k).choose j : PowerSeries K) * X ^ (j + k) *
        ((1 - C (α + β) * X)⁻¹) ^ (j + k + 1) := by
  apply egf_injective
  rw [egf_binomialProduct, mul_assoc, egf_natCast_mul, egf_shifted, egf_shifted, egf_shifted]
  rw [← exp_mul_exp_eq_exp_add, pow_add]
  have h : ((j + k).choose j : K) * ((j + k).factorial : K)⁻¹ =
      (j.factorial : K)⁻¹ * (k.factorial : K)⁻¹ := by
    rw [Nat.cast_add_choose K]
    field_simp [Nat.factorial_ne_zero]
  conv_rhs => rw [← mul_assoc, ← map_mul, h, map_mul]
  ac_rfl

/-- **Binomial product with a geometric series.** For every field $K$ of characteristic $0$, every
power series $A(x)$ over $K$ and every $\beta \in K$,

$$A(x) \odot \frac{1}{1 - \beta x} = \frac{1}{1 - \beta x} A\left(\frac{x}{1 - \beta x}\right),$$

where $\odot$ is the binomial product and $A(x/(1 - \beta x))$ is the substitution of the series
$x/(1 - \beta x)$, which has zero constant term, into $A$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Corollary 5 (`jis-2024-24.1.3-cor-5`). -/
public theorem binomialProduct_inv_one_sub {K : Type*} [Field K] [CharZero K]
    (A : PowerSeries K) (β : K) :
    binomialProduct A (1 - C β * X)⁻¹ =
      (1 - C β * X)⁻¹ * PowerSeries.subst (X * (1 - C β * X)⁻¹) A := by
  let G : PowerSeries K := (1 - C β * X)⁻¹
  have hsubst : constantCoeff (X * G) = 0 := by simp
  have hmono (k : ℕ) : binomialProduct (X ^ k) G = G * (X * G) ^ k := by
    rw [mul_pow, mul_left_comm, ← pow_succ']
    simpa [G] using binomialProduct_X_pow_mul_inv_pow k 0 (0 : K) β
  -- Each coefficient of the substitution involves only finitely many monomials of `A`.
  ext n
  change coeff n (binomialProduct A G) = coeff n (G * PowerSeries.subst (X * G) A)
  rw [coeff_binomialProduct, ← riordan_array_sum_eq_coeff_subst G (X * G) A hsubst n]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [← hmono, coeff_binomialProduct]
  simp only [coeff_X_pow, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', ite_eq_left hk]
  ac_rfl

end MetaMathlibExt
