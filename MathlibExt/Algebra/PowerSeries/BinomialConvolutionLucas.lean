/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.RingTheory.PowerSeries.BinomialProduct
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.Ring

/-!
# Binomial square of the Lucas generating function

Over an algebraic closure, a Lucas generating function is the sum of two geometric series,
including when the two parameters coincide. The binomial theorem then gives the convolution.
-/

namespace MetaMathlibExt

open PowerSeries

private theorem coeff_geometric {K : Type*} [Field K] (a : K) (n : ℕ) :
    coeff n (1 - C a * X)⁻¹ = a ^ n := by
  have h : (mk fun j ↦ a ^ j) * (1 - C a * X) = 1 := by
    simpa [rescale_mk, Pi.one_apply] using
      congrArg (rescale a) (mk_one_mul_one_sub_eq_one K)
  rw [(inv_eq_iff_mul_eq_one (by simp)).2 h, coeff_mk]

private theorem coeff_lucas_of_roots {K : Type*} [Field K] {a b α β : K}
    (hs : α + β = a) (hp : α * β = -b) {g : PowerSeries K}
    (hg : g * (1 - C a * X - C b * X ^ 2) = 2 - C a * X) (n : ℕ) :
    coeff n g = α ^ n + β ^ n := by
  let A : PowerSeries K := 1 - C α * X
  let B : PowerSeries K := 1 - C β * X
  have hb : b = -(α * β) := by rw [hp, neg_neg]
  have hD : 1 - C a * X - C b * X ^ 2 = A * B := by
    dsimp [A, B]
    rw [← hs, hb, map_add, map_neg, map_mul]
    ring
  have hN : 2 - C a * X = A + B := by
    dsimp [A, B]
    rw [← hs, map_add]
    ring
  have hA : constantCoeff A ≠ 0 := by simp [A]
  have hB : constantCoeff B ≠ 0 := by simp [B]
  have h : g = A⁻¹ + B⁻¹ := by
    apply mul_right_cancel₀ (b := A * B) (mul_ne_zero (fun e ↦ hA (e ▸ map_zero _))
      (fun e ↦ hB (e ▸ map_zero _)))
    rw [← hD, hg, hN, hD, add_mul, ← mul_assoc, PowerSeries.inv_mul_cancel A hA,
      one_mul, mul_left_comm B⁻¹ A B, PowerSeries.inv_mul_cancel B hB, mul_one, add_comm]
  rw [h, map_add, coeff_geometric α, coeff_geometric β]

/-- **Binomial square of the Lucas generating function.** Let $K$ be a field of characteristic
$0$, let $a, b \in K$, and let $g(x) = \sum_{n \ge 0} G_n x^n$ be a power series over $K$ with
$g(x)(1 - ax - bx^2) = 2 - ax$. Then

$$g \odot g = \frac{2}{1 - ax} + g(2x),$$

where $\odot$ is the binomial product, and
$\sum_{k=0}^{n} \binom{n}{k} G_k G_{n-k} = 2a^n + 2^n G_n$ for every $n \ge 0$.

Source: Ira M. Gessel and Ishan Kar, *Binomial Convolutions for Rational Power Series*,
Journal of Integer Sequences 27 (2024), Article 24.1.3, Theorem 11 (`jis-2024-24.1.3-thm-11`). -/
public theorem binomialProduct_lucasV_generatingFunction {K : Type*} [Field K]
    [CharZero K] (a b : K) (g : PowerSeries K)
    (hg : g * (1 - C a * X - C b * X ^ 2) = 2 - C a * X) :
    binomialProduct g g = 2 * (1 - C a * X)⁻¹ + PowerSeries.rescale 2 g ∧
      ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1),
          (n.choose k : K) * PowerSeries.coeff k g * PowerSeries.coeff (n - k) g =
        2 * a ^ n + 2 ^ n * PowerSeries.coeff n g := by
  let L := AlgebraicClosure K
  let i : K →+* L := algebraMap K L
  let p : Polynomial L := Polynomial.X ^ 2 - Polynomial.C (i a) * Polynomial.X -
    Polynomial.C (i b)
  have hp : p.degree ≠ 0 := by
    intro h
    have hz : p.coeff 2 = 0 := Polynomial.coeff_eq_zero_of_degree_lt (by rw [h]; norm_num)
    simp [p, Polynomial.coeff_X_pow] at hz
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root p hp
  -- The complementary parameter gives the factorization even when it equals α.
  let β := i a - α
  have hs : α + β = i a := by dsimp [β]; ring
  have hm : α * β = -i b := by
    simp only [p, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at hα
    calc
      α * β = -(α ^ 2 - i a * α - i b) - i b := by dsimp [β]; ring
      _ = -i b := by rw [hα, neg_zero, zero_sub]
  have hg' : map i g * (1 - C (i a) * X - C (i b) * X ^ 2) = 2 - C (i a) * X := by
    simpa only [map_mul, map_sub, map_one, map_ofNat, map_pow, map_C, map_X] using
      congrArg (map i) hg
  have hcoeff (n : ℕ) : i (coeff n g) = α ^ n + β ^ n := by
    simpa only [coeff_map] using coeff_lucas_of_roots hs hm hg' n
  have hconv (n : ℕ) : ∑ k ∈ Finset.range (n + 1),
      (n.choose k : K) * coeff k g * coeff (n - k) g = 2 * a ^ n + 2 ^ n * coeff n g := by
    apply i.injective
    simp only [map_sum, map_add, map_mul, map_natCast, map_pow, map_ofNat, hcoeff]
    have hpow (x y : L) : ∑ k ∈ Finset.range (n + 1),
        (n.choose k : L) * x ^ k * y ^ (n - k) = (x + y) ^ n := by
      rw [add_pow]
      exact Finset.sum_congr rfl (fun k _ ↦ by ac_rfl)
    simp only [mul_add, add_mul, Finset.sum_add_distrib, hpow]
    rw [add_comm β α, hs, ← two_mul α, ← two_mul β, mul_pow, mul_pow]
    ring
  refine ⟨?_, hconv⟩
  ext n
  rw [coeff_binomialProduct, hconv, map_add, coeff_rescale, ← map_ofNat C, coeff_C_mul,
    coeff_geometric]

end MetaMathlibExt
