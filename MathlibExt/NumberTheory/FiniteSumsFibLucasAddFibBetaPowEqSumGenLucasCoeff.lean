/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Bernoulli
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.NumberTheory.BernoulliFibonacciExpansion
public import MathlibExt.NumberTheory.BernoulliFibonacciMultinomial
public import MathlibExt.NumberTheory.BernoulliFibonacciVanishing
public import MathlibExt.NumberTheory.EulerLucasBinomialSum
public import MathlibExt.NumberTheory.ForwardDiffPow
public import MathlibExt.NumberTheory.GenocchiNumber
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.RingTheory.PowerSeries.Exp
import MathlibExt.NumberTheory.ChurchBicknellFibonacciConvolution

/-!
# Genocchi–Lucas expansion of `(x + β)^m`

This module defines the Genocchi–Lucas coefficients `genLucasCoeff` and proves the
Genocchi–Lucas expansion of `(x + β)^m`.

Binet's formula for the Lucas numbers and the generating series of the Genocchi numbers show
that the Genocchi–Lucas coefficient `genLucasCoeff n` equals `2 * √5 * β ^ n`. The identity
then follows from the binomial theorem.

Statements from Fatima Zohra Bensaci, Rachid Boumahdi, and
Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas
Numbers", *Journal of Integer Sequences* 27 (2024), Article
24.7.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Boumahdi/boumahdi12.tex>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

open MetaMathlibExt

/-- **Genocchi–Lucas coefficients.** For a natural number $n$, the Genocchi–Lucas coefficient is
the real number
$$
c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2 \sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1},
$$
where $G_k$ are the Genocchi numbers and $L_k$ the Lucas numbers.

These are the inner coefficients of the corrected Theorem 11 of Bensaci, Boumahdi and Khaldi,
"Finite Sums Involving Fibonacci and Lucas Numbers"; the paper's printed coefficient omits the
last term. -/
noncomputable def genLucasCoeff (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), (Real.sqrt 5) ^ k *
      (Nat.choose n k : ℝ) * (genocchiNumber k : ℝ) *
      ((lucasNumber (n - k + 1) : ℝ) / (n - k + 1 : ℕ))) +
    2 * (Real.sqrt 5) ^ (n + 1) *
      ((genocchiNumber (n + 1) : ℝ) / (n + 1 : ℕ))

open Finset PowerSeries
open scoped goldenRatio

/-- The exponential generating series of `√5 ^ k * G k`. -/
private noncomputable abbrev genSeries : PowerSeries ℝ :=
  rescale (Real.sqrt 5) (PowerSeries.map (algebraMap ℚ ℝ) genocchiPowerSeries)

/-- The exponential generating series of `L (j + 1) / (j + 1)`. -/
private noncomputable def lucSeries : PowerSeries ℝ :=
  mk fun j => (lucasNumber (j + 1) : ℝ) / (j + 1 : ℕ) / j.factorial

/-- The exponential generating series of `2 * √5 ^ (n + 1) * G (n + 1) / (n + 1)`. -/
private noncomputable def corrSeries : PowerSeries ℝ :=
  mk fun n => 2 * (Real.sqrt 5) ^ (n + 1) *
    ((genocchiNumber (n + 1) : ℝ) / (n + 1 : ℕ)) / n.factorial

/-- The exponential series of `a t`. -/
private noncomputable abbrev expSeries (a : ℝ) := rescale a (exp ℝ)

-- The Genocchi series over `ℚ` times `e ^ x + 1` is `2x`; this repeats a private lemma of
-- `MathlibExt.NumberTheory.GenocchiBernoulli`.
private theorem genocchi_mul_exp_add_one :
    genocchiPowerSeries * (exp ℚ + 1) = 2 * X := by
  rw [genocchiPowerSeries_eq, mul_assoc, PowerSeries.inv_mul_cancel]
  · ring
  · simp [map_add, PowerSeries.constantCoeff_exp]

/-- The Genocchi series times `e ^ (√5 t) + 1` is `2√5 t`. -/
private theorem genSeries_mul :
    genSeries * (expSeries (Real.sqrt 5) + 1) = C (2 * Real.sqrt 5) * X := by
  have hmap : PowerSeries.map (algebraMap ℚ ℝ) genocchiPowerSeries * (exp ℝ + 1)
      = 2 * X := by
    have h := congrArg (PowerSeries.map (algebraMap ℚ ℝ)) genocchi_mul_exp_add_one
    simpa [map_mul, map_add, map_one, map_exp, map_X, map_ofNat] using h
  have h := congrArg (rescale (Real.sqrt 5)) hmap
  simp only [map_mul, map_add, map_one, rescale_X, map_ofNat] at h
  have hC : (C (2 * Real.sqrt 5) : PowerSeries ℝ) = 2 * C (Real.sqrt 5) := by
    rw [map_mul, map_ofNat]
  rw [hC, mul_assoc]
  exact h

/-- Coefficients of the Genocchi exponential generating series. -/
private theorem coeff_genSeries (k : ℕ) :
    coeff k genSeries
      = (Real.sqrt 5) ^ k * (genocchiNumber k : ℝ) / k.factorial := by
  have hkf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hG : ((genocchiNumber k : ℚ) : ℝ)
      = (k.factorial : ℝ) * ((coeff k genocchiPowerSeries : ℚ) : ℝ) := by
    simp [genocchiNumber_eq]
  unfold genSeries
  rw [coeff_rescale, coeff_map, eq_ratCast, hG]
  field_simp

/-- Coefficients of the Lucas-number exponential generating series. -/
private theorem coeff_lucSeries (j : ℕ) :
    coeff j lucSeries
      = (lucasNumber (j + 1) : ℝ) / (j + 1 : ℕ) / j.factorial := by
  rw [lucSeries, coeff_mk]

/-- The constant coefficient of `2` is `2`. -/
private theorem coeff_zero_two : coeff 0 (2 : PowerSeries ℝ) = 2 := by
  rw [← map_ofNat C 2, coeff_C, ite_eq_left rfl]

/-- Binet's formula: the Lucas series times `t` is `e ^ (φt) + e ^ (ψt) - 2`. -/
private theorem lucSeries_mul_X :
    lucSeries * X = expSeries φ + expSeries ψ - 2 := by
  ext n
  cases n with
  | zero =>
    simp only [coeff_zero_mul_X, map_sub, map_add, expSeries, coeff_rescale, coeff_exp,
      pow_zero, one_mul, coeff_zero_two, Nat.factorial_zero, Nat.cast_one, div_one, map_one]
    norm_num
  | succ n =>
    have h1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h02' : coeff (n + 1) (2 : PowerSeries ℝ) = 0 := by
      rw [← map_ofNat C 2, coeff_C, ite_eq_right (by omega)]
    rw [coeff_succ_mul_X, lucSeries, coeff_mk]
    simp only [map_sub, map_add, expSeries, coeff_rescale, coeff_exp, h02', sub_zero,
      ← add_mul, cb_lucas_binet, map_div₀, map_one, map_mul, map_natCast,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp

/-- The constant coefficient of the Genocchi series is `0`. -/
private theorem coeff_zero_genocchi : coeff 0 genocchiPowerSeries = 0 := by
  rw [genocchiPowerSeries_eq]
  have h : (2 : PowerSeries ℚ) * X * (exp ℚ + 1)⁻¹ = (2 * (exp ℚ + 1)⁻¹) * X := by
    ring
  rw [h, coeff_zero_mul_X]

/-- The correction series times `t` is twice the Genocchi series. -/
private theorem corrSeries_mul_X : corrSeries * X = C 2 * genSeries := by
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_mul_X, coeff_C_mul]
    unfold genSeries
    rw [coeff_rescale, pow_zero, one_mul, coeff_map, coeff_zero_genocchi, map_zero,
      mul_zero]
  | succ n =>
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [coeff_succ_mul_X, corrSeries, coeff_mk, coeff_C_mul, coeff_genSeries,
      Nat.factorial_succ]
    push_cast
    field_simp

/-- The correction series times `e ^ (√5 t) + 1` is `2√5 * 2`. -/
private theorem corrSeries_mul :
    corrSeries * (expSeries (Real.sqrt 5) + 1) = C (2 * Real.sqrt 5) * 2 := by
  apply mul_right_cancel₀ X_ne_zero
  calc corrSeries * (expSeries (Real.sqrt 5) + 1) * X
      = (corrSeries * X) * (expSeries (Real.sqrt 5) + 1) := by ring
    _ = (C 2 * genSeries) * (expSeries (Real.sqrt 5) + 1) := by rw [corrSeries_mul_X]
    _ = C 2 * (C (2 * Real.sqrt 5) * X) := by rw [mul_assoc, genSeries_mul]
    _ = C (2 * Real.sqrt 5) * 2 * X := by
        have h2 : (C (2 : ℝ) : PowerSeries ℝ) = 2 := map_ofNat C 2
        rw [h2]
        ring

/-- The series `e ^ (√5 t) + 1` is nonzero. -/
private theorem expAddOne_ne_zero : expSeries (Real.sqrt 5) + 1 ≠ 0 := by
  intro h0
  have h1 : coeff 0 (expSeries (Real.sqrt 5) : PowerSeries ℝ) = 1 := by
    simp [expSeries, coeff_rescale, coeff_exp]
  have h2 : coeff 0 (1 : PowerSeries ℝ) = 1 := by simp [coeff_one]
  have hc : coeff 0 (expSeries (Real.sqrt 5) + 1 : PowerSeries ℝ) = 0 := by
    rw [h0, map_zero]
  rw [map_add, h1, h2] at hc
  norm_num at hc

/-- The Genocchi–Lucas generating series is `2√5 e ^ (ψt)`. -/
private theorem main_series :
    genSeries * lucSeries + corrSeries = C (2 * Real.sqrt 5) * expSeries ψ := by
  have hψ : ψ + Real.sqrt 5 = φ := by unfold Real.goldenConj Real.goldenRatio; ring
  have h1 : expSeries ψ * expSeries (Real.sqrt 5) = expSeries φ := by
    rw [expSeries, expSeries, expSeries, exp_mul_exp_eq_exp_add, hψ]
  apply mul_right_cancel₀ expAddOne_ne_zero
  calc (genSeries * lucSeries + corrSeries) * (expSeries (Real.sqrt 5) + 1)
      = (genSeries * (expSeries (Real.sqrt 5) + 1)) * lucSeries
        + corrSeries * (expSeries (Real.sqrt 5) + 1) := by ring
    _ = (C (2 * Real.sqrt 5) * X) * lucSeries + C (2 * Real.sqrt 5) * 2 := by
        rw [genSeries_mul, corrSeries_mul]
    _ = C (2 * Real.sqrt 5) * (lucSeries * X) + C (2 * Real.sqrt 5) * 2 := by ring
    _ = C (2 * Real.sqrt 5) * (expSeries φ + expSeries ψ - 2)
        + C (2 * Real.sqrt 5) * 2 := by rw [lucSeries_mul_X]
    _ = C (2 * Real.sqrt 5) * (expSeries φ + expSeries ψ) := by ring
    _ = C (2 * Real.sqrt 5) * expSeries ψ * (expSeries (Real.sqrt 5) + 1) := by
        rw [← h1]
        ring

/-- For every natural `n`, the Genocchi–Lucas coefficient is `2 * √5` times the `n`th power of the
conjugate golden ratio. -/
private theorem genLucasCoeff_eq (n : ℕ) :
    genLucasCoeff n = 2 * Real.sqrt 5 * fibBeta ^ n := by
  have hψ : ψ = fibBeta := by unfold fibBeta Real.goldenConj; ring
  have hnf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  calc genLucasCoeff n
      = (n.factorial : ℝ) * coeff n (genSeries * lucSeries + corrSeries) := by
        rw [genLucasCoeff, map_add, coeff_mul,
          Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_add, mul_sum]
        congr 1
        · refine sum_congr rfl fun k hk => ?_
          have hkn := mem_range_succ_iff.mp hk
          have hkf : (k.factorial : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          have hnkf : ((n - k).factorial : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          have hnk1 : ((n - k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          rw [Nat.cast_choose ℝ hkn, coeff_genSeries, coeff_lucSeries]
          field_simp
        · rw [corrSeries, coeff_mk]
          field_simp
    _ = 2 * Real.sqrt 5 * fibBeta ^ n := by
        rw [main_series, coeff_C_mul, expSeries, coeff_rescale, coeff_exp, ← hψ]
        simp only [map_div₀, map_one, map_natCast]
        field_simp

/-- **Genocchi–Lucas expansion of $(x + \beta)^m$.** Let $\beta = (1 - \sqrt{5})/2$, and for every
natural number $n$ let
$$
c_n = \sum_{k=0}^{n} \sqrt{5}^{\,k} \binom{n}{k} G_k \frac{L_{n-k+1}}{n-k+1} +
2 \sqrt{5}^{\,n+1} \frac{G_{n+1}}{n+1}
$$
be the Genocchi–Lucas coefficient, where $G_k$ are the Genocchi numbers and $L_k$ the Lucas
numbers. Then for every natural number $m$ and every real number $x$,
$$
(x + \beta)^m = \frac{1}{2\sqrt{5}} \sum_{n=0}^{m} \binom{m}{n} c_n x^{m-n}.
$$

This corrects the paper's Theorem 11, whose inner sum omits the term
$2 \sqrt{5}^{\,n+1} G_{n+1}/(n+1)$; without it the identity already fails at $m = 0$, giving $0$
instead of $1$.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 11. -/
theorem add_fibBeta_pow_eq_sum_genLucasCoeff (m : ℕ)
    (x : ℝ) :
    (x + fibBeta) ^ m =
      (1 / (2 * Real.sqrt 5)) * ∑ n ∈ Finset.range (m + 1),
        (Nat.choose m n : ℝ) * genLucasCoeff n * x ^ (m - n) := by
  have h5 : Real.sqrt 5 ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 5)
  have h25 : (2 : ℝ) * Real.sqrt 5 ≠ 0 := mul_ne_zero (by norm_num) h5
  rw [add_comm x fibBeta, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [genLucasCoeff_eq]
  field_simp

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
