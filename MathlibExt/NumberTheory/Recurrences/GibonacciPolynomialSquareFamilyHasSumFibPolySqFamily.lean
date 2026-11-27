/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import MathlibExt.NumberTheory.Recurrences.GibonacciPolynomialRatioTelescoping
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

/-!
# Sums involving a family of gibonacci polynomial squares

We prove the unconditional sum of a family of Fibonacci polynomial squares
(`hasSum_fibPoly_sq_family`), identifying each term with a difference of successive
Fibonacci polynomial ratios.

Statements from Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares:
Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023.
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Series over a family of Fibonacci polynomial squares.** Let $x > 0$ be real, let
$\alpha = (x + \sqrt{x^2 + 4})/2$, and let $f_n = f_n(x)$ be the Fibonacci polynomials, given by
$f_0 = 0$, $f_1 = 1$ and $f_{n+2} = x f_{n+1} + f_n$, evaluated at $x$. Let $k$, $r$, $t$ be
positive integers and $p$ a natural number with $t \le 2p$. Then the series
$$\sum_{n=1}^{\infty} \frac{(-1)^{tk} f_r f_{2pk}}{f_{(2pn+t-p)k}^2 - (-1)^{tk} f_{pk}^2}$$
converges unconditionally, and its sum is $f_{tk+r} / f_{tk} - \alpha^r$.

This is the Fibonacci-polynomial case of Theorem 3.1 of the source. The source takes $x$ to be an
integer; the statement is made for real $x > 0$, which contains the positive integers.

Source: Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares:
Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023, Theorem 3.1
(`fq-2024-koshy11112023-thm-3.1`). -/
public theorem hasSum_fibPoly_sq_family {x : ℝ} (hx : 0 < x) {k p r t : ℕ} (hk : 0 < k)
    (hr : 0 < r) (ht : 0 < t) (htp : t ≤ 2 * p) :
    HasSum (fun n : ℕ =>
        (-1) ^ (t * k) * aeval x (generalizedFibonacciPolynomial 0 1 X 1 r) *
            aeval x (generalizedFibonacciPolynomial 0 1 X 1 (2 * p * k)) /
          (aeval x (generalizedFibonacciPolynomial 0 1 X 1 ((2 * p * (n + 1) + t - p) * k)) ^ 2 -
            (-1) ^ (t * k) * aeval x (generalizedFibonacciPolynomial 0 1 X 1 (p * k)) ^ 2))
      (aeval x (generalizedFibonacciPolynomial 0 1 X 1 (t * k + r)) /
          aeval x (generalizedFibonacciPolynomial 0 1 X 1 (t * k)) -
        ((x + Real.sqrt (x ^ 2 + 4)) / 2) ^ r) := by
  let W : ℕ → ℝ := fun n => aeval x (generalizedFibonacciPolynomial 0 1 X 1 n)
  have hW : ∀ j, W (j + 2) = x * W (j + 1) + 1 * W j := by
    intro j
    simp [W]
  have hW0 : W 0 = 0 := by simp [W]
  have hW1 : W 1 = 1 := by simp [W]
  have hcat : ∀ s i j, W (s + i) * W (s + j) - W s * W (s + i + j) =
      (-1) ^ s * W j * W i := fun s i j => by
    have h := horadam_generalized_catalan_identity x 1 W W W hW hW hW hW0 hW1 s i j
    rw [hW0, hW1] at h
    linear_combination h
  have hpos : ∀ n, 0 < W (n + 1) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [hW1]
    | one =>
      have h := hW 0
      simp only [zero_add, hW0, hW1, mul_one, mul_zero, add_zero] at h
      rw [show (1 : ℕ) + 1 = 2 from rfl, h]
      exact hx
    | more n ih0 ih1 =>
      have e : n + 2 + 1 = n + 1 + 2 := by omega
      rw [e, hW (n + 1)]
      exact add_pos (mul_pos hx ih1) (by simpa using ih0)
  have hposW : ∀ n, n ≠ 0 → 0 < W n := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simpa using hpos m
  have htel := hasSum_gibonacciPoly_pow_ratio_telescoping
    (generalizedFibonacciPolynomial 0 1 X 1) (Or.inl rfl) hx hk hr ht (m := 1) one_pos htp
  simp only [pow_one, one_mul] at htel
  refine htel.congr_fun fun n => ?_
  have hXeq : 2 * p * (n + 1) = 2 * p * n + 2 * p := by ring
  have hXge : 2 * p ≤ 2 * p * (n + 1) := by omega
  have hle : 2 * p ≤ 2 * p * (n + 1) + t := by omega
  have hAB : (2 * p * (n + 1) + t - 2 * p) * k + 2 * p * k =
      (2 * p * (n + 1) + t) * k := by
    rw [← add_mul, Nat.sub_add_cancel hle]
  have hArB : (2 * p * (n + 1) + t - 2 * p) * k + r + 2 * p * k =
      (2 * p * (n + 1) + t) * k + r := by omega
  have hAM : (2 * p * (n + 1) + t - 2 * p) * k + p * k =
      (2 * p * (n + 1) + t - p) * k := by
    have h : 2 * p * (n + 1) + t - 2 * p + p = 2 * p * (n + 1) + t - p := by omega
    rw [← add_mul, h]
  have hAM2 : (2 * p * (n + 1) + t - 2 * p) * k + p * k + p * k =
      (2 * p * (n + 1) + t) * k := by
    have h2 : p * k + p * k = 2 * p * k := by ring
    omega
  have hAeq : (2 * p * (n + 1) + t - 2 * p) * k = 2 * (p * n * k) + t * k := by
    have h1 : 2 * p * (n + 1) + t = (2 * p * n + t) + 2 * p := by ring
    rw [h1, Nat.add_sub_cancel]
    ring
  have hneg1 : (-1 : ℝ) ^ (2 * (p * n * k)) = 1 := by
    rw [pow_mul]
    norm_num
  have hneg : (-1 : ℝ) ^ ((2 * p * (n + 1) + t - 2 * p) * k) = (-1) ^ (t * k) := by
    rw [hAeq, pow_add, hneg1, one_mul]
  have hApos0 : 0 < (2 * p * (n + 1) + t - 2 * p) * k := Nat.mul_pos (by omega) hk
  have hBpos0 : 0 < (2 * p * (n + 1) + t) * k := Nat.mul_pos (by omega) hk
  have hA0 : W ((2 * p * (n + 1) + t - 2 * p) * k) ≠ 0 := (hposW _ (by omega)).ne'
  have hB0 : W ((2 * p * (n + 1) + t) * k) ≠ 0 := (hposW _ (by omega)).ne'
  have hAB0 : W ((2 * p * (n + 1) + t - 2 * p) * k) * W ((2 * p * (n + 1) + t) * k) ≠ 0 :=
    mul_ne_zero hA0 hB0
  have h1 := hcat ((2 * p * (n + 1) + t - 2 * p) * k) r (2 * p * k)
  rw [hAB, hArB, hneg] at h1
  have hN : (-1) ^ (t * k) * W r * W (2 * p * k) =
      W ((2 * p * (n + 1) + t - 2 * p) * k + r) * W ((2 * p * (n + 1) + t) * k) -
        W ((2 * p * (n + 1) + t - 2 * p) * k) * W ((2 * p * (n + 1) + t) * k + r) := by
    linear_combination -h1
  have h2 := hcat ((2 * p * (n + 1) + t - 2 * p) * k) (p * k) (p * k)
  rw [hAM2, hAM, hneg] at h2
  have hD : W ((2 * p * (n + 1) + t - p) * k) ^ 2 - (-1) ^ (t * k) * W (p * k) ^ 2 =
      W ((2 * p * (n + 1) + t - 2 * p) * k) * W ((2 * p * (n + 1) + t) * k) := by
    linear_combination h2
  change (-1) ^ (t * k) * W r * W (2 * p * k) /
        (W ((2 * p * (n + 1) + t - p) * k) ^ 2 - (-1) ^ (t * k) * W (p * k) ^ 2) =
      W ((2 * p * (n + 1) + t - 2 * p) * k + r) / W ((2 * p * (n + 1) + t - 2 * p) * k) -
        W ((2 * p * (n + 1) + t) * k + r) / W ((2 * p * (n + 1) + t) * k)
  rw [hN, hD]
  field_simp

end

end MetaMathlibExt
