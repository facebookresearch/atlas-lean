/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalks
import Mathlib.Algebra.BigOperators.Field
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Self-convolution of higher-order Fibonacci numbers

For `m ≥ 1`, an integer-indexed rational sequence `F` with the order-`m` Fibonacci recurrence
and initial values `F₀ = ⋯ = Fₘ₋₂ = 0` and `Fₘ₋₁ = 1` has a self-convolution formula in terms of
weighted sums and first moments at every natural index `n ≥ 2*m - 2`. This is the range in which
the shift in Theorem 4 is nonnegative; below it the convolution vanishes, but the displayed
weighted-sum formula does not.

## References

* Jan Sedlák and Antonín Slavík, *Walks in Tiled Rectangles and Self-Convolutions of Higher-Order
  Fibonacci Numbers*, *Journal of Integer Sequences* 29 (2026), Article 26.3.7, pp. 1–15,
  Theorem 4. The proof obtains the recurrence of Theorem 1 by formal differentiation, then
  solves it as in Theorem 3.
* Saber Elaydi, *An Introduction to Difference Equations*, 3rd ed., Springer, 2005,
  formula (1.2.6), cited in the proof of Theorem 3 for the first-order recurrence solution.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted

open PowerSeries

private noncomputable def shiftedSeries (F : ℤ → ℚ) (m : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk (fun n => F ((n : ℤ) + (m : ℤ) - 1))

-- Subtract consecutive recurrence equations: all but the first and last summands cancel.
private lemma recurrence_difference {m : ℕ} (hm : 1 ≤ m) {F : ℤ → ℚ}
    (hF : IsHigherFibRecurrence m F) (t : ℤ) :
    F (t + 1) - 2 * F t + F (t - m) = 0 := by
  have h₁ := hF (t + 1)
  have h₀ := hF t
  rw [← Nat.sub_add_cancel hm, Finset.sum_range_succ'] at h₁
  rw [← Nat.sub_add_cancel hm, Finset.sum_range_succ] at h₀
  have hi (j : ℕ) : t + 1 - (↑(j + 1) : ℤ) - 1 = t - (j : ℤ) - 1 := by
    push_cast
    ring
  have hm' : t - (↑(m - 1) : ℤ) - 1 = t - (m : ℤ) := by
    rw [Nat.cast_sub hm]
    ring
  simp only [hi, Nat.cast_zero, sub_zero, add_sub_cancel_right] at h₁
  rw [hm'] at h₀
  linear_combination h₁ - h₀

-- The factor 1 - X makes the denominator sparse.
private lemma sparse_denominator_mul {m : ℕ} (hm : 1 ≤ m) {F : ℤ → ℚ}
    (hF : IsStandardHigherFib m F) :
    (1 - 2 * X + X ^ (m + 1)) * shiftedSeries F m = 1 - X := by
  have hnext : F (m : ℤ) = 1 := by
    rw [hF.1 (m : ℤ), Finset.sum_eq_single 0]
    · simpa using hF.2.2
    · intro j hj hj0
      have hjm := Finset.mem_range.mp hj
      have hj₂ : j + 1 ≤ m := by omega
      have hindex : ((m : ℤ) - (j : ℤ) - 1) = ((m - (j + 1) : ℕ) : ℤ) := by
        rw [Nat.cast_sub hj₂]
        push_cast
        ring
      rw [hindex]
      exact hF.2.1 _ (by omega)
    · simp [show 0 < m by omega]
  apply PowerSeries.ext
  intro n
  simp only [shiftedSeries, add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_ofNat_mul, coeff_X_pow_mul', coeff_mk]
  rcases n with _ | (_ | n)
  · simp [coeff_zero_X_mul, hF.2.2]
  · norm_num [coeff_succ_X_mul, hF.2.2, hnext, show ¬ m + 1 ≤ 1 by omega]
  · have hdiff := recurrence_difference hm hF.1 ((n : ℤ) + m)
    have hsame : (n : ℤ) + (m : ℤ) - (m : ℤ) = n := by ring
    rw [hsame] at hdiff
    have htail : (if m + 1 ≤ n + 1 + 1 then
          F ((↑(n + 1 + 1 - (m + 1)) : ℤ) + (m : ℤ) - 1) else 0) = F (n : ℤ) := by
      split_ifs with h
      · congr 1
        rw [Nat.cast_sub h]
        push_cast
        ring
      · exact (hF.2.1 n (by omega)).symm
    have hcurr : (↑(n + 1 + 1) : ℤ) + (m : ℤ) - 1 = (n : ℤ) + (m : ℤ) + 1 := by
      push_cast
      ring
    have hprev : (↑(n + 1) : ℤ) + (m : ℤ) - 1 = (n : ℤ) + (m : ℤ) := by
      push_cast
      ring
    rw [coeff_succ_X_mul, coeff_mk, htail, hcurr, hprev, coeff_one, coeff_X]
    simp [hdiff]

private lemma coeff_shifted_square (F : ℤ → ℚ) (m n : ℕ) :
    coeff n (shiftedSeries F m * shiftedSeries F m) = higherFibWalk F m n := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, higherFibWalk]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [shiftedSeries, coeff_mk, Nat.cast_sub (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]

private lemma shifted_square_identity {m : ℕ} (hm : 1 ≤ m) {F : ℤ → ℚ}
    (hF : IsStandardHigherFib m F) :
    ((m : ℚ⟦X⟧) + 1 - 2 * (m : ℚ⟦X⟧) * X) * (shiftedSeries F m * shiftedSeries F m) =
      ((m : ℚ⟦X⟧) + 1 - (m : ℚ⟦X⟧) * X) * shiftedSeries F m +
        (1 - X) * (X * derivative (R := ℚ) (shiftedSeries F m)) := by
  let A := shiftedSeries F m
  let E : ℚ⟦X⟧ := 1 - 2 * X + X ^ (m + 1)
  let b : ℚ⟦X⟧ := (m : ℚ⟦X⟧) + 1
  have hEA : E * A = 1 - X := sparse_denominator_mul hm hF
  have hD : E * derivative (R := ℚ) A + A * derivative (R := ℚ) E = -1 := by
    simpa only [Derivation.leibniz, smul_eq_mul, map_sub, derivative_one, derivative_X, zero_sub]
      using congrArg (derivative (R := ℚ)) hEA
  have hE : E ≠ 0 := by
    intro he
    have hz := congrArg (constantCoeff (R := ℚ)) he
    simp [E] at hz
  have h2X : derivative (R := ℚ) ((2 : ℚ⟦X⟧) * X) = 2 := by
    simpa only [map_ofNat] using derivative_C_mul_X (2 : ℚ)
  have hE' : b * E - X * derivative (R := ℚ) E = b - 2 * (m : ℚ⟦X⟧) * X := by
    simp only [E, b, map_add, map_sub, derivative_one, h2X, derivative_X_pow_succ,
      map_natCast, map_one, zero_sub]
    rw [pow_succ' X m]
    ring
  change (b - 2 * (m : ℚ⟦X⟧) * X) * (A * A) =
    (b - (m : ℚ⟦X⟧) * X) * A + (1 - X) * (X * derivative (R := ℚ) A)
  apply mul_left_cancel₀ hE
  calc
    _ = (1 - X) * A * (b * E - X * derivative (R := ℚ) E) := by
      rw [hE']
      linear_combination A * (b - 2 * (m : ℚ⟦X⟧) * X) * hEA
    _ = _ := by
      dsimp only [b]
      linear_combination -(1 - X) * X * hD - X * hEA

private lemma convolution_shift {m n : ℕ} (hm : 1 ≤ m) (hn : 2 * m - 2 ≤ n) {F : ℤ → ℚ}
    (hF : IsStandardHigherFib m F) :
    (∑ i ∈ Finset.range (n + 1), F (i : ℤ) * F ((n : ℤ) - (i : ℤ))) =
      higherFibWalk F m (n - (2 * m - 2)) := by
  let G : ℚ⟦X⟧ := PowerSeries.mk (fun k => F (k : ℤ))
  let A := shiftedSeries F m
  have hG : G = X ^ (m - 1) * A := by
    apply PowerSeries.ext
    intro k
    simp only [G, A, shiftedSeries, coeff_mk, coeff_X_pow_mul']
    split_ifs with hk
    · congr 1
      rw [Nat.cast_sub hk, Nat.cast_sub hm]
      ring
    · exact hF.2.1 k (by omega)
  calc
    _ = coeff n (G * G) := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [G, coeff_mk, Nat.cast_sub (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    _ = coeff n (X ^ (2 * m - 2) * (A * A)) := by
      rw [hG, show 2 * m - 2 = (m - 1) + (m - 1) by omega, pow_add]
      ac_rfl
    _ = _ := by
      rw [coeff_X_pow_mul', ite_eq_left hn]
      exact coeff_shifted_square F m _

/-- **Self-convolution of higher-order Fibonacci numbers.** Let $m \ge 1$ and let
$(F_n)_{n \in \mathbb{Z}}$ be a sequence of rational numbers with
$F_n = F_{n-1} + \dots + F_{n-m}$ for every integer $n$, $F_i = 0$ for $0 \le i < m - 1$ and
$F_{m-1} = 1$. For $p \ge 0$ let $w_p = \sum_{j=0}^{p} F_{j+m-1} F_{p-j+m-1}$; for integers
$N$, $l$ and rational $q$ let $S(N, l, q) = \sum_{k=0}^{N} q^k F_{k+l}$ and
$S_2(N, l, q) = \sum_{k=0}^{N} k q^k F_{k+l}$, both equal to $0$ when $N < 0$. Put
$q = (m+1)/(2m)$. Then for every integer $n \ge 2m - 2$, writing $p = n - 2m + 2$,

$$
\sum_{i=0}^{n} F_i F_{n-i} = w_p = \left(\frac{2m}{m+1}\right)^{p} +
\frac{(2m)^{p-1}}{(m+1)^{p}} \bigl((m+2) S(p-1, m, q) + S_2(p-1, m, q) -
m S(p-1, m-1, q) - S_2(p-1, m-1, q)\bigr).
$$

The source states the formula for all $n \ge 0$, but for $m \ge 2$ it fails when
$n < 2m - 2$: at $m = 2$ and $n = 0$ the left side is $0$ and the right side is $9/16$.

Source: Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles
and Self-Convolutions of Higher-Order Fibonacci Numbers",
Theorem 4. -/
theorem higherFib_selfConvolution_eq_weighted_sums
    (m : ℕ) (hm : 1 ≤ m) (F : ℤ → ℚ)
    (hF : IsStandardHigherFib m F) (n : ℕ) (hn : 2 * m - 2 ≤ n) :
    (∑ i ∈ Finset.range (n + 1), F (i : ℤ) * F ((n : ℤ) - (i : ℤ))) =
        higherFibWalk F m (n - (2 * m - 2)) ∧
      (∑ i ∈ Finset.range (n + 1), F (i : ℤ) * F ((n : ℤ) - (i : ℤ))) =
        (2 * (m : ℚ) / ((m : ℚ) + 1)) ^ ((n : ℤ) - 2 * (m : ℤ) + 2) +
          ((2 * (m : ℚ)) ^ ((n : ℤ) - 2 * (m : ℤ) + 1) /
              ((m : ℚ) + 1) ^ ((n : ℤ) - 2 * (m : ℤ) + 2)) *
            (((m : ℚ) + 2) *
                weightedHigherFibSum F m ((n : ℤ) - 2 * (m : ℤ) + 1)
                  (m : ℤ) (((m : ℚ) + 1) / (2 * (m : ℚ))) +
              weightedHigherFibMomentSum F m
                ((n : ℤ) - 2 * (m : ℤ) + 1) (m : ℤ)
                (((m : ℚ) + 1) / (2 * (m : ℚ))) -
              (m : ℚ) *
                weightedHigherFibSum F m ((n : ℤ) - 2 * (m : ℤ) + 1)
                  ((m : ℤ) - 1) (((m : ℚ) + 1) / (2 * (m : ℚ))) -
              weightedHigherFibMomentSum F m
                ((n : ℤ) - 2 * (m : ℤ) + 1) ((m : ℤ) - 1)
                (((m : ℚ) + 1) / (2 * (m : ℚ)))) := by
  have hshift := convolution_shift hm hn hF
  refine ⟨hshift, ?_⟩
  let p := n - (2 * m - 2)
  have hp : (n : ℤ) - 2 * (m : ℤ) + 2 = (p : ℤ) := by dsimp [p]; omega
  have hp' : (n : ℤ) - 2 * (m : ℤ) + 1 = (p : ℤ) - 1 := by omega
  let a : ℚ := 2 * (m : ℚ)
  let b : ℚ := (m : ℚ) + 1
  let q := b / a
  let r := a / b
  have ha : a ≠ 0 := by
    have hm₀ : 0 < m := by omega
    dsimp [a]
    positivity
  have hb : b ≠ 0 := by dsimp [b]; positivity
  let w := higherFibWalk F m
  let c (k : ℕ) := ((k : ℚ) + (m : ℚ) + 2) * F ((k : ℤ) + (m : ℤ)) -
    ((k : ℚ) + (m : ℚ)) * F ((k : ℤ) + (m : ℤ) - 1)
  have hw₀ : w 0 = 1 := by simp [w, higherFibWalk, hF.2.2]
  have hstep (n : ℕ) : b * w (n + 1) - a * w n = c n := by
    let A := shiftedSeries F m
    have hseries := shifted_square_identity hm hF
    change ((m : ℚ⟦X⟧) + 1 - 2 * (m : ℚ⟦X⟧) * X) * (A * A) =
      ((m : ℚ⟦X⟧) + 1 - (m : ℚ⟦X⟧) * X) * A +
        (1 - X) * (X * derivative (R := ℚ) A) at hseries
    have hweighted (k : ℕ) : coeff k (X * derivative (R := ℚ) A) = (k : ℚ) * coeff k A := by
      cases k with
      | zero => simp [coeff_zero_X_mul]
      | succ k => simp [coeff_succ_X_mul, coeff_derivative, mul_comm]
    have hA (k : ℕ) : coeff k A = F ((k : ℤ) + (m : ℤ) - 1) := coeff_mk _ _
    have hW (k : ℕ) : coeff k (A * A) = higherFibWalk F m k := coeff_shifted_square F m k
    have hcoeff := congrArg (coeff (R := ℚ) (n + 1)) hseries
    simp only [add_mul, sub_mul, one_mul, mul_assoc, map_add, map_sub, coeff_ofNat_mul,
      coeff_natCast_mul, coeff_succ_X_mul, hweighted, Nat.cast_add, Nat.cast_one,
      hW, hA] at hcoeff
    rw [show (n : ℤ) + 1 + (m : ℤ) - 1 = (n : ℤ) + (m : ℤ) by ring] at hcoeff
    dsimp only [a, b, w, c]
    linear_combination hcoeff
  -- Multiplication by q^k turns the first-order recurrence into a telescoping sum.
  let f (k : ℕ) := q ^ k * w k
  have htel : q ^ p * w p - 1 = (∑ k ∈ Finset.range p, q ^ k * c k) / a := by
    calc
      _ = ∑ k ∈ Finset.range p, (f (k + 1) - f k) := by
        rw [Finset.sum_range_sub]
        simp [f, hw₀]
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        rw [← hstep, show f (k + 1) = q ^ k * q * w (k + 1) by simp [f, pow_succ]]
        dsimp only [f, q]
        field_simp
  have hinv : r * q = 1 := by dsimp only [r, q]; field_simp
  have hform : w p = r ^ p + (r ^ p / a) * (∑ k ∈ Finset.range p, q ^ k * c k) := by
    calc
      w p = r ^ p * (q ^ p * w p) := by rw [← mul_assoc, ← mul_pow, hinv, one_pow, one_mul]
      _ = _ := by linear_combination r ^ p * htel
  have hfactor : a ^ ((p : ℤ) - 1) / b ^ (p : ℤ) = r ^ p / a := by
    rw [zpow_sub₀ ha, zpow_one, zpow_natCast, zpow_natCast, show r = a / b from rfl, div_pow]
    ring
  have hs (l : ℤ) :
      weightedHigherFibSum F m ((p : ℤ) - 1) l q =
        ∑ k ∈ Finset.range p, q ^ k * F ((k : ℤ) + l) := by
    cases p with
    | zero => norm_num [weightedHigherFibSum]
    | succ k =>
      rw [show (↑(k + 1) : ℤ) - 1 = (k : ℤ) by omega]
      simp [weightedHigherFibSum, zpow_natCast]
  have hs₂ (l : ℤ) :
      weightedHigherFibMomentSum F m ((p : ℤ) - 1) l q =
        ∑ k ∈ Finset.range p, (k : ℚ) * q ^ k * F ((k : ℤ) + l) := by
    cases p with
    | zero => norm_num [weightedHigherFibMomentSum]
    | succ k =>
      rw [show (↑(k + 1) : ℤ) - 1 = (k : ℤ) by omega]
      simp [weightedHigherFibMomentSum, zpow_natCast]
  rw [hshift, hp, hp']
  change w p = r ^ (p : ℤ) + (a ^ ((p : ℤ) - 1) / b ^ (p : ℤ)) * _
  change _ = _ + _ * (((m : ℚ) + 2) * weightedHigherFibSum F m ((p : ℤ) - 1) (m : ℤ) q +
    weightedHigherFibMomentSum F m ((p : ℤ) - 1) (m : ℤ) q -
    (m : ℚ) * weightedHigherFibSum F m ((p : ℤ) - 1) ((m : ℤ) - 1) q -
    weightedHigherFibMomentSum F m ((p : ℤ) - 1) ((m : ℤ) - 1) q)
  rw [zpow_natCast, hfactor, hform]
  congr 2
  simp only [hs, hs₂, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (k : ℤ) + ((m : ℤ) - 1) = (k : ℤ) + (m : ℤ) - 1 by ring]
  dsimp only [c]
  ring

end MathlibExt.NumberTheory.Recurrences.HigherFibonacciWalksWanted
