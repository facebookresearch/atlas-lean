/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.SpecialFunctions.Gamma.BetaPowerProduct
import all MathlibExt.LinearAlgebra.PowerSumMatrix

/-!
# An alternating sum of binomial ratios

For positive `k`, the sum of the signed binomial ratios is `2 / (k * (k + 1))`.
The identity also holds at `k = 0` with Lean's convention for division by zero.
For `k ≥ 2`, integrate the trace of the `k`-th power of `diag(x, 1 - x)` over `[0, 1]`:
the determinant terms give equal-power beta integrals, while reflection reduces the trace
integral to twice the integral of `x ^ k`.

## References

* Peiran Ding, Yanjun Zhu and Lei Wang, *A New Formula for the Sum of Integer Powers Based on
  Elementary Matrix Theory*, INTEGERS 25 (2025), Article A98, pp. 1–15, Theorem 4 (§3.3, p. 11).
  This proof uses Theorem 1 (eqs. (5)–(6)) and Lemma 3 rather than the paper's limit argument.
  <https://math.colgate.edu/~integers/z98/z98.pdf>
* A K Amir, G Jeriko and M Jusmawati, *A method for calculating the sum of diagonal and anti
  diagonal of power matrices without explicitly calculating its matrices*, Journal of Physics:
  Conference Series 1277 (2019), Article 012038, pp. 1–9, §2, Theorem 1. Cited for the
  trace formula by Ding, Zhu and Wang.
* Wu-Sheng Wang, *Some properties of k-gamma and k-beta functions*, ITM Web of Conferences 7
  (2016), Article 07003, pp. 1–6. Cited for the beta–gamma identity in the proof of Lemma 3.
* `MathlibExt.LinearAlgebra.PowerSumMatrix` supplies `trace_pow_factorial`, `choose_cast_eq`
  and `factorial_cast_eq`; `MathlibExt.Analysis.SpecialFunctions.Gamma.BetaPowerProduct`
  supplies `intervalIntegral.integral_pow_one_sub_pow`.
-/

namespace MathlibExt.LinearAlgebra.PowerSumMatrixWanted

open Finset intervalIntegral
open MeasureTheory (volume)

private theorem sum_choose_div_choose_eq_real {k : ℕ} (hk : 2 ≤ k) :
    ∑ r ∈ range (k / 2 + 1),
        (-1 : ℝ) ^ r / (((k - r : ℕ) : ℝ) * (2 * r + 1)) *
          (Nat.choose (k - r) r : ℝ) * (Nat.choose (2 * r) r : ℝ)⁻¹ =
      2 / ((k : ℝ) * (k + 1)) := by
  let c (r : ℕ) : ℝ := (-1 : ℝ) ^ r *
    (((k - r - 1).factorial : ℝ) / ((r.factorial : ℝ) * ((k - 2 * r).factorial : ℝ)))
  have htrace (x : ℝ) : x ^ k + (1 - x) ^ k = (k : ℝ) *
      ∑ r ∈ range (k / 2 + 1), c r * (x ^ r * (1 - x) ^ r) := by
    let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![x, 1 - x]
    have hpow : (M ^ k).trace = x ^ k + (1 - x) ^ k := by
      simp [M, Matrix.diagonal_pow, Fin.sum_univ_two]
    have htr : M.trace = 1 := by
      simp [M, Fin.sum_univ_two]
    have hdet : M.det = x * (1 - x) := by
      simp [M, Matrix.det_diagonal, Fin.prod_univ_two]
    simpa only [hpow, hdet, htr, one_pow, mul_one, mul_pow, c] using trace_pow_factorial M k hk
  have hleft : (∫ x in (0 : ℝ)..1, x ^ k + (1 - x) ^ k) = 2 / ((k : ℝ) + 1) := by
    have hp : IntervalIntegrable (fun x : ℝ ↦ x ^ k) volume 0 1 :=
      (continuous_id.pow k).intervalIntegrable 0 1
    have hq : IntervalIntegrable (fun x : ℝ ↦ (1 - x) ^ k) volume 0 1 :=
      ((continuous_const.sub continuous_id).pow k).intervalIntegrable 0 1
    have hreflect : (∫ x in (0 : ℝ)..1, (1 - x) ^ k) = ∫ x in (0 : ℝ)..1, x ^ k := by
      simpa only [sub_self, sub_zero] using
        integral_comp_sub_left (a := (0 : ℝ)) (b := 1) (fun x : ℝ ↦ x ^ k) 1
    rw [integral_add hp hq, hreflect, integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero]
    ring
  have hi (r : ℕ) (_ : r ∈ range (k / 2 + 1)) :
      IntervalIntegrable (fun x : ℝ ↦ c r * (x ^ r * (1 - x) ^ r)) volume 0 1 :=
    (show Continuous (fun x : ℝ ↦ c r * (x ^ r * (1 - x) ^ r)) by fun_prop).intervalIntegrable 0 1
  have hsum := calc
    2 / ((k : ℝ) + 1) = ∫ x in (0 : ℝ)..1, x ^ k + (1 - x) ^ k := hleft.symm
    _ = ∫ x in (0 : ℝ)..1, (k : ℝ) *
        ∑ r ∈ range (k / 2 + 1), c r * (x ^ r * (1 - x) ^ r) :=
      integral_congr fun x _ ↦ htrace x
    _ = (k : ℝ) * ∑ r ∈ range (k / 2 + 1),
        c r * (1 / ((2 * r + 1 : ℝ) * ((2 * r).choose r : ℝ))) := by
      rw [integral_const_mul, integral_finsetSum hi]
      simp only [integral_const_mul, integral_pow_one_sub_pow]
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  calc
    _ = ∑ r ∈ range (k / 2 + 1),
        c r * (1 / ((2 * r + 1 : ℝ) * ((2 * r).choose r : ℝ))) := by
      refine sum_congr rfl fun r hr ↦ ?_
      rw [mem_range] at hr
      have hkr : 0 < k - r := by omega
      have hrk : r ≤ k - r := by omega
      have hsub : k - r - r = k - 2 * r := by omega
      have hkrR : ((k - r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hkr.ne'
      have hcoeff : ((k - r).choose r : ℝ) / ((k - r : ℕ) : ℝ) =
          ((k - r - 1).factorial : ℝ) / ((r.factorial : ℝ) * ((k - 2 * r).factorial : ℝ)) := by
        rw [choose_cast_eq _ _ hrk, hsub, factorial_cast_eq hkr]
        field_simp [hkrR, factorial_cast_ne_zero]
      simp only [c]
      rw [← hcoeff]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ = _ := by
      rw [mul_comm (k : ℝ)] at hsum
      apply (eq_div_iff (show (k : ℝ) * ((k : ℝ) + 1) ≠ 0 by positivity)).2
      rw [← mul_assoc, ← hsum]
      exact div_mul_cancel₀ _ (by positivity)

/-- **Theorem 4**: for every positive integer `k`,
`∑_{r=0}^{⌊k/2⌋} (-1)^r / ((k - r)(2r + 1)) * C(k - r, r)
  * C(2r, r)^(-1) = 2 / (k (k + 1))`. Stated for all
`k ∈ ℕ`: at `k = 0` both sides are `0` under division by
zero.

Source: Peiran Ding, Yanjun Zhu and Lei Wang, "A New
Formula for the Sum of Integer Powers Based on
Elementary Matrix Theory", INTEGERS 25 (2025), Article A98, Theorem 4
(`integers-2025-A98-thm-4`). -/
public theorem sum_choose_div_choose_eq (k : ℕ) :
    ∑ r ∈ Finset.range (k / 2 + 1),
        (-1 : ℚ) ^ r / (((k - r : ℕ) : ℚ) * (2 * r + 1)) *
          (Nat.choose (k - r) r : ℚ) *
          (Nat.choose (2 * r) r : ℚ)⁻¹ =
      2 / ((k : ℚ) * (k + 1)) := by
  by_cases hk : 2 ≤ k
  · apply Rat.cast_injective (α := ℝ)
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_inv, Rat.cast_pow,
      Rat.cast_neg, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat] using
      sum_choose_div_choose_eq_real hk
  · obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    all_goals norm_num [Finset.sum_range_succ]

end MathlibExt.LinearAlgebra.PowerSumMatrixWanted
