/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import MathlibExt.Analysis.ScalarCalculus

/-!
# Integral formula for paired reciprocals

Expanding the geometric series with ratio `x ^ m` gives the integrand on `(0, 1)`.
The terms are dominated by `(1 - x) * x ^ i`, whose sum is one on this interval.
-/

open MeasureTheory Set

namespace MetaMathlibExt
namespace tsum_alternating_inv_eq_integral

private lemma integral_term (s : ℝ) (hs : 0 ≤ s) (m i : ℕ) :
    (∫ x in (0 : ℝ)..1, (1 - x) * x ^ s * (x ^ m) ^ i) =
      1 / (s + ↑(m * i) + 1) - 1 / (s + ↑(m * i) + 1 + 1) := by
  let t : ℝ := s + ↑(m * i)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  obtain ⟨hint, hval⟩ := (ScalarCalculus.hasDerivAt_and_integral_powerLaw t).2 (by linarith)
  obtain ⟨hint', hval'⟩ :=
    (ScalarCalculus.hasDerivAt_and_integral_powerLaw (t + 1)).2 (by linarith)
  rw [← hval, ← hval', ← intervalIntegral.integral_sub hint hint']
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro x hx
  dsimp only
  rw [Real.rpow_add_one hx.1.ne', show x ^ t = x ^ s * x ^ (m * i) from
    Real.rpow_add_natCast hx.1.ne' s (m * i), pow_mul]
  ring

private lemma hasSum_bound {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasSum (fun i : ℕ => (1 - x) * x ^ i) 1 := by
  simpa [mul_inv_cancel₀ (sub_ne_zero.mpr hx.2.ne')] using
    (hasSum_geometric_of_lt_one hx.1.le hx.2).mul_left (1 - x)

private lemma hasSum_integrals {s : ℝ} (hs : 0 ≤ s) {m : ℕ} (hm : m ≠ 0) :
    HasSum (fun i : ℕ => ∫ x in (0 : ℝ)..1, (1 - x) * x ^ s * (x ^ m) ^ i)
      (∫ x in (0 : ℝ)..1, (1 - x) * x ^ s / (1 - x ^ m)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (bound := fun (i : ℕ) (x : ℝ) => (1 - x) * x ^ i)
  · intro i
    apply Continuous.aestronglyMeasurable
    fun_prop
  · intro i
    refine ae_of_all _ fun x hx => ?_
    rw [uIoc_of_le zero_le_one] at hx
    have hx₀ := hx.1.le
    have hx₁ := sub_nonneg.mpr hx.2
    have hxm := pow_le_of_le_one hx.1.le hx.2 hm
    have hxs := Real.rpow_le_one hx.1.le hx.2 hs
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ (1 - x) * x ^ s * (x ^ m) ^ i)]
    calc
      (1 - x) * x ^ s * (x ^ m) ^ i ≤ (1 - x) * 1 * x ^ i := by
        gcongr
      _ = _ := by rw [mul_one]
  · filter_upwards [volume.ae_ne 1] with x hxne hx
    rw [uIoc_of_le zero_le_one] at hx
    exact (hasSum_bound ⟨hx.1, hx.2.lt_of_ne hxne⟩).summable
  · apply (intervalIntegrable_const (c := (1 : ℝ))).congr_uIoo
    rw [uIoo_of_le zero_le_one]
    exact fun x hx => (hasSum_bound hx).tsum_eq.symm
  · filter_upwards [volume.ae_ne 1] with x hxne hx
    rw [uIoc_of_le zero_le_one] at hx
    have hxm := (pow_le_of_le_one hx.1.le hx.2 hm).trans_lt (hx.2.lt_of_ne hxne)
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one (pow_nonneg hx.1.le m) hxm).mul_left ((1 - x) * x ^ s)

end tsum_alternating_inv_eq_integral

set_option linter.unusedVariables false in
/-- **Integral formula for an alternating series of reciprocals.** Let $r$ and $m$ be natural
numbers with $2 \le r \le m$ and let $\alpha$ be a real number with $0 \le \alpha < 1$. Then

$$\sum_{i \ge 0} \Bigl( \frac{1}{r + im - \alpha} - \frac{1}{r + 1 + im - \alpha} \Bigr) =
\int_0^1 \frac{(1 - x)\, x^{r - 1 - \alpha}}{1 - x^m} \, dx.$$

Source: Nicholas Dent and Caleb M. Shor, *On Residues of Rounded Shifted
Fractions with a Common Numerator*, Journal of Integer Sequences 27 (2024),
Article 24.2.5, Proposition 36 (`jis-2024-24.2.5-prop-36`). -/
public theorem tsum_alternating_inv_eq_integral (r m : ℕ) (hr : 2 ≤ r)
    (hrm : r ≤ m) (α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    ∑' i : ℕ, (1 / ((r : ℝ) + i * m - α) - 1 / ((r : ℝ) + 1 + i * m - α)) =
      ∫ x in (0 : ℝ)..1, (1 - x) * x ^ ((r : ℝ) - 1 - α) / (1 - x ^ m) := by
  have hs : 0 ≤ (r : ℝ) - 1 - α := by
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hsum := tsum_alternating_inv_eq_integral.hasSum_integrals hs (m := m) (by omega)
  rw [← hsum.tsum_eq]
  apply tsum_congr
  intro i
  rw [tsum_alternating_inv_eq_integral.integral_term _ hs]
  push_cast
  ring_nf

end MetaMathlibExt
