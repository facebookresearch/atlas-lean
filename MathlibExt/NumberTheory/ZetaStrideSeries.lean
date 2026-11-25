/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import MathlibExt.Analysis.SpecialFunctions.Log.AlternatingHarmonic

/-!
# A series for integer zeta values

The sum of `1 / (n ^ t * (2 * n - 1))` over positive integers is expressed in terms of
`Real.log 2` and the zeta values at the integers from `2` to `t`.
-/

namespace MetaMathlibExt

open Filter Topology

namespace tsum_inv_pow_mul_two_mul_sub_one

private theorem hasSum_base :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * (2 * n + 1))) (2 * Real.log 2) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity) _).2
  -- Pair consecutive terms in the even partial sums of the alternating harmonic series.
  have h := Real.tendsto_sum_alternating_harmonic.comp
    (tendsto_atTop_mono (fun n : ℕ => show n ≤ 2 * n by omega) tendsto_id)
  apply (h.const_mul 2).congr
  intro N
  change 2 * (∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i / (i + 1)) = _
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ _ (2 * N), Finset.sum_range_succ _ N, mul_add, mul_add, ih]
    rw [pow_succ _ (2 * N), (even_two.mul_right N).neg_one_pow]
    push_cast
    rw [add_assoc, add_right_inj]
    field_simp
    ring

private theorem hasSum_zeta {k : ℕ} (hk : 1 < k) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ k) (riemannZeta k) := by
  simpa [AddCircle.coe_period (1 : ℝ), HurwitzZeta.hurwitzZeta_zero] using
    (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (a := 1) (by simp) (s := k) (by simpa using hk))

private theorem hasSum_closed (k : ℕ) :
    HasSum (fun n : ℕ => ((1 / (((n : ℝ) + 1) ^ (k + 1) * (2 * n + 1)) : ℝ) : ℂ))
      (2 ^ (k + 1) * Real.log 2 -
        ∑ j ∈ Finset.Icc 1 k, (2 : ℂ) ^ (k - j) * riemannZeta ((j : ℂ) + 1)) := by
  induction k with
  | zero => simpa using Complex.hasSum_ofReal.mpr hasSum_base
  | succ k ih =>
    -- Subtract the zeta series from twice the preceding series, term by term.
    have h := (ih.mul_left 2).sub (hasSum_zeta (k := k + 1 + 1) (by omega))
    convert h using 1
    · funext n
      push_cast
      have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hodd : (n : ℂ) * 2 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n * 2)
      rw [pow_succ _ (k + 1)]
      field_simp [hn, hodd]
      ring
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
      simp only [Nat.sub_self, pow_zero, one_mul, Nat.cast_add, Nat.cast_one]
      have hcoeff : (∑ j ∈ Finset.Icc 1 k, (2 : ℂ) ^ (k + 1 - j) * riemannZeta ((j : ℂ) + 1)) =
          2 * ∑ j ∈ Finset.Icc 1 k, (2 : ℂ) ^ (k - j) * riemannZeta ((j : ℂ) + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjk := (Finset.mem_Icc.mp hj).2
        rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ']
        ring
      rw [hcoeff, pow_succ' (2 : ℂ) (k + 1)]
      ring

end tsum_inv_pow_mul_two_mul_sub_one

/-- **Closed form of $\sum_{n \ge 1} 1/(n^t(2n-1))$.** For every integer $t \ge 1$,
$$\sum_{n \ge 1} \frac{1}{n^t (2n-1)} = 2^t \log 2 - \sum_{j=1}^{t-1} 2^{t-1-j} \zeta(j+1),$$
where $\zeta$ is the Riemann zeta function.

Source: Anthony Sofo and Junesang Choi, *New Series Representations for the Riemann Zeta
Function and Its Associated Functions*, INTEGERS 24 (2024), Article A45, Corollary 1,
equation (22). -/
public theorem tsum_inv_pow_mul_two_mul_sub_one (t : ℕ) (ht : 0 < t) :
    ((∑' n : ℕ, 1 / (((n : ℝ) + 1) ^ t * (2 * ((n : ℝ) + 1) - 1)) : ℝ) : ℂ) =
      2 ^ t * Real.log 2 -
        ∑ j ∈ Finset.Icc 1 (t - 1), (2 : ℂ) ^ (t - 1 - j) * riemannZeta ((j : ℂ) + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  rw [Complex.ofReal_tsum]
  simpa only [Nat.succ_sub_one, show ∀ n : ℕ, 2 * ((n : ℝ) + 1) - 1 = 2 * n + 1 by intro n; ring]
    using (tsum_inv_pow_mul_two_mul_sub_one.hasSum_closed k).tsum_eq

end MetaMathlibExt
