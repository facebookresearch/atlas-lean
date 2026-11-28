/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Dilog
import MathlibExt.Analysis.SpecialFunctions.RogersDilog
import MathlibExt.NumberTheory.SanfordCoupledRecurrence

/-!
# Sanford's symmetric dilogarithm series

For `0 < a < 1`, we prove Sanford's symmetric series by summing Abel's five-term
relation along Sanford's coupled recurrence and using the reflection identity at the endpoints.

## References

* Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
  INTEGERS 25 (2025), Article A52, pp. 1–15, Corollary 1 and equations (1) and (2).
-/

open Filter Real Set
open scoped Topology

namespace MetaMathlibExt
namespace rogersDilog_sanford_symmetric_series

local notation "step" => (fun x y : ℝ => x * (1 - y) / (1 - x * y))

-- Sum along the recurrence. The starting arguments are complementary, and the
-- limiting pair is (1 - r, 0), so reflection leaves just L r.
private lemma hasSum_products {X Y : ℕ → ℝ} {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hX : X 0 ∈ Ioo (0 : ℝ) 1) (hY : Y 0 = 1 - X 0)
    (rec : ∀ n, X (n + 1) = step (X n) (Y n) ∧ Y (n + 1) = step (Y n) (X n))
    (limX : Tendsto X atTop (𝓝 (1 - r))) (limY : Tendsto Y atTop (𝓝 0)) :
    HasSum (fun n => rogersDilog (X n * Y n)) (rogersDilog r) := by
  have mem (n : ℕ) : X n ∈ Ioo (0 : ℝ) 1 ∧ Y n ∈ Ioo (0 : ℝ) 1 := by
    induction n with
    | zero => exact ⟨hX, hY ▸ ⟨sub_pos.mpr hX.2, sub_lt_self _ hX.1⟩⟩
    | succ n ih =>
      rw [(rec n).1, (rec n).2]
      exact ⟨abel_five_term_arg_mem_Ioo ih.1 ih.2, abel_five_term_arg_mem_Ioo ih.2 ih.1⟩
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => rogersDilog_nonneg (by
    simpa only [Ioo.coe_mul] using
      (((⟨X n, (mem n).1⟩ : Ioo (0 : ℝ) 1) * ⟨Y n, (mem n).2⟩).2))) _).2
  have sum_range (n : ℕ) : ∑ k ∈ Finset.range n, rogersDilog (X k * Y k) =
      π ^ 2 / 6 - (rogersDilog (X n) + rogersDilog (Y n)) := by
    induction n with
    | zero => simp [hY, rogersDilog_reflection (Ioo_subset_Icc_self hX)]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, (rec n).1, (rec n).2]
      linarith [rogersDilog_five_term (mem n).1 (mem n).2]
  have limL {f : ℕ → ℝ} {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (hf : Tendsto f atTop (𝓝 b))
      (hm : ∀ n, f n ∈ Ioo (0 : ℝ) 1) :
      Tendsto (fun n => rogersDilog (f n)) atTop (𝓝 (rogersDilog b)) :=
    (continuousOn_rogersDilog b hb).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hf, Eventually.of_forall fun n => Ioo_subset_Icc_self (hm n)⟩)
  have hlim := ((limL ⟨sub_nonneg.mpr hr.2.le, sub_le_self _ hr.1.le⟩ limX
    (fun n => (mem n).1)).add (limL (by simp) limY (fun n => (mem n).2))).const_sub (π ^ 2 / 6)
  have hend : π ^ 2 / 6 - (rogersDilog (1 - r) + rogersDilog 0) = rogersDilog r := by
    rw [rogersDilog_zero, add_zero, ← rogersDilog_reflection (Ioo_subset_Icc_self hr),
      add_sub_cancel_right]
  simpa only [sum_range, hend] using hlim

private lemma symmetric_series {u v : ℝ} (hv : 0 < v) (hvu : v < u) (hs : u + v = 1) :
    HasSum (fun n : ℕ => rogersDilog ((u - v) ^ 2 * v ^ (n + 1) * u ^ (n + 1) /
      (u ^ (n + 2) - v ^ (n + 2)) ^ 2)) (rogersDilog (v / u)) := by
  have hu := hv.trans hvu
  have hu₁ : u < 1 := by linarith
  have hv₁ := hvu.trans hu₁
  let r := v / u
  have hr : r ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hv hu, (div_lt_one hu).mpr hvu⟩
  have hur : u * r = v := by dsimp [r]; field_simp
  let D (n : ℕ) := u ^ (n + 2) - v ^ (n + 2)
  let X (n : ℕ) := u * (u - v) * u ^ n / D n
  let Y (n : ℕ) := v * (u - v) * v ^ n / D n
  have hrec (n : ℕ) : X (n + 1) = step (X n) (Y n) ∧ Y (n + 1) = step (Y n) (X n) := by
    dsimp only
    rw [mul_comm (Y n) (X n)]
    simpa only [X, Y, D, show 1 - v = u by linarith, show 1 - u = v by linarith, pow_succ']
      using sanford_coupled_recurrence hu hu₁ hv hv₁ hvu.ne' n
  have hD₀ : D 0 = u - v := by
    change u ^ 2 - v ^ 2 = u - v
    linear_combination (u - v) * hs
  have hX₀ : X 0 = u := by simp [X, hD₀, sub_ne_zero.mpr hvu.ne']
  have hY₀ : Y 0 = v := by simp [Y, hD₀, sub_ne_zero.mpr hvu.ne']
  -- Divide both coordinates by the larger exponential before taking the limit.
  have hvpow (k : ℕ) : v ^ k = u ^ k * r ^ k := by rw [← mul_pow, hur]
  have hD (n : ℕ) : D n = u ^ (n + 2) * (1 - r ^ (n + 2)) := by
    dsimp only [D]
    rw [hvpow]
    ring
  have hX (n : ℕ) : X n = (1 - r) / (1 - r ^ (n + 2)) := by
    have hnum : u * (u - v) * u ^ n = u ^ (n + 2) * (1 - r) := by
      rw [← hur, pow_add]
      ring
    dsimp only [X]
    rw [hD, hnum, mul_div_mul_left _ _ (pow_ne_zero _ hu.ne')]
  have hY (n : ℕ) : Y n = X n * r ^ (n + 1) := by
    dsimp only [Y, X]
    rw [div_mul_eq_mul_div, hvpow, pow_succ r, ← hur]
    ring
  have hp (k : ℕ) : Tendsto (fun n : ℕ => r ^ (n + k)) atTop (𝓝 0) := by
    simpa only [pow_add, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr.1.le hr.2).mul_const (r ^ k)
  have limX : Tendsto X atTop (𝓝 (1 - r)) := by
    rw [funext hX]
    simpa only [Pi.div_def, sub_zero, div_one] using
      (tendsto_const_nhds (x := 1 - r)).div ((hp 2).const_sub 1) (by norm_num)
  have limY : Tendsto Y atTop (𝓝 0) := by
    rw [funext hY]
    simpa only [mul_zero] using limX.mul (hp 1)
  have hsum := hasSum_products hr (hX₀ ▸ ⟨hu, hu₁⟩) (by rw [hX₀, hY₀]; linarith)
    hrec limX limY
  apply hsum.congr_fun
  intro n
  congr 1
  simp only [X, Y, div_mul_div_comm, ← sq (D n)]
  change _ / (D n) ^ 2 = _ / (D n) ^ 2
  congr 1
  rw [pow_succ v, pow_succ u]
  ring

end rogersDilog_sanford_symmetric_series

open rogersDilog_sanford_symmetric_series

/-- **Sanford's symmetric dilogarithm series.** Write $L(x) = \sum_{m \ge 1} x^m/m^2 +
\frac{1}{2} \log x \log(1 - x)$ for the Rogers dilogarithm on $[0, 1]$ (with $\log 0 = 0$). For
every real number $a \in (0, 1)$,
$$
\sum_{n \ge 1} L\left(\frac{a^2 \left(\frac{1 - a}{2}\right)^n \left(\frac{1 + a}{2}\right)^n}
{\left(\left(\frac{1 + a}{2}\right)^{n+1} - \left(\frac{1 - a}{2}\right)^{n+1}\right)^2}\right) =
L\left(\frac{1 - a}{1 + a}\right).
$$

Source: Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
INTEGERS 25 (2025), Article A52, Corollary 1 (`integers-2025-A52-cor-1`). -/
public theorem rogersDilog_sanford_symmetric_series {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    let L : ℝ → ℝ := fun x => (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) +
      log x * log (1 - x) / 2
    ∑' n : ℕ, L (a ^ 2 * (1 / 2 - a / 2) ^ (n + 1) * (1 / 2 + a / 2) ^ (n + 1) /
        ((1 / 2 + a / 2) ^ (n + 2) - (1 / 2 - a / 2) ^ (n + 2)) ^ 2) =
      L ((1 - a) / (1 + a)) := by
  intro R
  let u := 1 / 2 + a / 2
  let v := 1 / 2 - a / 2
  have hv : 0 < v := by dsimp [v]; linarith
  have hvu : v < u := by dsimp [v, u]; linarith
  have hs : u + v = 1 := by dsimp [u, v]; ring
  have hd : u - v = a := by dsimp [u, v]; ring
  have hr : v / u = (1 - a) / (1 + a) := by
    dsimp [v, u]
    field_simp
  simpa only [hd, hr, R, rogersDilog_eq_tsum_add_log_mul_log] using
    (symmetric_series hv hvu hs).tsum_eq

end MetaMathlibExt
