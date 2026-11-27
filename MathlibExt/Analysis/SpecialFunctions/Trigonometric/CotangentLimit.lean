/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# A limit of weighted cotangents

The weighted sum of cotangents at `x / (k - 1)` and `x / (k + 1)` tends to `4 / x`
for every nonzero real `x` as the natural number `k` tends to infinity.
-/

namespace MetaMathlibExt

open Real Filter Topology

namespace tendsto_cot_div_pred_add_cot_div_succ

private lemma mul_sinc (t : ℝ) : t * sinc t = sin t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [sinc_of_ne_zero ht, mul_div_cancel₀ _ ht]

/-- After the sine addition formulas, both terms have the same factor `2 / x`. -/
private lemma cot_sum_eq {x k : ℝ} (hx : x ≠ 0) (hk : 1 < k)
    (a b : ℝ) (ha : a = x / (k - 1)) (hb : b = x / (k + 1))
    (hsa : sinc a ≠ 0) (hsb : sinc b ≠ 0) :
    (1 / k - 1) * cot a + (1 / k + 1) * cot b =
      2 / x * (sinc (a + b) + sinc (a - b)) / (sinc a * sinc b) := by
  have hk₀ : k ≠ 0 := by linarith
  have hm : k - 1 ≠ 0 := (sub_pos.mpr hk).ne'
  have hp : k + 1 ≠ 0 := by linarith
  have ha₀ : a ≠ 0 := ha ▸ div_ne_zero hx hm
  have hb₀ : b ≠ 0 := hb ▸ div_ne_zero hx hp
  have hadd : (a + b) / k = 2 / x * (a * b) := by
    rw [ha, hb]
    field_simp
    ring
  have hsub : a - b = 2 / x * (a * b) := by
    rw [ha, hb]
    field_simp
    ring
  calc
    _ = (sin (a + b) / k + sin (a - b)) / (sin a * sin b) := by
      rw [sin_add, sin_sub, cot_eq_cos_div_sin, cot_eq_cos_div_sin]
      have hsin_a : sin a ≠ 0 := mul_sinc a ▸ mul_ne_zero ha₀ hsa
      have hsin_b : sin b ≠ 0 := mul_sinc b ▸ mul_ne_zero hb₀ hsb
      field_simp
      ring
    _ = _ := by
      simp only [← mul_sinc, mul_div_right_comm (a + b), hadd]
      rw [hsub]
      field_simp

end tendsto_cot_div_pred_add_cot_div_succ

/-- **The cotangent limit $4/x$.** For every nonzero real number $x$, as $k \to \infty$ through the
natural numbers,
$$\left(\frac{1}{k} - 1\right)\cot\frac{x}{k-1} + \left(\frac{1}{k} + 1\right)\cot\frac{x}{k+1}
\to \frac{4}{x}.$$

The paper states this for every real number $x$; the hypothesis $x \neq 0$ is added because at
$x = 0$ the cotangents and $4/x$ are undefined.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 8
(`jis-2025-25.2.3-lem-8`). -/
public theorem tendsto_cot_div_pred_add_cot_div_succ {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun k : ℕ => (1 / (k : ℝ) - 1) * cot (x / (k - 1)) +
      (1 / (k : ℝ) + 1) * cot (x / (k + 1))) atTop (𝓝 (4 / x)) := by
  let a (k : ℕ) := x / ((k : ℝ) - 1)
  let b (k : ℕ) := x / ((k : ℝ) + 1)
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa [a, sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop).const_div_atTop x
  have hb : Tendsto b atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).const_div_atTop x
  have hs {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
      Tendsto (fun k => sinc (f k)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (continuous_sinc.tendsto 0).comp hf
  have hsum := hs (f := fun k => a k + b k) (by simpa using ha.add hb)
  have hdiff := hs (f := fun k => a k - b k) (by simpa using ha.sub hb)
  have hlim := ((hsum.add hdiff).const_mul (2 / x)).div ((hs ha).mul (hs hb)) (by norm_num)
  rw [show (2 / x * (1 + 1) / (1 * 1)) = 4 / x by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1, (hs ha).eventually_ne one_ne_zero,
      (hs hb).eventually_ne one_ne_zero] with k hk hsa hsb
  exact (tendsto_cot_div_pred_add_cot_div_succ.cot_sum_eq hx (by exact_mod_cast hk)
    (a k) (b k) rfl rfl hsa hsb).symm

end MetaMathlibExt
