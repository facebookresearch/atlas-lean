/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DowkerHalfSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Decimal bounds for Watson's alternating cosecant sum

For even `n`, reflection and the double-angle identities turn the cosecant sum into
a trapezoidal sum for the tangent on `[0, π / 4]`. We bound the quadrature error on
each subinterval before adding the endpoint corrections.
-/

namespace MetaMathlibExt

open Real Finset

namespace watson_alternating_simple_bounds

private lemma csc_double (x : ℝ) :
    1 / sin (2 * x) = cot x - cot (2 * x) := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_two_mul, cos_two_mul]
  by_cases hs : sin x = 0
  · simp [hs]
  by_cases hc : cos x = 0
  · simp [hc]
  field_simp
  ring

private lemma cot_double (x : ℝ) :
    2 * cot (2 * x) = cot x - tan x := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, tan_eq_sin_div_cos, sin_two_mul, cos_two_mul']
  by_cases hs : sin x = 0
  · simp [hs]
  by_cases hc : cos x = 0
  · simp [hc]
  field_simp

/-- Subtract twice the even terms of an unsigned sum. -/
private lemma alternating_sum (f : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ range (2 * m), (-1 : ℝ) ^ (k + 1) * f k =
      (∑ k ∈ range (2 * m), f k) - 2 * ∑ k ∈ range m, f (2 * k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ]
    simp only [sum_range_succ, pow_succ, pow_mul] at ih ⊢
    norm_num at ih ⊢
    linarith

/-- Pair the cotangents at supplementary angles. The signs agree because `n` is even. -/
private lemma cot_sum_zero (n : ℕ) (he : Even n) (h : ℝ) (hh : (n : ℝ) * h = π / 2) :
    ∑ k ∈ Ico 1 n, (-1 : ℝ) ^ (k + 1) * cot (2 * (k * h)) = 0 := by
  let f (k : ℕ) := (-1 : ℝ) ^ (k + 1) * cot (2 * (k * h))
  change ∑ k ∈ Ico 1 n, f k = 0
  have href : (∑ k ∈ Ico 1 n, f (n - k)) = ∑ k ∈ Ico 1 n, f k := by
    simpa using sum_Ico_reflect f 1 (n := n) (m := n) (by omega)
  have hneg : (∑ k ∈ Ico 1 n, f (n - k)) = -(∑ k ∈ Ico 1 n, f k) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k hk => ?_
    have hk' := (mem_Ico.mp hk).2.le
    have hang : 2 * (((n - k : ℕ) : ℝ) * h) = π - 2 * (k * h) := by
      rw [Nat.cast_sub hk']
      linarith only [hh]
    have hs : (-1 : ℝ) ^ (n - k + 1) = (-1) ^ (k + 1) := by
      apply neg_one_pow_congr
      simp only [Nat.even_iff] at he ⊢
      omega
    simp [f, hs, hang, cot_eq_cos_div_sin, cos_pi_sub, sin_pi_sub, neg_div]
  linarith

private lemma tangent_sum (n m : ℕ) (hn : n = 2 * m) (hnpos : 0 < n)
    (h : ℝ) (hh : (n : ℝ) * h = π / 2) :
    watsonAlternatingCosecantSum n =
      ∑ k ∈ range m, (tan (k * h) + tan (((k + 1 : ℕ) : ℝ) * h)) := by
  have he : Even n := ⟨m, by omega⟩
  have hangle (k : ℕ) : π * k / n = 2 * (k * h) := by
    apply (div_eq_iff (by exact_mod_cast hnpos.ne')).2
    linear_combination -2 * (k : ℝ) * hh
  let f (k : ℕ) := cot (k * h)
  have halt : watsonAlternatingCosecantSum n =
      ∑ k ∈ range n, (-1 : ℝ) ^ (k + 1) * f k := by
    unfold watsonAlternatingCosecantSum
    rw [show Icc 1 (n - 1) = Ico 1 n by ext k; simp; omega, sum_range_eq_add_Ico _ hnpos]
    simp only [hangle, csc_double, mul_sub, sum_sub_distrib, cot_sum_zero n he h hh, sub_zero]
    simp [f, cot_eq_cos_div_sin]
  have href : (∑ k ∈ range m, f (m + k)) =
      ∑ k ∈ range m, tan (((k + 1 : ℕ) : ℝ) * h) := by
    rw [← sum_range_reflect (fun k => f (m + k)) m]
    apply sum_congr rfl
    intro k hk
    have hk' : k < m := mem_range.mp hk
    have heq : m + (m - 1 - k) = n - (k + 1) := by omega
    have hang : ((n - (k + 1) : ℕ) : ℝ) * h = π / 2 - (k + 1 : ℕ) * h := by
      rw [Nat.cast_sub (by omega)]
      linarith only [hh]
    simp [f, heq, hang, cot_eq_cos_div_sin, cos_pi_div_two_sub, sin_pi_div_two_sub,
      tan_eq_sin_div_cos]
  have hd (k : ℕ) : 2 * f (2 * k) = f k - tan (k * h) := by
    simpa [f, mul_assoc] using cot_double (k * h)
  rw [halt, hn, alternating_sum, two_mul m, sum_range_add, href, mul_sum, sum_add_distrib]
  simp_rw [hd]
  rw [sum_sub_distrib]
  ring

-- The first three derivatives of tangent, written as polynomials in its value.
private noncomputable def d₁ (x : ℝ) := 1 + tan x ^ 2
private noncomputable def d₂ (x : ℝ) := 2 * tan x + 2 * tan x ^ 3
private noncomputable def d₃ (x : ℝ) := 2 + 8 * tan x ^ 2 + 6 * tan x ^ 4
private noncomputable def d₄ (x : ℝ) := (16 * tan x + 24 * tan x ^ 3) * d₁ x

private lemma tan_derivatives {x : ℝ} (hx : cos x ≠ 0) :
    HasDerivAt (fun y => -log (cos y)) (tan x) x ∧ HasDerivAt tan (d₁ x) x ∧
      HasDerivAt d₁ (d₂ x) x ∧ HasDerivAt d₂ (d₃ x) x ∧ HasDerivAt d₃ (d₄ x) x := by
  have ht : HasDerivAt tan (d₁ x) x := by
    simpa [d₁, ← inv_one_add_tan_sq hx, one_div] using hasDerivAt_tan hx
  refine ⟨((hasDerivAt_cos x).log hx).neg.congr_deriv ?_, ht, ?_, ?_, ?_⟩
  · simp [tan_eq_sin_div_cos, neg_div]
  · apply ((ht.pow 2).const_add 1).congr_deriv
    dsimp [d₁, d₂]
    ring
  · apply ((ht.const_mul 2).add ((ht.pow 3).const_mul 2)).congr_deriv
    dsimp [d₁, d₃]
    ring
  · apply ((((ht.pow 2).const_mul 8).const_add 2).add ((ht.pow 4).const_mul 6)).congr_deriv
    dsimp [d₄]
    ring

private lemma endpoints_le_of_deriv {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hs : ∀ x ∈ Set.Icc a b, 0 ≤ f' x) : f a ≤ f b := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hs x (interior_subset hx)) (Set.left_mem_Icc.mpr hab)
    (Set.right_mem_Icc.mpr hab) hab

private noncomputable def correctedPrimitive (h x : ℝ) : ℝ :=
  -log (cos x) + h ^ 2 / 12 * d₁ x

/-- Integrating the fourth derivative against the kernel
`(x - a)² (b - x)² / 24` gives the error after the first endpoint correction. -/
private lemma cell_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 4) :
    let h := b - a
    let error := correctedPrimitive h b - correctedPrimitive h a - h / 2 * (tan a + tan b)
    0 ≤ error ∧ error ≤ h ^ 4 / 384 * (d₃ b - d₃ a) := by
  let w (x : ℝ) := (x - a) ^ 2 * (b - x) ^ 2 / 24
  let w₁ (x : ℝ) := ((x - a) * (b - x) ^ 2 - (x - a) ^ 2 * (b - x)) / 12
  let w₂ (x : ℝ) := ((b - x) ^ 2 - 4 * (x - a) * (b - x) + (x - a) ^ 2) / 12
  let w₃ (x : ℝ) := ((x - a) - (b - x)) / 2
  let G (x : ℝ) := w x * d₃ x - w₁ x * d₂ x + w₂ x * d₁ x - w₃ x * tan x - log (cos x)
  have hG (x : ℝ) (hx : x ∈ Set.Icc a b) :
      HasDerivAt G (w x * d₄ x) x ∧ HasDerivAt d₃ (d₄ x) x := by
    have hc : cos x ≠ 0 := (cos_pos_of_mem_Ioo
      ⟨by linarith [hx.1, pi_pos], by linarith [hx.2, pi_pos]⟩).ne'
    obtain ⟨hlog, ht, ht₁, ht₂, ht₃⟩ := tan_derivatives hc
    have hu := (hasDerivAt_id x).sub_const a
    have hv := (hasDerivAt_id x).const_sub b
    have hw : HasDerivAt w (w₁ x) x := by
      apply (((hu.pow 2).mul (hv.pow 2)).div_const 24).congr_deriv
      dsimp [w₁]
      ring
    have hw₁ : HasDerivAt w₁ (w₂ x) x := by
      apply (((hu.mul (hv.pow 2)).sub ((hu.pow 2).mul hv)).div_const 12).congr_deriv
      dsimp [w₂]
      ring
    have hw₂ : HasDerivAt w₂ (w₃ x) x := by
      apply ((((hv.pow 2).sub ((hu.const_mul 4).mul hv)).add (hu.pow 2)).div_const 12).congr_deriv
      dsimp [w₃]
      ring
    have hw₃ : HasDerivAt w₃ 1 x := by
      apply ((hu.sub hv).div_const 2).congr_deriv
      norm_num
    refine ⟨?_, ht₃⟩
    change HasDerivAt (fun x => _ + -log (cos x)) _ _
    apply (((((hw.mul ht₃).sub (hw₁.mul ht₂)).add (hw₂.mul ht₁)).sub (hw₃.mul ht)).add
      hlog).congr_deriv
    ring
  have hd₄ (x : ℝ) (hx : x ∈ Set.Icc a b) : 0 ≤ d₄ x := by
    have := tan_nonneg_of_nonneg_of_le_pi_div_two (ha.trans hx.1)
      (show x ≤ π / 2 by linarith [hx.2, pi_pos])
    dsimp [d₄, d₁]
    positivity
  have hlo : G a ≤ G b := endpoints_le_of_deriv hab (fun x hx => (hG x hx).1) fun x hx =>
    mul_nonneg (by dsimp [w]; positivity) (hd₄ x hx)
  let c := (b - a) ^ 4 / 384
  have hhi : c * d₃ a - G a ≤ c * d₃ b - G b := by
    apply endpoints_le_of_deriv (f := fun x => c * d₃ x - G x) hab
      (fun x hx => ((hG x hx).2.const_mul c).sub (hG x hx).1)
    intro x hx
    have hprod : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
      nlinarith only [sq_nonneg ((x - a) - (b - x))]
    have hsq := pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)) hprod 2
    have hw : w x ≤ c := by dsimp [w, c]; linarith only [hsq]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right hw (hd₄ x hx))
  dsimp [G, w, w₁, w₂, w₃, c, correctedPrimitive] at hlo hhi ⊢
  constructor <;> linarith only [hlo, hhi]

/-- The endpoint corrections telescope along the uniform grid. -/
private lemma sum_bounds (n m : ℕ) (hn : n = 2 * m) (hnpos : 0 < n) (h : ℝ)
    (hh : (n : ℝ) * h = π / 2) (hpos : 0 < h) :
    let error := log 2 / 2 + h ^ 2 / 12 - h / 2 * watsonAlternatingCosecantSum n
    0 ≤ error ∧ error ≤ h ^ 4 / 384 * 14 := by
  let x (k : ℕ) := (k : ℝ) * h
  have hnm : (n : ℝ) = 2 * m := by exact_mod_cast hn
  have hxm : x m = π / 4 := by
    dsimp [x]
    rw [hnm] at hh
    linarith
  let e (k : ℕ) := correctedPrimitive h (x (k + 1)) - correctedPrimitive h (x k) -
    h / 2 * (tan (x k) + tan (x (k + 1)))
  have hc (k : ℕ) (hk : k ∈ range m) :
      0 ≤ e k ∧ e k ≤ h ^ 4 / 384 * (d₃ (x (k + 1)) - d₃ (x k)) := by
    have hstep : x (k + 1) - x k = h := by simp [x, add_mul]
    have hkm : k + 1 ≤ m := mem_range.mp hk
    have hright : x (k + 1) ≤ π / 4 := hxm ▸
      mul_le_mul_of_nonneg_right (by exact_mod_cast hkm) hpos.le
    simpa only [hstep, e] using cell_bounds (a := x k) (b := x (k + 1))
      (by dsimp [x]; positivity) (by linarith) hright
  have hlow := sum_nonneg (fun k hk => (hc k hk).1)
  have hhigh := sum_le_sum (fun k hk => (hc k hk).2)
  have hs : (∑ k ∈ range m, e k) = correctedPrimitive h (x m) -
      correctedPrimitive h (x 0) - h / 2 * watsonAlternatingCosecantSum n := by
    simp only [e, sum_sub_distrib _ (fun k => h / 2 * _), ← mul_sum,
      tangent_sum n m hn hnpos h hh]
    rw [sum_range_sub (fun k => correctedPrimitive h (x k))]
  rw [hs, ← mul_sum, sum_range_sub (fun k => d₃ (x k))] at hhigh
  rw [hs] at hlow
  have hx₀ : x 0 = 0 := by simp [x]
  simp only [hxm, hx₀, correctedPrimitive, d₁, d₃, tan_pi_div_four, tan_zero, cos_zero,
    cos_pi_div_four, log_one, log_div (by positivity : √2 ≠ 0) two_ne_zero,
    log_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hlow hhigh
  constructor <;> linarith only [hlow, hhigh]

/-- At the first admissible index the sum is exactly `2 √2 - 1`. -/
private lemma four_lower :
    2 * (4 : ℝ) * log 2 / π + 0.252 / 4 < watsonAlternatingCosecantSum 4 := by
  have hsin : sin (π * 3 / 4) = √2 / 2 := by
    rw [show π * 3 / 4 = π - π / 4 by ring, sin_pi_sub, sin_pi_div_four]
  have hval : watsonAlternatingCosecantSum 4 = 2 * √2 - 1 := by
    unfold watsonAlternatingCosecantSum
    rw [show Icc 1 (4 - 1 : ℕ) = {1, 2, 3} by decide]
    norm_num [hsin, sin_pi_div_four, show π * 2 / 4 = π / 2 by ring, sin_pi_div_two]
    field_simp
    nlinarith only [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hval]
  have hmain : 2 * (4 : ℝ) * log 2 / π < 1.7652 := by
    rw [div_lt_iff₀ pi_pos]
    linarith only [pi_gt_d4, log_two_lt_d9]
  have hsqrt : (1.4142 : ℝ) < √2 := by
    exact (lt_sqrt (by norm_num)).2 (by norm_num)
  linarith

end watson_alternating_simple_bounds

open watson_alternating_simple_bounds

/--
**Decimal bounds for Watson's alternating cosecant sum.** For every even natural number
$n \ge 4$, the alternating cosecant sum $C_n = \sum_{l=1}^{n-1} (-1)^{l+1} / \sin(\pi l / n)$
satisfies the strict inequalities
$$
\frac{2 n \log 2}{\pi} + \frac{0.252}{n} < C_n < \frac{2 n \log 2}{\pi} + \frac{0.262}{n}.
$$

Source: Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum
of Order One Half)*, INTEGERS 25 (2025), Article A30, Corollary 3.
-/
public theorem watson_alternating_simple_bounds
    (n : ℕ) (heven : Even n) (hn : 4 ≤ n) :
    2 * (n : ℝ) * Real.log 2 / Real.pi + (0.252 : ℝ) / (n : ℝ) <
        watsonAlternatingCosecantSum n ∧
      watsonAlternatingCosecantSum n <
        2 * (n : ℝ) * Real.log 2 / Real.pi + (0.262 : ℝ) / (n : ℝ) := by
  obtain ⟨m, hm⟩ := heven
  have hnm : n = 2 * m := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let h := π / (2 * n)
  have hpos : 0 < h := by dsimp [h]; positivity
  have hh : (n : ℝ) * h = π / 2 := by dsimp [h]; field_simp
  have hmain : h * (2 * (n : ℝ) * log 2 / π) = log 2 := by
    dsimp [h]
    field_simp
  obtain ⟨hlo, hhi⟩ := sum_bounds n m hnm (by omega) h hh hpos
  constructor
  · by_cases hfour : n = 4
    · simpa only [hfour, Nat.cast_ofNat] using four_lower
    have hn₆ : (6 : ℝ) ≤ n := by exact_mod_cast (show 6 ≤ n by omega)
    have hh' : h ≤ 0.262 := by
      linarith only [mul_le_mul_of_nonneg_right hn₆ hpos.le, hh, pi_lt_d4]
    have hcoef : (0.252 : ℝ) / n < h * (1 / 6 - 28 / 384 * h ^ 2) := by
      rw [div_lt_iff₀ hnpos, mul_right_comm, mul_comm h, hh]
      calc
        (0.252 : ℝ) < 3.14 / 2 * (1 / 6 - 28 / 384 * 0.262 ^ 2) := by norm_num
        _ ≤ _ := mul_le_mul (by linarith only [pi_gt_d2])
          (by linarith only [pow_le_pow_left₀ hpos.le hh' 2]) (by norm_num) (by positivity)
    apply lt_of_lt_of_le (add_lt_add_right hcoef _)
    apply (mul_le_mul_iff_of_pos_left hpos).mp
    rw [mul_add, hmain]
    linarith only [hhi]
  · have hcoef : h / 6 < (0.262 : ℝ) / n := by
      rw [lt_div_iff₀ hnpos]
      linarith only [hh, pi_lt_d4]
    apply lt_of_le_of_lt _ (add_lt_add_right hcoef _)
    apply (mul_le_mul_iff_of_pos_left hpos).mp
    rw [mul_add, hmain]
    linarith only [hlo]

end MetaMathlibExt
