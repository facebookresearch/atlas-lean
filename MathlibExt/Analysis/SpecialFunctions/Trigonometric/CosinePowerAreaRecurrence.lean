/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Algebra.Order.Field

/-!
# Recursion for the limiting areas between cosine powers

Average over a period, then integrate the cosine power against a linear weight.
The weighted integrals satisfy the recurrence by the differential equation for cosine powers.
-/

open Real Filter Topology Set intervalIntegral
open scoped BigOperators NNReal

namespace MetaMathlibExt

@[expose] public section

/-- **Area between powers of cosines.** For natural numbers $n$ and $k$, the area between the
curves $y = \cos^n x$ and $y = \cos^n(kx)$ on $[0, \pi]$ is
$A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$, where $\cos^n x$ means $(\cos x)^n$.

The paper's $A_n$ is the limit of $A_n(k)$ as $k \to \infty$ (Eq. (1)), with $k$ running over
the natural numbers.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Eq. (1). -/
public noncomputable def cosPowArea (n k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..π, |cos x ^ n - cos (k * x) ^ n|

end

private lemma abs_gap_sub_le (a b c : ℝ) : abs (|a - c| - |b - c|) ≤ |a - b| := by
  simpa only [Real.norm_eq_abs, sub_sub_sub_cancel_right] using
    (abs_norm_sub_norm_le (a - c) (b - c))

private lemma integral_abs_sub_le {f g : ℝ → ℝ} {a b E : ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ x ∈ uIoc a b, |f x - g x| ≤ E) :
    |(∫ x in a..b, f x) - ∫ x in a..b, g x| ≤ E * |b - a| := by
  rw [← integral_sub (hf.intervalIntegrable a b) (hg.intervalIntegrable a b), ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const (by simpa only [Real.norm_eq_abs] using h)

private noncomputable def meanGap (f : ℝ → ℝ) (b x : ℝ) : ℝ :=
  b⁻¹ * ∫ y in (0 : ℝ)..b, |f x - f y|

private lemma meanGap_lipschitz {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {b : ℝ} (hb : 0 < b) : LipschitzWith C (meanGap f b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  have hc := hf.continuous
  simp only [Real.dist_eq]
  rw [meanGap, meanGap, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hb)]
  have h := integral_abs_sub_le (a := 0) (b := b) (E := (C : ℝ) * |x - z|)
    (f := fun y => |f x - f y|) (g := fun y => |f z - f y|)
    (by fun_prop) (by fun_prop) (fun y _ => (abs_gap_sub_le _ _ _).trans (by
      simpa only [Real.dist_eq] using hf.dist_le_mul x z))
  rw [sub_zero, abs_of_pos hb] at h
  calc
    _ ≤ b⁻¹ * ((C : ℝ) * |x - z| * b) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

private lemma fold_periodic_even {f : ℝ → ℝ} {b : ℝ}
    (hp : Function.Periodic f (2 * b)) (he : ∀ x, f (-x) = f x) (i : ℕ) (y : ℝ) :
    f ((i : ℝ) * b + y) = if Even i then f y else f (b - y) := by
  split_ifs with hi
  · obtain ⟨j, hj⟩ := hi
    rw [hj, Nat.cast_add, show ((j : ℝ) + j) * b + y = y + j * (2 * b) by ring]
    exact (hp.nat_mul j) y
  · obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hi
    rw [hj, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      show (2 * (j : ℝ) + 1) * b + y = b + y + j * (2 * b) by ring,
      (hp.nat_mul j) (b + y), show b + y = (y - b) + 2 * b by ring, hp]
    convert (he (y - b)).symm using 1
    ring_nf

-- Freezing the first variable at the left endpoint gives exactly one mean on each cell.
private lemma integral_frozen_cell {f : ℝ → ℝ} {b k : ℝ}
    (hk : 0 < k) (hp : Function.Periodic f (2 * b)) (he : ∀ x, f (-x) = f x)
    (i : ℕ) (c : ℝ) :
    (∫ x in (i : ℝ) * (b / k)..(i + 1 : ℝ) * (b / k), |c - f (k * x)|) =
      k⁻¹ * ∫ y in (0 : ℝ)..b, |c - f y| := by
  rw [integral_comp_mul_left (fun y => |c - f y|) hk.ne', smul_eq_mul,
    show k * ((i : ℝ) * (b / k)) = (i : ℝ) * b by field_simp,
    show k * ((i + 1 : ℝ) * (b / k)) = i * b + b by field_simp]
  congr 1
  have h := integral_comp_add_left (a := 0) (b := b) (fun y => |c - f y|) ((i : ℝ) * b)
  rw [add_zero] at h
  rw [← h]
  simp only [fold_periodic_even hp he]
  split_ifs
  · rfl
  · simpa only [sub_self, sub_zero] using
      (integral_comp_sub_left (a := 0) (b := b) (fun y => |c - f y|) b)

-- The two freezing errors on each cell are at most the Lipschitz constant times its width squared.
private lemma gap_mean_error {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {b : ℝ} (hb : 0 < b) (hp : Function.Periodic f (2 * b)) (he : ∀ x, f (-x) = f x)
    {k : ℕ} (hk : 0 < k) :
    |(∫ x in (0 : ℝ)..b, |f x - f (k * x)|) - ∫ x in (0 : ℝ)..b, meanGap f b x| ≤
      (2 * (C : ℝ) * b ^ 2) * (k : ℝ)⁻¹ := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  let s := b / (k : ℝ)
  have hs : 0 < s := div_pos hb hk'
  let a (i : ℕ) := (i : ℝ) * s
  have ha₀ : a 0 = 0 := by simp [a]
  have haₖ : a k = b := by dsimp [a, s]; field_simp
  have hwidth (i : ℕ) : a (i + 1) - a i = s := by simp [a, add_mul, Nat.cast_add]
  have hc : Continuous f := hf.continuous
  have hg : Continuous (fun x => |f x - f (k * x)|) := by fun_prop
  have hM := meanGap_lipschitz hf hb
  have hm : Continuous (meanGap f b) := hM.continuous
  have hcell (i : ℕ) :
      |(∫ x in a i..a (i + 1), |f x - f (k * x)|) -
          ∫ x in a i..a (i + 1), meanGap f b x| ≤ 2 * (C : ℝ) * s ^ 2 := by
    have hab : a i ≤ a (i + 1) := by linarith [hwidth i]
    have hdist (x : ℝ) (hx : x ∈ uIoc (a i) (a (i + 1))) : |x - a i| ≤ s := by
      rw [uIoc_of_le hab] at hx
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
      linarith [hx.2, hwidth i]
    have h₁ := integral_abs_sub_le hg (g := fun x => |f (a i) - f (k * x)|) (by fun_prop)
      (E := (C : ℝ) * s) (a := a i) (b := a (i + 1)) (fun x hx =>
        (abs_gap_sub_le _ _ _).trans (by
          simpa only [Real.dist_eq] using (hf.dist_le_mul x (a i)).trans
            (mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using hdist x hx)
              C.coe_nonneg)))
    have h₂ := integral_abs_sub_le hm (g := fun _ => meanGap f b (a i)) continuous_const
      (E := (C : ℝ) * s) (a := a i) (b := a (i + 1)) (fun x hx =>
        by
          simpa only [Real.dist_eq] using (hM.dist_le_mul x (a i)).trans
            (mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using hdist x hx)
              C.coe_nonneg))
    have hfrozen := integral_frozen_cell hk' hp he i (f (a i))
    change (∫ x in (i : ℝ) * s..(i + 1 : ℝ) * s, |f (a i) - f (k * x)|) = _ at hfrozen
    rw [← Nat.cast_add_one] at hfrozen
    change (∫ x in a i..a (i + 1), |f (a i) - f (k * x)|) = _ at hfrozen
    rw [integral_const, hwidth i, smul_eq_mul, meanGap, ← mul_assoc,
      show s * b⁻¹ = (k : ℝ)⁻¹ by dsimp [s]; field_simp] at h₂
    rw [hfrozen, hwidth i, abs_of_pos hs] at h₁
    rw [abs_of_pos hs, abs_sub_comm] at h₂
    calc
      _ ≤ _ := abs_sub_le _ ((k : ℝ)⁻¹ * ∫ y in (0 : ℝ)..b, |f (a i) - f y|) _
      _ ≤ _ := by nlinarith only [h₁, h₂]
  have hsum₁ := sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (a := a) (n := k)
    (fun i _ => hg.intervalIntegrable (a i) (a (i + 1)))
  have hsum₂ := sum_integral_adjacent_intervals (μ := MeasureTheory.volume) (a := a) (n := k)
    (fun i _ => hm.intervalIntegrable (a i) (a (i + 1)))
  rw [ha₀, haₖ] at hsum₁ hsum₂
  rw [← hsum₁, ← hsum₂, ← Finset.sum_sub_distrib]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range k, (2 * (C : ℝ) * s ^ 2) := Finset.sum_le_sum (fun i _ => hcell i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; dsimp [s]; field_simp

private lemma tendsto_gap_mean {f : ℝ → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {b : ℝ} (hb : 0 < b) (hp : Function.Periodic f (2 * b)) (he : ∀ x, f (-x) = f x) :
    Tendsto (fun k : ℕ => ∫ x in (0 : ℝ)..b, |f x - f (k * x)|) atTop
      (𝓝 (∫ x in (0 : ℝ)..b, meanGap f b x)) := by
  apply (tendsto_sub_nhds_zero_iff).mp
  apply squeeze_zero_norm' (a := fun k : ℕ => (2 * (C : ℝ) * b ^ 2) * (k : ℝ)⁻¹)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    simpa only [Real.norm_eq_abs] using gap_mean_error hf hb hp he hk
  · simpa only [mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (2 * (C : ℝ) * b ^ 2)


private lemma primitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun z => ∫ y in (0 : ℝ)..z, f y) (f x) x :=
  integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

private noncomputable def weightedCos (n : ℕ) (b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..b, (b - 2 * x) * cos x ^ n

private lemma integral_meanGap {f : ℝ → ℝ} (hf : Continuous f) {b : ℝ} (hb : 0 < b)
    (hanti : AntitoneOn f (Icc 0 b)) :
    (∫ x in (0 : ℝ)..b, meanGap f b x) =
      (2 / b) * ∫ x in (0 : ℝ)..b, (b - 2 * x) * f x := by
  let F (x : ℝ) := ∫ y in (0 : ℝ)..x, f y
  have hF (x : ℝ) : HasDerivAt F (f x) x := primitive_hasDerivAt hf x
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hmean (x : ℝ) (hx : x ∈ Icc 0 b) :
      meanGap f b x = b⁻¹ * (2 * F x - F b + (b - 2 * x) * f x) := by
    unfold meanGap
    congr 1
    let g (y : ℝ) := |f x - f y|
    have hg : Continuous g := by dsimp [g]; fun_prop
    change (∫ y in (0 : ℝ)..b, g y) = _
    rw [← integral_add_adjacent_intervals (b := x)
      (hg.intervalIntegrable 0 x) (hg.intervalIntegrable x b)]
    have h₁ : (∫ y in (0 : ℝ)..x, g y) = ∫ y in (0 : ℝ)..x, f y - f x := by
      apply integral_congr
      intro y hy
      rw [uIcc_of_le hx.1] at hy
      have hy' : y ∈ Icc 0 b := ⟨hy.1, hy.2.trans hx.2⟩
      dsimp [g]
      rw [abs_of_nonpos (sub_nonpos.mpr (hanti hy' hx hy.2)), neg_sub]
    have h₂ : (∫ y in x..b, g y) = ∫ y in x..b, f x - f y := by
      apply integral_congr
      intro y hy
      rw [uIcc_of_le hx.2] at hy
      have hy' : y ∈ Icc 0 b := ⟨hx.1.trans hy.1, hy.2⟩
      exact abs_of_nonneg (sub_nonneg.mpr (hanti hx hy' hy.1))
    rw [h₁, h₂, integral_sub (hf.intervalIntegrable 0 x) (continuous_const.intervalIntegrable 0 x),
      integral_sub (continuous_const.intervalIntegrable x b) (hf.intervalIntegrable x b),
      ← integral_interval_sub_left (hf.intervalIntegrable 0 b) (hf.intervalIntegrable 0 x),
      integral_const, integral_const, smul_eq_mul, smul_eq_mul]
    change F x - (x - 0) * f x + ((b - x) * f x - (F b - F x)) = _
    ring
  have hparts := integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := b)
    (u := fun x => x) (v := F) (u' := fun _ => 1) (v' := f)
    (fun x _ => hasDerivAt_id x) (fun x _ => hF x)
    (continuous_const.intervalIntegrable 0 b) (hf.intervalIntegrable 0 b)
  simp only [zero_mul, sub_zero, one_mul] at hparts
  have hw : Continuous (fun x => (b - 2 * x) * f x) := by fun_prop
  have hw_eq : (∫ x in (0 : ℝ)..b, (b - 2 * x) * f x) =
      b * F b - 2 * ∫ x in (0 : ℝ)..b, x * f x := by
    calc
      _ = ∫ x in (0 : ℝ)..b, b * f x - 2 * (x * f x) :=
        integral_congr (fun x _ => by ring)
      _ = _ := by
        have h₁ : Continuous (fun x => b * f x) := by fun_prop
        have h₂ : Continuous (fun x => 2 * (x * f x)) := by fun_prop
        rw [integral_sub (h₁.intervalIntegrable 0 b) (h₂.intervalIntegrable 0 b),
          integral_const_mul, integral_const_mul]
  calc
    _ = ∫ x in (0 : ℝ)..b, b⁻¹ * (2 * F x - F b + (b - 2 * x) * f x) := by
      apply integral_congr
      rw [uIcc_of_le hb.le]
      exact hmean
    _ = _ := by
      have hF₂ : Continuous (fun x => 2 * F x) := by fun_prop
      have hF₃ : Continuous (fun x => 2 * F x - F b) := by fun_prop
      rw [integral_const_mul, integral_add (hF₃.intervalIntegrable 0 b)
          (hw.intervalIntegrable 0 b),
        integral_sub (hF₂.intervalIntegrable 0 b) (continuous_const.intervalIntegrable 0 b),
        integral_const_mul, integral_const, smul_eq_mul, sub_zero, hw_eq, hparts]
      ring

private lemma hasDerivAt_pow_cos (m : ℕ) (x : ℝ) :
    HasDerivAt (fun t => cos t ^ (m + 2))
      (-((m : ℝ) + 2) * cos x ^ (m + 1) * sin x) x := by
  convert (hasDerivAt_cos x).pow (m + 2) using 1
  push_cast
  ring

private lemma hasDerivAt_pow_cos_derivative (m : ℕ) (x : ℝ) :
    HasDerivAt (fun t => -((m : ℝ) + 2) * cos t ^ (m + 1) * sin t)
      (((m : ℝ) + 2) * ((m : ℝ) + 1) * cos x ^ m - ((m : ℝ) + 2) ^ 2 * cos x ^ (m + 2)) x := by
  convert (((hasDerivAt_cos x).pow (m + 1)).const_mul (-((m : ℝ) + 2))).mul
    (hasDerivAt_sin x) using 1
  push_cast
  simp only [Pi.pow_apply, pow_succ (cos x) (m + 1), pow_succ (cos x) m]
  linear_combination (-((m : ℝ) + 2) * ((m : ℝ) + 1) * cos x ^ m) * (sin_sq_add_cos_sq x)

-- Differentiate the product of the linear weight and the derivative. Adding twice
-- the cosine power cancels the term coming from the derivative of the weight.
private lemma weightedCos_recursion (m : ℕ) (b : ℝ) (h : sin b = 0 ∨ cos b = 0) :
    ((m : ℝ) + 2) ^ 2 * weightedCos (m + 2) b =
      ((m : ℝ) + 2) * ((m : ℝ) + 1) * weightedCos m b + 2 * (1 - cos b ^ (m + 2)) := by
  let w (x : ℝ) := b - 2 * x
  let g (x : ℝ) := -((m : ℝ) + 2) * cos x ^ (m + 1) * sin x
  let A := ((m : ℝ) + 2) * ((m : ℝ) + 1)
  let B := ((m : ℝ) + 2) ^ 2
  have hwd (x : ℝ) : HasDerivAt w (-2) x := by
    convert (hasDerivAt_const x b).sub ((hasDerivAt_id x).const_mul (2 : ℝ)) using 1
    · rfl
    · norm_num
  have hd (x : ℝ) : HasDerivAt (fun t => w t * g t + 2 * cos t ^ (m + 2))
      (A * (w x * cos x ^ m) - B * (w x * cos x ^ (m + 2))) x := by
    convert ((hwd x).mul (hasDerivAt_pow_cos_derivative m x)).add
      ((hasDerivAt_pow_cos m x).const_mul 2) using 1
    dsimp [A, B, g]
    ring
  have hc₁ : Continuous (fun x => A * (w x * cos x ^ m)) := by dsimp [w]; fun_prop
  have hc₂ : Continuous (fun x => B * (w x * cos x ^ (m + 2))) := by dsimp [w]; fun_prop
  have hi := integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := b) (fun x _ => hd x)
    ((hc₁.sub hc₂).intervalIntegrable 0 b)
  have hg₀ : g 0 = 0 := by simp [g]
  have hgᵦ : g b = 0 := by rcases h with h | h <;> simp [g, h]
  rw [integral_sub (hc₁.intervalIntegrable 0 b) (hc₂.intervalIntegrable 0 b),
    integral_const_mul, integral_const_mul, hg₀, hgᵦ] at hi
  simp only [mul_zero, zero_add, cos_zero, one_pow] at hi
  change A * weightedCos m b - B * weightedCos (m + 2) b = _ at hi
  linarith only [hi]

private lemma cosPow_lipschitz (n : ℕ) : LipschitzWith (n : ℝ≥0) (fun x : ℝ => cos x ^ n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_natCast]
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => cos t ^ n) (f' := fun t => (n : ℝ) * cos t ^ (n - 1) * -sin t)
    (s := univ) (x := y) (y := x)
  · intro t _
    exact ((hasDerivAt_cos t).pow n).hasDerivWithinAt
  · intro t _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg n)]
    calc
      _ ≤ ((n : ℝ) * 1) * 1 := by
        gcongr
        · exact pow_le_one₀ (abs_nonneg _) (abs_cos_le_one t)
        · exact abs_sin_le_one t
      _ = _ := by ring
  · exact convex_univ
  · exact mem_univ y
  · exact mem_univ x

private lemma cosPowArea_odd_limit {n : ℕ} (hn : Odd n) :
    Tendsto (fun k : ℕ => cosPowArea n k) atTop (𝓝 ((2 / π) * weightedCos n π)) := by
  let f (x : ℝ) := cos x ^ n
  have hc : LipschitzWith (n : ℝ≥0) f := cosPow_lipschitz n
  have hp : Function.Periodic f (2 * π) := by
    intro x
    change cos (x + 2 * π) ^ n = cos x ^ n
    rw [show x + 2 * π = (x + π) + π by ring, cos_add_pi, cos_add_pi, neg_neg]
  have he (x : ℝ) : f (-x) = f x := by simp [f]
  have hanti : AntitoneOn f (Icc 0 π) := fun x hx y hy hxy =>
    hn.strictMono_pow.monotone (strictAntiOn_cos.antitoneOn hx hy hxy)
  have hl := tendsto_gap_mean hc pi_pos hp he
  rw [integral_meanGap hc.continuous pi_pos hanti] at hl
  exact hl

private lemma cosPowArea_even_eq {n : ℕ} (hn : Even n) (k : ℕ) :
    cosPowArea n k = 2 * ∫ x in (0 : ℝ)..(π / 2), |cos x ^ n - cos (k * x) ^ n| := by
  let g (x : ℝ) := |cos x ^ n - cos (k * x) ^ n|
  have hc : Continuous g := by dsimp [g]; fun_prop
  have hsym (x : ℝ) : g (π - x) = g x := by
    have hshift : cos ((k : ℝ) * (π - x)) = (-1) ^ k * cos ((k : ℝ) * x) := by
      rw [mul_sub, cos_sub, cos_nat_mul_pi, sin_nat_mul_pi, zero_mul, add_zero]
    have hsign : (((-1 : ℝ) ^ k) ^ n) = 1 := by
      rw [← pow_mul, (hn.mul_left k).neg_pow, one_pow]
    dsimp [g]
    rw [cos_pi_sub, hn.neg_pow, hshift, mul_pow, hsign, one_mul]
  have hr := integral_comp_sub_left (a := (0 : ℝ)) (b := π / 2) g π
  simp only [hsym, sub_zero, show π - π / 2 = π / 2 by ring] at hr
  change (∫ x in (0 : ℝ)..π, g x) = 2 * ∫ x in (0 : ℝ)..(π / 2), g x
  rw [← integral_add_adjacent_intervals (hc.intervalIntegrable 0 (π / 2))
    (hc.intervalIntegrable (π / 2) π), ← hr, two_mul]

private lemma cosPowArea_even_limit {n : ℕ} (hn : Even n) :
    Tendsto (fun k : ℕ => cosPowArea n k) atTop (𝓝 ((4 / (π / 2)) * weightedCos n (π / 2))) := by
  let f (x : ℝ) := cos x ^ n
  have hb : 0 < π / 2 := half_pos pi_pos
  have hc : LipschitzWith (n : ℝ≥0) f := cosPow_lipschitz n
  have hp : Function.Periodic f (2 * (π / 2)) := by
    intro x
    change cos (x + 2 * (π / 2)) ^ n = cos x ^ n
    rw [show 2 * (π / 2) = π by ring, cos_add_pi, hn.neg_pow]
  have he (x : ℝ) : f (-x) = f x := by simp [f]
  have himp {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (π / 2)) : x ∈ Icc (0 : ℝ) π :=
    ⟨hx.1, hx.2.trans (by linarith [pi_pos])⟩
  have hanti : AntitoneOn f (Icc 0 (π / 2)) := by
    intro x hx y hy hxy
    exact pow_le_pow_left₀ (cos_nonneg_of_mem_Icc ⟨by linarith [hy.1], hy.2⟩)
      (strictAntiOn_cos.antitoneOn (himp hx) (himp hy) hxy) n
  have hl := tendsto_gap_mean hc hb hp he
  rw [integral_meanGap hc.continuous hb hanti] at hl
  have h := hl.const_mul 2
  change Tendsto (fun k : ℕ => 2 * ∫ x in (0 : ℝ)..(π / 2), |cos x ^ n - cos (k * x) ^ n|)
    atTop (𝓝 (2 * ((2 / (π / 2)) * weightedCos n (π / 2)))) at h
  rw [show 2 * ((2 / (π / 2)) * weightedCos n (π / 2)) =
    (4 / (π / 2)) * weightedCos n (π / 2) by ring] at h
  exact h.congr fun k => (cosPowArea_even_eq hn k).symm

private lemma scaled_recursion (m : ℕ) (b r : ℝ) (h : sin b = 0 ∨ cos b = 0) :
    r * weightedCos (m + 2) b = ((m : ℝ) + 2 - 1) / ((m : ℝ) + 2) *
      (r * weightedCos m b) + r * (2 * (1 - cos b ^ (m + 2))) / (((m : ℝ) + 2) ^ 2) := by
  have hm : (m : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hm]
  linear_combination r * weightedCos_recursion m b h

public section

/-- **Recursion for the limiting areas between cosine powers.** For natural numbers $n$ and $k$,
let $A_n(k) = \int_0^\pi |\cos^n x - \cos^n(kx)|\,dx$. For every natural number $n \ge 3$ there
are real numbers $L$ and $L'$ such that $A_n(k) \to L$ and $A_{n-2}(k) \to L'$ as $k \to \infty$
through the natural numbers, and $L = \frac{n-1}{n} L' + \frac{c}{n^2 \pi}$, where $c = 8$ if $n$
is odd and $c = 16$ if $n$ is even.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 3
(`jis-2025-25.2.3-thm-3`). -/
public theorem cosPowArea_limit_recursion {n : ℕ} (hn : 3 ≤ n) :
    ∃ L L' : ℝ, Tendsto (fun k => cosPowArea n k) atTop (𝓝 L) ∧
      Tendsto (fun k => cosPowArea (n - 2) k) atTop (𝓝 L') ∧
      L = ((n : ℝ) - 1) / n * L' + (if Odd n then 8 else 16) / ((n : ℝ) ^ 2 * π) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  have hodd : Odd (m + 2) ↔ Odd m := by simp [Nat.odd_iff]
  rw [Nat.add_sub_cancel]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  have hden : (m : ℝ) + 2 ≠ 0 := by positivity
  by_cases hm : Odd m
  · have hn' := hodd.mpr hm
    refine ⟨_, _, cosPowArea_odd_limit hn', cosPowArea_odd_limit hm, ?_⟩
    have h := scaled_recursion m π (2 / π) (Or.inl sin_pi)
    rw [cos_pi, hn'.neg_pow, one_pow] at h
    rw [ite_eq_left hn']
    convert h using 1
    field_simp [pi_ne_zero, hden]; ring
  · have he := Nat.not_odd_iff_even.mp hm
    have he' := Nat.not_odd_iff_even.mp (mt hodd.mp hm)
    refine ⟨_, _, cosPowArea_even_limit he', cosPowArea_even_limit he, ?_⟩
    have h := scaled_recursion m (π / 2) (4 / (π / 2)) (Or.inr cos_pi_div_two)
    rw [cos_pi_div_two, zero_pow (by omega : m + 2 ≠ 0)] at h
    rw [ite_eq_right (mt hodd.mp hm)]
    convert h using 1
    field_simp [pi_ne_zero, hden]; ring

end

end MetaMathlibExt
