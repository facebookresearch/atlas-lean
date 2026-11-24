/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Dilog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import MathlibExt.NumberTheory.SanfordCoupledRecurrence

/-!
# Sanford's symmetric dilogarithm series

We prove Sanford's symmetric series by summing Abel's five-term relation along
Sanford's coupled recurrence and using the reflection identity at the endpoints.
-/

open Filter Real Set
open scoped Topology

namespace MetaMathlibExt
namespace rogersDilog_sanford_symmetric_series

private noncomputable def L (x : ℝ) : ℝ :=
  li2PowerSeries x + log x * log (1 - x) / 2

private lemma L_nonneg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ L x := by
  unfold L li2PowerSeries
  exact add_nonneg (tsum_nonneg fun n => div_nonneg (pow_nonneg hx.1.le _) (sq_nonneg _))
    (div_nonneg (mul_nonneg_of_nonpos_of_nonpos (log_nonpos hx.1.le hx.2.le)
      (log_nonpos (sub_nonneg.mpr hx.2.le) (sub_le_self _ hx.1.le))) (by norm_num))

private lemma L_zero : L 0 = 0 := by simp [L, li2PowerSeries_zero]

private lemma L_reflect {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : L x + L (1 - x) = π ^ 2 / 6 := by
  rcases hx.1.eq_or_lt with rfl | hx₀
  · simp [L, li2PowerSeries_zero, li2PowerSeries_one]
  rcases hx.2.eq_or_lt with rfl | hx₁
  · simp [L, li2PowerSeries_zero, li2PowerSeries_one]
  simp only [L, sub_sub_cancel]
  linarith [li2PowerSeries_reflection ⟨hx₀, hx₁⟩]

-- Reflection expresses L in terms of two power series continuous at both endpoints.
private lemma L_continuousOn : ContinuousOn L (Icc 0 1) := by
  have h₁ := continuousOn_li2PowerSeries.mono (show Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 by
    intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)
  have h₂ : ContinuousOn (fun x => li2PowerSeries (1 - x)) (Icc (0 : ℝ) 1) :=
    h₁.comp (continuousOn_const.sub continuousOn_id)
      (fun x hx => ⟨sub_nonneg.mpr hx.2, sub_le_self 1 hx.1⟩)
  apply (((h₁.sub h₂).add (continuousOn_const (c := π ^ 2 / 6))).div_const 2).congr
  intro x hx
  have he := L_reflect hx
  simp only [L, sub_sub_cancel, Pi.add_apply, Pi.sub_apply] at he ⊢
  linarith

private lemma L_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt L (-(log (1 - x) / x + log x / (1 - x)) / 2) x := by
  have hd := hasDerivAt_li2PowerSeries (by simpa only [abs_of_pos hx.1] using hx.2) hx.1.ne'
  have hlog := ((hasDerivAt_id' x).const_sub 1).log (sub_pos.mpr hx.2).ne'
  refine (hd.add (((hasDerivAt_log hx.1.ne').mul hlog).div_const 2)).congr_deriv ?_
  ring

-- The two new arguments of Abel's relation are step x y and step y x.
private noncomputable def step (x y : ℝ) : ℝ := x * (1 - y) / (1 - x * y)

private lemma one_sub_step {x y : ℝ} (hd : 1 - x * y ≠ 0) :
    1 - step x y = (1 - x) / (1 - x * y) := by
  unfold step
  field_simp
  ring

private lemma mul_mem {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    x * y ∈ Ioo (0 : ℝ) 1 :=
  ⟨mul_pos hx.1 hy.1, (mul_lt_of_lt_one_right hx.1 hy.2).trans hx.2⟩

private lemma step_mem {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    step x y ∈ Ioo (0 : ℝ) 1 := by
  have hd := sub_pos.mpr (mul_mem hx hy).2
  refine ⟨div_pos (mul_pos hx.1 (sub_pos.mpr hy.2)) hd, sub_pos.mp ?_⟩
  rw [one_sub_step hd.ne']
  exact div_pos (sub_pos.mpr hx.2) hd

-- Vary x with y fixed. After expanding the four logarithms of the two new
-- arguments and their complements, the derivative of the five-term difference vanishes.
private lemma fiveTerm_deriv {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => L z - L (z * y) - L (step z y) - L (step y z)) 0 x := by
  have hxy := mul_mem hx hy
  have hd := (sub_pos.mpr hxy.2).ne'
  have hdx := (sub_pos.mpr hx.2).ne'
  have hdy := (sub_pos.mpr hy.2).ne'
  have hprod := (hasDerivAt_id' x).mul_const y
  have hden := hprod.const_sub 1
  have hu := ((hasDerivAt_id' x).mul_const (1 - y)).div hden hd
  have hv := (((hasDerivAt_id' x).const_sub 1).const_mul y).div
    (((hasDerivAt_id' x).const_mul y).const_sub 1) (by simpa only [mul_comm y x] using hd)
  refine ((((L_hasDerivAt hx).sub ((L_hasDerivAt hxy).comp x hprod)).sub
    ((L_hasDerivAt (step_mem hx hy)).comp x hu)).sub
      ((L_hasDerivAt (step_mem hy hx)).comp x hv)).congr_deriv ?_
  rw [one_sub_step hd, one_sub_step (by rwa [mul_comm y x]), step, step, mul_comm y x]
  rw [log_div hdx hd, log_div hdy hd, log_div (mul_ne_zero hx.1.ne' hdy) hd,
    log_div (mul_ne_zero hy.1.ne' hdx) hd, log_mul hx.1.ne' hy.1.ne',
    log_mul hx.1.ne' hdy, log_mul hy.1.ne' hdx]
  field_simp [hx.1.ne', hy.1.ne', hdx, hdy, hd]
  ring

private lemma fiveTerm {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    L x + L y = L (x * y) + L (step x y) + L (step y x) := by
  let F (z : ℝ) := L z - L (z * y) - L (step z y) - L (step y z)
  have compL {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 x)) (h₀ : f 0 ∈ Icc 0 1)
      (hi : ∀ z ∈ Ioo (0 : ℝ) 1, f z ∈ Ioo 0 1) :
      ContinuousOn (fun z => L (f z)) (Icc 0 x) := by
    apply L_continuousOn.comp hc
    intro z hz
    rcases hz.1.eq_or_lt with rfl | h
    · exact h₀
    · exact Ioo_subset_Icc_self (hi z ⟨h, hz.2.trans_lt hx.2⟩)
  have hd (z : ℝ) (hz : z ∈ Icc 0 x) : 1 - z * y ≠ 0 :=
    (sub_pos.mpr ((mul_le_mul_of_nonneg_right hz.2 hy.1.le).trans_lt (mul_mem hx hy).2)).ne'
  have hu : ContinuousOn (fun z => step z y) (Icc 0 x) :=
    (continuousOn_id.mul continuousOn_const).div
      (continuousOn_const.sub (continuousOn_id.mul continuousOn_const)) hd
  have hv : ContinuousOn (step y) (Icc 0 x) :=
    (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      (fun z hz => by simpa only [mul_comm y z] using hd z hz)
  have hc : ContinuousOn F (Icc 0 x) :=
    (((L_continuousOn.mono (Icc_subset_Icc_right hx.2.le)).sub
      (compL (continuousOn_id.mul continuousOn_const) (by simp) (fun _ hz => mul_mem hz hy))).sub
      (compL hu (by simp [step]) (fun _ hz => step_mem hz hy))).sub
      (compL hv (by simpa [step] using Ioo_subset_Icc_self hy) (fun _ hz => step_mem hy hz))
  obtain ⟨c, hc', he⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0) hx.1 hc
    (fun z hz => fiveTerm_deriv ⟨hz.1, hz.2.trans hx.2⟩ hy)
  have heq := (div_eq_zero_iff.mp he.symm).resolve_right (by simpa using hx.1.ne')
  simp only [F, step, zero_mul, mul_zero, sub_zero, mul_one,
    div_one, L_zero] at heq ⊢
  linarith

-- Sum along the recurrence. The starting arguments are complementary, and the
-- limiting pair is (1 - r, 0), so reflection leaves just L r.
private lemma hasSum_products {X Y : ℕ → ℝ} {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hX : X 0 ∈ Ioo (0 : ℝ) 1) (hY : Y 0 = 1 - X 0)
    (rec : ∀ n, X (n + 1) = step (X n) (Y n) ∧ Y (n + 1) = step (Y n) (X n))
    (limX : Tendsto X atTop (𝓝 (1 - r))) (limY : Tendsto Y atTop (𝓝 0)) :
    HasSum (fun n => L (X n * Y n)) (L r) := by
  have mem (n : ℕ) : X n ∈ Ioo (0 : ℝ) 1 ∧ Y n ∈ Ioo (0 : ℝ) 1 := by
    induction n with
    | zero => exact ⟨hX, hY ▸ ⟨sub_pos.mpr hX.2, sub_lt_self _ hX.1⟩⟩
    | succ n ih =>
      rw [(rec n).1, (rec n).2]
      exact ⟨step_mem ih.1 ih.2, step_mem ih.2 ih.1⟩
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => L_nonneg (mul_mem (mem n).1 (mem n).2)) _).2
  have sum_range (n : ℕ) : ∑ k ∈ Finset.range n, L (X k * Y k) =
      π ^ 2 / 6 - (L (X n) + L (Y n)) := by
    induction n with
    | zero => simp [hY, L_reflect (Ioo_subset_Icc_self hX)]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, (rec n).1, (rec n).2]
      linarith [fiveTerm (mem n).1 (mem n).2]
  have limL {f : ℕ → ℝ} {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (hf : Tendsto f atTop (𝓝 b))
      (hm : ∀ n, f n ∈ Ioo (0 : ℝ) 1) : Tendsto (fun n => L (f n)) atTop (𝓝 (L b)) :=
    (L_continuousOn b hb).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hf, Eventually.of_forall fun n => Ioo_subset_Icc_self (hm n)⟩)
  have hlim := ((limL ⟨sub_nonneg.mpr hr.2.le, sub_le_self _ hr.1.le⟩ limX
    (fun n => (mem n).1)).add (limL (by simp) limY (fun n => (mem n).2))).const_sub (π ^ 2 / 6)
  have hend : π ^ 2 / 6 - (L (1 - r) + L 0) = L r := by
    rw [L_zero, add_zero, ← L_reflect (Ioo_subset_Icc_self hr), add_sub_cancel_right]
  simpa only [sum_range, hend] using hlim

private lemma symmetric_series {u v : ℝ} (hv : 0 < v) (hvu : v < u) (hs : u + v = 1) :
    HasSum (fun n : ℕ => L ((u - v) ^ 2 * v ^ (n + 1) * u ^ (n + 1) /
      (u ^ (n + 2) - v ^ (n + 2)) ^ 2)) (L (v / u)) := by
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
    unfold step
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
  simpa only [hd, hr, R, L, li2PowerSeries, Nat.cast_add, Nat.cast_one] using
    (symmetric_series hv hvu hs).tsum_eq

end MetaMathlibExt
