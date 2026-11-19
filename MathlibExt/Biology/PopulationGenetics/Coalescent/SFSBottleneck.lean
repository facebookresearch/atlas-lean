/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Coalescent.SFSGrowth
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# The site frequency spectrum under a population bottleneck

A sample of `n` gene copies is drawn from a population whose size `s` units of `2N₀`
generations before the present (`N₀` the present size) is `N₀ η(s)` with the piecewise-constant
**bottleneck history** `η(s) = f` for `a ≤ s < a + d` and `η(s) = 1` otherwise
(`bottleneckSize`): the population was at its present size, crashed to the relative size
`f > 0` at time `a + d` before the present, stayed there for `d ≥ 0` time units and recovered
`a ≥ 0` time units ago. Pairs of lineages coalesce at rate `1 / η(s)`, so the cumulative
intensity is `R(s) = ∫_0^s 1/η = s + (1/f - 1) · |[0, s] ∩ [a, a + d]|` (`bottleneckRate`,
`cumRate_bottleneckSize`). `f < 1` is a bottleneck, `f > 1` a temporary expansion, and
`f = 1` or `d = 0` a constant population.

**The time change.** As for exponential growth (`SFSGrowth`), the genealogy is Kingman's
coalescent run on the clock `R` (Griffiths & Tavaré): a standard-coalescent event at standard
time `u` happens at real time `G(u) = R⁻¹(u) = u - (1 - f) · |[0, u] ∩ [a, a + d/f]|`
(`bottleneckTime`; `bottleneckTime_bottleneckRate`, `bottleneckRate_bottleneckTime`). `G` is
piecewise linear with slopes `1`, `f`, `1`: the bottleneck occupies the standard-time window
`[a, a + d/f]`, compressed by the factor `f` in real time. The epoch with `k` lineages lasts
`T^b_k = G(V_k) - G(V_{k+1})` in real time, `V_k = T_k + ⋯ + T_n` (`bottleneckHolding`,
`bottleneckTimes`). The topology is untouched, so its independence from the holding times is
inherited from Kingman's coalescent.

**Expected spectrum.** By `VariableSFS.integral_sfs_of_indep`,
`E ξ_i = (θ / 2) ∑_{k=2}^{n} k C(n-i-1, k-2) / C(n-1, k-1) · E T^b_k` for `1 ≤ i ≤ n - 1`
(`integral_sfs_bottleneck`). For `f ≤ 1` the time change is `1`-Lipschitz, so every epoch is
shortened and every entry is at most Fu's constant-size value `θ / i`
(`integral_sfs_bottleneck_le`). For a genuine bottleneck (`f < 1`, `d > 0`) the oldest epoch
overlaps the bottleneck window with positive probability, so it is strictly shortened on
average and every entry is strictly below `θ / i` when `θ > 0` (`integral_sfs_bottleneck_lt`).
For `f ≥ 1` every entry is at least `θ / i` (`integral_sfs_bottleneck_ge`), and `f = 1` or
`d = 0` gives exactly `θ / i` (`integral_sfs_bottleneck_eq`). The most recent epoch has mean
Bhaskar–Song's first-coalescence time `E T^b_n = ∫_0^∞ exp(-C(n,2) R(s)) ds`
(`integral_bottleneckTimes_top`), and the real time to the most recent common ancestor is `G`
of the standard one (`sum_bottleneckHolding`).

Not formalized here: the normalized-spectrum effects of a bottleneck (the relative excess or
deficit of rare variants depending on the timing), closed forms of `E T^b_k` for `k < n`, the
covariance of the spectrum, and the derivation of the time change from a time-inhomogeneous
Wright–Fisher model.

Source: R. C. Griffiths and S. Tavaré (1994), the coalescent of a population of variable size
as Kingman's coalescent time-changed by the inverse of `R(s) = ∫_0^s 1/η`; the bottleneck
history of F. Tajima (1989) and M. Nei, T. Maruyama and R. Chakraborty (1975); the expected
spectrum formula of Griffiths & Tavaré (1998) and Polanski & Kimmel (2003), formalized in
`VariableSFS`.

## Main results

* `cumRate_bottleneckSize`: `R(s) = s + (1/f - 1) · |[0, s] ∩ [a, a + d]|`.
* `bottleneckTime_bottleneckRate`, `bottleneckRate_bottleneckTime`, `lt_bottleneckTime_iff`:
  `G = R⁻¹`.
* `bottleneckTime_sub_le`, `le_bottleneckTime_sub`, `bottleneckTime_lt_bottleneckTime`: `G` is
  strictly increasing, `1`-Lipschitz for `f ≤ 1` and expanding for `f ≥ 1`.
* `integral_bottleneckTimes_le`, `integral_bottleneckTimes_ge`, `integral_bottleneckTimes_eq`,
  `integral_bottleneckTimes_two_lt`: comparison of `E T^b_k` with `1 / C(k,2)`.
* `integral_bottleneckTimes_top`: `E T^b_n = firstCoalMean (bottleneckSize a d f) n`.
* `integral_sfs_bottleneck`: the expected spectrum under a bottleneck.
* `integral_sfs_bottleneck_le`, `integral_sfs_bottleneck_lt`, `integral_sfs_bottleneck_ge`,
  `integral_sfs_bottleneck_eq`: comparison with `θ / i`.

## References

* R. C. Griffiths and S. Tavaré, *Sampling theory for neutral alleles in a varying
  environment*, Phil. Trans. R. Soc. Lond. B 344 (1994), 403–410.
* F. Tajima, *The effect of change in population size on DNA polymorphism*, Genetics 123
  (1989), 597–601.
* M. Nei, T. Maruyama and R. Chakraborty, *The bottleneck effect and genetic variability in
  populations*, Evolution 29 (1975), 1–10.
* R. C. Griffiths and S. Tavaré, *The age of a mutation in a general coalescent tree*,
  Stoch. Models 14 (1998), 273–295.
* A. Polanski and M. Kimmel, *New explicit expressions for relative frequencies of
  single-nucleotide polymorphisms with application to statistical inference on population
  growth*, Genetics 165 (2003), 427–436.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.SFSBottleneck

open SiteFrequencySpectrum VariableSFS SFSGrowth

/-! ### The bottleneck history and its time change -/

/-- The relative population size `η(s)` at time `s` before the present (in units of `2N₀`
generations) under a **bottleneck**: `f` during `a ≤ s < a + d`, and `1` (the present size)
otherwise. -/
def bottleneckSize (a d f s : ℝ) : ℝ := if a ≤ s ∧ s < a + d then f else 1

/-- The length `|[0, u] ∩ [a, a + w]| = min (max (u - a) 0) w` of the part of the window
`[a, a + w]` before time `u` (for `a ≥ 0`, `w ≥ 0`). -/
def bottleneckOverlap (a w u : ℝ) : ℝ := min (max (u - a) 0) w

/-- The cumulative coalescence intensity `R(s) = s + (1/f - 1) · |[0, s] ∩ [a, a + d]|` of the
bottleneck history (`cumRate_bottleneckSize`). -/
def bottleneckRate (a d f s : ℝ) : ℝ := s + (f⁻¹ - 1) * bottleneckOverlap a d s

/-- The **Griffiths–Tavaré time change** for a bottleneck:
`G(u) = u - (1 - f) · |[0, u] ∩ [a, a + d/f]|`, the real time at which the intensity `R`
reaches `u` (`bottleneckTime_bottleneckRate`, `bottleneckRate_bottleneckTime`). A
standard-coalescent event at time `u` happens at real time `G(u)`. -/
def bottleneckTime (a d f u : ℝ) : ℝ := u - (1 - f) * bottleneckOverlap a (d / f) u

section TimeChange

variable {a d f w u v s : ℝ}

theorem bottleneckOverlap_of_le (hw : 0 ≤ w) (hu : u ≤ a) : bottleneckOverlap a w u = 0 := by
  rw [bottleneckOverlap, max_eq_right (sub_nonpos.2 hu), min_eq_left hw]

theorem bottleneckOverlap_of_mem (hau : a ≤ u) (hu : u ≤ a + w) :
    bottleneckOverlap a w u = u - a := by
  rw [bottleneckOverlap, max_eq_left (sub_nonneg.2 hau), min_eq_left (by linarith)]

theorem bottleneckOverlap_of_ge (hw : 0 ≤ w) (hu : a + w ≤ u) : bottleneckOverlap a w u = w := by
  rw [bottleneckOverlap, max_eq_left (by linarith), min_eq_right (by linarith)]

theorem bottleneckOverlap_nonneg (hw : 0 ≤ w) (u : ℝ) : 0 ≤ bottleneckOverlap a w u :=
  le_min (le_max_right _ _) hw

theorem bottleneckOverlap_le (ha : 0 ≤ a) (hu : 0 ≤ u) : bottleneckOverlap a w u ≤ u := by
  unfold bottleneckOverlap
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The overlap is monotone in `u`. -/
theorem bottleneckOverlap_mono (huv : u ≤ v) :
    bottleneckOverlap a w u ≤ bottleneckOverlap a w v := by
  unfold bottleneckOverlap
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The overlap is `1`-Lipschitz in `u`. -/
theorem bottleneckOverlap_sub_le (hw : 0 ≤ w) (huv : u ≤ v) :
    bottleneckOverlap a w v - bottleneckOverlap a w u ≤ v - u := by
  unfold bottleneckOverlap
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The overlap grows strictly across the window: if `u < v`, `u < a + w` and `a < v`, then
`[u, v]` meets the window `[a, a + w]` in an interval of positive length. -/
theorem bottleneckOverlap_lt (hw : 0 < w) (hu : u < a + w) (hv : a < v) (huv : u < v) :
    bottleneckOverlap a w u < bottleneckOverlap a w v := by
  unfold bottleneckOverlap
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The time change is the identity for a constant population (`f = 1` or `d = 0`). -/
theorem bottleneckTime_eq_self (h : f = 1 ∨ d = 0) (u : ℝ) : bottleneckTime a d f u = u := by
  rcases h with rfl | rfl
  · simp [bottleneckTime]
  · simp only [bottleneckTime, bottleneckOverlap, zero_div, min_eq_right (le_max_right _ _),
      mul_zero, sub_zero]

/-- The present is fixed by the time change: `G(0) = 0` (for a bottleneck in the past). -/
theorem bottleneckTime_zero (ha : 0 ≤ a) (hd : 0 ≤ d) (hf : 0 < f) :
    bottleneckTime a d f 0 = 0 := by
  rw [bottleneckTime, bottleneckOverlap_of_le (div_nonneg hd hf.le) ha, mul_zero, sub_zero]

/-- `G` inverts the intensity: `G(R(s)) = s`. -/
theorem bottleneckTime_bottleneckRate (hd : 0 ≤ d) (hf : 0 < f) (s : ℝ) :
    bottleneckTime a d f (bottleneckRate a d f s) = s := by
  have hw : 0 ≤ d / f := div_nonneg hd hf.le
  have hinv : f * f⁻¹ = 1 := mul_inv_cancel₀ hf.ne'
  rcases le_total s a with h1 | h1
  · rw [bottleneckRate, bottleneckOverlap_of_le hd h1, mul_zero, add_zero, bottleneckTime,
      bottleneckOverlap_of_le hw h1, mul_zero, sub_zero]
  rcases le_total s (a + d) with h2 | h2
  · have hR : bottleneckRate a d f s = a + (s - a) * f⁻¹ := by
      rw [bottleneckRate, bottleneckOverlap_of_mem h1 h2]; ring
    have hlo : a ≤ a + (s - a) * f⁻¹ :=
      le_add_of_nonneg_right (mul_nonneg (by linarith) (inv_nonneg.2 hf.le))
    have hhi : a + (s - a) * f⁻¹ ≤ a + d / f := by
      have : (s - a) * f⁻¹ ≤ d * f⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hf.le)
      rw [div_eq_mul_inv]
      linarith
    rw [bottleneckTime, hR, bottleneckOverlap_of_mem hlo hhi]
    linear_combination (s - a) * hinv
  · have hR : bottleneckRate a d f s = s + (f⁻¹ - 1) * d := by
      rw [bottleneckRate, bottleneckOverlap_of_ge hd h2]
    have hge : a + d / f ≤ s + (f⁻¹ - 1) * d := by
      have : a + d / f - (s + (f⁻¹ - 1) * d) = a + d - s := by ring
      linarith
    rw [bottleneckTime, hR, bottleneckOverlap_of_ge hw hge]
    linear_combination d * hinv

/-- The intensity inverts `G`: `R(G(u)) = u`. -/
theorem bottleneckRate_bottleneckTime (hd : 0 ≤ d) (hf : 0 < f) (u : ℝ) :
    bottleneckRate a d f (bottleneckTime a d f u) = u := by
  have hw : 0 ≤ d / f := div_nonneg hd hf.le
  have hinv : f * f⁻¹ = 1 := mul_inv_cancel₀ hf.ne'
  rcases le_total u a with h1 | h1
  · rw [bottleneckTime, bottleneckOverlap_of_le hw h1, mul_zero, sub_zero, bottleneckRate,
      bottleneckOverlap_of_le hd h1, mul_zero, add_zero]
  rcases le_total u (a + d / f) with h2 | h2
  · have hG : bottleneckTime a d f u = a + f * (u - a) := by
      rw [bottleneckTime, bottleneckOverlap_of_mem h1 h2]; ring
    have hlo : a ≤ a + f * (u - a) := le_add_of_nonneg_right (mul_nonneg hf.le (by linarith))
    have hhi : a + f * (u - a) ≤ a + d := by
      have h3 : f * (u - a) ≤ f * (d / f) := mul_le_mul_of_nonneg_left (by linarith) hf.le
      have h4 : f * (d / f) = d := by rw [div_eq_mul_inv]; linear_combination d * hinv
      linarith
    rw [hG, bottleneckRate, bottleneckOverlap_of_mem hlo hhi]
    linear_combination (u - a) * hinv
  · have hG : bottleneckTime a d f u = u - d / f + d := by
      rw [bottleneckTime, bottleneckOverlap_of_ge hw h2]
      linear_combination d * hinv
    rw [hG, bottleneckRate, bottleneckOverlap_of_ge hd (by linarith)]
    ring

/-- The increment of `G` over `[u, v]`. -/
theorem bottleneckTime_sub (a d f u v : ℝ) :
    bottleneckTime a d f v - bottleneckTime a d f u =
      (v - u) - (1 - f) * (bottleneckOverlap a (d / f) v - bottleneckOverlap a (d / f) u) := by
  unfold bottleneckTime
  ring

/-- `G` is monotone. -/
theorem bottleneckTime_sub_nonneg (hd : 0 ≤ d) (hf : 0 < f) (huv : u ≤ v) :
    0 ≤ bottleneckTime a d f v - bottleneckTime a d f u := by
  have hw : 0 ≤ d / f := div_nonneg hd hf.le
  have h0 := sub_nonneg.2 (bottleneckOverlap_mono (a := a) (w := d / f) huv)
  have h1 := bottleneckOverlap_sub_le (a := a) hw huv
  rw [bottleneckTime_sub]
  rcases le_total f 1 with hf1 | hf1
  · nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hf1)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hf1) h0]

/-- `G` is strictly increasing. -/
theorem bottleneckTime_lt_bottleneckTime (hd : 0 ≤ d) (hf : 0 < f) (huv : u < v) :
    bottleneckTime a d f u < bottleneckTime a d f v := by
  have hw : 0 ≤ d / f := div_nonneg hd hf.le
  have h0 := sub_nonneg.2 (bottleneckOverlap_mono (a := a) (w := d / f) huv.le)
  have h1 := bottleneckOverlap_sub_le (a := a) hw huv.le
  rw [← sub_pos, bottleneckTime_sub]
  rcases le_total f 1 with hf1 | hf1
  · nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hf1), mul_pos hf (sub_pos.2 huv)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hf1) h0]

/-- For a bottleneck (`f ≤ 1`) the time change is `1`-Lipschitz: `G(v) - G(u) ≤ v - u`. -/
theorem bottleneckTime_sub_le (hf1 : f ≤ 1) (huv : u ≤ v) :
    bottleneckTime a d f v - bottleneckTime a d f u ≤ v - u := by
  have h0 := sub_nonneg.2 (bottleneckOverlap_mono (a := a) (w := d / f) huv)
  rw [bottleneckTime_sub]
  nlinarith [mul_nonneg (sub_nonneg.2 hf1) h0]

/-- For an expansion (`f ≥ 1`) the time change is expanding: `v - u ≤ G(v) - G(u)`. -/
theorem le_bottleneckTime_sub (hf1 : 1 ≤ f) (huv : u ≤ v) :
    v - u ≤ bottleneckTime a d f v - bottleneckTime a d f u := by
  have h0 := sub_nonneg.2 (bottleneckOverlap_mono (a := a) (w := d / f) huv)
  rw [bottleneckTime_sub]
  nlinarith [mul_nonneg (sub_nonneg.2 hf1) h0]

/-- In every case `G(v) - G(u) ≤ max 1 f · (v - u)`. -/
theorem bottleneckTime_sub_le_max (hd : 0 ≤ d) (hf : 0 < f) (huv : u ≤ v) :
    bottleneckTime a d f v - bottleneckTime a d f u ≤ max 1 f * (v - u) := by
  have hw : 0 ≤ d / f := div_nonneg hd hf.le
  have h1 := bottleneckOverlap_sub_le (a := a) hw huv
  have hvu : 0 ≤ v - u := sub_nonneg.2 huv
  rcases le_total f 1 with hf1 | hf1
  · exact (bottleneckTime_sub_le hf1 huv).trans
      (le_mul_of_one_le_left hvu (le_max_left _ _))
  · have h2 : f * (v - u) ≤ max 1 f * (v - u) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hvu
    rw [bottleneckTime_sub]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hf1)]

/-- `t < G(y) ↔ R(t) < y`. -/
theorem lt_bottleneckTime_iff (hd : 0 ≤ d) (hf : 0 < f) (t y : ℝ) :
    t < bottleneckTime a d f y ↔ bottleneckRate a d f t < y := by
  have hmono : StrictMono (bottleneckTime a d f) := fun _ _ h =>
    bottleneckTime_lt_bottleneckTime hd hf h
  have := hmono.lt_iff_lt (a := bottleneckRate a d f t) (b := y)
  rwa [bottleneckTime_bottleneckRate hd hf] at this

theorem continuous_bottleneckOverlap (a w : ℝ) : Continuous (bottleneckOverlap a w) :=
  ((continuous_id.sub continuous_const).max continuous_const).min continuous_const

theorem measurable_bottleneckTime (a d f : ℝ) : Measurable (bottleneckTime a d f) :=
  (continuous_id.sub (continuous_const.mul (continuous_bottleneckOverlap a (d / f)))).measurable

/-- The intensity is nonnegative on `[0, ∞)`. -/
theorem bottleneckRate_nonneg (ha : 0 ≤ a) (hd : 0 ≤ d) (hf : 0 < f) (hs : 0 ≤ s) :
    0 ≤ bottleneckRate a d f s := by
  have h0 := bottleneckOverlap_nonneg (a := a) hd s
  have h1 := bottleneckOverlap_le (w := d) ha hs
  have h2 : 0 ≤ f⁻¹ * bottleneckOverlap a d s := mul_nonneg (inv_nonneg.2 hf.le) h0
  have hR : bottleneckRate a d f s =
      (s - bottleneckOverlap a d s) + f⁻¹ * bottleneckOverlap a d s := by
    rw [bottleneckRate]; ring
  linarith

/-- **The intensity of the bottleneck history**: for `a, d, s ≥ 0`,
`R(s) = ∫_0^s 1/η = s + (1/f - 1) · |[0, s] ∩ [a, a + d]|`. -/
theorem cumRate_bottleneckSize (ha : 0 ≤ a) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    cumRate (bottleneckSize a d f) s = bottleneckRate a d f s := by
  have hfun : (fun r => (bottleneckSize a d f r)⁻¹) =
      fun r => 1 + (f⁻¹ - 1) * (Set.Ico a (a + d)).indicator 1 r := by
    funext r
    simp only [bottleneckSize, Set.indicator, Set.mem_Ico, Pi.one_apply]
    split_ifs <;> simp
  have hi : IntervalIntegrable ((Set.Ico a (a + d)).indicator (1 : ℝ → ℝ)) volume 0 s :=
    ⟨(intervalIntegrable_const (c := (1 : ℝ))).1.indicator measurableSet_Ico,
      (intervalIntegrable_const (c := (1 : ℝ))).2.indicator measurableSet_Ico⟩
  have hvol : volume (Set.Ioc 0 s ∩ Set.Ico a (a + d)) = volume (Set.Icc a (min s (a + d))) := by
    rw [measure_congr (Ioc_ae_eq_Icc.inter Ico_ae_eq_Icc), Set.Icc_inter_Icc, max_eq_right ha]
  rw [cumRate, hfun, intervalIntegral.integral_add intervalIntegrable_const
    (hi.const_mul (f⁻¹ - 1)), intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    intervalIntegral.integral_of_le hs, setIntegral_indicator measurableSet_Ico]
  simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one, sub_zero]
  rw [measureReal_def, hvol, Real.volume_Icc, ENNReal.toReal_ofReal', bottleneckRate]
  congr 2
  unfold bottleneckOverlap
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-! ### The time-changed genealogy -/

/-- The **holding times under a bottleneck**: the epoch with `k` lineages, which lasts from
`V_{k+1}` to `V_k` in standard time, lasts `G(V_k) - G(V_{k+1})` in real time. -/
def bottleneckHolding (a d f : ℝ) (n : ℕ) (T : ℕ → ℝ) (k : ℕ) : ℝ :=
  bottleneckTime a d f (epochEnd n T k) - bottleneckTime a d f (epochEnd n T (k + 1))

variable {n k : ℕ} {T : ℕ → ℝ}

/-- For a constant population the time change is the identity. -/
theorem bottleneckHolding_eq_self (h : f = 1 ∨ d = 0) (hk : k ≤ n) (T : ℕ → ℝ) :
    bottleneckHolding a d f n T k = T k := by
  rw [bottleneckHolding, bottleneckTime_eq_self h, bottleneckTime_eq_self h, epochEnd_eq_add hk]
  ring

/-- The real time to the most recent common ancestor is `G` of the standard one. -/
theorem sum_bottleneckHolding (ha : 0 ≤ a) (hd : 0 ≤ d) (hf : 0 < f) (n : ℕ) (T : ℕ → ℝ) :
    ∑ k ∈ Icc 2 n, bottleneckHolding a d f n T k = bottleneckTime a d f (∑ k ∈ Icc 2 n, T k) := by
  rcases lt_or_ge n 2 with hn | hn
  · simp [Icc_eq_empty_of_lt hn, bottleneckTime_zero ha hd hf]
  have h := sum_Icc_sub (M := ℝ) hn (fun k => bottleneckTime a d f (epochEnd n T k))
  rw [epochEnd_of_lt (by omega), bottleneckTime_zero ha hd hf, zero_sub] at h
  have e : ∀ k, bottleneckHolding a d f n T k =
      -(bottleneckTime a d f (epochEnd n T (k + 1)) - bottleneckTime a d f (epochEnd n T k)) :=
    fun k => by rw [bottleneckHolding, neg_sub]
  rw [sum_congr rfl fun k _ => e k, sum_neg_distrib, h, neg_neg, epochEnd]

/-- The epoch with `k` lineages as an increment of `G` over `[V_{k+1}, T_k + V_{k+1}]`. -/
theorem bottleneckHolding_eq (hk : k ≤ n) (T : ℕ → ℝ) :
    bottleneckHolding a d f n T k = bottleneckTime a d f (T k + epochEnd n T (k + 1)) -
      bottleneckTime a d f (epochEnd n T (k + 1)) := by
  rw [bottleneckHolding, epochEnd_eq_add hk]

/-- Bounds on one epoch: `0 ≤ T^b_k ≤ max 1 f · T_k`, `T^b_k ≤ T_k` for `f ≤ 1` and
`T_k ≤ T^b_k` for `f ≥ 1`. -/
theorem bottleneckHolding_bounds (hd : 0 ≤ d) (hf : 0 < f) (hT : ∀ j ∈ Icc 2 n, 0 ≤ T j)
    (hk : k ∈ Icc 2 n) :
    0 ≤ bottleneckHolding a d f n T k ∧ bottleneckHolding a d f n T k ≤ max 1 f * T k ∧
      (f ≤ 1 → bottleneckHolding a d f n T k ≤ T k) ∧
      (1 ≤ f → T k ≤ bottleneckHolding a d f n T k) := by
  have hk' := mem_Icc.1 hk
  have huv : epochEnd n T (k + 1) ≤ T k + epochEnd n T (k + 1) :=
    le_add_of_nonneg_left (hT k hk)
  rw [bottleneckHolding_eq hk'.2]
  refine ⟨bottleneckTime_sub_nonneg hd hf huv, ?_, fun hf1 => ?_, fun hf1 => ?_⟩
  · simpa only [add_sub_cancel_right] using bottleneckTime_sub_le_max hd hf huv
  · simpa only [add_sub_cancel_right] using bottleneckTime_sub_le hf1 huv
  · simpa only [add_sub_cancel_right] using le_bottleneckTime_sub hf1 huv

/-- **A bottleneck strictly shortens the oldest epoch when they overlap**: with `f < 1`,
`d > 0`, if `V_3 < a + d/f` (the epoch with two lineages starts before the bottleneck window
ends in standard time) and `T_2 > a`, then `T^b_2 < T_2`. -/
theorem bottleneckHolding_two_lt (ha : 0 ≤ a) (hd : 0 < d) (hf : 0 < f) (hf1 : f < 1)
    (hn : 2 ≤ n) (hT : ∀ j ∈ Icc 2 n, 0 ≤ T j) (h3 : epochEnd n T 3 < a + d / f)
    (h2 : a < T 2) : bottleneckHolding a d f n T 2 < T 2 := by
  have hu : 0 ≤ epochEnd n T 3 := epochEnd_nonneg hT (by norm_num)
  have hlt := bottleneckOverlap_lt (div_pos hd hf) h3
    (show a < T 2 + epochEnd n T 3 by linarith) (show epochEnd n T 3 < T 2 + epochEnd n T 3 by
      linarith)
  rw [bottleneckHolding_eq hn, show (2 : ℕ) + 1 = 3 from rfl, bottleneckTime_sub]
  have := mul_pos (sub_pos.2 hf1) (sub_pos.2 hlt)
  linarith

/-- The bottleneck holding times are a measurable function of the standard holding times. -/
theorem measurable_bottleneckHolding (a d f : ℝ) (n : ℕ) :
    Measurable fun (T : ℕ → ℝ) (k : ℕ) => bottleneckHolding a d f n T k := by
  refine measurable_pi_iff.2 fun k => ?_
  simp only [bottleneckHolding, epochEnd]
  exact ((measurable_bottleneckTime a d f).comp (Finset.measurable_sum _ fun j _ =>
    measurable_pi_apply j)).sub ((measurable_bottleneckTime a d f).comp
      (Finset.measurable_sum _ fun j _ => measurable_pi_apply j))

end TimeChange

/-! ### Kingman's coalescent under a bottleneck -/

section Kingman

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

variable {n : ℕ} (K : KingmanTimes μ n) (a d f : ℝ)

/-- The holding times of a Kingman genealogy after the Griffiths–Tavaré time change for a
bottleneck: `T^b_k = G(V_k) - G(V_{k+1})`. -/
def bottleneckTimes (k : ℕ) (ω : Ω) : ℝ := bottleneckHolding a d f n (fun j => K.T j ω) k

variable {K a d f}

/-- The vector of time-changed holding times is measurable. -/
theorem measurable_bottleneckTimes (hT : ∀ k, Measurable (K.T k)) :
    Measurable fun ω k => bottleneckTimes K a d f k ω :=
  (measurable_bottleneckHolding a d f n).comp (measurable_pi_iff.2 hT)

/-- Each time-changed holding time is measurable. -/
theorem measurable_bottleneckTimes_apply (hT : ∀ k, Measurable (K.T k)) (k : ℕ) :
    Measurable (bottleneckTimes K a d f k) :=
  (measurable_pi_apply k).comp (measurable_bottleneckTimes hT)

/-- The time-changed genealogy is coarser than the Kingman one. -/
theorem comap_bottleneckTimes_le :
    MeasurableSpace.comap (fun ω k => bottleneckTimes K a d f k ω) MeasurableSpace.pi ≤
      MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi := by
  rw [show (fun ω k => bottleneckTimes K a d f k ω) =
      (fun (T : ℕ → ℝ) (k : ℕ) => bottleneckHolding a d f n T k) ∘ (fun ω k => K.T k ω) from rfl,
    ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_bottleneckHolding a d f n).comap_le

/-- A.s. bounds on every epoch, from `bottleneckHolding_bounds`. -/
theorem ae_bottleneckTimes_bounds (hd : 0 ≤ d) (hf : 0 < f) : ∀ᵐ ω ∂μ, ∀ k ∈ Icc 2 n,
    0 ≤ bottleneckTimes K a d f k ω ∧ bottleneckTimes K a d f k ω ≤ max 1 f * K.T k ω ∧
      (f ≤ 1 → bottleneckTimes K a d f k ω ≤ K.T k ω) ∧
      (1 ≤ f → K.T k ω ≤ bottleneckTimes K a d f k ω) := by
  filter_upwards [ae_T_pos K] with ω hω k hk
  exact bottleneckHolding_bounds hd hf (fun j hj => (hω j hj).le) hk

/-- Each time-changed holding time is integrable (it is dominated by `max 1 f · T_k`). -/
theorem integrable_bottleneckTimes (hd : 0 ≤ d) (hf : 0 < f) (hT : ∀ k, Measurable (K.T k))
    {k : ℕ} (hk : k ∈ Icc 2 n) : Integrable (bottleneckTimes K a d f k) μ := by
  refine ((K.integrable_T hk).const_mul (max 1 f)).mono'
    (measurable_bottleneckTimes_apply hT k).aestronglyMeasurable ?_
  filter_upwards [ae_bottleneckTimes_bounds (K := K) hd hf] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (hω k hk).1]
  exact (hω k hk).2.1

/-- A bottleneck shortens every epoch on average: `E T^b_k ≤ 1 / C(k,2)` for `f ≤ 1`. -/
theorem integral_bottleneckTimes_le (hd : 0 ≤ d) (hf : 0 < f) (hf1 : f ≤ 1)
    (hT : ∀ k, Measurable (K.T k)) {k : ℕ} (hk : k ∈ Icc 2 n) :
    μ[bottleneckTimes K a d f k] ≤ ((k.choose 2 : ℕ) : ℝ)⁻¹ := by
  rw [← K.integral_T hk]
  refine integral_mono_ae (integrable_bottleneckTimes hd hf hT hk) (K.integrable_T hk) ?_
  filter_upwards [ae_bottleneckTimes_bounds (K := K) hd hf] with ω hω using (hω k hk).2.2.1 hf1

/-- An expansion lengthens every epoch on average: `1 / C(k,2) ≤ E T^b_k` for `f ≥ 1`. -/
theorem integral_bottleneckTimes_ge (hd : 0 ≤ d) (hf1 : 1 ≤ f)
    (hT : ∀ k, Measurable (K.T k)) {k : ℕ} (hk : k ∈ Icc 2 n) :
    ((k.choose 2 : ℕ) : ℝ)⁻¹ ≤ μ[bottleneckTimes K a d f k] := by
  have hf : 0 < f := zero_lt_one.trans_le hf1
  rw [← K.integral_T hk]
  refine integral_mono_ae (K.integrable_T hk) (integrable_bottleneckTimes hd hf hT hk) ?_
  filter_upwards [ae_bottleneckTimes_bounds (K := K) hd hf] with ω hω using (hω k hk).2.2.2 hf1

/-- For a constant population the time-changed genealogy is Kingman's. -/
theorem integral_bottleneckTimes_eq (h : f = 1 ∨ d = 0) {k : ℕ} (hk : k ∈ Icc 2 n) :
    μ[bottleneckTimes K a d f k] = ((k.choose 2 : ℕ) : ℝ)⁻¹ := by
  simp only [bottleneckTimes, bottleneckHolding_eq_self h (mem_Icc.1 hk).2]
  exact K.integral_T hk

/-- With positive probability `V_3 < c` and `T_2 > a`, for `0 ≤ a < c`: the epoch with two
lineages can start before `c` and outlast `a`. Proof by independence of the holding times:
the event contains `{T_2 > a} ∩ ⋂_{j ≥ 3} {T_j ≤ c / n}`. -/
theorem measure_epochEnd_three_lt_pos (K : KingmanTimes μ n) {a c : ℝ} (ha : 0 ≤ a)
    (hc : a < c) (hn : 2 ≤ n) :
    0 < μ {ω | epochEnd n (fun j => K.T j ω) 3 < c ∧ a < K.T 2 ω} := by
  have hc0 : 0 < c := ha.trans_lt hc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  set ε : ℝ := c / n with hε
  have hε0 : 0 < ε := div_pos hc0 hn0
  let S : Icc 2 n → Set ℝ := fun k => if (k : ℕ) = 2 then Set.Ioi a else Set.Iic ε
  have hS : ∀ k ∈ (Finset.univ : Finset (Icc 2 n)), MeasurableSet (S k) := fun k _ => by
    simp only [S]
    split_ifs
    · exact measurableSet_Ioi
    · exact measurableSet_Iic
  have hprod := K.indep.measure_inter_preimage_eq_mul Finset.univ hS
  have hfac : ∀ k : Icc 2 n, μ (K.T k ⁻¹' S k) ≠ 0 := by
    intro k h0
    have hr := KingmanTimes.choose_two_pos k.2
    have := isProbabilityMeasure_expMeasure hr
    have hreal : μ.real (K.T k ⁻¹' S k) = 0 := by
      rw [measureReal_def, h0, ENNReal.toReal_zero]
    simp only [S] at hreal
    split_ifs at hreal with hk2
    · change μ.real {ω | a < K.T k ω} = 0 at hreal
      rw [(K.hasLaw k k.2).measureReal_eq (p := fun y => a < y) measurableSet_Ioi,
        show {y : ℝ | a < y} = (Set.Iic a)ᶜ by ext; simp,
        probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, cdf_expMeasure_eq hr] at hreal
      simp only [ha, ↓reduceIte, sub_sub_cancel] at hreal
      exact (Real.exp_pos _).ne' hreal
    · change μ.real {ω | K.T k ω ≤ ε} = 0 at hreal
      rw [(K.hasLaw k k.2).measureReal_eq (p := fun y => y ≤ ε) measurableSet_Iic,
        show {y : ℝ | y ≤ ε} = Set.Iic ε from rfl, ← cdf_eq_real, cdf_expMeasure_eq hr] at hreal
      simp only [hε0.le, ↓reduceIte, sub_eq_zero] at hreal
      have := (Real.exp_eq_one_iff _).1 hreal.symm
      linarith [mul_pos hr hε0]
  have hpos : 0 < μ (⋂ k ∈ (Finset.univ : Finset (Icc 2 n)), K.T k ⁻¹' S k) := by
    rw [hprod]
    exact pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => hfac k)
  refine hpos.trans_le (measure_mono fun ω hω => ?_)
  have hω' : ∀ k : Icc 2 n, K.T k ω ∈ S k := fun k =>
    Set.mem_iInter₂.1 hω k (Finset.mem_univ k)
  change _ ∧ _
  refine ⟨?_, ?_⟩
  · have hle : ∀ j ∈ Icc 3 n, K.T j ω ≤ ε := fun j hj => by
      have hj' := mem_Icc.1 hj
      have := hω' ⟨j, mem_Icc.2 ⟨by omega, hj'.2⟩⟩
      simpa [S, show j ≠ 2 by omega] using this
    calc epochEnd n (fun j => K.T j ω) 3 ≤ ∑ _j ∈ Icc 3 n, ε := sum_le_sum hle
      _ = ((n + 1 - 3 : ℕ) : ℝ) * ε := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
      _ < (n : ℝ) * ε := mul_lt_mul_of_pos_right (Nat.cast_lt.2 (by omega)) hε0
      _ = c := by rw [hε]; field_simp
  · have := hω' ⟨2, mem_Icc.2 ⟨le_rfl, hn⟩⟩
    simpa [S] using this

/-- **A genuine bottleneck strictly shortens the oldest epoch on average**: for `a ≥ 0`,
`d > 0` and `0 < f < 1`, `E T^b_2 < 1 = 1 / C(2,2)`. -/
theorem integral_bottleneckTimes_two_lt [IsProbabilityMeasure μ] (ha : 0 ≤ a) (hd : 0 < d)
    (hf : 0 < f) (hf1 : f < 1) (hT : ∀ k, Measurable (K.T k)) (hn : 2 ≤ n) :
    μ[bottleneckTimes K a d f 2] < (((2 : ℕ).choose 2 : ℕ) : ℝ)⁻¹ := by
  have hk : 2 ∈ Icc 2 n := mem_Icc.2 ⟨le_rfl, hn⟩
  have hint := integrable_bottleneckTimes (K := K) (a := a) hd.le hf hT hk
  rw [← K.integral_T hk, ← sub_pos, ← integral_sub (K.integrable_T hk) hint]
  have hnn : 0 ≤ᵐ[μ] fun ω => K.T 2 ω - bottleneckTimes K a d f 2 ω := by
    filter_upwards [ae_bottleneckTimes_bounds (K := K) (a := a) hd.le hf] with ω hω
    exact sub_nonneg.2 ((hω 2 hk).2.2.1 hf1.le)
  refine (integral_pos_iff_support_of_nonneg_ae hnn ((K.integrable_T hk).sub hint)).2 ?_
  refine (measure_epochEnd_three_lt_pos K ha
    (show a < a + d / f by linarith [div_pos hd hf]) hn).trans_le (measure_mono_ae ?_)
  filter_upwards [ae_T_pos K] with ω hω hE
  have hE' : epochEnd n (fun j => K.T j ω) 3 < a + d / f ∧ a < K.T 2 ω := hE
  exact Function.mem_support.2 (sub_pos.2 (bottleneckHolding_two_lt ha hd hf hf1 hn
    (fun j hj => (hω j hj).le) hE'.1 hE'.2)).ne'

end Kingman

/-! ### The expected spectrum under a bottleneck -/

section Spectrum

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
  {K : KingmanTimes μ n} {a d f : ℝ} {τ : Ω → List (List ℕ)} {θ : ℝ} {ξ : ℕ → Ω → ℝ}

/-- **Expected site frequency spectrum under a bottleneck.** Let the genealogy of a sample of
`n` gene copies from a population with the bottleneck history `bottleneckSize a d f`
(`d ≥ 0`, `f > 0`) be Kingman's coalescent (holding times `K.T`, independent random-joining
block-size history `τ`) run through the Griffiths–Tavaré time change, so that the epoch with
`k` lineages lasts `T^b_k = G(V_k) - G(V_{k+1})` (`bottleneckTimes`). If, given this
genealogy, the count `ξ i` is integrable with conditional mean `(θ / 2) L^b_i` (neutral
infinite-sites mutation at rate `θ / 2` per lineage per unit of real time), then for
`1 ≤ i ≤ n - 1`, `E ξ_i = (θ / 2) ∑_{k=2}^{n} k C(n-i-1, k-2) / C(n-1, k-1) · E T^b_k`. -/
theorem integral_sfs_bottleneck (hd : 0 ≤ d) (hf : 0 < f) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => bottleneckTimes K a d f k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => bottleneckTimes K a d f k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    μ[ξ i] = variableSFS θ n (fun k => μ[bottleneckTimes K a d f k]) i :=
  integral_sfs_of_indep (measurable_bottleneckTimes_apply hT)
    (fun _ hk => integrable_bottleneckTimes hd hf hT hk) hτ hτ_law
    (indep_of_indep_of_le_right h_indep comap_bottleneckTimes_le) hξ_int hξ hi hin

/-- **A bottleneck lowers the expected spectrum**: under the hypotheses of
`integral_sfs_bottleneck` with `θ ≥ 0` and `f ≤ 1`, `E ξ_i ≤ θ / i`. -/
theorem integral_sfs_bottleneck_le (hθ : 0 ≤ θ) (hd : 0 ≤ d) (hf : 0 < f) (hf1 : f ≤ 1)
    (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => bottleneckTimes K a d f k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => bottleneckTimes K a d f k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    μ[ξ i] ≤ θ / i := by
  rw [integral_sfs_bottleneck hd hf hT hτ hτ_law h_indep hξ_int hξ hi hin,
    ← variableSFS_inv_choose_two θ hi hin]
  exact variableSFS_le_variableSFS hθ (fun k hk => integral_bottleneckTimes_le hd hf hf1 hT hk) i

/-- **A genuine bottleneck strictly lowers every entry of the expected spectrum**: under the
hypotheses of `integral_sfs_bottleneck` with `θ > 0`, `a ≥ 0`, `d > 0` and `0 < f < 1`,
`E ξ_i < θ / i` for every `1 ≤ i ≤ n - 1`. -/
theorem integral_sfs_bottleneck_lt (hθ : 0 < θ) (ha : 0 ≤ a) (hd : 0 < d) (hf : 0 < f)
    (hf1 : f < 1) (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => bottleneckTimes K a d f k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => bottleneckTimes K a d f k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    μ[ξ i] < θ / i := by
  have hn : 2 ≤ n := by omega
  rw [integral_sfs_bottleneck hd.le hf hT hτ hτ_law h_indep hξ_int hξ hi hin,
    ← variableSFS_inv_choose_two θ hi hin]
  exact variableSFS_lt_variableSFS hθ
    (fun k hk => integral_bottleneckTimes_le hd.le hf hf1.le hT hk)
    (integral_bottleneckTimes_two_lt ha hd hf hf1 hT hn) hi hin

/-- **An expansion raises the expected spectrum**: under the hypotheses of
`integral_sfs_bottleneck` with `θ ≥ 0` and `f ≥ 1`, `θ / i ≤ E ξ_i`. -/
theorem integral_sfs_bottleneck_ge (hθ : 0 ≤ θ) (hd : 0 ≤ d) (hf1 : 1 ≤ f)
    (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => bottleneckTimes K a d f k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => bottleneckTimes K a d f k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    θ / i ≤ μ[ξ i] := by
  rw [integral_sfs_bottleneck hd (zero_lt_one.trans_le hf1) hT hτ hτ_law h_indep hξ_int hξ hi
    hin, ← variableSFS_inv_choose_two θ hi hin]
  exact variableSFS_le_variableSFS hθ (fun k hk => integral_bottleneckTimes_ge hd hf1 hT hk) i

/-- **A constant population recovers Fu's spectrum**: with `f = 1` or `d = 0`,
`E ξ_i = θ / i`. -/
theorem integral_sfs_bottleneck_eq (h : f = 1 ∨ d = 0) (hd : 0 ≤ d) (hf : 0 < f)
    (hT : ∀ k, Measurable (K.T k))
    (hτ : MeasurableSpace.comap τ ⊤ ≤ mΩ)
    (hτ_law : ∀ ps, μ.real (τ ⁻¹' {ps}) = randomJoining (n - 1) (List.replicate n 1) ps)
    (h_indep : Indep (MeasurableSpace.comap τ ⊤)
      (MeasurableSpace.comap (fun ω k => K.T k ω) MeasurableSpace.pi) μ)
    (hξ_int : ∀ i, Integrable (ξ i) μ)
    (hξ : ∀ i, μ[ξ i | MeasurableSpace.comap τ ⊤ ⊔
        MeasurableSpace.comap (fun ω k => bottleneckTimes K a d f k ω) MeasurableSpace.pi] =ᵐ[μ]
      fun ω => θ / 2 * sfsLength n i (τ ω) (fun k => bottleneckTimes K a d f k ω))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    μ[ξ i] = θ / i := by
  rw [integral_sfs_bottleneck hd hf hT hτ hτ_law h_indep hξ_int hξ hi hin,
    ← variableSFS_inv_choose_two θ hi hin]
  unfold variableSFS
  congr 1
  exact sum_congr rfl fun k hk => by simp only [integral_bottleneckTimes_eq h hk]

end Spectrum

/-! ### The most recent epoch and the first-coalescence time -/

section FirstCoalescence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ} {K : KingmanTimes μ n}
  {a d f : ℝ}

/-- The most recent epoch (`n` lineages) lasts `G(T_n)` in real time. -/
theorem bottleneckTimes_top (ha : 0 ≤ a) (hd : 0 ≤ d) (hf : 0 < f) (ω : Ω) :
    bottleneckTimes K a d f n ω = bottleneckTime a d f (K.T n ω) := by
  simp [bottleneckTimes, bottleneckHolding, epochEnd, bottleneckTime_zero ha hd hf]

/-- **The first coalescence under a bottleneck** (Griffiths & Tavaré): the expected real
duration of the most recent epoch (`n` lineages) is Bhaskar–Song's first-coalescence time
`c_n = ∫_0^∞ exp(-C(n,2) R(s)) ds` for the bottleneck history. Proof by the tail formula
`E X = ∫_0^∞ P(X > t) dt` and `P(G(T_n) > t) = P(T_n > R(t)) = exp(-C(n,2) R(t))`. -/
theorem integral_bottleneckTimes_top (ha : 0 ≤ a) (hd : 0 ≤ d) (hf : 0 < f)
    (hT : ∀ k, Measurable (K.T k)) (hn : 2 ≤ n) :
    μ[bottleneckTimes K a d f n] = firstCoalMean (bottleneckSize a d f) n := by
  have hk : n ∈ Icc 2 n := mem_Icc.2 ⟨hn, le_rfl⟩
  have hc := KingmanTimes.choose_two_pos hk
  have := isProbabilityMeasure_expMeasure hc
  have hnn : 0 ≤ᵐ[μ] bottleneckTimes K a d f n := by
    filter_upwards [ae_bottleneckTimes_bounds (K := K) (a := a) hd hf] with ω hω using (hω n hk).1
  rw [Integrable.integral_eq_integral_meas_lt (integrable_bottleneckTimes hd hf hT hk) hnn,
    firstCoalMean]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := le_of_lt ht
  have hset : {ω | t < bottleneckTimes K a d f n ω} = {ω | bottleneckRate a d f t < K.T n ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, bottleneckTimes_top ha hd hf]
    exact lt_bottleneckTime_iff hd hf t _
  rw [hset, cumRate_bottleneckSize ha hd ht0,
    (K.hasLaw n hk).measureReal_eq (p := fun y => bottleneckRate a d f t < y)
      measurableSet_Ioi, show {y : ℝ | bottleneckRate a d f t < y} =
      (Set.Iic (bottleneckRate a d f t))ᶜ by ext; simp,
    probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, cdf_expMeasure_eq hc]
  simp only [bottleneckRate_nonneg ha hd hf ht0, ↓reduceIte, neg_mul]
  ring

end FirstCoalescence

end MathlibExt.Biology.PopulationGenetics.Coalescent.SFSBottleneck
