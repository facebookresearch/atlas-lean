/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Asymptotics of the digamma function

We extend the series expansion of the digamma function `ψ = Γ'/Γ` to every point that is not a
pole of `Γ`, and prove `ψ(z) = log z + O(1 / ‖z‖)` uniformly in every sector
`|arg z| ≤ π - δ`.

## Main statements

* `Complex.summable_one_div_natCast_add_sub_one_div_natCast_add`: the series
  `∑ₙ (1 / (n + a) - 1 / (n + b))` converges for all `a b : ℂ`.
* `Complex.digamma_eq_tsum_sub_eulerMascheroniConstant`:
  `ψ(z) = ∑ₙ (1 / (n + 1) - 1 / (n + z)) - γ` for `z ∉ {0, -1, -2, …}`.
* `Complex.exists_norm_digamma_sub_log_le`: for every `δ > 0` there is `C` with
  `‖ψ(z) - log z‖ ≤ C / ‖z‖` whenever `z ≠ 0` and `-π + δ ≤ arg z ≤ π - δ`.
-/

@[expose] public section

open Filter Topology

namespace Complex

/-- **The digamma series converges.** For any `a b : ℂ`, `∑ₙ (1 / (n + a) - 1 / (n + b))` is
summable. -/
theorem summable_one_div_natCast_add_sub_one_div_natCast_add (a b : ℂ) :
    Summable fun n : ℕ => 1 / ((n : ℂ) + a) - 1 / ((n : ℂ) + b) := by
  have hg : Summable (fun n : ℕ => 4 * ‖b - a‖ / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    simpa [div_eq_mul_inv] using this.mul_left (4 * ‖b - a‖)
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (‖a‖ + ‖b‖) + 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : 2 * (‖a‖ + ‖b‖) + 1 < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
  have ha := norm_sub_norm_le (n : ℂ) (-a)
  have hb := norm_sub_norm_le (n : ℂ) (-b)
  rw [norm_neg, sub_neg_eq_add, norm_natCast] at ha hb
  have hna : ((n : ℝ) + 1) / 2 ≤ ‖(n : ℂ) + a‖ := by linarith [norm_nonneg b]
  have hnb : ((n : ℝ) + 1) / 2 ≤ ‖(n : ℂ) + b‖ := by linarith [norm_nonneg a]
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hpa : 0 < ‖(n : ℂ) + a‖ := by linarith
  have hpb : 0 < ‖(n : ℂ) + b‖ := by linarith
  have hea : (n : ℂ) + a ≠ 0 := norm_pos_iff.1 hpa
  have heb : (n : ℂ) + b ≠ 0 := norm_pos_iff.1 hpb
  have heq : 1 / ((n : ℂ) + a) - 1 / ((n : ℂ) + b) =
      (b - a) / (((n : ℂ) + a) * ((n : ℂ) + b)) := by
    field_simp; ring
  rw [heq, norm_div, norm_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : ((n : ℝ) + 1) ^ 2 ≤ 4 * (‖(n : ℂ) + a‖ * ‖(n : ℂ) + b‖) := by nlinarith
  nlinarith [norm_nonneg (b - a)]

/-- `1 / (N + z) → 0` as `N → ∞`. -/
theorem tendsto_one_div_natCast_add_atTop (z : ℂ) :
    Tendsto (fun N : ℕ => 1 / ((N : ℂ) + z)) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => (N : ℂ) + z) atTop (Bornology.cobounded ℂ) :=
    (tendsto_add_const_cobounded z).comp tendsto_natCast_atTop_cobounded
  refine (tendsto_inv₀_cobounded.comp h).congr fun N => ?_
  simp [one_div]

/-- **The digamma series.** For `z` not a pole of `Γ`,
`ψ(z) = ∑ₙ (1 / (n + 1) - 1 / (n + z)) - γ`. -/
theorem digamma_eq_tsum_sub_eulerMascheroniConstant {z : ℂ} (hz : ∀ n : ℕ, z ≠ -(n : ℂ)) :
    digamma z = (∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))) -
      Real.eulerMascheroniConstant := by
  set a : ℂ → ℕ → ℂ := fun z n => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z) with ha_def
  have hsum : ∀ z : ℂ, Summable (a z) := fun z =>
    summable_one_div_natCast_add_sub_one_div_natCast_add 1 z
  -- shift
  have hshift : ∀ z : ℂ, ∑' n, a z n = ∑' n, a (z + 1) n - 1 / z := by
    intro z
    have ht : ∀ N : ℕ, ∑ n ∈ Finset.range N, (a z n - a (z + 1) n) =
        1 / ((N : ℂ) + z) - 1 / z := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]; simp only [ha_def]; push_cast; ring
    have hlim : Tendsto (fun N : ℕ => 1 / ((N : ℂ) + z) - 1 / z) atTop (𝓝 (0 - 1 / z)) :=
      (tendsto_one_div_natCast_add_atTop z).sub tendsto_const_nhds
    have h1 := (((hsum z).hasSum).sub ((hsum (z + 1)).hasSum)).tendsto_sum_nat
    have := tendsto_nhds_unique h1 (hlim.congr (fun N => (ht N).symm))
    linear_combination this
  -- the half-plane `1 < Re z`
  have hpos : ∀ z : ℂ, 1 < z.re → digamma z = ∑' n, a z n - Real.eulerMascheroniConstant := by
    intro z hz
    have h := (hasSum_digamma_series z hz).tsum_eq
    simp only [digammaSeriesTerm] at h
    change ∑' n, a z n = _ at h
    rw [h]; ring
  have key : ∀ m : ℕ, ∀ z : ℂ, (∀ n : ℕ, z ≠ -(n : ℂ)) → 1 - (m : ℝ) < z.re →
      digamma z = ∑' n, a z n - Real.eulerMascheroniConstant := by
    intro m
    induction m with
    | zero => intro z _ hz; exact hpos z (by simpa using hz)
    | succ m ih =>
      intro z hz hre
      have hz1 : ∀ n : ℕ, z + 1 ≠ -(n : ℂ) := by
        intro n h
        apply hz (n + 1)
        push_cast
        linear_combination h
      have h1 := ih (z + 1) hz1 (by simp; push_cast at hre; linarith)
      have h2 := digamma_apply_add_one z hz
      rw [hshift z]
      rw [h2] at h1
      rw [one_div]
      linear_combination h1
  obtain ⟨m, hm⟩ := exists_nat_gt (1 - z.re)
  exact key m z hz (by linarith)

/-- **`ψ(z) = log z + O(1 / ‖z‖)` in sectors.** For every `δ > 0` there is a constant `C` such
that `‖ψ(z) - log z‖ ≤ C / ‖z‖` uniformly for `z ≠ 0` with `-π + δ ≤ arg z ≤ π - δ`. -/
theorem exists_norm_digamma_sub_log_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → -Real.pi + δ ≤ arg z → arg z ≤ Real.pi - δ →
      ‖digamma z - log z‖ ≤ C / ‖z‖ := by
  by_cases hδπ : δ ≤ Real.pi
  swap
  · refine ⟨0, fun z _ h1 h2 => ?_⟩
    exfalso; linarith
  set m : ℝ := (1 - Real.cos δ) / 2 with hm
  have hcosδ : Real.cos δ < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hδπ hδ
    simpa using h
  have hm0 : 0 < m := by rw [hm]; linarith
  set K : ℝ := 1 / (2 * m) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K + 1 / 2, fun z hz0 h1 h2 => ?_⟩
  set a : ℝ := ‖z‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 hz0
  have hre : -(a * Real.cos δ) ≤ z.re := by
    have hc : Real.cos (Real.pi - δ) ≤ Real.cos (arg z) := by
      rw [← Real.cos_abs (arg z)]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
      rw [abs_le]; constructor <;> linarith
    rw [Real.cos_pi_sub, cos_arg hz0] at hc
    rw [← ha] at hc
    have := (le_div_iff₀ ha0).1 hc
    linarith
  have hsec : ∀ u : ℝ, 0 ≤ u → m * (u + a) ^ 2 ≤ ‖(u : ℂ) + z‖ ^ 2 := by
    intro u hu
    have hn : ‖(u : ℂ) + z‖ ^ 2 = (u + z.re) ^ 2 + z.im ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; simp; ring
    have ha2 : a ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [ha, ← normSq_eq_norm_sq, normSq_apply]; ring
    rw [hn, hm]
    have hc1 : -1 ≤ Real.cos δ := Real.neg_one_le_cos δ
    nlinarith [mul_le_mul_of_nonneg_left hre (by linarith : (0 : ℝ) ≤ 2 * u),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + Real.cos δ) (sq_nonneg (u - a))]
  have hslit : z ∈ slitPlane := by
    rw [mem_slitPlane_iff_arg]
    refine ⟨?_, hz0⟩
    intro h; rw [h] at h2; linarith
  have hslit' : ∀ u : ℝ, 0 ≤ u → (u : ℂ) + z ∈ slitPlane := by
    intro u hu
    have hz := hslit
    rw [mem_slitPlane_iff] at hz ⊢
    rcases hz with h | h
    · left; simp; linarith
    · right; simpa using h
  have hne : ∀ u : ℝ, 0 ≤ u → (u : ℂ) + z ≠ 0 :=
    fun u hu => slitPlane_ne_zero (hslit' u hu)
  -- one Euler–Maclaurin step
  have hstep : ∀ n : ℕ, ‖1 / ((n : ℂ) + z) -
      (log ((n : ℂ) + 1 + z) - log ((n : ℂ) + z)) -
      (1 / ((n : ℂ) + z) - 1 / ((n : ℂ) + 1 + z)) / 2‖
      ≤ K * (1 / ((n : ℝ) + a) - 1 / ((n : ℝ) + 1 + a)) := by
    intro n
    set h : ℝ → ℂ := fun u => ((n : ℂ) + 1 / 2 - u) / ((u : ℂ) + z) ^ 2 with hh
    have hnn : ∀ u ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1), 0 ≤ u := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith)] at hu
      linarith [hu.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hhc : ContinuousOn h (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu; exact pow_ne_zero 2 (hne u (hnn u hu))
    have heq : ∫ u in (n : ℝ)..((n : ℝ) + 1), h u = 1 / ((n : ℂ) + z) -
        (log ((n : ℂ) + 1 + z) - log ((n : ℂ) + z)) -
        (1 / ((n : ℂ) + z) - 1 / ((n : ℂ) + 1 + z)) / 2 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ =>
        -log ((u : ℂ) + z) - ((n : ℂ) + 1 / 2 - u) / ((u : ℂ) + z))]
      · push_cast; ring
      · intro u hu
        have hs := hslit' u (hnn u hu)
        have h0 := hne u (hnn u hu)
        have h1 : HasDerivAt (fun w : ℂ => w + z) 1 (u : ℂ) := (hasDerivAt_id _).add_const z
        have hl := h1.clog hs
        have hq := ((hasDerivAt_id (u : ℂ)).const_sub ((n : ℂ) + 1 / 2)).div h1 h0
        have h2 := (hl.neg.sub hq).congr_of_eventuallyEq
          (f₁ := fun w : ℂ => -log (w + z) - ((n : ℂ) + 1 / 2 - w) / (w + z))
          (Eventually.of_forall fun w => by simp)
        convert h2.comp_ofReal using 1
        simp only [hh, id]
        field_simp
        ring
      · exact hhc.intervalIntegrable
    rw [← heq]
    have hbd : ∀ u ∈ Set.uIoc (n : ℝ) ((n : ℝ) + 1), ‖h u‖ ≤ K / (u + a) ^ 2 := by
      intro u hu
      rw [Set.uIoc_of_le (by linarith)] at hu
      have hu0 : 0 ≤ u := by linarith [hu.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hqr : (n : ℂ) + 1 / 2 - u = (((n : ℝ) + 1 / 2 - u : ℝ) : ℂ) := by push_cast; ring
      have hq8 : |(n : ℝ) + 1 / 2 - u| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
      have hpos : 0 < (u + a) ^ 2 := by positivity
      have hs := hsec u hu0
      simp only [hh]
      rw [norm_div, norm_pow, hqr, norm_real, Real.norm_eq_abs]
      have hn2 : 0 < ‖(u : ℂ) + z‖ ^ 2 := by
        have := hne u hu0; positivity
      rw [div_le_div_iff₀ hn2 hpos, hK]
      calc |(n : ℝ) + 1 / 2 - u| * (u + a) ^ 2 ≤ 1 / 2 * (u + a) ^ 2 := by gcongr
        _ = 1 / (2 * m) * (m * (u + a) ^ 2) := by field_simp
        _ ≤ 1 / (2 * m) * ‖(u : ℂ) + z‖ ^ 2 := by gcongr
    have hKc : ContinuousOn (fun u : ℝ => K / (u + a) ^ 2)
        (Set.uIcc (n : ℝ) ((n : ℝ) + 1)) := by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro u hu; have := hnn u hu; positivity
    refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith)
      (Eventually.of_forall fun u hu => hbd u (by
        rw [Set.uIoc_of_le (by linarith)]; exact hu)) hKc.intervalIntegrable).trans (le_of_eq ?_)
    have hne' : ∀ u ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1), u + a ≠ 0 := by
      intro u hu; have := hnn u hu; positivity
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => -K / (u + a))]
    · have h1 : (n : ℝ) + a ≠ 0 := by positivity
      have h2 : (n : ℝ) + 1 + a ≠ 0 := by positivity
      field_simp
      ring
    · intro u hu
      have hu' := hne' u hu
      have := ((hasDerivAt_id u).add_const a).inv hu'
      convert this.const_mul (-K) using 1
      · ext x; simp [div_eq_mul_inv]
      · simp only [id]; field_simp
    · exact hKc.intervalIntegrable
  -- summing the steps
  set R : ℕ → ℂ := fun N => ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + z) -
    (log ((N : ℂ) + z) - log z) - (1 / z - 1 / ((N : ℂ) + z)) / 2 with hR
  have hRN : ∀ N : ℕ, ‖R N‖ ≤ K * (1 / a - 1 / ((N : ℝ) + a)) := by
    intro N
    induction N with
    | zero => simp [hR]
    | succ N ih =>
      have hsplit : R (N + 1) = R N + (1 / ((N : ℂ) + z) -
          (log ((N : ℂ) + 1 + z) - log ((N : ℂ) + z)) -
          (1 / ((N : ℂ) + z) - 1 / ((N : ℂ) + 1 + z)) / 2) := by
        simp only [hR, Finset.sum_range_succ]
        push_cast
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have := hstep N
      push_cast
      linarith
  -- the series for the digamma function
  have hnotpole : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n h
    apply hne n (Nat.cast_nonneg n)
    rw [h]; push_cast; ring
  have hdig := digamma_eq_tsum_sub_eulerMascheroniConstant hnotpole
  have hsumm : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)) :=
    summable_one_div_natCast_add_sub_one_div_natCast_add 1 z
  have hdig' : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)))
      atTop (𝓝 (digamma z + Real.eulerMascheroniConstant)) := by
    have := hsumm.hasSum.tendsto_sum_nat
    rw [hdig]; simpa using this
  have hH : ∀ N : ℕ, ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) = ((harmonic N : ℝ) : ℂ) := by
    intro N; simp [harmonic, one_div]
  have hlogr : Tendsto (fun N : ℕ => log (((N : ℂ) + z) / N)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 1 + z * (1 / ((N : ℂ) + 0))) atTop (𝓝 (1 + z * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_one_div_natCast_add_atTop 0))
    have h2 : Tendsto (fun N : ℕ => log (1 + z * (1 / ((N : ℂ) + 0)))) atTop (𝓝 (log 1)) :=
      ((continuousAt_clog (by simp)).tendsto).comp (by simpa using h1)
    rw [log_one] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    congr 1
    rw [add_zero]
    field_simp
  have hharm : Tendsto (fun N : ℕ => ((((harmonic N : ℝ) - Real.log N : ℝ)) : ℂ))
      atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) :=
    (continuous_ofReal.tendsto _).comp Real.tendsto_harmonic_sub_log
  have hrec := tendsto_one_div_natCast_add_atTop z
  set W : ℕ → ℂ := fun N =>
    ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))
      - ((((harmonic N : ℝ) - Real.log N : ℝ) : ℂ) - log (((N : ℂ) + z) / N))
      - 1 / ((N : ℂ) + z) / 2 with hW
  have hWlim : Tendsto W atTop (𝓝 (digamma z)) := by
    have := (hdig'.sub (hharm.sub hlogr)).sub (hrec.div_const 2)
    rw [show digamma z = digamma z + Real.eulerMascheroniConstant -
      ((Real.eulerMascheroniConstant : ℂ) - 0) - 0 / 2 by ring]
    exact this
  have hWR : ∀ N : ℕ, 1 ≤ N → W N - (log z - 1 / (2 * z)) = -R N := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hz1 := hne N (Nat.cast_nonneg N)
    push_cast at hz1
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
    have hlog : log ((N : ℂ) + z) = Real.log N + log (((N : ℂ) + z) / N) := by
      have h := log_mul_ofReal (N : ℝ) hNpos (((N : ℂ) + z) / N) (div_ne_zero hz1 hN0)
      rw [← h]
      congr 1
      push_cast
      field_simp
    simp only [hW, hR, Finset.sum_sub_distrib, hH, hlog]
    push_cast
    ring
  have hlim := (continuous_norm.tendsto _).comp (hWlim.sub_const (log z - 1 / (2 * z)))
  have hmain : ‖digamma z - (log z - 1 / (2 * z))‖ ≤ K / a := by
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN => ?_⟩)
    simp only [Function.comp, hWR N hN, norm_neg]
    refine (hRN N).trans ?_
    have : 0 < 1 / ((N : ℝ) + a) := by positivity
    have := mul_pos hK0 this
    rw [mul_sub, div_eq_mul_one_div K a]
    linarith
  have h2z : ‖1 / (2 * z)‖ = 1 / 2 / a := by
    rw [norm_div, norm_mul, ← ha]; simp; ring
  calc ‖digamma z - log z‖
      = ‖(digamma z - (log z - 1 / (2 * z))) + -(1 / (2 * z))‖ := by
        congr 1; ring
    _ ≤ ‖digamma z - (log z - 1 / (2 * z))‖ + ‖1 / (2 * z)‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_neg]
    _ ≤ K / a + 1 / 2 / a := by rw [h2z]; linarith
    _ = (K + 1 / 2) / ‖z‖ := by rw [← ha]; ring

end Complex
