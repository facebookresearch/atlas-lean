/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Yamada–Watanabe approximating functions

For a modulus `h` satisfying the Osgood divergence condition
`∫₀^ε h(u)⁻² du = ∞`, this file constructs the even `C²` approximations to
`|x|` used in Yamada–Watanabe pathwise-uniqueness arguments. The construction
uses continuity of `h`, positivity on `(0, ∞)`, and the divergence condition;
the classical strictly increasing form is recorded as a corollary.

## Main results

* `ProbabilityTheory.SDE.exists_yamadaWatanabe_approx`: there are
  `1 = a 0 > a 1 > ⋯ → 0` with `∫_{a(n+1)}^{a n} h⁻² = n + 1` and even `C²`
  functions `φ n → |·|` with `|φ n'| ≤ 1` and
  `0 ≤ φ n'' ≤ 2 / ((n + 1) h(|x|)²)`, where `φ n''` vanishes outside
  `a (n + 1) < |x| < a n`.
* `ProbabilityTheory.SDE.exists_yamadaWatanabe_approx_of_strictMonoOn`: the
  same conclusion under the classical strictly increasing hypothesis, with
  positivity derived from `h 0 = 0`.

## References

* R. Höpfner, "An extension of the Yamada-Watanabe condition for pathwise
  uniqueness to stochastic differential equations with jumps",
  *Electronic Communications in Probability* 14 (2009), 447–456.
-/

@[expose] public section

open Filter Topology MeasureTheory

namespace ProbabilityTheory.SDE

private lemma continuousAt_inv_sq {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ici 0))
    (hpos : ∀ u, 0 < u → 0 < h u) {u : ℝ} (hu : 0 < u) :
    ContinuousAt (fun v => (h v ^ 2)⁻¹) u :=
  ((hcont.continuousAt (Ici_mem_nhds hu)).pow 2).inv₀ (pow_ne_zero 2 (hpos u hu).ne')

private lemma intervalIntegrable_inv_sq {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ici 0))
    (hpos : ∀ u, 0 < u → 0 < h u) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    IntervalIntegrable (fun v => (h v ^ 2)⁻¹) volume s t := by
  refine ContinuousOn.intervalIntegrable fun u hu => ?_
  refine (continuousAt_inv_sq hcont hpos ?_).continuousWithinAt
  rcases Set.mem_uIcc.1 hu with h1 | h1 <;> linarith [h1.1]

/-- The Osgood condition makes `∫ u in t..b, (h u ^ 2)⁻¹` unbounded as `t → 0⁺`. -/
private lemma exists_lt_integral {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ici 0))
    (hpos : ∀ u, 0 < u → 0 < h u)
    (hosgood : ∀ ε, 0 < ε → ∫⁻ u in Set.Ioc 0 ε, ENNReal.ofReal ((h u ^ 2)⁻¹) = ⊤)
    {b : ℝ} (hb : 0 < b) (C : ℝ) : ∃ t, 0 < t ∧ t < b ∧ C < ∫ u in t..b, (h u ^ 2)⁻¹ := by
  by_contra H
  push Not at H
  have hI : IntegrableOn (fun u => (h u ^ 2)⁻¹) (Set.Ioc 0 b) := by
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded (l := atTop)
      (a := fun i : ℕ => b / ((i : ℝ) + 2)) (b := fun _ => b) (I := C) (fun i => ?_) ?_
      tendsto_const_nhds (Eventually.of_forall fun i => ?_)
    · exact (intervalIntegrable_inv_sq hcont hpos (by positivity) hb).1
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    · have hi : 0 < b / ((i : ℝ) + 2) := by positivity
      have hib : b / ((i : ℝ) + 2) < b := by
        have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      have hnorm : ∀ x : ℝ, ‖(h x ^ 2)⁻¹‖ = (h x ^ 2)⁻¹ := fun x =>
        Real.norm_of_nonneg (inv_nonneg.2 (sq_nonneg _))
      simp only [hnorm]
      rw [← intervalIntegral.integral_of_le hib.le]
      exact H _ hi hib
  have := hI.lintegral_lt_top
  rw [hosgood b hb] at this
  exact lt_irrefl _ this

private lemma exists_integral_eq {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ici 0))
    (hpos : ∀ u, 0 < u → 0 < h u)
    (hosgood : ∀ ε, 0 < ε → ∫⁻ u in Set.Ioc 0 ε, ENNReal.ofReal ((h u ^ 2)⁻¹) = ⊤)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    ∃ t, 0 < t ∧ t < b ∧ ∫ u in t..b, (h u ^ 2)⁻¹ = c := by
  obtain ⟨t₀, ht₀, ht₀b, hC⟩ := exists_lt_integral hcont hpos hosgood hb c
  have hG : ContinuousOn (fun t => ∫ u in t..b, (h u ^ 2)⁻¹) (Set.Icc t₀ b) := by
    have hi : IntegrableOn (fun u => (h u ^ 2)⁻¹) (Set.uIcc t₀ b) volume := by
      rw [Set.uIcc_of_le ht₀b.le]
      exact ContinuousOn.integrableOn_Icc fun u hu =>
        (continuousAt_inv_sq hcont hpos (by linarith [hu.1])).continuousWithinAt
    have := intervalIntegral.continuousOn_primitive_interval_left hi
    rwa [Set.uIcc_of_le ht₀b.le] at this
  obtain ⟨t, ht, hGt⟩ := intermediate_value_Icc' ht₀b.le hG
    ⟨by simp only [intervalIntegral.integral_same]; exact hc.le, hC.le⟩
  refine ⟨t, by linarith [ht.1], lt_of_le_of_ne ht.2 ?_, hGt⟩
  rintro rfl
  simp only [intervalIntegral.integral_same] at hGt
  linarith

/-- The sequence `1 = a 0 > a 1 > ⋯ → 0` with `∫ u in a (n + 1)..a n, (h u ^ 2)⁻¹ = n + 1`. -/
private lemma exists_seq {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ici 0))
    (hpos : ∀ u, 0 < u → 0 < h u)
    (hosgood : ∀ ε, 0 < ε → ∫⁻ u in Set.Ioc 0 ε, ENNReal.ofReal ((h u ^ 2)⁻¹) = ⊤) :
    ∃ a : ℕ → ℝ, a 0 = 1 ∧ StrictAnti a ∧ (∀ n, 0 < a n) ∧ Tendsto a atTop (𝓝 0) ∧
      ∀ n : ℕ, ∫ u in a (n + 1)..a n, (h u ^ 2)⁻¹ = n + 1 := by
  have hstep : ∀ (b : ℝ) (n : ℕ), ∃ t : ℝ, 0 < b →
      0 < t ∧ t < b ∧ ∫ u in t..b, (h u ^ 2)⁻¹ = (n : ℝ) + 1 := by
    intro b n
    by_cases hb : 0 < b
    · obtain ⟨t, h1, h2, h3⟩ := exists_integral_eq hcont hpos hosgood hb
        (by positivity : (0 : ℝ) < n + 1)
      exact ⟨t, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h' => absurd h' hb⟩
  choose T hT using hstep
  obtain ⟨a, ha0, haS⟩ : ∃ a : ℕ → ℝ, a 0 = 1 ∧ ∀ n, a (n + 1) = T (a n) n :=
    ⟨fun n => Nat.rec (motive := fun _ => ℝ) 1 (fun k ak => T ak k) n, rfl, fun _ => rfl⟩
  have hapos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => rw [ha0]; exact one_pos
    | succ k ih => rw [haS]; exact (hT _ _ ih).1
  have hlt : ∀ n, a (n + 1) < a n := fun n => by rw [haS]; exact (hT _ _ (hapos n)).2.1
  have hint : ∀ n : ℕ, ∫ u in a (n + 1)..a n, (h u ^ 2)⁻¹ = n + 1 := fun n => by
    rw [haS]; exact (hT _ _ (hapos n)).2.2
  have hanti : StrictAnti a := strictAnti_nat_of_succ_lt hlt
  refine ⟨a, ha0, hanti, hapos, ?_, hint⟩
  have hsum : ∀ n : ℕ, (n : ℝ) ≤ ∫ u in a n..1, (h u ^ 2)⁻¹ := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ k ih =>
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_inv_sq hcont hpos (hapos (k + 1)) (hapos k))
        (intervalIntegrable_inv_sq hcont hpos (hapos k) one_pos), hint k]
      push_cast
      linarith
  rw [tendsto_order]
  refine ⟨fun l hl => Eventually.of_forall fun n => lt_trans hl (hapos n), fun u hu => ?_⟩
  by_contra H
  have H' : ∀ n, u ≤ a n := by
    intro n
    by_contra H2
    push Not at H2
    exact H (eventually_atTop.2 ⟨n, fun m hm => lt_of_le_of_lt (hanti.antitone hm) H2⟩)
  have hM : ∀ n : ℕ, (n : ℝ) ≤ ∫ v in u..1, (h v ^ 2)⁻¹ := by
    intro n
    have h2 : 0 ≤ ∫ v in u..a n, (h v ^ 2)⁻¹ :=
      intervalIntegral.integral_nonneg (H' n) fun v _ => inv_nonneg.2 (sq_nonneg _)
    have h3 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_inv_sq hcont hpos hu (hapos n))
      (intervalIntegrable_inv_sq hcont hpos (hapos n) one_pos)
    linarith [hsum n]
  obtain ⟨n, hn⟩ := exists_nat_gt (∫ v in u..1, (h v ^ 2)⁻¹)
  linarith [hM n]

/-- A continuous probability density supported in `(b, c)` and bounded by `2 / (N * h v ^ 2)`.
It is the derivative of `Θ (F v / N)` on `[b, c]`, where `F` is a primitive of `h⁻²` vanishing
at `b` and `Θ s = 3 s ^ 2 - 2 s ^ 3`, clamped so that it vanishes outside `(b, c)`. -/
private lemma exists_density {h : ℝ → ℝ} (hcont : ContinuousOn h (Set.Ici 0))
    (hpos : ∀ u, 0 < u → 0 < h u) {b c N : ℝ} (hb : 0 < b) (hbc : b < c) (hN : 0 < N)
    (hI : ∫ u in b..c, (h u ^ 2)⁻¹ = N) :
    ∃ ρ : ℝ → ℝ, Continuous ρ ∧ (∀ v, 0 ≤ ρ v) ∧ (∀ v, ρ v ≠ 0 → b < v ∧ v < c) ∧
      (∀ v, ρ v ≤ 2 / (N * h v ^ 2)) ∧ ∫ v in b..c, ρ v = 1 := by
  obtain ⟨p, hp⟩ : ∃ p : ℝ → ℝ, ∀ v, p v = max b (min v c) := ⟨_, fun _ => rfl⟩
  have hp_cont : Continuous p := by
    rw [show p = fun v => max b (min v c) from funext hp]
    exact continuous_const.max (continuous_id.min continuous_const)
  have hp_ge : ∀ v, b ≤ p v := fun v => by rw [hp]; exact le_max_left _ _
  have hp_eq : ∀ v, b ≤ v → v ≤ c → p v = v := fun v h1 h2 => by
    rw [hp, min_eq_left h2, max_eq_right h1]
  have hhp_pos : ∀ v, 0 < h (p v) := fun v => hpos _ (lt_of_lt_of_le hb (hp_ge v))
  have hhp_cont : Continuous fun v => h (p v) :=
    hcont.comp_continuous hp_cont fun v => Set.mem_Ici.2 (le_trans hb.le (hp_ge v))
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ v, g v = (h (p v) ^ 2)⁻¹ := ⟨_, fun _ => rfl⟩
  have hg_cont : Continuous g := by
    rw [show g = fun v => (h (p v) ^ 2)⁻¹ from funext hg]
    exact (hhp_cont.pow 2).inv₀ fun v => pow_ne_zero 2 (hhp_pos v).ne'
  have hg_pos : ∀ v, 0 < g v := fun v => by rw [hg]; exact inv_pos.2 (pow_pos (hhp_pos v) 2)
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ v, F v = ∫ u in b..v, g u := ⟨_, fun _ => rfl⟩
  have hF_deriv : ∀ v, HasDerivAt F (g v) v := by
    intro v
    rw [show F = fun v => ∫ u in b..v, g u from funext hF]
    exact (hg_cont.integral_hasStrictDerivAt b v).hasDerivAt
  have hF_cont : Continuous F :=
    continuous_iff_continuousAt.2 fun v => (hF_deriv v).continuousAt
  have hF_mono : StrictMono F := strictMono_of_hasDerivAt_pos hF_deriv hg_pos
  have hFb : F b = 0 := by rw [hF, intervalIntegral.integral_same]
  have hFc : F c = N := by
    rw [hF, ← hI]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hbc.le] at hu
    simp only [hg, hp_eq u hu.1 hu.2]
  obtain ⟨t, ht⟩ : ∃ t : ℝ → ℝ, ∀ v, t v = max 0 (min (F v / N) 1) := ⟨_, fun _ => rfl⟩
  have ht_cont : Continuous t := by
    rw [show t = fun v => max 0 (min (F v / N) 1) from funext ht]
    exact continuous_const.max ((hF_cont.div_const N).min continuous_const)
  have ht_mem : ∀ v, 0 ≤ t v ∧ t v ≤ 1 := fun v => by
    rw [ht]; exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have ht_eq : ∀ v, b ≤ v → v ≤ c → t v = F v / N := by
    intro v h1 h2
    have hF1 : 0 ≤ F v / N := div_nonneg (hFb ▸ hF_mono.monotone h1) hN.le
    have hF2 : F v / N ≤ 1 := by
      rw [div_le_one₀ hN]; exact hFc ▸ hF_mono.monotone h2
    rw [ht, min_eq_left hF2, max_eq_right hF1]
  have ht_zero : ∀ v, v ≤ b → t v = 0 := by
    intro v hv
    have hF1 : F v / N ≤ 0 := by
      rw [div_le_iff₀ hN, zero_mul]; exact hFb ▸ hF_mono.monotone hv
    rw [ht, max_eq_left (le_trans (min_le_left _ _) hF1)]
  have ht_one : ∀ v, c ≤ v → t v = 1 := by
    intro v hv
    have hF1 : 1 ≤ F v / N := by
      rw [le_div_iff₀ hN, one_mul]; exact hFc ▸ hF_mono.monotone hv
    rw [ht, min_eq_right hF1, max_eq_right zero_le_one]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ → ℝ, ∀ v, ρ v = 6 * t v * (1 - t v) / (N * h (p v) ^ 2) :=
    ⟨_, fun _ => rfl⟩
  have hden : ∀ v, 0 < N * h (p v) ^ 2 := fun v => mul_pos hN (pow_pos (hhp_pos v) 2)
  have hρ_cont : Continuous ρ := by
    rw [show ρ = fun v => 6 * t v * (1 - t v) / (N * h (p v) ^ 2) from funext hρ]
    exact ((continuous_const.mul ht_cont).mul (continuous_const.sub ht_cont)).div
      (continuous_const.mul (hhp_cont.pow 2)) fun v => (hden v).ne'
  have hρ_nonneg : ∀ v, 0 ≤ ρ v := by
    intro v
    obtain ⟨h1, h2⟩ := ht_mem v
    rw [hρ]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) h1) (by linarith)) (hden v).le
  have hρ_supp : ∀ v, ρ v ≠ 0 → b < v ∧ v < c := by
    intro v hv
    by_contra hcon
    rw [not_and_or, not_lt, not_lt] at hcon
    apply hv
    rcases hcon with h1 | h1
    · rw [hρ, ht_zero v h1]; ring
    · rw [hρ, ht_one v h1]; ring
  refine ⟨ρ, hρ_cont, hρ_nonneg, hρ_supp, fun v => ?_, ?_⟩
  · by_cases hv : ρ v = 0
    · rw [hv]; exact div_nonneg zero_le_two (mul_nonneg hN.le (sq_nonneg _))
    · obtain ⟨h1, h2⟩ := hρ_supp v hv
      obtain ⟨h3, h4⟩ := ht_mem v
      rw [hρ, hp_eq v h1.le h2.le]
      have hpos' : 0 < N * h v ^ 2 := mul_pos hN (pow_pos (hpos v (by linarith)) 2)
      apply div_le_div_of_nonneg_right _ hpos'.le
      nlinarith [sq_nonneg (t v - 1 / 2)]
  · have hΦ : ∀ v ∈ Set.uIcc b c,
        HasDerivAt (fun w => 3 * (F w / N) ^ 2 - 2 * (F w / N) ^ 3) (ρ v) v := by
      intro v hv
      rw [Set.uIcc_of_le hbc.le] at hv
      have hd := (hF_deriv v).div_const N
      convert ((hd.pow 2).const_mul 3).sub ((hd.pow 3).const_mul 2) using 1
      rw [hρ, ht_eq v hv.1 hv.2, hg]
      have := (hhp_pos v).ne'
      norm_num
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ (hρ_cont.intervalIntegrable b c)]
    simp only [hFb, hFc, div_self hN.ne', zero_div]
    norm_num

/-- The even double primitive `x ↦ S x + S (-x)`, with `S x = ∫₀ˣ ∫₀ʳ ρ`, of a probability
density `ρ` supported in `(b, c)` with `0 < b`. -/
private lemma exists_even_primitive {b c : ℝ} (hb : 0 < b) (hbc : b < c) {ρ : ℝ → ℝ}
    (hρc : Continuous ρ) (hρ0 : ∀ v, 0 ≤ ρ v) (hρs : ∀ v, ρ v ≠ 0 → b < v ∧ v < c)
    (hρ1 : ∫ v in b..c, ρ v = 1) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 2 φ ∧ (∀ x, φ (-x) = φ x) ∧ (∀ x, |x| - c ≤ φ x ∧ φ x ≤ |x|) ∧
      (∀ x, |deriv φ x| ≤ 1) ∧ ∀ x, iteratedDeriv 2 φ x = ρ |x| := by
  have hρz : ∀ v, v ≤ b ∨ c ≤ v → ρ v = 0 := by
    intro v hv
    by_contra hne
    obtain ⟨h1, h2⟩ := hρs v hne
    rcases hv with hv | hv <;> linarith
  have hρi : ∀ x y : ℝ, IntervalIntegrable ρ volume x y := fun x y =>
    hρc.intervalIntegrable x y
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, ∀ v, R v = ∫ u in (0 : ℝ)..v, ρ u := ⟨_, fun _ => rfl⟩
  have hR_deriv : ∀ v, HasDerivAt R (ρ v) v := by
    intro v
    rw [show R = fun v => ∫ u in (0 : ℝ)..v, ρ u from funext hR]
    exact (hρc.integral_hasStrictDerivAt 0 v).hasDerivAt
  have hR_cont : Continuous R :=
    continuous_iff_continuousAt.2 fun v => (hR_deriv v).continuousAt
  have hR_mono : Monotone R := monotone_of_hasDerivAt_nonneg hR_deriv hρ0
  have hR_zero : ∀ v, v ≤ b → R v = 0 := by
    intro v hv
    rw [hR, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
      intervalIntegral.integral_zero]
    intro u hu
    refine hρz u (Or.inl ?_)
    rcases Set.mem_uIcc.1 hu with h | h <;> linarith [h.1, h.2]
  have hR_c : R c = 1 := by
    rw [hR, ← intervalIntegral.integral_add_adjacent_intervals (hρi 0 b) (hρi b c), ← hR,
      hR_zero b le_rfl, hρ1, zero_add]
  have hR_one : ∀ v, c ≤ v → R v = 1 := by
    intro v hv
    have h0 : ∫ u in c..v, ρ u = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
        intervalIntegral.integral_zero]
      intro u hu
      refine hρz u (Or.inr ?_)
      rw [Set.uIcc_of_le hv] at hu
      exact hu.1
    rw [hR, ← intervalIntegral.integral_add_adjacent_intervals (hρi 0 c) (hρi c v), ← hR, hR_c,
      h0, add_zero]
  have hR_bd : ∀ v, 0 ≤ R v ∧ R v ≤ 1 := by
    intro v
    constructor
    · rw [← hR_zero (min v b) (min_le_right _ _)]
      exact hR_mono (min_le_left _ _)
    · rw [← hR_one (max v c) (le_max_right _ _)]
      exact hR_mono (le_max_left _ _)
  have hRi : ∀ x y : ℝ, IntervalIntegrable R volume x y := fun x y =>
    hR_cont.intervalIntegrable x y
  obtain ⟨S, hS⟩ : ∃ S : ℝ → ℝ, ∀ x, S x = ∫ r in (0 : ℝ)..x, R r := ⟨_, fun _ => rfl⟩
  have hS_deriv : ∀ x, HasDerivAt S (R x) x := by
    intro x
    rw [show S = fun x => ∫ r in (0 : ℝ)..x, R r from funext hS]
    exact (hR_cont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hS_neg : ∀ y, 0 ≤ y → S (-y) = 0 := by
    intro y hy
    rw [hS, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)),
      intervalIntegral.integral_zero]
    intro u hu
    refine hR_zero u ?_
    rcases Set.mem_uIcc.1 hu with h | h <;> linarith [h.1, h.2]
  have hS_bd : ∀ y, 0 ≤ y → y - c ≤ S y ∧ S y ≤ y := by
    intro y hy
    constructor
    · rcases le_total y c with hyc | hyc
      · have : 0 ≤ S y := by
          rw [hS]
          exact intervalIntegral.integral_nonneg hy fun u _ => (hR_bd u).1
        linarith
      · have h2 : ∫ r in c..y, R r = y - c := by
          rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)),
            intervalIntegral.integral_const, smul_eq_mul, mul_one]
          intro u hu
          rw [Set.uIcc_of_le hyc] at hu
          exact hR_one u hu.1
        have h3 : 0 ≤ ∫ r in (0 : ℝ)..c, R r :=
          intervalIntegral.integral_nonneg (by linarith) fun u _ => (hR_bd u).1
        rw [hS, ← intervalIntegral.integral_add_adjacent_intervals (hRi 0 c) (hRi c y), h2]
        linarith
    · rw [hS]
      have := intervalIntegral.integral_mono_on hy (hRi 0 y)
        (continuous_const.intervalIntegrable (μ := volume) (u := fun _ => (1 : ℝ)) 0 y)
        fun u _ => (hR_bd u).2
      simpa using this
  have hφ_deriv : ∀ x, HasDerivAt (fun x => S x + S (-x)) (R x - R (-x)) x := by
    intro x
    have h2 : HasDerivAt (fun x => S (-x)) (-R (-x)) x := by
      have := (hS_deriv (-x)).comp x (hasDerivAt_neg x)
      rwa [mul_neg_one] at this
    exact ((hS_deriv x).add h2).congr_deriv (by ring)
  have hφ' : deriv (fun x => S x + S (-x)) = fun x => R x - R (-x) :=
    funext fun x => (hφ_deriv x).deriv
  have hψ_deriv : ∀ x, HasDerivAt (fun x => R x - R (-x)) (ρ x + ρ (-x)) x := by
    intro x
    have h2 : HasDerivAt (fun x => R (-x)) (-ρ (-x)) x := by
      have := (hR_deriv (-x)).comp x (hasDerivAt_neg x)
      rwa [mul_neg_one] at this
    exact ((hR_deriv x).sub h2).congr_deriv (by ring)
  have hψ' : deriv (fun x => R x - R (-x)) = fun x => ρ x + ρ (-x) :=
    funext fun x => (hψ_deriv x).deriv
  refine ⟨fun x => S x + S (-x), ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · have h1 : ContDiff ℝ 1 (fun x => R x - R (-x)) := by
      rw [contDiff_one_iff_deriv, hψ']
      exact ⟨fun x => (hψ_deriv x).differentiableAt, hρc.add (hρc.comp continuous_neg)⟩
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv, hφ']
    exact ⟨fun x => (hφ_deriv x).differentiableAt, fun h => absurd h (by simp), h1⟩
  · simp only [neg_neg]; ring
  · have hφabs : S x + S (-x) = S |x| := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx, hS_neg x hx, add_zero]
      · have := hS_neg (-x) (by linarith)
        rw [neg_neg] at this
        rw [abs_of_nonpos hx, this, zero_add]
    simp only [hφabs]
    exact hS_bd |x| (abs_nonneg x)
  · rw [hφ']
    have hbound : |R x - R (-x)| ≤ 1 := by
      obtain ⟨h1, h2⟩ := hR_bd x
      obtain ⟨h3, h4⟩ := hR_bd (-x)
      rw [abs_le]
      constructor <;> linarith
    exact hbound
  · rw [iteratedDeriv_succ, iteratedDeriv_one, hφ', hψ']
    have heq : ρ x + ρ (-x) = ρ |x| := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx, hρz (-x) (Or.inl (by linarith)), add_zero]
      · rw [abs_of_nonpos hx, hρz x (Or.inl (by linarith)), zero_add]
    exact heq

/-- **Yamada–Watanabe approximating functions.** If `h : [0, ∞) → [0, ∞)` is continuous,
positive on `(0, ∞)`, and `∫⁻_{(0,ε]} h⁻² = ∞` for every `ε > 0`, there are
`1 = a 0 > a 1 > ⋯ → 0` with `∫_{a (n+1)}^{a n} h⁻² = n + 1`, and even `C²`
functions `φ n → |·|` with `|φ n'| ≤ 1` and `0 ≤ φ n'' ≤ 2 / ((n + 1) h(|x|)²)`, where
`φ n''` vanishes outside `a (n+1) < |x| < a n`. -/
theorem exists_yamadaWatanabe_approx {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ici 0)) (hpos : ∀ u, 0 < u → 0 < h u)
    (hosgood : ∀ ε, 0 < ε → ∫⁻ u in Set.Ioc 0 ε, ENNReal.ofReal ((h u ^ 2)⁻¹) = ⊤) :
    ∃ (a : ℕ → ℝ) (φ : ℕ → ℝ → ℝ),
      a 0 = 1 ∧ StrictAnti a ∧ (∀ n, 0 < a n) ∧ Tendsto a atTop (𝓝 0) ∧
      (∀ n, ∫ u in a (n + 1)..a n, (h u ^ 2)⁻¹ = n + 1) ∧
      (∀ n, ContDiff ℝ 2 (φ n)) ∧ (∀ n x, φ n (-x) = φ n x) ∧
      (∀ x, Tendsto (fun n => φ n x) atTop (𝓝 |x|)) ∧
      (∀ n x, |deriv (φ n) x| ≤ 1) ∧
      (∀ n x, 0 ≤ iteratedDeriv 2 (φ n) x ∧
        iteratedDeriv 2 (φ n) x ≤ 2 / ((n + 1) * h |x| ^ 2)) ∧
      (∀ n x, iteratedDeriv 2 (φ n) x ≠ 0 → a (n + 1) < |x| ∧ |x| < a n) := by
  obtain ⟨a, ha0, hanti, hapos, hlim, hint⟩ := exists_seq hcont hpos hosgood
  have key : ∀ n : ℕ, ∃ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ ∧ (∀ x, ψ (-x) = ψ x) ∧
      (∀ x, |x| - a n ≤ ψ x ∧ ψ x ≤ |x|) ∧ (∀ x, |deriv ψ x| ≤ 1) ∧
      (∀ x, 0 ≤ iteratedDeriv 2 ψ x ∧ iteratedDeriv 2 ψ x ≤ 2 / ((n + 1) * h |x| ^ 2)) ∧
      (∀ x, iteratedDeriv 2 ψ x ≠ 0 → a (n + 1) < |x| ∧ |x| < a n) := by
    intro n
    have hlt : a (n + 1) < a n := hanti (Nat.lt_add_one n)
    obtain ⟨ρ, hρc, hρ0, hρs, hρb, hρ1⟩ :=
      exists_density hcont hpos (hapos (n + 1)) hlt (by positivity : (0 : ℝ) < n + 1) (hint n)
    obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := exists_even_primitive (hapos (n + 1)) hlt hρc hρ0 hρs hρ1
    exact ⟨ψ, h1, h2, h3, h4, fun x => by rw [h5]; exact ⟨hρ0 _, hρb _⟩,
      fun x hx => by rw [h5] at hx; exact hρs _ hx⟩
  choose φ hφ using key
  refine ⟨a, φ, ha0, hanti, hapos, hlim, hint, fun n => (hφ n).1, fun n => (hφ n).2.1,
    fun x => ?_, fun n => (hφ n).2.2.2.1, fun n => (hφ n).2.2.2.2.1,
    fun n => (hφ n).2.2.2.2.2⟩
  have hlow : Tendsto (fun n => |x| - a n) atTop (𝓝 |x|) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => |x|) atTop (𝓝 |x|)).sub hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => ((hφ n).2.2.1 x).1) fun n => ((hφ n).2.2.1 x).2

/-- Classical strictly increasing form of `exists_yamadaWatanabe_approx`: positivity
on `(0, ∞)` follows from strict monotonicity on `[0, ∞)` and `h 0 = 0`. -/
theorem exists_yamadaWatanabe_approx_of_strictMonoOn {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ici 0)) (hmono : StrictMonoOn h (Set.Ici 0))
    (h0 : h 0 = 0)
    (hosgood : ∀ ε, 0 < ε → ∫⁻ u in Set.Ioc 0 ε, ENNReal.ofReal ((h u ^ 2)⁻¹) = ⊤) :
    ∃ (a : ℕ → ℝ) (φ : ℕ → ℝ → ℝ),
      a 0 = 1 ∧ StrictAnti a ∧ (∀ n, 0 < a n) ∧ Tendsto a atTop (𝓝 0) ∧
      (∀ n, ∫ u in a (n + 1)..a n, (h u ^ 2)⁻¹ = n + 1) ∧
      (∀ n, ContDiff ℝ 2 (φ n)) ∧ (∀ n x, φ n (-x) = φ n x) ∧
      (∀ x, Tendsto (fun n => φ n x) atTop (𝓝 |x|)) ∧
      (∀ n x, |deriv (φ n) x| ≤ 1) ∧
      (∀ n x, 0 ≤ iteratedDeriv 2 (φ n) x ∧
        iteratedDeriv 2 (φ n) x ≤ 2 / ((n + 1) * h |x| ^ 2)) ∧
      (∀ n x, iteratedDeriv 2 (φ n) x ≠ 0 → a (n + 1) < |x| ∧ |x| < a n) := by
  have hpos : ∀ u, 0 < u → 0 < h u := by
    intro u hu
    have hlt := hmono (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hu.le) hu
    rwa [h0] at hlt
  exact exists_yamadaWatanabe_approx hcont hpos hosgood

end ProbabilityTheory.SDE
