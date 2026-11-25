/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integral criterion for asymptotic equivalence to the identity

This file proves a Tauberian-style criterion (ATLAS `NumberTheoryI` Lemma 16.8):
if `f : ℝ → ℝ` is nondecreasing on `[1, ∞)` and the integral
`x ↦ ∫ t in Set.Ioc 1 x, (f t - t) / t ^ 2` converges to a finite limit as
`x → ∞`, then `f x ~ x`.

The proof argues by contradiction on both sides. If `f x ≥ lam * x` for
arbitrarily large `x` (with `lam > 1`), monotonicity forces the integrand to
stay above an explicit positive constant on the whole interval
`[b, lam' * b]`, whose length is proportional to `b`; the resulting integral
lower bound contradicts the Cauchy property of the convergent integral.
The lower estimate is symmetric, using the interval `[mu * b, b]`.
-/

@[expose] public section

namespace Asymptotics

open Filter MeasureTheory Set Topology

/-- Cauchy-tail reformulation of convergence, used to control integral tails. -/
private lemma cauchy_of_tendsto {F : ℝ → ℝ} {L : ℝ}
    (hF : Tendsto F atTop (𝓝 L)) :
    ∀ c > 0, ∀ᶠ x in atTop, ∀ y, x ≤ y → |F y - F x| < c := by
  intro c hc
  rw [Metric.tendsto_atTop] at hF
  obtain ⟨N, hN⟩ := hF (c / 2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with x hx y hxy
  have h1 := hN x hx
  have h2 := hN y (le_trans hx hxy)
  rw [Real.dist_eq] at h1 h2
  linarith [abs_sub_le (F y) L (F x), abs_sub_comm L (F x), abs_sub_comm L (F y)]

/-- The integrand `(f t - t) / t ^ 2` is integrable over `Ioc a b` whenever
`1 ≤ a`, using monotonicity of `f` restricted to `[1, ∞)`. -/
private lemma integrableOn_g_Ioc (f : ℝ → ℝ) (hf : MonotoneOn f (Ici 1))
    (a b : ℝ) (ha : 1 ≤ a) :
    IntegrableOn (fun t => (f t - t) / t ^ 2) (Ioc a b) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have hsub : Icc a b ⊆ Ici 1 := fun x hx => mem_Ici.mpr (le_trans ha hx.1)
  have h1 : IntegrableOn f (Icc a b) :=
    (hf.mono hsub).integrableOn_isCompact isCompact_Icc
  have h2 : (fun t => (f t - t) / t ^ 2) = fun t => (f t - t) * (1 / t ^ 2) := by
    ext t
    ring
  rw [h2]
  apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
  exact (h1.sub
    (continuousOn_id.integrableOn_compact isCompact_Icc)).mul_continuousOn
    (ContinuousOn.div continuousOn_const (continuousOn_pow 2)
      (fun x hx => pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha0 hx.1))))
    isCompact_Icc

/-- Splitting a set integral over adjacent `Ioc` intervals. -/
private lemma integral_Ioc_split' {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) (hg1 : IntegrableOn g (Ioc a b))
    (hg2 : IntegrableOn g (Ioc b c)) :
    ∫ x in Ioc a c, g x = (∫ x in Ioc a b, g x) + (∫ x in Ioc b c, g x) := by
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc]
  exact setIntegral_union
    (by rw [disjoint_left]; intro x hx1 hx2; exact lt_irrefl b (lt_of_lt_of_le hx2.1 hx1.2))
    measurableSet_Ioc hg1 hg2

/-- Integral of a constant over an `Ioc` interval. -/
private lemma integral_const_Ioc {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    ∫ _ in Ioc a b, c = c * (b - a) := by
  simp only [setIntegral_const, smul_eq_mul, mul_comm]
  congr 1
  simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : 0 ≤ b - a)]

/-- Upper one-sided bound: eventually `f x < lam * x` for every `lam > 1`. -/
private lemma upper_bound_of_convergent_integral (f : ℝ → ℝ)
    (hf : MonotoneOn f (Ici 1)) {L : ℝ}
    (hL : Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2) atTop (𝓝 L))
    {lam : ℝ} (hlam : 1 < lam) :
    ∀ᶠ x in atTop, f x < lam * x := by
  set c₀ := (lam - 1) ^ 2 / (lam + 1) ^ 2 with hc₀_def
  have hlam_sub_pos : 0 < lam - 1 := by linarith
  have hlam_add_pos : 0 < lam + 1 := by linarith
  have hc₀_pos : 0 < c₀ :=
    div_pos (sq_pos_of_pos hlam_sub_pos) (sq_pos_of_pos hlam_add_pos)
  set lam' := (lam + 1) / 2 with hlam'_def
  have hlam'_gt1 : 1 < lam' := by linarith
  have hlam'_lt_lam : lam' < lam := by linarith
  set g := fun t => (f t - t) / t ^ 2 with hg_def
  set F := fun x => ∫ t in Ioc 1 x, g t with hF_def
  have hcauchy := cauchy_of_tendsto hL c₀ hc₀_pos
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ x in atTop, lam * x ≤ f x :=
    hcon.mono (fun x hx => not_lt.mp hx)
  have h_combined := (hcauchy.and (eventually_ge_atTop 1)).and_frequently hfreq
  obtain ⟨_, ⟨⟨hb_cauchy, hb1⟩, hb_large⟩⟩ :=
    h_combined.forall_exists_of_atTop 0 |>.choose_spec
  set b := (h_combined.forall_exists_of_atTop 0).choose with hb_def
  have hb_pos : 0 < b := by linarith
  have hlam'b_ge_b : b ≤ lam' * b :=
    le_mul_of_one_le_left (le_of_lt hb_pos) (le_of_lt hlam'_gt1)
  have hint : IntegrableOn g (Ioc b (lam' * b)) :=
    integrableOn_g_Ioc f hf b (lam' * b) hb1
  have hconst_int :
      IntegrableOn (fun _ => (lam - 1) / (2 * lam' ^ 2 * b)) (Ioc b (lam' * b)) := by
    apply integrableOn_const (hs := ?_)
    exact ((measure_mono Ioc_subset_Icc_self).trans_lt
      isCompact_Icc.measure_lt_top).ne
  have hpw : ∀ t ∈ Ioc b (lam' * b), (lam - 1) / (2 * lam' ^ 2 * b) ≤ g t := by
    intro t ht
    have htb : b < t := ht.1
    have htub : t ≤ lam' * b := ht.2
    have ht_pos : 0 < t := lt_trans hb_pos htb
    have hb_mem : b ∈ Ici (1 : ℝ) := mem_Ici.mpr hb1
    have ht_mem : t ∈ Ici (1 : ℝ) := mem_Ici.mpr (le_trans hb1 (le_of_lt htb))
    have hft : lam * b ≤ f t := le_trans hb_large (hf hb_mem ht_mem (le_of_lt htb))
    have h_num : (lam - 1) / 2 * b ≤ f t - t := by
      have hcalc : (lam - lam') * b = (lam - 1) / 2 * b := by rw [hlam'_def]; ring
      nlinarith
    have h_denom : t ^ 2 ≤ (lam' * b) ^ 2 := sq_le_sq' (by linarith) htub
    change (lam - 1) / (2 * lam' ^ 2 * b) ≤ (f t - t) / t ^ 2
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * lam' ^ 2 * b) (by positivity : 0 < t ^ 2)]
    calc (lam - 1) * t ^ 2 ≤ (lam - 1) * (lam' * b) ^ 2 :=
            mul_le_mul_of_nonneg_left h_denom (by linarith)
      _ = 2 * lam' ^ 2 * b * ((lam - 1) / 2 * b) := by ring
      _ ≤ 2 * lam' ^ 2 * b * (f t - t) :=
            mul_le_mul_of_nonneg_left h_num (by positivity)
      _ = (f t - t) * (2 * lam' ^ 2 * b) := by ring
  have h_lower :
      (lam - 1) / (2 * lam' ^ 2 * b) * ((lam' - 1) * b) ≤
        ∫ t in Ioc b (lam' * b), g t := by
    calc (lam - 1) / (2 * lam' ^ 2 * b) * ((lam' - 1) * b)
        = ∫ _ in Ioc b (lam' * b), (lam - 1) / (2 * lam' ^ 2 * b) := by
            rw [integral_const_Ioc hlam'b_ge_b]; ring
      _ ≤ ∫ t in Ioc b (lam' * b), g t :=
            setIntegral_mono_on hconst_int hint measurableSet_Ioc hpw
  have h_product : (lam - 1) / (2 * lam' ^ 2 * b) * ((lam' - 1) * b) = c₀ := by
    rw [hlam'_def, hc₀_def]; field_simp; ring
  have h_integral_ge_c₀ : c₀ ≤ ∫ t in Ioc b (lam' * b), g t := by linarith
  have h_split : F (lam' * b) = F b + ∫ t in Ioc b (lam' * b), g t := by
    change ∫ t in Ioc 1 (lam' * b), g t =
      (∫ t in Ioc 1 b, g t) + ∫ t in Ioc b (lam' * b), g t
    exact integral_Ioc_split' hb1 hlam'b_ge_b
      (integrableOn_g_Ioc f hf 1 b le_rfl) hint
  have hcauchy_b := hb_cauchy (lam' * b) hlam'b_ge_b
  have h_tail_small : |∫ t in Ioc b (lam' * b), g t| < c₀ := by
    have heq : ∫ t in Ioc b (lam' * b), g t = F (lam' * b) - F b := by linarith
    rw [heq]; exact hcauchy_b
  have h_integral_nonneg : 0 ≤ ∫ t in Ioc b (lam' * b), g t :=
    le_trans (le_of_lt hc₀_pos) h_integral_ge_c₀
  linarith [abs_of_nonneg h_integral_nonneg]

/-- Lower one-sided bound: eventually `x / lam < f x` for every `lam > 1`. -/
private lemma lower_bound_of_convergent_integral (f : ℝ → ℝ)
    (hf : MonotoneOn f (Ici 1)) {L : ℝ}
    (hL : Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2) atTop (𝓝 L))
    {lam : ℝ} (hlam : 1 < lam) :
    ∀ᶠ x in atTop, x / lam < f x := by
  set c₀ := (lam - 1) ^ 2 / (4 * lam ^ 2) with hc₀_def
  set mu := (lam + 1) / (2 * lam) with hmu_def
  have hlam_pos : 0 < lam := by linarith
  have hc₀_pos : 0 < c₀ := div_pos (sq_pos_of_pos (by linarith)) (by positivity)
  have hmu_pos : 0 < mu := by positivity
  have hmu_lt1 : mu < 1 := by
    rw [hmu_def]; rw [div_lt_one (by positivity)]; linarith
  set g := fun t => (f t - t) / t ^ 2 with hg_def
  set F := fun x => ∫ t in Ioc 1 x, g t with hF_def
  have hcauchy := cauchy_of_tendsto hL c₀ hc₀_pos
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ x in atTop, f x ≤ x / lam :=
    hcon.mono (fun x hx => not_lt.mp hx)
  have hcauchy_mu : ∀ᶠ b in atTop, ∀ y, mu * b ≤ y → |F y - F (mu * b)| < c₀ := by
    have htend : Tendsto (fun b => mu * b) atTop atTop :=
      Filter.tendsto_atTop_atTop_of_monotone
        (fun a b hab => mul_le_mul_of_nonneg_left hab (le_of_lt hmu_pos))
        (fun b => ⟨b / mu, by
          rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hmu_pos)]⟩)
    exact htend.eventually hcauchy
  have h_combined := (hcauchy_mu.and (eventually_ge_atTop lam)).and_frequently hfreq
  obtain ⟨_, ⟨⟨hb_cauchy_mu, hb_lam⟩, hb_small⟩⟩ :=
    h_combined.forall_exists_of_atTop 0 |>.choose_spec
  set b := (h_combined.forall_exists_of_atTop 0).choose with hb_def_eq
  have hb_pos : 0 < b := by linarith
  have hmub_pos : 0 < mu * b := mul_pos hmu_pos hb_pos
  have hmub_le_b : mu * b ≤ b :=
    mul_le_of_le_one_left (le_of_lt hb_pos) (le_of_lt hmu_lt1)
  have hmub_ge1 : 1 ≤ mu * b := by
    have h1 : (1 : ℝ) ≤ (lam + 1) / 2 := by linarith
    have h2 : (lam + 1) / 2 = mu * lam := by rw [hmu_def]; field_simp
    calc (1 : ℝ) ≤ mu * lam := by linarith
      _ ≤ mu * b := mul_le_mul_of_nonneg_left hb_lam (le_of_lt hmu_pos)
  have hint : IntegrableOn g (Ioc (mu * b) b) :=
    integrableOn_g_Ioc f hf (mu * b) b hmub_ge1
  have hconst_int :
      IntegrableOn (fun _ => -((lam - 1) / (2 * lam * b))) (Ioc (mu * b) b) := by
    apply integrableOn_const (hs := ?_)
    exact ((measure_mono Ioc_subset_Icc_self).trans_lt
      isCompact_Icc.measure_lt_top).ne
  have hpw : ∀ t ∈ Ioc (mu * b) b, g t ≤ -((lam - 1) / (2 * lam * b)) := by
    intro t ht
    have htl : mu * b < t := ht.1
    have htu : t ≤ b := ht.2
    have ht_pos : 0 < t := lt_trans hmub_pos htl
    have ht_mem : t ∈ Ici (1 : ℝ) := mem_Ici.mpr (le_trans hmub_ge1 (le_of_lt htl))
    have hb_mem : b ∈ Ici (1 : ℝ) := mem_Ici.mpr (le_trans hmub_ge1 hmub_le_b)
    have hft : f t ≤ b / lam := le_trans (hf ht_mem hb_mem htu) hb_small
    change (f t - t) / t ^ 2 ≤ -((lam - 1) / (2 * lam * b))
    rw [show -((lam - 1) / (2 * lam * b)) = -(lam - 1) / (2 * lam * b) from by ring]
    rw [div_le_div_iff₀ (sq_pos_of_pos ht_pos)
      (mul_pos (mul_pos two_pos hlam_pos) hb_pos)]
    have h1 : (f t - t) * (2 * lam) ≤ -(b * (lam - 1)) := by
      have hft_sub : f t - t ≤ b / lam - mu * b := by linarith
      have heq : (b / lam - mu * b) * (2 * lam) = -(b * (lam - 1)) := by
        rw [hmu_def]; field_simp; ring
      nlinarith
    have h2 : (f t - t) * (2 * lam * b) ≤ -(lam - 1) * b ^ 2 := by
      nlinarith [sq_nonneg b]
    linarith [mul_le_mul_of_nonpos_left (sq_le_sq' (show -b ≤ t by linarith) htu)
              (show -(lam - 1) ≤ 0 by linarith)]
  have h_upper : ∫ t in Ioc (mu * b) b, g t ≤ -c₀ := by
    have h1 : ∫ t in Ioc (mu * b) b, g t ≤
        ∫ _ in Ioc (mu * b) b, -((lam - 1) / (2 * lam * b)) :=
      setIntegral_mono_on hint hconst_int measurableSet_Ioc hpw
    have h2 : ∫ _ in Ioc (mu * b) b, -((lam - 1) / (2 * lam * b)) =
        -((lam - 1) / (2 * lam * b)) * (b - mu * b) :=
      integral_const_Ioc hmub_le_b _
    have h3 : -((lam - 1) / (2 * lam * b)) * (b - mu * b) = -c₀ := by
      rw [hmu_def, hc₀_def]; field_simp; ring
    linarith
  have h_split : F b = F (mu * b) + ∫ t in Ioc (mu * b) b, g t := by
    change ∫ t in Ioc 1 b, g t =
      (∫ t in Ioc 1 (mu * b), g t) + ∫ t in Ioc (mu * b) b, g t
    exact integral_Ioc_split' hmub_ge1 hmub_le_b
      (integrableOn_g_Ioc f hf 1 (mu * b) le_rfl) hint
  have hcauchy_b := hb_cauchy_mu b hmub_le_b
  have h_eq : ∫ t in Ioc (mu * b) b, g t = F b - F (mu * b) := by linarith
  have h_tail : |∫ t in Ioc (mu * b) b, g t| < c₀ := by rw [h_eq]; exact hcauchy_b
  have h_nonpos : ∫ t in Ioc (mu * b) b, g t ≤ 0 := le_trans h_upper (by linarith)
  rw [abs_of_nonpos h_nonpos] at h_tail
  linarith

/-- **Integral criterion for asymptotic equivalence to the identity.** Let $f$ be a real function
on $\mathbb{R}$ that is nondecreasing on $[1, \infty)$, and suppose that the integral
$\int_1^x (f(t) - t) / t^2 \, dt$ converges to a finite limit as $x \to \infty$. Then
$f(x) \sim x$ as $x \to \infty$.

No monotonicity is assumed below $1$.

Source: ATLAS `NumberTheoryI` Lemma 16.8. -/
theorem isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq
    (f : ℝ → ℝ) (hf : MonotoneOn f (Ici 1))
    (hconv : ∃ L : ℝ,
      Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2)
        atTop (𝓝 L)) :
    f ~[atTop] (fun x : ℝ => x) := by
  rw [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx; exact ne_of_gt hx)]
  obtain ⟨L, hL⟩ := hconv
  rw [tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a ≤ 0
    · have h := lower_bound_of_convergent_integral f hf hL
        (show (1 : ℝ) < 2 by norm_num)
      filter_upwards [h, eventually_gt_atTop 0] with x hfx hx
      have hfx_pos : 0 < f x := by linarith [show (0 : ℝ) < x / 2 by linarith]
      change a < f x / x
      calc a ≤ 0 := ha0
        _ < f x / x := div_pos hfx_pos hx
    · push Not at ha0
      have hlam : 1 < 1 / a := by rw [lt_div_iff₀ ha0]; linarith
      have h := lower_bound_of_convergent_integral f hf hL hlam
      filter_upwards [h, eventually_gt_atTop 0] with x hfx hx
      change a < f x / x
      rw [lt_div_iff₀ hx]
      have hxx : x / (1 / a) = a * x := by field_simp
      linarith
  · intro a ha
    have h := upper_bound_of_convergent_integral f hf hL ha
    filter_upwards [h, eventually_gt_atTop 0] with x hfx hx
    change f x / x < a
    rw [div_lt_iff₀ hx]
    linarith

end Asymptotics
