/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Code.SLE.LoewnerODE

open Complex Set Filter Topology
open scoped NNReal ComplexConjugate

namespace StatMech.SLE







lemma im_loewnerField (W : ℝ → ℝ) (t : ℝ) (w : ℂ) :
    (loewnerField W t w).im = -2 * w.im / Complex.normSq (w - (W t : ℂ)) := by
  rw [loewnerField_apply, Complex.div_im]; simp [Complex.normSq]; ring




lemma im_loewnerField_nonpos {W : ℝ → ℝ} {t : ℝ} {w : ℂ} (hw : 0 ≤ w.im) :
    (loewnerField W t w).im ≤ 0 := by
  rw [im_loewnerField]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (Complex.normSq_nonneg _)


lemma re_loewnerField (W : ℝ → ℝ) (t : ℝ) (w : ℂ) :
    (loewnerField W t w).re =
      2 * (w.re - W t) / Complex.normSq (w - (W t : ℂ)) := by
  rw [loewnerField_apply, Complex.div_re]
  simp [Complex.normSq]


def loewnerReflection (z : ℂ) : ℂ := -conj z

@[simp] lemma loewnerReflection_re (z : ℂ) : (loewnerReflection z).re = -z.re := by
  simp [loewnerReflection]

@[simp] lemma loewnerReflection_im (z : ℂ) : (loewnerReflection z).im = z.im := by
  simp [loewnerReflection]

@[simp] lemma loewnerReflection_involutive (z : ℂ) :
    loewnerReflection (loewnerReflection z) = z := by
  simp [loewnerReflection]



lemma loewnerReflection_loewnerField (W : ℝ → ℝ) (t : ℝ) (w : ℂ) :
    loewnerReflection (loewnerField W t w) =
      loewnerField (fun s ↦ -W s) t (loewnerReflection w) := by
  simp only [loewnerReflection, loewnerField_apply, map_mul, map_ofNat, map_inv₀,
    map_sub, Complex.conj_ofReal, Complex.ofReal_neg, div_eq_mul_inv]
  rw [show -conj w - -(W t : ℂ) = -(conj w - (W t : ℂ)) by ring]
  rw [inv_neg]
  ring






lemma hasDerivAt_im_of {g : ℝ → ℂ} {v : ℂ} {t : ℝ} (h : HasDerivAt g v t) :
    HasDerivAt (fun u => (g u).im) v.im t := by
  have h2 : HasDerivAt (fun u => Complex.imCLM (g u)) (Complex.imCLM v) t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h
  simpa using h2


lemma hasDerivWithinAt_im_of {g : ℝ → ℂ} {v : ℂ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt g v s t) :
    HasDerivWithinAt (fun u => (g u).im) v.im s t := by
  have h2 : HasDerivWithinAt (fun u => Complex.imCLM (g u)) (Complex.imCLM v) s t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t h
  simpa using h2


lemma hasDerivAt_re_of {g : ℝ → ℂ} {v : ℂ} {t : ℝ} (h : HasDerivAt g v t) :
    HasDerivAt (fun u => (g u).re) v.re t := by
  have h2 : HasDerivAt (fun u => Complex.reCLM (g u)) (Complex.reCLM v) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  simpa using h2


lemma hasDerivWithinAt_re_of {g : ℝ → ℂ} {v : ℂ} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt g v s t) :
    HasDerivWithinAt (fun u => (g u).re) v.re s t := by
  have h2 : HasDerivWithinAt (fun u => Complex.reCLM (g u)) (Complex.reCLM v) s t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t h
  simpa using h2







theorem antitoneOn_im_of_isLoewnerSolution {W : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) {a b : ℝ}
    {g : ℝ → ℂ}
    (hcont : ContinuousOn (fun s => (g s).im) (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (loewnerField W t (g t)) t)
    (hs : ∀ t ∈ Ioo a b, g t ∈ loewnerStrip δ) :
    AntitoneOn (fun s => (g s).im) (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont
  · rw [interior_Icc]; intro t ht
    exact ((hasDerivAt_im_of (hd t ht)).differentiableAt).differentiableWithinAt
  · rw [interior_Icc]; intro t ht
    rw [(hasDerivAt_im_of (hd t ht)).deriv]
    exact im_loewnerField_nonpos (le_trans hδ.le (hs t ht))





lemma normSq_sub_ofReal_ge {δ : ℝ} {x : ℝ} {w : ℂ} (hw : δ ≤ w.im) (hδ : 0 ≤ δ) :
    δ ^ 2 ≤ Complex.normSq (w - (x : ℂ)) := by
  have hb : δ ≤ ‖w - (x : ℂ)‖ := le_norm_sub_ofReal hw
  rw [Complex.normSq_eq_norm_sq]
  calc δ ^ 2 = δ * δ := sq δ
    _ ≤ ‖w - (x : ℂ)‖ * ‖w - (x : ℂ)‖ := mul_le_mul hb hb hδ (norm_nonneg _)
    _ = ‖w - (x : ℂ)‖ ^ 2 := (sq _).symm











theorem im_ge_exp_mul_of_isLoewnerSolution {W : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) {a b : ℝ}
    {g : ℝ → ℂ}
    (hcont : ContinuousOn (fun s => (g s).im) (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
    (hs : ∀ t ∈ Ico a b, g t ∈ loewnerStrip δ) :
    ∀ t ∈ Icc a b, (g a).im * Real.exp (-(2 / δ ^ 2) * (t - a)) ≤ (g t).im := by
  set K : ℝ := -(2 / δ ^ 2) with hK
  have hmain : ∀ t ∈ Icc a b,
      (fun s => -(g s).im) t ≤ gronwallBound (-(g a).im) K 0 (t - a) := by
    apply le_gronwallBound_of_liminf_deriv_right_le
    · exact hcont.neg
    · intro x hx r hr
      exact ((hasDerivWithinAt_im_of (hd x hx)).neg).liminf_right_slope_le hr
    · rfl
    · intro x hx
      have hgim : δ ≤ (g x).im := hs x hx
      rw [im_loewnerField, add_zero, hK]
      have hns : δ ^ 2 ≤ Complex.normSq (g x - (W x : ℂ)) := normSq_sub_ofReal_ge hgim hδ.le
      have hxim : 0 ≤ (g x).im := le_trans hδ.le hgim
      rw [neg_mul_neg, ← sub_nonneg]
      have key : (2 / δ ^ 2) * (g x).im - -(-2 * (g x).im / Complex.normSq (g x - ↑(W x)))
          = 2 * (g x).im * (1 / δ ^ 2 - 1 / Complex.normSq (g x - ↑(W x))) := by ring
      rw [key]
      refine mul_nonneg (by positivity) ?_
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by positivity) hns
  intro t ht
  have hb := hmain t ht
  rw [gronwallBound_ε0] at hb
  simp only at hb
  have h2 : (g a).im * Real.exp (K * (t - a)) ≤ (g t).im := by nlinarith [hb]
  rwa [hK] at h2




theorem im_ge_exp_mul_of_normSq_ge
    {W : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) {a b : ℝ} {g : ℝ → ℂ}
    (hcont : ContinuousOn (fun s => (g s).im) (Icc a b))
    (hd : ∀ t ∈ Ico a b,
      HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
    (hupper : ∀ t ∈ Ico a b, 0 ≤ (g t).im)
    (hden : ∀ t ∈ Ico a b,
      δ ^ 2 ≤ Complex.normSq (g t - (W t : ℂ))) :
    ∀ t ∈ Icc a b,
      (g a).im * Real.exp (-(2 / δ ^ 2) * (t - a)) ≤ (g t).im := by
  set K : ℝ := -(2 / δ ^ 2) with hK
  have hmain : ∀ t ∈ Icc a b,
      (fun s => -(g s).im) t ≤ gronwallBound (-(g a).im) K 0 (t - a) := by
    apply le_gronwallBound_of_liminf_deriv_right_le
    · exact hcont.neg
    · intro x hx r hr
      exact ((hasDerivWithinAt_im_of (hd x hx)).neg).liminf_right_slope_le hr
    · rfl
    · intro x hx
      rw [im_loewnerField, add_zero, hK]
      have hns := hden x hx
      have hxim := hupper x hx
      rw [neg_mul_neg, ← sub_nonneg]
      have key : (2 / δ ^ 2) * (g x).im -
          -(-2 * (g x).im / Complex.normSq (g x - ↑(W x))) =
          2 * (g x).im *
            (1 / δ ^ 2 - 1 / Complex.normSq (g x - ↑(W x))) := by
        ring
      rw [key]
      refine mul_nonneg (by positivity) ?_
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by positivity) hns
  intro t ht
  have hb := hmain t ht
  rw [gronwallBound_ε0] at hb
  simp only at hb
  have h2 : (g a).im * Real.exp (K * (t - a)) ≤ (g t).im := by
    nlinarith [hb]
  rwa [hK] at h2






theorem mem_upperHalfPlane_of_isLoewnerSolution {W : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    {a b : ℝ} {g : ℝ → ℂ}
    (hcont : ContinuousOn (fun s => (g s).im) (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
    (hs : ∀ t ∈ Ico a b, g t ∈ loewnerStrip δ)
    (h0 : 0 < (g a).im) :
    ∀ t ∈ Icc a b, g t ∈ upperHalfPlane := by
  intro t ht
  rw [mem_upperHalfPlane]
  have hlb := im_ge_exp_mul_of_isLoewnerSolution hδ hcont hd hs t ht
  have hpos : 0 < (g a).im * Real.exp (-(2 / δ ^ 2) * (t - a)) :=
    mul_pos h0 (Real.exp_pos _)
  exact lt_of_lt_of_le hpos hlb









lemma eventually_ne_zero_cocompact : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
  have h : Tendsto (norm : ℂ → ℝ) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  filter_upwards [h.eventually_gt_atTop 0] with z hz
  intro hz0; rw [hz0] at hz; simp at hz


lemma tendsto_inv_cocompact : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
  rw [← Metric.cobounded_eq_cocompact (α := ℂ)]; exact Filter.tendsto_inv₀_cobounded




lemma tendsto_cocompact_of_sub {f : ℂ → ℂ}
    (hf : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0)) :
    Tendsto f (cocompact ℂ) (cocompact ℂ) := by
  have goal_iff : Tendsto f (cocompact ℂ) (cocompact ℂ) ↔
      Tendsto (fun z => ‖f z‖) (cocompact ℂ) atTop := by
    rw [← Metric.cobounded_eq_cocompact (α := ℂ), tendsto_norm_atTop_iff_cobounded]
  rw [goal_iff]
  have hsub : Tendsto (fun z => ‖f z - z‖) (cocompact ℂ) (𝓝 0) := by
    have := hf.norm; simpa using this
  have hzn : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  apply tendsto_atTop_mono (f := fun z => ‖z‖ - ‖f z - z‖)
  · intro z
    have : ‖z‖ ≤ ‖f z‖ + ‖f z - z‖ :=
      calc ‖z‖ = ‖f z - (f z - z)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖f z‖ + ‖f z - z‖ := norm_sub_le _ _
    linarith
  · have : Tendsto (fun z => ‖z‖ + -‖f z - z‖) (cocompact ℂ) atTop :=
      Filter.Tendsto.atTop_add hzn (by simpa using hsub.neg)
    simpa [sub_eq_add_neg] using this


lemma eventually_ne_zero_of_tendsto_cocompact {f : ℂ → ℂ}
    (hfc : Tendsto f (cocompact ℂ) (cocompact ℂ)) : ∀ᶠ z in cocompact ℂ, f z ≠ 0 :=
  hfc.eventually eventually_ne_zero_cocompact



lemma tendsto_div_self_cocompact {f : ℂ → ℂ}
    (hf : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun z => f z / z) (cocompact ℂ) (𝓝 1) := by
  have hprod : Tendsto (fun z => (f z - z) * z⁻¹) (cocompact ℂ) (𝓝 0) := by
    have := hf.mul tendsto_inv_cocompact; simpa using this
  have h1 : Tendsto (fun z => 1 + (f z - z) * z⁻¹) (cocompact ℂ) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ)) (f := cocompact ℂ)).add hprod
    simpa using this
  apply h1.congr'
  filter_upwards [eventually_ne_zero_cocompact] with z hz0
  field_simp; ring


lemma tendsto_self_div_cocompact {f : ℂ → ℂ}
    (hf : Tendsto (fun z => f z - z) (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun z => z / f z) (cocompact ℂ) (𝓝 1) := by
  have hinv : Tendsto (fun z => (f z / z)⁻¹) (cocompact ℂ) (𝓝 (1 : ℂ)⁻¹) :=
    (tendsto_div_self_cocompact hf).inv₀ (by norm_num)
  rw [inv_one] at hinv
  apply hinv.congr'
  filter_upwards with z; rw [inv_div]







theorem hasHalfPlaneCapacity_comp {f g : ℂ → ℂ} {a b : ℝ}
    (hf : HasHalfPlaneCapacity f a) (hg : HasHalfPlaneCapacity g b) :
    HasHalfPlaneCapacity (g ∘ f) (a + b) := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  have hfc : Tendsto f (cocompact ℂ) (cocompact ℂ) := tendsto_cocompact_of_sub hf1
  refine ⟨?_, ?_⟩
  · 
    have hgf : Tendsto (fun z => g (f z) - f z) (cocompact ℂ) (𝓝 0) := hg1.comp hfc
    have : Tendsto (fun z => (g (f z) - f z) + (f z - z)) (cocompact ℂ) (𝓝 0) := by
      have := hgf.add hf1; simpa using this
    simpa [Function.comp, sub_add_sub_cancel] using this
  · 
    have hcomp : Tendsto (fun z => f z * (g (f z) - f z)) (cocompact ℂ) (𝓝 (b : ℂ)) :=
      hg2.comp hfc
    have hratio : Tendsto (fun z => z / f z) (cocompact ℂ) (𝓝 1) :=
      tendsto_self_div_cocompact hf1
    have hterm2 : Tendsto (fun z => z * (g (f z) - f z)) (cocompact ℂ) (𝓝 (b : ℂ)) := by
      have hprod : Tendsto (fun z => (z / f z) * (f z * (g (f z) - f z))) (cocompact ℂ)
          (𝓝 ((1 : ℂ) * (b : ℂ))) := hratio.mul hcomp
      rw [one_mul] at hprod
      apply hprod.congr'
      filter_upwards [eventually_ne_zero_of_tendsto_cocompact hfc] with z hz0
      field_simp
    have hsum : Tendsto (fun z => z * (g (f z) - f z) + z * (f z - z)) (cocompact ℂ)
        (𝓝 ((b : ℂ) + (a : ℂ))) := hterm2.add hf2
    have heq : (fun z => z * ((g ∘ f) z - z))
        = (fun z => z * (g (f z) - f z) + z * (f z - z)) := by
      funext z; simp only [Function.comp_apply]; ring
    rw [heq]
    have hcast : (((a + b : ℝ)) : ℂ) = (b : ℂ) + (a : ℂ) := by push_cast; ring
    rw [hcast]; exact hsum



theorem hasHalfPlaneCapacity_comp_id_right {f : ℂ → ℂ} {a : ℝ}
    (hf : HasHalfPlaneCapacity f a) : HasHalfPlaneCapacity (f ∘ id) a := by
  have := hasHalfPlaneCapacity_comp hasHalfPlaneCapacity_id hf
  rwa [zero_add] at this


theorem hasHalfPlaneCapacity_comp_id_left {f : ℂ → ℂ} {a : ℝ}
    (hf : HasHalfPlaneCapacity f a) : HasHalfPlaneCapacity (id ∘ f) a := by
  have := hasHalfPlaneCapacity_comp hf hasHalfPlaneCapacity_id
  rwa [add_zero] at this














def HasCapacityRate (g : ℝ → ℂ → ℂ) (a : ℝ) : Prop :=
  ∀ t ∈ Set.Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a * t)



lemma HasCapacityRate.hcap_zero {g : ℝ → ℂ → ℂ} {a : ℝ} (h : HasCapacityRate g a) :
    HasHalfPlaneCapacity (g 0) 0 := by
  have := h 0 Set.self_mem_Ici; rwa [mul_zero] at this






theorem hcap_linear_of_decomposition {gs gincr gt : ℂ → ℂ} {cs ct : ℝ}
    (hcompose : gt = gincr ∘ gs)
    (hs : HasHalfPlaneCapacity gs cs)
    (hincr : HasHalfPlaneCapacity gincr (ct - cs)) :
    HasHalfPlaneCapacity gt ct := by
  rw [hcompose]
  have := hasHalfPlaneCapacity_comp hs hincr
  rwa [add_sub_cancel] at this










def MonotoneHullFamily (K : ℝ → Set ℂ) : Prop :=
  (∀ t, IsCompactHull (K t)) ∧ Monotone K


theorem subset_of_monotoneHull {K : ℝ → Set ℂ} (h : MonotoneHullFamily K)
    {s t : ℝ} (hst : s ≤ t) : K s ⊆ K t :=
  h.2 hst




theorem complement_antitone_of_monotoneHull {K : ℝ → Set ℂ}
    (h : MonotoneHullFamily K) :
    Antitone (fun t => upperHalfPlane \ K t) :=
  fun _ _ hst => Set.diff_subset_diff_right (h.2 hst)


theorem isCompactHull_of_monotoneHull {K : ℝ → Set ℂ} (h : MonotoneHullFamily K)
    (t : ℝ) : IsCompactHull (K t) :=
  h.1 t

end StatMech.SLE
