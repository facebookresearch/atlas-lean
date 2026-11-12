/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Code.SLE.Defs

open Complex Set Metric Filter Topology
open scoped NNReal

namespace StatMech.SLE






def loewnerStrip (δ : ℝ) : Set ℂ := {w : ℂ | δ ≤ w.im}

@[simp] lemma mem_loewnerStrip {δ : ℝ} {w : ℂ} : w ∈ loewnerStrip δ ↔ δ ≤ w.im := Iff.rfl


lemma loewnerStrip_subset_upperHalfPlane {δ : ℝ} (hδ : 0 < δ) :
    loewnerStrip δ ⊆ upperHalfPlane :=
  fun _ hw => mem_upperHalfPlane.mpr (lt_of_lt_of_le hδ (mem_loewnerStrip.mp hw))


lemma isClosed_loewnerStrip (δ : ℝ) : IsClosed (loewnerStrip δ) := by
  simpa only [loewnerStrip] using (isClosed_le continuous_const Complex.continuous_im)








lemma le_norm_sub_ofReal {δ : ℝ} {x : ℝ} {w : ℂ} (hw : δ ≤ w.im) :
    δ ≤ ‖w - (x : ℂ)‖ := by
  have h1 : (w - (x : ℂ)).im = w.im := by simp
  calc δ ≤ w.im := hw
    _ = (w - (x : ℂ)).im := h1.symm
    _ ≤ ‖w - (x : ℂ)‖ := Complex.im_le_norm _






lemma loewnerField_lipschitzOnWith (W : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    LipschitzOnWith ((2 / δ ^ 2).toNNReal) (loewnerField W t) (loewnerStrip δ) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro w1 hw1 w2 hw2
  simp only [mem_loewnerStrip] at hw1 hw2
  set x := W t with hx
  have hb1 : δ ≤ ‖w1 - (x : ℂ)‖ := le_norm_sub_ofReal hw1
  have hb2 : δ ≤ ‖w2 - (x : ℂ)‖ := le_norm_sub_ofReal hw2
  have hn1 : w1 - (x : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hb1; linarith
  have hn2 : w2 - (x : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hb2; linarith
  rw [loewnerField_apply, loewnerField_apply, dist_eq_norm, dist_eq_norm]
  have key : 2 / (w1 - (x : ℂ)) - 2 / (w2 - (x : ℂ))
      = 2 * (w2 - w1) / ((w1 - (x : ℂ)) * (w2 - (x : ℂ))) := by
    field_simp; ring
  rw [key, norm_div, norm_mul, norm_mul, Real.coe_toNNReal _ (by positivity)]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2, norm_sub_rev w2 w1, div_le_iff₀ (by positivity)]
  have hprod : δ ^ 2 ≤ ‖w1 - (x : ℂ)‖ * ‖w2 - (x : ℂ)‖ :=
    calc δ ^ 2 = δ * δ := sq δ
      _ ≤ ‖w1 - (x : ℂ)‖ * ‖w2 - (x : ℂ)‖ := mul_le_mul hb1 hb2 hδ.le (by positivity)
  calc 2 * ‖w1 - w2‖ = 2 / δ ^ 2 * ‖w1 - w2‖ * δ ^ 2 := by
        rw [mul_comm (2 / δ ^ 2) ‖w1 - w2‖, mul_assoc,
          div_mul_cancel₀ _ (by positivity : (δ : ℝ) ^ 2 ≠ 0), mul_comm]
    _ ≤ 2 / δ ^ 2 * ‖w1 - w2‖ * (‖w1 - (x : ℂ)‖ * ‖w2 - (x : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)



lemma loewnerField_norm_le (W : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ)
    {w : ℂ} (hw : w ∈ loewnerStrip δ) : ‖loewnerField W t w‖ ≤ 2 / δ := by
  simp only [mem_loewnerStrip] at hw
  have hb : δ ≤ ‖w - (W t : ℂ)‖ := le_norm_sub_ofReal hw
  rw [loewnerField_apply, norm_div]
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  exact div_le_div_of_nonneg_left (by norm_num) hδ hb





lemma continuousOn_loewnerField_time {W : ℝ → ℝ} (hW : Continuous W) {δ : ℝ}
    (hδ : 0 < δ) {w : ℂ} (hw : w ∈ loewnerStrip δ) (s : Set ℝ) :
    ContinuousOn (fun t => loewnerField W t w) s := by
  simp only [mem_loewnerStrip] at hw
  have hwpos : 0 < w.im := lt_of_lt_of_le hδ hw
  have hden : ∀ t, w - (W t : ℂ) ≠ 0 := by
    intro t h
    have him : (w - (W t : ℂ)).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    rw [him] at hwpos; exact lt_irrefl _ hwpos
  apply Continuous.continuousOn
  simp only [loewnerField_apply]
  exact Continuous.div continuous_const
    (continuous_const.sub (Complex.continuous_ofReal.comp hW)) hden






lemma closedBall_subset_loewnerStrip {z₀ : ℂ} {a δ : ℝ} (h : δ ≤ z₀.im - a) :
    closedBall z₀ a ⊆ loewnerStrip δ := by
  intro w hw
  simp only [mem_loewnerStrip]
  rw [mem_closedBall, dist_eq_norm] at hw
  have hle : |w.im - z₀.im| ≤ ‖w - z₀‖ := by simpa using Complex.abs_im_le_norm (w - z₀)
  have h2 : |w.im - z₀.im| ≤ a := le_trans hle hw
  linarith [(abs_le.mp h2).1]















lemma isPicardLindelof_loewnerField {W : ℝ → ℝ} (hW : Continuous W) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im) (t₀ : ℝ) :
    IsPicardLindelof (loewnerField W)
      (tmin := t₀ - (z₀.im ^ 2 / 8)) (tmax := t₀ + (z₀.im ^ 2 / 8))
      ⟨t₀, by constructor <;> nlinarith [hz₀]⟩ z₀
      (z₀.im / 2).toNNReal 0 (2 / (z₀.im / 2)).toNNReal ((2 / (z₀.im / 2) ^ 2).toNNReal) := by
  set δ : ℝ := z₀.im / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set a : ℝ := z₀.im / 2 with hadef
  have ha : 0 < a := by positivity
  set L : ℝ := 2 / δ with hLdef
  have hL : 0 < L := by positivity
  
  have hsub : closedBall z₀ a ⊆ loewnerStrip δ :=
    closedBall_subset_loewnerStrip (by rw [hadef, hδdef]; linarith)
  constructor
  · 
    intro t _
    exact (loewnerField_lipschitzOnWith W hδ t).mono
      (by rw [Real.coe_toNNReal _ ha.le]; exact hsub)
  · 
    intro w hw
    rw [Real.coe_toNNReal _ ha.le] at hw
    exact continuousOn_loewnerField_time hW hδ (hsub hw) _
  · 
    intro t _ w hw
    rw [Real.coe_toNNReal _ ha.le] at hw
    rw [Real.coe_toNNReal _ hL.le]
    exact loewnerField_norm_le W hδ t (hsub hw)
  · 
    have hcoe : ((⟨t₀, by constructor <;> nlinarith [hz₀]⟩ :
        Icc (t₀ - z₀.im ^ 2 / 8) (t₀ + z₀.im ^ 2 / 8)) : ℝ) = t₀ := rfl
    rw [NNReal.coe_zero, sub_zero, Real.coe_toNNReal _ ha.le, Real.coe_toNNReal _ hL.le, hcoe]
    have hmax : max (t₀ + z₀.im ^ 2 / 8 - t₀) (t₀ - (t₀ - z₀.im ^ 2 / 8)) = z₀.im ^ 2 / 8 := by
      rw [show t₀ + z₀.im ^ 2 / 8 - t₀ = z₀.im ^ 2 / 8 by ring,
        show t₀ - (t₀ - z₀.im ^ 2 / 8) = z₀.im ^ 2 / 8 by ring, max_self]
    rw [hmax, hLdef, hadef, hδdef]
    have hne : z₀.im ≠ 0 := ne_of_gt hz₀
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    field_simp
    linarith






lemma isPicardLindelof_loewnerField_neighborhood
    {W : ℝ → ℝ} (hW : Continuous W) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im) (t₀ : ℝ) :
    IsPicardLindelof (loewnerField W)
      (tmin := t₀ - (z₀.im ^ 2 / 16)) (tmax := t₀ + (z₀.im ^ 2 / 16))
      ⟨t₀, by constructor <;> nlinarith [sq_pos_of_pos hz₀]⟩ z₀
      (z₀.im / 2).toNNReal (z₀.im / 4).toNNReal
      (2 / (z₀.im / 2)).toNNReal ((2 / (z₀.im / 2) ^ 2).toNNReal) := by
  have hbase := isPicardLindelof_loewnerField hW hz₀ t₀
  refine hbase.shrink
    ⟨t₀, by constructor <;> nlinarith [sq_pos_of_pos hz₀]⟩ ?_ ?_ le_rfl ?_
  · nlinarith [sq_pos_of_pos hz₀]
  · nlinarith [sq_pos_of_pos hz₀]
  · have ha : 0 ≤ z₀.im / 2 := by positivity
    have hr : 0 ≤ z₀.im / 4 := by positivity
    have hL : 0 ≤ 2 / (z₀.im / 2) := by positivity
    rw [Real.coe_toNNReal _ hL, Real.coe_toNNReal _ ha,
      Real.coe_toNNReal _ hr]
    have hmax :
        max (t₀ + z₀.im ^ 2 / 16 - t₀)
          (t₀ - (t₀ - z₀.im ^ 2 / 16)) = z₀.im ^ 2 / 16 := by
      rw [show t₀ + z₀.im ^ 2 / 16 - t₀ = z₀.im ^ 2 / 16 by ring,
        show t₀ - (t₀ - z₀.im ^ 2 / 16) = z₀.im ^ 2 / 16 by ring,
        max_self]
    rw [hmax]
    field_simp
    linarith









theorem exists_isLoewnerSolutionOn_Icc {W : ℝ → ℝ} (hW : Continuous W) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g t₀ = z₀ ∧
      ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
        HasDerivWithinAt g (loewnerField W t (g t)) (Icc (t₀ - ε) (t₀ + ε)) t := by
  have hpl := isPicardLindelof_loewnerField hW hz₀ t₀
  obtain ⟨g, hg0, hgd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨z₀.im ^ 2 / 8, by positivity, g, hg0, hgd⟩




theorem exists_isLoewnerSolution_hasDerivAt {W : ℝ → ℝ} (hW : Continuous W) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g t₀ = z₀ ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt g (loewnerField W t (g t)) t := by
  obtain ⟨ε, hε, g, hg0, hgd⟩ := exists_isLoewnerSolutionOn_Icc hW hz₀ t₀
  refine ⟨ε, hε, g, hg0, fun t ht => ?_⟩
  exact (hgd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)





theorem exists_isLoewnerSolutionOn {W : ℝ → ℝ} (hW : Continuous W) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ → ℂ, g t₀ z₀ = z₀ ∧
      IsLoewnerSolutionOn W g z₀ (Icc (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨ε, hε, γ, hγ0, hγd⟩ := exists_isLoewnerSolutionOn_Icc hW hz₀ t₀
  refine ⟨ε, hε, fun t _ => γ t, hγ0, fun t ht => ?_⟩
  simpa only [IsLoewnerSolutionOn] using hγd t ht












theorem loewnerSolution_unique_Ioo {W : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) {g h : ℝ → ℂ}
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (loewnerField W t (g t)) t ∧ g t ∈ loewnerStrip δ)
    (hh : ∀ t ∈ Ioo a b, HasDerivAt h (loewnerField W t (h t)) t ∧ h t ∈ loewnerStrip δ)
    (heq : g t₀ = h t₀) :
    EqOn g h (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo
    (v := loewnerField W) (s := fun _ => loewnerStrip δ) (K := (2 / δ ^ 2).toNNReal)
    (fun t _ => loewnerField_lipschitzOnWith W hδ t) ht₀ hg hh heq






theorem loewnerSolution_unique_Icc_right {W : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) {a b : ℝ}
    {g h : ℝ → ℂ}
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico a b, g t ∈ loewnerStrip δ)
    (hh : ContinuousOn h (Icc a b))
    (hh' : ∀ t ∈ Ico a b, HasDerivWithinAt h (loewnerField W t (h t)) (Ici t) t)
    (hhs : ∀ t ∈ Ico a b, h t ∈ loewnerStrip δ)
    (heq : g a = h a) :
    EqOn g h (Icc a b) :=
  ODE_solution_unique_of_mem_Icc_right
    (v := loewnerField W) (s := fun _ => loewnerStrip δ) (K := (2 / δ ^ 2).toNNReal)
    (fun t _ => loewnerField_lipschitzOnWith W hδ t) hg hg' hgs hh hh' hhs heq





theorem exists_unique_loewnerSolution {W : ℝ → ℝ} (hW : Continuous W) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, (g t₀ = z₀ ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt g (loewnerField W t (g t)) t) ∧
      ∀ h : ℝ → ℂ, h t₀ = z₀ →
        (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasDerivAt h (loewnerField W t (h t)) t ∧ h t ∈ loewnerStrip (z₀.im / 2)) →
        (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), g t ∈ loewnerStrip (z₀.im / 2)) →
        EqOn g h (Ioo (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨ε, hε, g, hg0, hgd⟩ := exists_isLoewnerSolution_hasDerivAt hW hz₀ t₀
  refine ⟨ε, hε, g, ⟨hg0, hgd⟩, fun h hh0 hhprop hgstrip => ?_⟩
  have ht₀mem : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  refine loewnerSolution_unique_Ioo (by positivity) ht₀mem
    (fun t ht => ⟨hgd t ht, hgstrip t ht⟩) (fun t ht => hhprop t ht) ?_
  rw [hg0, hh0]

end StatMech.SLE
