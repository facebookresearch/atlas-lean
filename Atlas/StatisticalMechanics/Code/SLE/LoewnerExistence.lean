/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Code.SLE.LoewnerProps

open Complex Set Metric Filter Topology
open scoped NNReal

namespace StatMech.SLE


















theorem picard_exists_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E}
    {a L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a 0 L K) :
    ∃ α : ℝ → E, α t₀ = x₀ ∧
      (∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t) ∧
      (∀ t, α t ∈ closedBall x₀ a) := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf (mem_closedBall_self le_rfl)
  refine ⟨α.compProj, ?_, fun t ht => ?_, fun t => α.compProj_mem_closedBall hf.mul_max_le⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ ht' => α.compProj_mem_closedBall hf.mul_max_le) x₀ ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]






theorem picard_exists_ball_family_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E}
    {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E,
      (∀ x ∈ closedBall x₀ r,
        α x t₀ = x ∧
          (∀ t ∈ Icc tmin tmax,
            HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t) ∧
          (∀ t, α x t ∈ closedBall x₀ a)) ∧
      ∃ C : ℝ≥0, ∀ t ∈ Icc tmin tmax,
        LipschitzOnWith C (fun x ↦ α x t) (closedBall x₀ r) := by
  classical
  have hex (x : E) (hx : x ∈ closedBall x₀ r) :=
    ODE.FunSpace.exists_isFixedPt_next hf hx
  choose α hα using hex
  let α' : E → ℝ → E := fun x ↦ if hx : x ∈ closedBall x₀ r then
    (α x hx).compProj else 0
  refine ⟨α', ?_, ?_⟩
  · intro x hx
    have hfixed := hα x hx
    refine ⟨?_, ?_, ?_⟩
    · simp only [α', dif_pos hx, ODE.FunSpace.compProj_val]
      rw [← hfixed, ODE.FunSpace.next_apply₀]
    · intro t ht
      simp only [α', dif_pos hx]
      apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
        (α x hx).continuous_compProj.continuousOn
        (fun _ _ ↦ (α x hx).compProj_mem_closedBall hf.mul_max_le)
        x ht |>.congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hfixed]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
    · intro t
      simp only [α', dif_pos hx]
      exact (α x hx).compProj_mem_closedBall hf.mul_max_le
  · obtain ⟨C, hC⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    refine ⟨C, fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
    simp only [α', dif_pos hx, dif_pos hy, ODE.FunSpace.compProj_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact hC x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)






theorem loewner_local_flow_chart {W : ℝ → ℝ} (hW : Continuous W)
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) (t₀ : ℝ) :
    ∃ α : ℂ → ℝ → ℂ,
      (∀ z ∈ closedBall z₀ (z₀.im / 4),
        α z t₀ = z ∧
          (∀ t ∈ Icc (t₀ - z₀.im ^ 2 / 16) (t₀ + z₀.im ^ 2 / 16),
            HasDerivWithinAt (α z) (loewnerField W t (α z t))
              (Icc (t₀ - z₀.im ^ 2 / 16) (t₀ + z₀.im ^ 2 / 16)) t) ∧
          (∀ t, α z t ∈ loewnerStrip (z₀.im / 2))) ∧
      ∃ C : ℝ≥0,
        ∀ t ∈ Icc (t₀ - z₀.im ^ 2 / 16) (t₀ + z₀.im ^ 2 / 16),
          LipschitzOnWith C (fun z ↦ α z t) (closedBall z₀ (z₀.im / 4)) := by
  have hpl := isPicardLindelof_loewnerField_neighborhood hW hz₀ t₀
  obtain ⟨α, hα, C, hC⟩ := picard_exists_ball_family_lipschitz hpl
  have ha : 0 ≤ z₀.im / 2 := by positivity
  have hr : 0 ≤ z₀.im / 4 := by positivity
  have hsub : closedBall z₀ (z₀.im / 2) ⊆ loewnerStrip (z₀.im / 2) :=
    closedBall_subset_loewnerStrip (by linarith)
  refine ⟨α, ?_, C, ?_⟩
  · intro z hz
    have hz' : z ∈ closedBall z₀ (z₀.im / 4).toNNReal := by
      rwa [Real.coe_toNNReal _ hr]
    obtain ⟨hzero, hderiv, hball⟩ := hα z hz'
    refine ⟨hzero, hderiv, fun t ↦ hsub ?_⟩
    have := hball t
    rwa [Real.coe_toNNReal _ ha] at this
  · intro t ht
    have hCt := hC t ht
    simpa only [Real.coe_toNNReal _ hr] using hCt












theorem loewner_local_existence_strip_explicit {W : ℝ → ℝ}
    (hW : Continuous W) {z : ℂ}
    (hz : 0 < z.im) :
    ∃ g : ℝ → ℂ, g 0 = z ∧
      (∀ t ∈ Icc (0 : ℝ) (z.im ^ 2 / 8),
        HasDerivWithinAt g (loewnerField W t (g t))
          (Icc (0 : ℝ) (z.im ^ 2 / 8)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) (z.im ^ 2 / 8),
        g t ∈ loewnerStrip (z.im / 2)) := by
  set E : ℝ := z.im ^ 2 / 8 with hEdef
  have hE : 0 < E := by positivity
  set δ : ℝ := z.im / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hpl := isPicardLindelof_loewnerField hW hz 0
  obtain ⟨γ, hγ0, hγd, hγball⟩ := picard_exists_ball hpl
  
  have hsub : closedBall z δ ⊆ loewnerStrip δ :=
    closedBall_subset_loewnerStrip (by rw [hδdef]; linarith)
  have hcoe : ((z.im / 2).toNNReal : ℝ) = δ := by
    rw [Real.coe_toNNReal _ (by positivity), hδdef]
  have hγstrip : ∀ t, γ t ∈ loewnerStrip δ := by
    intro t
    apply hsub
    have := hγball t
    rwa [hcoe] at this
  
  have hsubIcc : Icc (0 : ℝ) E ⊆ Icc (0 - E) (0 + E) := Icc_subset_Icc (by linarith) (by linarith)
  refine ⟨γ, hγ0, ?_, fun t _ ↦ hγstrip t⟩
  simpa only [hEdef] using
    (fun t ht ↦ (hγd t (hsubIcc ht)).mono hsubIcc)




theorem loewner_local_existence_strip {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ}
    (hz : 0 < z.im) :
    ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g 0 = z ∧
      (∀ t ∈ Icc (0 : ℝ) ε,
        HasDerivWithinAt g (loewnerField W t (g t)) (Icc (0 : ℝ) ε) t) ∧
      (∀ t ∈ Icc (0 : ℝ) ε, g t ∈ loewnerStrip (z.im / 2)) := by
  obtain ⟨g, hg0, hgd, hgstrip⟩ := loewner_local_existence_strip_explicit hW hz
  exact ⟨z.im ^ 2 / 8, by positivity, g, hg0, hgd, hgstrip⟩








theorem loewner_local_existence {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ}
    (hz : 0 < z.im) :
    ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g 0 = z ∧
      (∀ t ∈ Icc (0 : ℝ) ε, HasDerivWithinAt g (loewnerField W t (g t)) (Icc (0 : ℝ) ε) t) ∧
      (∀ t ∈ Icc (0 : ℝ) ε, g t ∈ upperHalfPlane) := by
  obtain ⟨ε, hε, g, hg0, hgd, hgstrip⟩ := loewner_local_existence_strip hW hz
  set δ : ℝ := z.im / 2 with hδdef
  have hδ : 0 < δ := by positivity
  refine ⟨ε, hε, g, hg0, hgd, ?_⟩
  apply mem_upperHalfPlane_of_isLoewnerSolution hδ
  · 
    have hcont : ContinuousOn g (Icc (0 : ℝ) ε) := fun t ht => (hgd t ht).continuousWithinAt
    exact Complex.continuous_im.comp_continuousOn hcont
  · 
    intro t ht
    exact (hgd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · intro t ht; exact hgstrip t (Ico_subset_Icc_self ht)
  · rw [hg0]; exact hz








theorem loewner_solution_unique_of_strip {W : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) {ε : ℝ}
    {z : ℂ} {g h : ℝ → ℂ}
    (hg0 : g 0 = z) (hh0 : h 0 = z)
    (hgc : ContinuousOn g (Icc 0 ε))
    (hgd : ∀ t ∈ Ico 0 ε, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico 0 ε, g t ∈ loewnerStrip δ)
    (hhc : ContinuousOn h (Icc 0 ε))
    (hhd : ∀ t ∈ Ico 0 ε, HasDerivWithinAt h (loewnerField W t (h t)) (Ici t) t)
    (hhs : ∀ t ∈ Ico 0 ε, h t ∈ loewnerStrip δ) :
    EqOn g h (Icc 0 ε) :=
  loewnerSolution_unique_Icc_right hδ hgc hgd hgs hhc hhd hhs (by rw [hg0, hh0])








theorem loewner_solution_unique {W : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} {g h : ℝ → ℂ}
    (hg0 : g 0 = z) (hh0 : h 0 = z)
    (hgc : ContinuousOn g (Icc 0 ε))
    (hgd : ∀ t ∈ Ico 0 ε, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
    (hgu : ∀ t ∈ Icc 0 ε, 0 < (g t).im)
    (hhc : ContinuousOn h (Icc 0 ε))
    (hhd : ∀ t ∈ Ico 0 ε, HasDerivWithinAt h (loewnerField W t (h t)) (Ici t) t)
    (hhu : ∀ t ∈ Icc 0 ε, 0 < (h t).im) :
    EqOn g h (Icc 0 ε) := by
  
  have hcomp : IsCompact (Icc (0 : ℝ) ε) := isCompact_Icc
  have hne : (Icc (0 : ℝ) ε).Nonempty := ⟨0, by constructor <;> [rfl; linarith]⟩
  have himcg : ContinuousOn (fun t => (g t).im) (Icc 0 ε) :=
    Complex.continuous_im.comp_continuousOn hgc
  have himch : ContinuousOn (fun t => (h t).im) (Icc 0 ε) :=
    Complex.continuous_im.comp_continuousOn hhc
  obtain ⟨tg, htgmem, htgmin⟩ := hcomp.exists_isMinOn hne himcg
  obtain ⟨th, hthmem, hthmin⟩ := hcomp.exists_isMinOn hne himch
  set δ : ℝ := min (g tg).im (h th).im with hδdef
  have hδ : 0 < δ := lt_min (hgu tg htgmem) (hhu th hthmem)
  have hgs : ∀ t ∈ Ico 0 ε, g t ∈ loewnerStrip δ := by
    intro t ht
    rw [mem_loewnerStrip]
    exact le_trans (min_le_left _ _) (htgmin (Ico_subset_Icc_self ht))
  have hhs : ∀ t ∈ Ico 0 ε, h t ∈ loewnerStrip δ := by
    intro t ht
    rw [mem_loewnerStrip]
    exact le_trans (min_le_right _ _) (hthmin (Ico_subset_Icc_self ht))
  exact loewner_solution_unique_of_strip hδ hg0 hh0 hgc hgd hgs hhc hhd hhs
















theorem loewner_local_existsUnique {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ}
    (hz : 0 < z.im) :
    ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ,
      (g 0 = z ∧
        (∀ t ∈ Icc (0 : ℝ) ε, HasDerivWithinAt g (loewnerField W t (g t)) (Icc (0 : ℝ) ε) t) ∧
        (∀ t ∈ Icc (0 : ℝ) ε, g t ∈ upperHalfPlane)) ∧
      ∀ h : ℝ → ℂ, h 0 = z →
        ContinuousOn h (Icc 0 ε) →
        (∀ t ∈ Ico 0 ε, HasDerivWithinAt h (loewnerField W t (h t)) (Ici t) t) →
        (∀ t ∈ Icc 0 ε, h t ∈ upperHalfPlane) →
        EqOn g h (Icc 0 ε) := by
  obtain ⟨ε, hε, g, hg0, hgd, hgU⟩ := loewner_local_existence hW hz
  refine ⟨ε, hε, g, ⟨hg0, hgd, hgU⟩, fun h hh0 hhc hhd hhU => ?_⟩
  have hgc : ContinuousOn g (Icc (0 : ℝ) ε) := fun t ht => (hgd t ht).continuousWithinAt
  
  have hgd' : ∀ t ∈ Ico 0 ε, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t :=
    fun t ht => (hgd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  exact loewner_solution_unique hε hg0 hh0 hgc hgd' (fun t ht => hgU t ht) hhc hhd
    (fun t ht => hhU t ht)

end StatMech.SLE
