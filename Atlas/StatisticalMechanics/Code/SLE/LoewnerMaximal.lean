/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.SLE.LoewnerExistence

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace StatMech.SLE



theorem positiveOn_Icc_of_deriv_nonneg_while_pos
    {T : ℝ} {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc (0 : ℝ) T)) (hzero : 0 < f 0)
    (hderiv : ∀ s ∈ Ioo (0 : ℝ) T, 0 < f s →
      ∃ v : ℝ, HasDerivAt f v s ∧ 0 ≤ v) :
    ∀ s ∈ Icc (0 : ℝ) T, 0 < f s := by
  intro s hs
  by_contra hnot
  have hfs : f s ≤ 0 := le_of_not_gt hnot
  have hspos : 0 < s := by
    rcases hs.1.eq_or_lt with rfl | hspos
    · exact False.elim ((not_lt_of_ge hfs) hzero)
    · exact hspos
  have hcontS : ContinuousOn f (Icc (0 : ℝ) s) :=
    hcont.mono (Icc_subset_Icc_right hs.2)
  have hzeroMem : (0 : ℝ) ∈ Icc (f s) (f 0) := ⟨hfs, hzero.le⟩
  obtain ⟨r, hr, hre⟩ := intermediate_value_Icc' hspos.le hcontS hzeroMem
  let Z : Set ℝ := {q | q ∈ Icc (0 : ℝ) s ∧ f q = 0}
  have hZclosed : IsClosed Z := by
    dsimp [Z]
    exact isClosed_Icc.isClosed_eq hcontS continuousOn_const
  have hZcompact : IsCompact Z :=
    IsCompact.of_isClosed_subset isCompact_Icc hZclosed (fun _ hq ↦ hq.1)
  have hZnonempty : Z.Nonempty := ⟨r, hr, hre⟩
  obtain ⟨r₀, hr₀Z, hr₀min⟩ :=
    hZcompact.exists_isMinOn hZnonempty continuousOn_id
  have hr₀pos : 0 < r₀ := by
    have hr₀nonneg : 0 ≤ r₀ := hr₀Z.1.1
    rcases hr₀nonneg.eq_or_lt with hr₀zero | hr₀pos
    · rw [← hr₀zero] at hr₀Z
      exact False.elim (hzero.ne' hr₀Z.2)
    · exact hr₀pos
  have hposBefore : ∀ q ∈ Ioo (0 : ℝ) r₀, 0 < f q := by
    intro q hq
    by_contra hqnot
    have hfq : f q ≤ 0 := le_of_not_gt hqnot
    have hcontQ : ContinuousOn f (Icc (0 : ℝ) q) :=
      hcont.mono (Icc_subset_Icc_right
        (hq.2.le.trans (hr₀Z.1.2.trans hs.2)))
    have hmem : (0 : ℝ) ∈ Icc (f q) (f 0) := ⟨hfq, hzero.le⟩
    obtain ⟨p, hp, hpe⟩ := intermediate_value_Icc' hq.1.le hcontQ hmem
    have hpZ : p ∈ Z :=
      ⟨⟨hp.1, hp.2.trans (hq.2.le.trans hr₀Z.1.2)⟩, hpe⟩
    exact (not_lt_of_ge (hr₀min hpZ)) (hp.2.trans_lt hq.2)
  have hmono : MonotoneOn f (Icc (0 : ℝ) r₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r₀)
      (hcont.mono (Icc_subset_Icc_right (hr₀Z.1.2.trans hs.2)))
    · rw [interior_Icc]
      intro q hq
      exact (hderiv q ⟨hq.1, hq.2.trans_le (hr₀Z.1.2.trans hs.2)⟩
        (hposBefore q hq)).choose_spec.1.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro q hq
      obtain ⟨v, hv, hvnonneg⟩ :=
        hderiv q ⟨hq.1, hq.2.trans_le (hr₀Z.1.2.trans hs.2)⟩
          (hposBefore q hq)
      rw [hv.deriv]
      exact hvnonneg
  have := hmono ⟨le_rfl, hr₀pos.le⟩ ⟨hr₀pos.le, le_rfl⟩ hr₀Z.1.1
  rw [hr₀Z.2] at this
  linarith



structure LoewnerForwardSolution (W : ℝ → ℝ) (z : ℂ) (T : ℝ) where
  curve : ℝ → ℂ
  initial : curve 0 = z
  deriv : ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt curve (loewnerField W t (curve t)) (Icc (0 : ℝ) T) t
  upper : ∀ t ∈ Icc (0 : ℝ) T, curve t ∈ upperHalfPlane


def LoewnerForwardSolution.restrict {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (g : LoewnerForwardSolution W z T) {S : ℝ} (hST : S ≤ T) :
    LoewnerForwardSolution W z S where
  curve := g.curve
  initial := g.initial
  deriv := by
    intro t ht
    exact (g.deriv t ⟨ht.1, ht.2.trans hST⟩).mono (Icc_subset_Icc_right hST)
  upper := by
    intro t ht
    exact g.upper t ⟨ht.1, ht.2.trans hST⟩


theorem LoewnerForwardSolution.continuousOn {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (g : LoewnerForwardSolution W z T) : ContinuousOn g.curve (Icc (0 : ℝ) T) :=
  fun t ht ↦ (g.deriv t ht).continuousWithinAt



def LoewnerForwardSolution.reflect {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (g : LoewnerForwardSolution W z T) :
    LoewnerForwardSolution (fun t ↦ -W t) (loewnerReflection z) T where
  curve := fun t ↦ loewnerReflection (g.curve t)
  initial := by simp [g.initial]
  deriv := by
    intro t ht
    have hconj : HasDerivWithinAt (fun s ↦ conj (g.curve s))
        (conj (loewnerField W t (g.curve t))) (Icc (0 : ℝ) T) t := by
      simpa only [Complex.conjCLE_apply] using
        Complex.conjCLE.hasFDerivAt.comp_hasDerivWithinAt t (g.deriv t ht)
    have hreflect : HasDerivWithinAt
        (fun s ↦ loewnerReflection (g.curve s))
        (loewnerReflection (loewnerField W t (g.curve t))) (Icc (0 : ℝ) T) t := by
      simpa only [loewnerReflection, Pi.neg_apply] using hconj.neg
    simpa only [loewnerReflection_loewnerField] using hreflect
  upper := by
    intro t ht
    rw [mem_upperHalfPlane]
    simpa only [loewnerReflection_im] using
      mem_upperHalfPlane.mp (g.upper t ht)



theorem LoewnerForwardSolution.re_gt_driverBarrier
    {W : ℝ → ℝ} {z : ℂ} {T M d : ℝ}
    (g : LoewnerForwardSolution W z T) (hd : 0 < d)
    (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M)
    (hz : M + d ≤ z.re) :
    ∀ s ∈ Icc (0 : ℝ) T, M + d / 2 < (g.curve s).re := by
  let f : ℝ → ℝ := fun s ↦ (g.curve s).re - (M + d / 2)
  have hfcont : ContinuousOn f (Icc (0 : ℝ) T) :=
    (Complex.continuous_re.comp_continuousOn g.continuousOn).sub continuousOn_const
  have hfzero : 0 < f 0 := by
    dsimp [f]
    rw [g.initial]
    linarith
  have hfderiv : ∀ s ∈ Ioo (0 : ℝ) T, 0 < f s →
      ∃ v : ℝ, HasDerivAt f v s ∧ 0 ≤ v := by
    intro s hs hfs
    have hsIcc : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hcurve := (g.deriv s hsIcc).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hreDeriv : HasDerivAt f (loewnerField W s (g.curve s)).re s := by
      simpa [f] using (hasDerivAt_re_of hcurve).sub_const (M + d / 2)
    have hnum : 0 < (g.curve s).re - W s := by
      have hWs := hW s hsIcc
      dsimp [f] at hfs
      linarith
    have hsubne : g.curve s - (W s : ℂ) ≠ 0 := by
      intro heq
      have himzero : (g.curve s).im = 0 := by
        simpa using congrArg Complex.im heq
      exact (mem_upperHalfPlane.mp (g.upper s hsIcc)).ne' himzero
    have hden : 0 < Complex.normSq (g.curve s - (W s : ℂ)) :=
      Complex.normSq_pos.mpr hsubne
    refine ⟨(loewnerField W s (g.curve s)).re, hreDeriv, ?_⟩
    rw [re_loewnerField]
    exact (div_pos (mul_pos (by norm_num) hnum) hden).le
  have hpos := positiveOn_Icc_of_deriv_nonneg_while_pos hfcont hfzero hfderiv
  intro s hs
  exact sub_pos.mp (hpos s hs)



theorem LoewnerForwardSolution.im_ge_exp_of_driverBarrier
    {W : ℝ → ℝ} {z : ℂ} {T M d : ℝ}
    (g : LoewnerForwardSolution W z T) (hd : 0 < d)
    (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M)
    (hz : M + d ≤ z.re) :
    ∀ s ∈ Icc (0 : ℝ) T,
      z.im * Real.exp (-(2 / (d / 2) ^ 2) * s) ≤ (g.curve s).im := by
  have hre := g.re_gt_driverBarrier hd hW hz
  have hδ : 0 < d / 2 := by positivity
  have hden : ∀ s ∈ Ico (0 : ℝ) T,
      (d / 2) ^ 2 ≤ Complex.normSq (g.curve s - (W s : ℂ)) := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self hs
    have hWs := hW s hsIcc
    have hgap : d / 2 < (g.curve s).re - W s := by
      linarith [hre s hsIcc]
    rw [Complex.normSq_apply]
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
    nlinarith [sq_nonneg ((g.curve s).im - 0)]
  have him := im_ge_exp_mul_of_normSq_ge hδ
    (Complex.continuous_im.comp_continuousOn g.continuousOn)
    (fun s hs ↦ (g.deriv s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (fun s hs ↦ (mem_upperHalfPlane.mp (g.upper s
      (Ico_subset_Icc_self hs))).le)
    hden
  intro s hs
  have := him s hs
  rw [g.initial, sub_zero] at this
  exact this



theorem LoewnerForwardSolution.im_antitoneOn
    {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (g : LoewnerForwardSolution W z T) :
    AntitoneOn (fun t ↦ (g.curve t).im) (Icc (0 : ℝ) T) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
  · exact Complex.continuous_im.comp_continuousOn g.continuousOn
  · rw [interior_Icc]
    intro t ht
    exact ((hasDerivAt_im_of ((g.deriv t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))).differentiableAt).differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [(hasDerivAt_im_of ((g.deriv t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))).deriv]
    exact im_loewnerField_nonpos
      (mem_upperHalfPlane.mp (g.upper t ⟨ht.1.le, ht.2.le⟩)).le



theorem LoewnerForwardSolution.hasDerivWithinAt_Ici {W : ℝ → ℝ} {z : ℂ}
    {T : ℝ} (g : LoewnerForwardSolution W z T) :
    ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt g.curve (loewnerField W t (g.curve t)) (Ici t) t := by
  intro t ht
  exact (g.deriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht)



theorem LoewnerForwardSolution.eqOn_overlap {W : ℝ → ℝ} {z : ℂ} {S T : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (g : LoewnerForwardSolution W z S) (h : LoewnerForwardSolution W z T) :
    EqOn g.curve h.curve (Icc (0 : ℝ) (min S T)) := by
  have hmin : 0 < min S T := lt_min hS hT
  let g' := g.restrict (min_le_left S T)
  let h' := h.restrict (min_le_right S T)
  exact loewner_solution_unique hmin g'.initial h'.initial
    g'.continuousOn g'.hasDerivWithinAt_Ici
    (fun t ht ↦ mem_upperHalfPlane.mp (g'.upper t ht))
    h'.continuousOn h'.hasDerivWithinAt_Ici
    (fun t ht ↦ mem_upperHalfPlane.mp (h'.upper t ht))




theorem LoewnerForwardSolution.initial_eq_of_eq_at
    {W : ℝ → ℝ} {z w : ℂ} {S T t : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (g : LoewnerForwardSolution W z S) (h : LoewnerForwardSolution W w T)
    (ht0 : 0 < t) (htS : t < S) (htT : t < T)
    (heq : g.curve t = h.curve t) : z = w := by
  let U := min S T
  have hU : 0 < U := lt_min hS hT
  let g' := g.restrict (min_le_left S T)
  let h' := h.restrict (min_le_right S T)
  have hcomp : IsCompact (Icc (0 : ℝ) U) := isCompact_Icc
  have hne : (Icc (0 : ℝ) U).Nonempty := ⟨0, le_rfl, hU.le⟩
  have himcg : ContinuousOn (fun u ↦ (g'.curve u).im) (Icc 0 U) :=
    Complex.continuous_im.comp_continuousOn g'.continuousOn
  have himch : ContinuousOn (fun u ↦ (h'.curve u).im) (Icc 0 U) :=
    Complex.continuous_im.comp_continuousOn h'.continuousOn
  obtain ⟨ug, hugmem, hugmin⟩ := hcomp.exists_isMinOn hne himcg
  obtain ⟨uh, huhmem, huhmin⟩ := hcomp.exists_isMinOn hne himch
  let δ : ℝ := min (g'.curve ug).im (h'.curve uh).im
  have hδ : 0 < δ := lt_min
    (mem_upperHalfPlane.mp (g'.upper ug hugmem))
    (mem_upperHalfPlane.mp (h'.upper uh huhmem))
  have hg : ∀ u ∈ Ioo (0 : ℝ) U,
      HasDerivAt g'.curve (loewnerField W u (g'.curve u)) u ∧
        g'.curve u ∈ loewnerStrip δ := by
    intro u hu
    refine ⟨(g'.deriv u ⟨hu.1.le, hu.2.le⟩).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2), ?_⟩
    rw [mem_loewnerStrip]
    exact (min_le_left _ _).trans (hugmin (Ioo_subset_Icc_self hu))
  have hh : ∀ u ∈ Ioo (0 : ℝ) U,
      HasDerivAt h'.curve (loewnerField W u (h'.curve u)) u ∧
        h'.curve u ∈ loewnerStrip δ := by
    intro u hu
    refine ⟨(h'.deriv u ⟨hu.1.le, hu.2.le⟩).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2), ?_⟩
    rw [mem_loewnerStrip]
    exact (min_le_right _ _).trans (huhmin (Ioo_subset_Icc_self hu))
  have htU : t ∈ Ioo (0 : ℝ) U := ⟨ht0, lt_min htS htT⟩
  have heqOpen : EqOn g'.curve h'.curve (Ioo (0 : ℝ) U) :=
    loewnerSolution_unique_Ioo hδ htU hg hh heq
  have heqClosed : EqOn g'.curve h'.curve (Icc (0 : ℝ) U) :=
    heqOpen.of_subset_closure g'.continuousOn h'.continuousOn
      Ioo_subset_Icc_self (by rw [closure_Ioo hU.ne])
  calc
    z = g'.curve 0 := g'.initial.symm
    _ = h'.curve 0 := heqClosed ⟨le_rfl, hU.le⟩
    _ = w := h'.initial



def LoewnerForwardSolution.timeShift
    {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (g : LoewnerForwardSolution W z T) (s : ℝ) (hs0 : 0 ≤ s) :
    LoewnerForwardSolution (fun u ↦ W (s + u)) (g.curve s) (T - s) where
  curve := fun u ↦ g.curve (s + u)
  initial := by simp
  deriv := by
    intro u hu
    have hmap : MapsTo (fun r : ℝ ↦ s + r) (Icc (0 : ℝ) (T - s)) (Icc 0 T) := by
      intro r hr
      change 0 ≤ s + r ∧ s + r ≤ T
      constructor <;> linarith [hr.1, hr.2]
    have hsu : s + u ∈ Icc (0 : ℝ) T := hmap hu
    have hinner : HasDerivWithinAt (fun r : ℝ ↦ s + r) 1
        (Icc (0 : ℝ) (T - s)) u := by
      simpa using ((hasDerivAt_const u s).add (hasDerivAt_id u)).hasDerivWithinAt
    simpa only [Function.comp_def, one_smul] using
      (g.deriv (s + u) hsu).scomp u hinner hmap
  upper := by
    intro u hu
    exact g.upper (s + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩




theorem exists_loewnerBackwardSegment
    {W : ℝ → ℝ} (hW : Continuous W) {s u : ℝ} (hu : 0 ≤ u)
    {y : ℂ} (hy : 0 < y.im) (hshort : u < y.im ^ 2 / 16) :
    ∃ x : ℂ, ∃ g : LoewnerForwardSolution (fun r ↦ W (s + r)) x u,
      g.curve u = y := by
  obtain ⟨α, hα, C, hC⟩ := loewner_local_flow_chart hW hy (s + u)
  have hyball : y ∈ closedBall y (y.im / 4) :=
    mem_closedBall_self (by positivity)
  obtain ⟨hendpoint, hderiv, hstrip⟩ := hα y hyball
  have hmap : MapsTo (fun r : ℝ ↦ s + r) (Icc (0 : ℝ) u)
      (Icc (s + u - y.im ^ 2 / 16) (s + u + y.im ^ 2 / 16)) := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  let x : ℂ := α y s
  let g : LoewnerForwardSolution (fun r ↦ W (s + r)) x u :=
    { curve := fun r ↦ α y (s + r)
      initial := by simp [x]
      deriv := by
        intro r hr
        have hinner : HasDerivWithinAt (fun q : ℝ ↦ s + q) 1
            (Icc (0 : ℝ) u) r := by
          simpa using ((hasDerivAt_const r s).add (hasDerivAt_id r)).hasDerivWithinAt
        have hd := (hderiv (s + r) (hmap hr)).scomp r hinner hmap
        simpa only [Function.comp_def, one_smul] using hd
      upper := by
        intro r hr
        exact loewnerStrip_subset_upperHalfPlane (by positivity) (hstrip (s + r)) }
  refine ⟨x, g, ?_⟩
  simpa [g] using hendpoint



noncomputable def LoewnerForwardSolution.appendCurve
    {W : ℝ → ℝ} {z : ℂ} {S T : ℝ}
    (g : LoewnerForwardSolution W z S)
    (h : LoewnerForwardSolution (fun u ↦ W (S + u)) (g.curve S) T) :
    ℝ → ℂ := fun t ↦ if t ≤ S then g.curve t else h.curve (t - S)


noncomputable def LoewnerForwardSolution.append
    {W : ℝ → ℝ} {z : ℂ} {S T : ℝ}
    (g : LoewnerForwardSolution W z S)
    (h : LoewnerForwardSolution (fun u ↦ W (S + u)) (g.curve S) T)
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    LoewnerForwardSolution W z (S + T) where
  curve := g.appendCurve h
  initial := by simp [LoewnerForwardSolution.appendCurve, hS, g.initial]
  deriv := by
    intro t ht
    by_cases hleft : t < S
    · have htS : t ∈ Icc (0 : ℝ) S := ⟨ht.1, hleft.le⟩
      have hlocal : Icc (0 : ℝ) S ∈ 𝓝[Icc (0 : ℝ) (S + T)] t := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hleft)] with x hx hxs
        exact ⟨hx.1, hxs⟩
      have hd := (g.deriv t htS).mono_of_mem_nhdsWithin hlocal
      have happ : (g.appendCurve h) t = g.curve t := by
        simp [LoewnerForwardSolution.appendCurve, hleft.le]
      rw [happ]
      apply hd.congr_of_eventuallyEq_of_mem _ ht
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hleft)] with x hx
      change x ≤ S at hx
      simp [LoewnerForwardSolution.appendCurve, hx]
    · by_cases hright : S < t
      · have hsub : t - S ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [ht.2]⟩
        let k : ℝ → ℂ := fun x ↦ h.curve (x - S)
        have hmap : MapsTo (fun x : ℝ ↦ x - S) (Icc S (S + T)) (Icc 0 T) := by
          intro x hx
          change 0 ≤ x - S ∧ x - S ≤ T
          constructor <;> linarith [hx.1, hx.2]
        have hinner : HasDerivWithinAt (fun x : ℝ ↦ x - S) 1
            (Icc S (S + T)) t := by
          simpa using ((hasDerivAt_id t).sub_const S).hasDerivWithinAt
        have hk : HasDerivWithinAt k
            (loewnerField W t (k t)) (Icc S (S + T)) t := by
          have hraw := (h.deriv (t - S) hsub).scomp t hinner hmap
          convert hraw using 1
          simp only [one_smul]
          change loewnerField W t (h.curve (t - S)) =
            loewnerField W (S + (t - S)) (h.curve (t - S))
          rw [show S + (t - S) = t by ring]
        have hlocal : Icc S (S + T) ∈ 𝓝[Icc (0 : ℝ) (S + T)] t := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hright)] with x hx hxs
          exact ⟨hxs, hx.2⟩
        have hk' := hk.mono_of_mem_nhdsWithin hlocal
        have happ : (g.appendCurve h) t = k t := by
          simp [LoewnerForwardSolution.appendCurve, k, not_le.mpr hright]
        rw [happ]
        apply hk'.congr_of_eventuallyEq_of_mem _ ht
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hright)] with x hx
        change S ≤ x at hx
        rcases hx.eq_or_lt with rfl | hxlt
        · simp [LoewnerForwardSolution.appendCurve, k, h.initial]
        · simp [LoewnerForwardSolution.appendCurve, k, not_le.mpr hxlt]
      · have hts : t = S := le_antisymm (not_lt.mp hright) (not_lt.mp hleft)
        subst t
        let k : ℝ → ℂ := fun x ↦ h.curve (x - S)
        have hmap : MapsTo (fun x : ℝ ↦ x - S) (Icc S (S + T)) (Icc 0 T) := by
          intro x hx
          change 0 ≤ x - S ∧ x - S ≤ T
          constructor <;> linarith [hx.1, hx.2]
        have hinner : HasDerivWithinAt (fun x : ℝ ↦ x - S) 1
            (Icc S (S + T)) S := by
          simpa using ((hasDerivAt_id S).sub_const S).hasDerivWithinAt
        have hk : HasDerivWithinAt k
            (loewnerField W S (k S)) (Icc S (S + T)) S := by
          have hh := h.deriv 0 ⟨le_rfl, hT⟩
          have hraw := hh.scomp_of_eq S hinner hmap (by ring : (0 : ℝ) = S - S)
          convert hraw using 1
          simp [k]
        have hkvalue : k S = g.curve S := by simp [k, h.initial]
        have happLeft : EqOn (g.appendCurve h) g.curve (Icc (0 : ℝ) S) := by
          intro x hx
          simp [LoewnerForwardSolution.appendCurve, hx.2]
        have happRight : EqOn (g.appendCurve h) k (Icc S (S + T)) := by
          intro x hx
          rcases hx.1.eq_or_lt with rfl | hxlt
          · simp [LoewnerForwardSolution.appendCurve, k, h.initial]
          · simp [LoewnerForwardSolution.appendCurve, k, not_le.mpr hxlt]
        have hdl : HasDerivWithinAt (g.appendCurve h)
            (loewnerField W S ((g.appendCurve h) S)) (Icc (0 : ℝ) S) S := by
          have happS : (g.appendCurve h) S = g.curve S :=
            happLeft ⟨hS, le_rfl⟩
          rw [happS]
          exact (g.deriv S ⟨hS, le_rfl⟩).congr happLeft happS
        have hdr : HasDerivWithinAt (g.appendCurve h)
            (loewnerField W S ((g.appendCurve h) S)) (Icc S (S + T)) S := by
          have hk' : HasDerivWithinAt k
              (loewnerField W S (g.curve S)) (Icc S (S + T)) S := by
            rwa [hkvalue] at hk
          have happS : (g.appendCurve h) S = g.curve S := by
            simp [LoewnerForwardSolution.appendCurve]
          rw [happS]
          exact hk'.congr happRight (happRight ⟨le_rfl, by linarith⟩)
        have hdu := hdl.union hdr
        have hsets : Icc (0 : ℝ) S ∪ Icc S (S + T) = Icc 0 (S + T) := by
          ext x
          change ((0 ≤ x ∧ x ≤ S) ∨ (S ≤ x ∧ x ≤ S + T)) ↔
            (0 ≤ x ∧ x ≤ S + T)
          constructor
          · intro hx
            rcases hx with hx | hx
            · constructor <;> linarith [hx.1, hx.2, hT]
            · constructor <;> linarith [hx.1, hx.2, hS]
          · intro hx
            by_cases hxs : x ≤ S
            · exact Or.inl ⟨hx.1, hxs⟩
            · exact Or.inr ⟨le_of_not_ge hxs, hx.2⟩
        rwa [hsets] at hdu
  upper := by
    intro t ht
    by_cases hts : t ≤ S
    · simp only [LoewnerForwardSolution.appendCurve, if_pos hts]
      exact g.upper t ⟨ht.1, hts⟩
    · simp only [LoewnerForwardSolution.appendCurve, if_neg hts]
      exact h.upper (t - S) ⟨by linarith, by linarith [ht.2]⟩


theorem LoewnerForwardSolution.append_terminal
    {W : ℝ → ℝ} {z : ℂ} {S T : ℝ}
    (g : LoewnerForwardSolution W z S)
    (h : LoewnerForwardSolution (fun u ↦ W (S + u)) (g.curve S) T)
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    (g.append h hS hT).curve (S + T) = h.curve T := by
  rcases hT.eq_or_lt with hT0 | hT0
  · subst T
    simp [LoewnerForwardSolution.append, LoewnerForwardSolution.appendCurve,
      h.initial]
  · have hnot : ¬ S + T ≤ S := by linarith
    simp [LoewnerForwardSolution.append, LoewnerForwardSolution.appendCurve,
      hnot]



theorem exists_loewnerBackwardSolution_steps
    {W : ℝ → ℝ} (hW : Continuous W) {u : ℝ} (hu : 0 ≤ u)
    (n : ℕ) {y : ℂ} (hy : 0 < y.im) (hshort : u < y.im ^ 2 / 16) :
    ∃ x : ℂ, ∃ g : LoewnerForwardSolution W x ((n : ℝ) * u),
      g.curve ((n : ℝ) * u) = y := by
  induction n generalizing y with
  | zero =>
      simp only [Nat.cast_zero, zero_mul]
      let g : LoewnerForwardSolution W y (((0 : ℕ) : ℝ) * u) :=
        { curve := fun _ ↦ y
          initial := rfl
          deriv := by
            intro r hr
            simp only [Nat.cast_zero, zero_mul] at hr ⊢
            have hr0 : r = 0 := le_antisymm hr.2 hr.1
            subst r
            rw [show Icc (0 : ℝ) 0 = {0} by simp]
            exact HasFDerivWithinAt.singleton
          upper := by
            intro r hr
            simp only [Nat.cast_zero, zero_mul] at hr
            have hr0 : r = 0 := le_antisymm hr.2 hr.1
            subst r
            exact mem_upperHalfPlane.mpr hy }
      exact ⟨y, g, rfl⟩
  | succ n ih =>
      obtain ⟨xmid, hlast, hlastEnd⟩ :=
        exists_loewnerBackwardSegment hW (s := (n : ℝ) * u) hu hy hshort
      have hxmid : 0 < xmid.im := by
        rw [← hlast.initial]
        exact mem_upperHalfPlane.mp (hlast.upper 0 ⟨le_rfl, hu⟩)
      have him : y.im ≤ xmid.im := by
        have hant := hlast.im_antitoneOn
          (show (0 : ℝ) ∈ Icc 0 u from ⟨le_rfl, hu⟩)
          (show u ∈ Icc 0 u from ⟨hu, le_rfl⟩) hu
        change (hlast.curve u).im ≤ (hlast.curve 0).im at hant
        rw [hlast.initial, hlastEnd] at hant
        exact hant
      have hshortMid : u < xmid.im ^ 2 / 16 := by
        calc
          u < y.im ^ 2 / 16 := hshort
          _ ≤ xmid.im ^ 2 / 16 := by gcongr
      obtain ⟨x, gprefix, hprefixEnd⟩ := ih hxmid hshortMid
      let hlast' : LoewnerForwardSolution
          (fun r ↦ W ((n : ℝ) * u + r))
          (gprefix.curve ((n : ℝ) * u)) u :=
        { curve := hlast.curve
          initial := hlast.initial.trans hprefixEnd.symm
          deriv := hlast.deriv
          upper := hlast.upper }
      have hlast'End : hlast'.curve u = y := by
        simpa [hlast'] using hlastEnd
      let g := gprefix.append hlast'
        (mul_nonneg (Nat.cast_nonneg n) hu) hu
      have gEnd : g.curve ((n : ℝ) * u + u) = y :=
        (gprefix.append_terminal hlast'
          (mul_nonneg (Nat.cast_nonneg n) hu) hu).trans hlast'End
      rw [show (((n + 1 : ℕ) : ℝ) * u) = (n : ℝ) * u + u by
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]]
      exact ⟨x, g, gEnd⟩



theorem exists_loewnerBackwardSolution
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : 0 < y.im) :
    ∃ x : ℂ, ∃ g : LoewnerForwardSolution W x t, g.curve t = y := by
  obtain ⟨n, hn⟩ := exists_nat_gt (16 * t / y.im ^ 2)
  have hquot : 0 ≤ 16 * t / y.im ^ 2 := by positivity
  have hn0 : 0 < (n : ℝ) := hquot.trans_lt hn
  let u : ℝ := t / (n : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hnu : (n : ℝ) * u = t := by
    dsimp [u]
    field_simp
  have hshort : u < y.im ^ 2 / 16 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 16 * t < (n : ℝ) * y.im ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hy)).mp hn
    nlinarith
  obtain ⟨x, g, hg⟩ :=
    exists_loewnerBackwardSolution_steps hW hu n hy hshort
  rw [← hnu]
  exact ⟨x, g, hg⟩




theorem exists_loewnerForwardSolution_steps_of_driverBarrier
    {W : ℝ → ℝ} (hWcont : Continuous W) {T M d u : ℝ}
    (hd : 0 < d) (hu : 0 ≤ u)
    {z : ℂ} (hzim : 0 < z.im) (hzre : M + d ≤ z.re)
    (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M)
    (hstep : u <
      (z.im * Real.exp (-(2 / (d / 2) ^ 2) * T)) ^ 2 / 8)
    (n : ℕ) (hnT : (n : ℝ) * u ≤ T) :
    Nonempty (LoewnerForwardSolution W z ((n : ℝ) * u)) := by
  induction n with
  | zero =>
      let g : LoewnerForwardSolution W z (((0 : ℕ) : ℝ) * u) :=
        { curve := fun _ ↦ z
          initial := rfl
          deriv := by
            intro r hr
            simp only [Nat.cast_zero, zero_mul] at hr ⊢
            have hr0 : r = 0 := le_antisymm hr.2 hr.1
            subst r
            rw [show Icc (0 : ℝ) 0 = {0} by simp]
            exact HasFDerivWithinAt.singleton
          upper := by
            intro r hr
            simp only [Nat.cast_zero, zero_mul] at hr
            have hr0 : r = 0 := le_antisymm hr.2 hr.1
            subst r
            exact mem_upperHalfPlane.mpr hzim }
      exact ⟨g⟩
  | succ n ih =>
      let s : ℝ := (n : ℝ) * u
      have hs0 : 0 ≤ s := mul_nonneg (Nat.cast_nonneg n) hu
      have hsT : s ≤ T := by
        dsimp [s]
        calc
          (n : ℝ) * u ≤ ((n + 1 : ℕ) : ℝ) * u := by
            gcongr
            exact_mod_cast Nat.le_succ n
          _ ≤ T := hnT
      obtain ⟨g⟩ := ih hsT
      let y : ℂ := g.curve s
      have hyUpper : y ∈ upperHalfPlane := g.upper s ⟨hs0, le_rfl⟩
      have hypos : 0 < y.im := mem_upperHalfPlane.mp hyUpper
      have hWprefix : ∀ r ∈ Icc (0 : ℝ) s, W r ≤ M := by
        intro r hr
        exact hW r ⟨hr.1, hr.2.trans hsT⟩
      have himRaw := g.im_ge_exp_of_driverBarrier hd hWprefix hzre s
        (show s ∈ Icc (0 : ℝ) s from ⟨hs0, le_rfl⟩)
      have hcoef : 0 < 2 / (d / 2) ^ 2 := by positivity
      have hexp : Real.exp (-(2 / (d / 2) ^ 2) * T) ≤
          Real.exp (-(2 / (d / 2) ^ 2) * s) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have himLower :
          z.im * Real.exp (-(2 / (d / 2) ^ 2) * T) ≤ y.im := by
        exact (mul_le_mul_of_nonneg_left hexp hzim.le).trans himRaw
      have hlowerPos :
          0 < z.im * Real.exp (-(2 / (d / 2) ^ 2) * T) :=
        mul_pos hzim (Real.exp_pos _)
      have hstepY : u < y.im ^ 2 / 8 := by
        calc
          u < (z.im * Real.exp (-(2 / (d / 2) ^ 2) * T)) ^ 2 / 8 := hstep
          _ ≤ y.im ^ 2 / 8 := by nlinarith
      have hWshift : Continuous (fun r ↦ W (s + r)) :=
        hWcont.comp (continuous_const.add continuous_id)
      obtain ⟨curve, hcurve0, hcurveDeriv, hcurveStrip⟩ :=
        loewner_local_existence_strip_explicit hWshift hypos
      let hfull : LoewnerForwardSolution (fun r ↦ W (s + r)) y
          (y.im ^ 2 / 8) :=
        { curve := curve
          initial := hcurve0
          deriv := hcurveDeriv
          upper := by
            intro r hr
            exact loewnerStrip_subset_upperHalfPlane (by positivity)
              (hcurveStrip r hr) }
      let hseg : LoewnerForwardSolution (fun r ↦ W (s + r)) y u :=
        hfull.restrict hstepY.le
      let gh : LoewnerForwardSolution W z (s + u) :=
        g.append hseg hs0 hu
      have htime : (((n + 1 : ℕ) : ℝ) * u) = s + u := by
        simp only [s, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [htime]
      exact ⟨gh⟩



theorem exists_loewnerForwardSolution_of_driverBarrier
    {W : ℝ → ℝ} (hWcont : Continuous W) {T M d : ℝ}
    (hT : 0 ≤ T) (hd : 0 < d) {z : ℂ}
    (hzim : 0 < z.im) (hzre : M + d ≤ z.re)
    (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M) :
    Nonempty (LoewnerForwardSolution W z T) := by
  let δ : ℝ := z.im * Real.exp (-(2 / (d / 2) ^ 2) * T)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * T / δ ^ 2)
  have hquot : 0 ≤ 8 * T / δ ^ 2 := by positivity
  have hn0 : 0 < (n : ℝ) := hquot.trans_lt hn
  let u : ℝ := T / (n : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hnu : (n : ℝ) * u = T := by
    dsimp [u]
    field_simp
  have hstep : u < δ ^ 2 / 8 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 8 * T < (n : ℝ) * δ ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hδ)).mp hn
    nlinarith
  have hg := exists_loewnerForwardSolution_steps_of_driverBarrier
    hWcont hd hu hzim hzre hW (by simpa [δ] using hstep) n hnu.le
  rwa [hnu] at hg



theorem exists_loewnerForwardSolution_of_driverLowerBarrier
    {W : ℝ → ℝ} (hWcont : Continuous W) {T m d : ℝ}
    (hT : 0 ≤ T) (hd : 0 < d) {z : ℂ}
    (hzim : 0 < z.im) (hzre : z.re ≤ m - d)
    (hW : ∀ s ∈ Icc (0 : ℝ) T, m ≤ W s) :
    Nonempty (LoewnerForwardSolution W z T) := by
  have hzreflect : -m + d ≤ (loewnerReflection z).re := by
    simp only [loewnerReflection_re]
    linarith
  have hWreflect : ∀ s ∈ Icc (0 : ℝ) T, -W s ≤ -m := by
    intro s hs
    linarith [hW s hs]
  have hzimreflect : 0 < (loewnerReflection z).im := by
    simpa only [loewnerReflection_im] using hzim
  obtain ⟨g⟩ := exists_loewnerForwardSolution_of_driverBarrier
    (W := fun s ↦ -W s) (z := loewnerReflection z) (M := -m)
    hWcont.neg hT hd hzimreflect hzreflect hWreflect
  refine ⟨?_⟩
  simpa only [neg_neg, loewnerReflection_involutive] using g.reflect



def IsLoewnerAdmissibleDuration (W : ℝ → ℝ) (z : ℂ) (T : ℝ) : Prop :=
  0 < T ∧ Nonempty (LoewnerForwardSolution W z T)


theorem exists_isLoewnerAdmissibleDuration {W : ℝ → ℝ} (hW : Continuous W)
    {z : ℂ} (hz : 0 < z.im) : ∃ T, IsLoewnerAdmissibleDuration W z T := by
  obtain ⟨T, hT, g, hg0, hgd, hgu⟩ := loewner_local_existence hW hz
  exact ⟨T, hT, ⟨⟨g, hg0, hgd, hgu⟩⟩⟩


theorem IsLoewnerAdmissibleDuration.mono {W : ℝ → ℝ} {z : ℂ} {S T : ℝ}
    (hT : IsLoewnerAdmissibleDuration W z T) (hS : 0 < S) (hST : S ≤ T) :
    IsLoewnerAdmissibleDuration W z S := by
  rcases hT with ⟨_, ⟨g⟩⟩
  exact ⟨hS, ⟨g.restrict hST⟩⟩



noncomputable def loewnerLifetime (W : ℝ → ℝ) (z : ℂ) : ENNReal :=
  ⨆ T : {T : ℝ // IsLoewnerAdmissibleDuration W z T}, ENNReal.ofReal T.1


theorem ofReal_le_loewnerLifetime {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (hT : IsLoewnerAdmissibleDuration W z T) :
    ENNReal.ofReal T ≤ loewnerLifetime W z := by
  exact le_iSup (fun U : {U : ℝ // IsLoewnerAdmissibleDuration W z U} ↦
    ENNReal.ofReal U.1) ⟨T, hT⟩



theorem loewnerLifetime_pos {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ}
    (hz : 0 < z.im) : 0 < loewnerLifetime W z := by
  obtain ⟨T, hT⟩ := exists_isLoewnerAdmissibleDuration hW hz
  exact (ENNReal.ofReal_pos.mpr hT.1).trans_le (ofReal_le_loewnerLifetime hT)



theorem ofReal_im_sq_div_eight_le_loewnerLifetime
    {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) :
    ENNReal.ofReal (z.im ^ 2 / 8) ≤ loewnerLifetime W z := by
  obtain ⟨g, hg0, hgd, hgstrip⟩ := loewner_local_existence_strip_explicit hW hz
  have hE : 0 < z.im ^ 2 / 8 := by positivity
  have hδ : 0 < z.im / 2 := by positivity
  apply ofReal_le_loewnerLifetime
  refine ⟨hE, ⟨⟨g, hg0, hgd, ?_⟩⟩⟩
  intro t ht
  exact loewnerStrip_subset_upperHalfPlane hδ (hgstrip t ht)




theorem exists_admissibleDuration_gt_of_ofReal_lt_lifetime
    {W : ℝ → ℝ} {z : ℂ} {t : ℝ}
    (hlt : ENNReal.ofReal t < loewnerLifetime W z) :
    ∃ T, IsLoewnerAdmissibleDuration W z T ∧ t < T := by
  rw [loewnerLifetime, lt_iSup_iff] at hlt
  obtain ⟨T, hT⟩ := hlt
  refine ⟨T.1, T.2, ?_⟩
  exact ENNReal.ofReal_lt_ofReal_iff T.2.1 |>.mp hT




def IsBeforeLoewnerLifetime (W : ℝ → ℝ) (z : ℂ) (t : ℝ) : Prop :=
  0 ≤ t ∧ ENNReal.ofReal t < loewnerLifetime W z



theorem isBeforeLoewnerLifetime_iff_exists_admissible
    {W : ℝ → ℝ} {z : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    IsBeforeLoewnerLifetime W z t ↔
      ∃ T, IsLoewnerAdmissibleDuration W z T ∧ t < T := by
  constructor
  · intro h
    exact exists_admissibleDuration_gt_of_ofReal_lt_lifetime h.2
  · rintro ⟨T, hT, htT⟩
    refine ⟨ht, ?_⟩
    exact ((ENNReal.ofReal_lt_ofReal_iff hT.1).2 htT).trans_le
      (ofReal_le_loewnerLifetime hT)

private noncomputable def selectedLoewnerDuration {W : ℝ → ℝ} {z : ℂ} {t : ℝ}
    (ht : IsBeforeLoewnerLifetime W z t) : ℝ :=
  Classical.choose (exists_admissibleDuration_gt_of_ofReal_lt_lifetime ht.2)

private theorem selectedLoewnerDuration_spec {W : ℝ → ℝ} {z : ℂ} {t : ℝ}
    (ht : IsBeforeLoewnerLifetime W z t) :
    IsLoewnerAdmissibleDuration W z (selectedLoewnerDuration ht) ∧
      t < selectedLoewnerDuration ht :=
  Classical.choose_spec (exists_admissibleDuration_gt_of_ofReal_lt_lifetime ht.2)

private noncomputable def selectedLoewnerSolution {W : ℝ → ℝ} {z : ℂ} {t : ℝ}
    (ht : IsBeforeLoewnerLifetime W z t) :
    LoewnerForwardSolution W z (selectedLoewnerDuration ht) :=
  Classical.choice (selectedLoewnerDuration_spec ht).1.2



noncomputable def loewnerMaximalCurve (W : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  by
    classical
    exact if ht : IsBeforeLoewnerLifetime W z t then
      (selectedLoewnerSolution ht).curve t else z



theorem loewnerMaximalCurve_eq_forwardSolution
    {W : ℝ → ℝ} {z : ℂ} {T t : ℝ} (hT : 0 < T)
    (g : LoewnerForwardSolution W z T) (ht : t ∈ Ico (0 : ℝ) T) :
    loewnerMaximalCurve W z t = g.curve t := by
  have htLife : ENNReal.ofReal t < loewnerLifetime W z :=
    (ENNReal.ofReal_lt_ofReal_iff hT).2 ht.2 |>.trans_le
      (ofReal_le_loewnerLifetime ⟨hT, ⟨g⟩⟩)
  have htBefore : IsBeforeLoewnerLifetime W z t := ⟨ht.1, htLife⟩
  rw [loewnerMaximalCurve, dif_pos htBefore]
  have hselectedPos : 0 < selectedLoewnerDuration htBefore :=
    (selectedLoewnerDuration_spec htBefore).1.1
  have htCommon : t ∈ Icc (0 : ℝ) (min T (selectedLoewnerDuration htBefore)) :=
    ⟨ht.1, le_min ht.2.le (selectedLoewnerDuration_spec htBefore).2.le⟩
  exact (g.eqOn_overlap hT hselectedPos (selectedLoewnerSolution htBefore) htCommon).symm



theorem loewnerMaximalCurve_flow_of_forwardSolution
    {W : ℝ → ℝ} {z : ℂ} {T s u : ℝ} (hT : 0 < T)
    (g : LoewnerForwardSolution W z T) (hs0 : 0 ≤ s) (hu0 : 0 ≤ u)
    (hsuT : s + u < T) :
    loewnerMaximalCurve W z (s + u) =
      loewnerMaximalCurve (fun r ↦ W (s + r))
        (loewnerMaximalCurve W z s) u := by
  have hsT : s < T := lt_of_le_of_lt (le_add_of_nonneg_right hu0) hsuT
  let h := g.timeShift s hs0
  have hshiftT : 0 < T - s := sub_pos.mpr hsT
  rw [loewnerMaximalCurve_eq_forwardSolution hT g ⟨add_nonneg hs0 hu0, hsuT⟩,
    loewnerMaximalCurve_eq_forwardSolution hT g ⟨hs0, hsT⟩,
    loewnerMaximalCurve_eq_forwardSolution hshiftT h
      ⟨hu0, by linarith⟩]
  rfl


theorem loewnerMaximalCurve_zero {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ}
    (hz : 0 < z.im) : loewnerMaximalCurve W z 0 = z := by
  obtain ⟨T, hT, g, hg0, hgd, hgu⟩ := loewner_local_existence hW hz
  let G : LoewnerForwardSolution W z T := ⟨g, hg0, hgd, hgu⟩
  rw [loewnerMaximalCurve_eq_forwardSolution hT G ⟨le_rfl, hT⟩]
  exact G.initial



theorem loewnerMaximalCurve_mem_upperHalfPlane
    {W : ℝ → ℝ} {z : ℂ} {t : ℝ} (ht : IsBeforeLoewnerLifetime W z t) :
    loewnerMaximalCurve W z t ∈ upperHalfPlane := by
  let g := selectedLoewnerSolution ht
  have hT : 0 < selectedLoewnerDuration ht := (selectedLoewnerDuration_spec ht).1.1
  rw [loewnerMaximalCurve_eq_forwardSolution hT g
    ⟨ht.1, (selectedLoewnerDuration_spec ht).2⟩]
  exact g.upper t ⟨ht.1, (selectedLoewnerDuration_spec ht).2.le⟩



theorem loewnerMaximalCurve_im_antitoneOn {W : ℝ → ℝ} {z : ℂ} :
    AntitoneOn (fun t ↦ (loewnerMaximalCurve W z t).im)
      {t | IsBeforeLoewnerLifetime W z t} := by
  intro s hs t ht hst
  let g := selectedLoewnerSolution ht
  let T := selectedLoewnerDuration ht
  have hT : 0 < T := (selectedLoewnerDuration_spec ht).1.1
  have htT : t < T := (selectedLoewnerDuration_spec ht).2
  have hant : AntitoneOn (fun u ↦ (g.curve u).im) (Icc (0 : ℝ) T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact Complex.continuous_im.comp_continuousOn g.continuousOn
    · rw [interior_Icc]
      intro u hu
      exact ((hasDerivAt_im_of ((g.deriv u ⟨hu.1.le, hu.2.le⟩).hasDerivAt
        (Icc_mem_nhds hu.1 hu.2))).differentiableAt).differentiableWithinAt
    · rw [interior_Icc]
      intro u hu
      rw [(hasDerivAt_im_of ((g.deriv u ⟨hu.1.le, hu.2.le⟩).hasDerivAt
        (Icc_mem_nhds hu.1 hu.2))).deriv]
      exact im_loewnerField_nonpos
        (mem_upperHalfPlane.mp (g.upper u ⟨hu.1.le, hu.2.le⟩)).le
  have hsT : s < T := hst.trans_lt htT
  change (loewnerMaximalCurve W z t).im ≤ (loewnerMaximalCurve W z s).im
  rw [loewnerMaximalCurve_eq_forwardSolution hT g ⟨hs.1, hsT⟩,
    loewnerMaximalCurve_eq_forwardSolution hT g ⟨ht.1, htT⟩]
  exact hant ⟨hs.1, hsT.le⟩ ⟨ht.1, htT.le⟩ hst



theorem loewnerMaximalCurve_hasDerivAt
    {W : ℝ → ℝ} {z : ℂ} {t : ℝ} (ht0 : 0 < t)
    (htLife : ENNReal.ofReal t < loewnerLifetime W z) :
    HasDerivAt (loewnerMaximalCurve W z)
      (loewnerField W t (loewnerMaximalCurve W z t)) t := by
  have ht : IsBeforeLoewnerLifetime W z t := ⟨ht0.le, htLife⟩
  let g := selectedLoewnerSolution ht
  let T := selectedLoewnerDuration ht
  have hT : 0 < T := (selectedLoewnerDuration_spec ht).1.1
  have htT : t < T := (selectedLoewnerDuration_spec ht).2
  have heq : loewnerMaximalCurve W z =ᶠ[nhds t] g.curve := by
    filter_upwards [Ioo_mem_nhds ht0 htT] with s hs
    exact loewnerMaximalCurve_eq_forwardSolution hT g ⟨hs.1.le, hs.2⟩
  have hg : HasDerivAt g.curve (loewnerField W t (g.curve t)) t :=
    (g.deriv t ⟨ht0.le, htT.le⟩).hasDerivAt (Icc_mem_nhds ht0 htT)
  have hvalue : loewnerMaximalCurve W z t = g.curve t := heq.self_of_nhds
  rw [hvalue]
  exact hg.congr_of_eventuallyEq heq


theorem loewnerMaximalCurve_hasDerivWithinAt_zero
    {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) :
    HasDerivWithinAt (loewnerMaximalCurve W z)
      (loewnerField W 0 (loewnerMaximalCurve W z 0)) (Ici (0 : ℝ)) 0 := by
  obtain ⟨T, hT, g, hg0, hgd, hgu⟩ := loewner_local_existence hW hz
  let G : LoewnerForwardSolution W z T := ⟨g, hg0, hgd, hgu⟩
  have heq : loewnerMaximalCurve W z =ᶠ[nhdsWithin 0 (Ici (0 : ℝ))] G.curve := by
    filter_upwards [Ico_mem_nhdsGE_of_mem (⟨le_rfl, hT⟩ : (0 : ℝ) ∈ Ico 0 T)] with s hs
    exact loewnerMaximalCurve_eq_forwardSolution hT G hs
  have hG : HasDerivWithinAt G.curve (loewnerField W 0 (G.curve 0)) (Ici (0 : ℝ)) 0 :=
    (G.deriv 0 ⟨le_rfl, hT.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (⟨le_rfl, hT⟩ : (0 : ℝ) ∈ Ico 0 T))
  have hvalue : loewnerMaximalCurve W z 0 = G.curve 0 :=
    heq.self_of_nhdsWithin (mem_Ici.mpr le_rfl)
  rw [hvalue]
  exact hG.congr_of_eventuallyEq heq hvalue





theorem loewner_maximal_forward_exists {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ}
    (hz : 0 < z.im) :
    0 < loewnerLifetime W z ∧
      loewnerMaximalCurve W z 0 = z ∧
      (∀ t, IsBeforeLoewnerLifetime W z t →
        loewnerMaximalCurve W z t ∈ upperHalfPlane) ∧
      HasDerivWithinAt (loewnerMaximalCurve W z)
        (loewnerField W 0 (loewnerMaximalCurve W z 0)) (Ici (0 : ℝ)) 0 ∧
      ∀ t, 0 < t → ENNReal.ofReal t < loewnerLifetime W z →
        HasDerivAt (loewnerMaximalCurve W z)
          (loewnerField W t (loewnerMaximalCurve W z t)) t := by
  exact ⟨loewnerLifetime_pos hW hz, loewnerMaximalCurve_zero hW hz,
    fun _ ht ↦ loewnerMaximalCurve_mem_upperHalfPlane ht,
    loewnerMaximalCurve_hasDerivWithinAt_zero hW hz,
    fun _ ht htLife ↦ loewnerMaximalCurve_hasDerivAt ht htLife⟩





def loewnerUnswallowedDomain (W : ℝ → ℝ) (t : ℝ) : Set ℂ :=
  {z | z ∈ upperHalfPlane ∧ IsBeforeLoewnerLifetime W z t}


theorem mem_loewnerUnswallowedDomain_of_lt_im_sq_div_eight
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ upperHalfPlane) (hlt : t < z.im ^ 2 / 8) :
    z ∈ loewnerUnswallowedDomain W t := by
  have hzpos : 0 < z.im := mem_upperHalfPlane.mp hz
  have hE : 0 < z.im ^ 2 / 8 := by positivity
  refine ⟨hz, ht, ?_⟩
  exact ((ENNReal.ofReal_lt_ofReal_iff hE).2 hlt).trans_le
    (ofReal_im_sq_div_eight_le_loewnerLifetime hW hzpos)



theorem mem_loewnerUnswallowedDomain_of_forwardSolution
    {W : ℝ → ℝ} (hWcont : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ upperHalfPlane) (g : LoewnerForwardSolution W z t) :
    z ∈ loewnerUnswallowedDomain W t := by
  let y : ℂ := g.curve t
  have hy : 0 < y.im :=
    mem_upperHalfPlane.mp (g.upper t ⟨ht, le_rfl⟩)
  have hWshift : Continuous (fun r ↦ W (t + r)) :=
    hWcont.comp (continuous_const.add continuous_id)
  obtain ⟨E, hE, curve, hcurve0, hcurveDeriv, hcurveUpper⟩ :=
    loewner_local_existence hWshift hy
  let hseg : LoewnerForwardSolution (fun r ↦ W (t + r)) y E :=
    { curve := curve
      initial := hcurve0
      deriv := hcurveDeriv
      upper := hcurveUpper }
  let gh : LoewnerForwardSolution W z (t + E) :=
    g.append hseg ht hE.le
  have htotal : 0 < t + E := by linarith
  have hbefore : IsBeforeLoewnerLifetime W z t :=
    (isBeforeLoewnerLifetime_iff_exists_admissible ht).2
      ⟨t + E, ⟨htotal, ⟨gh⟩⟩, by linarith⟩
  exact ⟨hz, hbefore⟩



theorem mem_loewnerUnswallowedDomain_of_driverBarrier
    {W : ℝ → ℝ} (hWcont : Continuous W) {t M d : ℝ}
    (ht : 0 ≤ t) (hd : 0 < d) {z : ℂ} (hz : z ∈ upperHalfPlane)
    (hzre : M + d ≤ z.re)
    (hW : ∀ s ∈ Icc (0 : ℝ) t, W s ≤ M) :
    z ∈ loewnerUnswallowedDomain W t := by
  obtain ⟨g⟩ := exists_loewnerForwardSolution_of_driverBarrier
    hWcont ht hd (mem_upperHalfPlane.mp hz) hzre hW
  exact mem_loewnerUnswallowedDomain_of_forwardSolution hWcont ht hz g



theorem mem_loewnerUnswallowedDomain_of_driverLowerBarrier
    {W : ℝ → ℝ} (hWcont : Continuous W) {t m d : ℝ}
    (ht : 0 ≤ t) (hd : 0 < d) {z : ℂ} (hz : z ∈ upperHalfPlane)
    (hzre : z.re ≤ m - d)
    (hW : ∀ s ∈ Icc (0 : ℝ) t, m ≤ W s) :
    z ∈ loewnerUnswallowedDomain W t := by
  obtain ⟨g⟩ := exists_loewnerForwardSolution_of_driverLowerBarrier
    hWcont ht hd (mem_upperHalfPlane.mp hz) hzre hW
  exact mem_loewnerUnswallowedDomain_of_forwardSolution hWcont ht hz g


theorem loewnerUnswallowedDomain_nonempty {W : ℝ → ℝ} (hW : Continuous W)
    {t : ℝ} (ht : 0 ≤ t) : (loewnerUnswallowedDomain W t).Nonempty := by
  let z : ℂ := ((4 * (t + 1) : ℝ) : ℂ) * Complex.I
  have hzim : z.im = 4 * (t + 1) := by simp [z]
  have hzpos : 0 < z.im := by rw [hzim]; positivity
  have hlt : t < z.im ^ 2 / 8 := by
    rw [hzim]
    nlinarith [sq_nonneg t]
  exact ⟨z, mem_loewnerUnswallowedDomain_of_lt_im_sq_div_eight
    hW ht (mem_upperHalfPlane.mpr hzpos) hlt⟩




noncomputable def loewnerMaximalMaps (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  loewnerMaximalCurve W z t



theorem loewnerMaximalMaps_flow
    {W : ℝ → ℝ} {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W (s + u)) :
    loewnerMaximalMaps W (s + u) z =
      loewnerMaximalMaps (fun r ↦ W (s + r)) u (loewnerMaximalMaps W s z) := by
  let g := selectedLoewnerSolution hz.2
  have hT : 0 < selectedLoewnerDuration hz.2 :=
    (selectedLoewnerDuration_spec hz.2).1.1
  have hsuT : s + u < selectedLoewnerDuration hz.2 :=
    (selectedLoewnerDuration_spec hz.2).2
  simpa only [loewnerMaximalMaps] using
    loewnerMaximalCurve_flow_of_forwardSolution hT g hs hu hsuT



theorem loewnerMaximalMaps_mem_shiftedUnswallowedDomain
    {W : ℝ → ℝ} {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W (s + u)) :
    loewnerMaximalMaps W s z ∈
      loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := by
  let g := selectedLoewnerSolution hz.2
  let T := selectedLoewnerDuration hz.2
  have hT : 0 < T := (selectedLoewnerDuration_spec hz.2).1.1
  have hsuT : s + u < T := (selectedLoewnerDuration_spec hz.2).2
  have hsT : s < T := lt_of_le_of_lt (le_add_of_nonneg_right hu) hsuT
  let h := g.timeShift s hs
  have hshiftT : 0 < T - s := sub_pos.mpr hsT
  have hbefore : IsBeforeLoewnerLifetime (fun r ↦ W (s + r)) (g.curve s) u :=
    (isBeforeLoewnerLifetime_iff_exists_admissible hu).2
      ⟨T - s, ⟨hshiftT, ⟨h⟩⟩, by linarith⟩
  change loewnerMaximalCurve W z s ∈
    loewnerUnswallowedDomain (fun r ↦ W (s + r)) u
  rw [loewnerMaximalCurve_eq_forwardSolution hT g ⟨hs, hsT⟩]
  exact ⟨g.upper s ⟨hs, hsT.le⟩, hbefore⟩



theorem mem_loewnerUnswallowedDomain_zero {W : ℝ → ℝ} (hW : Continuous W)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : z ∈ loewnerUnswallowedDomain W 0 := by
  refine ⟨hz, le_rfl, ?_⟩
  simpa using loewnerLifetime_pos hW (mem_upperHalfPlane.mp hz)



theorem loewnerMaximalMaps_zero {W : ℝ → ℝ} (hW : Continuous W)
    {z : ℂ} (hz : z ∈ upperHalfPlane) : loewnerMaximalMaps W 0 z = z :=
  loewnerMaximalCurve_zero hW (mem_upperHalfPlane.mp hz)



theorem loewnerMaximalMaps_mem_upperHalfPlane {W : ℝ → ℝ} {t : ℝ} {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    loewnerMaximalMaps W t z ∈ upperHalfPlane :=
  loewnerMaximalCurve_mem_upperHalfPlane hz.2



theorem loewnerMaximalMaps_hasDerivAt {W : ℝ → ℝ} {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∈ loewnerUnswallowedDomain W t) :
    HasDerivAt (fun s ↦ loewnerMaximalMaps W s z)
      (loewnerField W t (loewnerMaximalMaps W t z)) t :=
  loewnerMaximalCurve_hasDerivAt ht hz.2.2



theorem loewnerMaximalMaps_hasDerivWithinAt_zero {W : ℝ → ℝ} (hW : Continuous W)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    HasDerivWithinAt (fun s ↦ loewnerMaximalMaps W s z)
      (loewnerField W 0 (loewnerMaximalMaps W 0 z)) (Ici (0 : ℝ)) 0 :=
  loewnerMaximalCurve_hasDerivWithinAt_zero hW (mem_upperHalfPlane.mp hz)



theorem loewnerMaximalMaps_injOn {W : ℝ → ℝ} (hW : Continuous W)
    {t : ℝ} (ht : 0 ≤ t) :
    InjOn (loewnerMaximalMaps W t) (loewnerUnswallowedDomain W t) := by
  rcases ht.eq_or_lt with rfl | ht0
  · intro z hz w hw heq
    calc
      z = loewnerMaximalMaps W 0 z := (loewnerMaximalMaps_zero hW hz.1).symm
      _ = loewnerMaximalMaps W 0 w := heq
      _ = w := loewnerMaximalMaps_zero hW hw.1
  · intro z hz w hw heq
    let g := selectedLoewnerSolution hz.2
    let h := selectedLoewnerSolution hw.2
    have hS : 0 < selectedLoewnerDuration hz.2 :=
      (selectedLoewnerDuration_spec hz.2).1.1
    have hT : 0 < selectedLoewnerDuration hw.2 :=
      (selectedLoewnerDuration_spec hw.2).1.1
    have htS : t < selectedLoewnerDuration hz.2 :=
      (selectedLoewnerDuration_spec hz.2).2
    have htT : t < selectedLoewnerDuration hw.2 :=
      (selectedLoewnerDuration_spec hw.2).2
    have hcurve : g.curve t = h.curve t := by
      rw [← loewnerMaximalCurve_eq_forwardSolution hS g ⟨ht0.le, htS⟩,
        ← loewnerMaximalCurve_eq_forwardSolution hT h ⟨ht0.le, htT⟩]
      exact heq
    exact g.initial_eq_of_eq_at hS hT h ht0 htS htT hcurve





theorem loewnerMaximalMaps_surjOn_upperHalfPlane
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    SurjOn (loewnerMaximalMaps W t)
      (loewnerUnswallowedDomain W t) upperHalfPlane := by
  intro y hyUpper
  have hy : 0 < y.im := mem_upperHalfPlane.mp hyUpper
  obtain ⟨x, g, hgEnd⟩ := exists_loewnerBackwardSolution hW ht hy
  have hWt : Continuous (fun u ↦ W (t + u)) :=
    hW.comp (continuous_const.add continuous_id)
  obtain ⟨E, hE, h, hh0, hhd, hhu⟩ :=
    loewner_local_existence hWt hy
  let h' : LoewnerForwardSolution (fun u ↦ W (t + u)) (g.curve t) E :=
    { curve := h
      initial := hh0.trans hgEnd.symm
      deriv := hhd
      upper := hhu }
  let gh : LoewnerForwardSolution W x (t + E) :=
    g.append h' ht hE.le
  have htotal : 0 < t + E := by linarith
  have hxUpper : x ∈ upperHalfPlane := by
    rw [← g.initial]
    exact g.upper 0 ⟨le_rfl, ht⟩
  have hbefore : IsBeforeLoewnerLifetime W x t :=
    (isBeforeLoewnerLifetime_iff_exists_admissible ht).2
      ⟨t + E, ⟨htotal, ⟨gh⟩⟩, by linarith⟩
  have ghAt : gh.curve t = y := by
    simp [gh, LoewnerForwardSolution.append,
      LoewnerForwardSolution.appendCurve, hgEnd]
  refine ⟨x, ⟨hxUpper, hbefore⟩, ?_⟩
  calc
    loewnerMaximalMaps W t x = gh.curve t := by
      exact loewnerMaximalCurve_eq_forwardSolution htotal gh ⟨ht, by linarith⟩
    _ = y := ghAt



theorem loewnerMaximalMaps_bijOn_upperHalfPlane
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    BijOn (loewnerMaximalMaps W t)
      (loewnerUnswallowedDomain W t) upperHalfPlane := by
  refine ⟨?_, loewnerMaximalMaps_injOn hW ht,
    loewnerMaximalMaps_surjOn_upperHalfPlane hW ht⟩
  intro z hz
  exact loewnerMaximalMaps_mem_upperHalfPlane hz




noncomputable def loewnerMaximalMapsInverse
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) (y : ℂ) : ℂ := by
  classical
  exact if hy : y ∈ upperHalfPlane then
      Classical.choose (loewnerMaximalMaps_surjOn_upperHalfPlane hW ht hy)
    else 0



theorem loewnerMaximalMapsInverse_congr_time
    {W : ℝ → ℝ} (hW : Continuous W) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s = t) :
    loewnerMaximalMapsInverse hW hs = loewnerMaximalMapsInverse hW ht := by
  subst t
  congr



theorem loewnerMaximalMapsInverse_mem
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : y ∈ upperHalfPlane) :
    loewnerMaximalMapsInverse hW ht y ∈ loewnerUnswallowedDomain W t := by
  rw [loewnerMaximalMapsInverse, dif_pos hy]
  exact (Classical.choose_spec
    (loewnerMaximalMaps_surjOn_upperHalfPlane hW ht hy)).1



theorem loewnerMaximalMaps_inverse
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : y ∈ upperHalfPlane) :
    loewnerMaximalMaps W t (loewnerMaximalMapsInverse hW ht y) = y := by
  rw [loewnerMaximalMapsInverse, dif_pos hy]
  exact (Classical.choose_spec
    (loewnerMaximalMaps_surjOn_upperHalfPlane hW ht hy)).2



theorem eq_loewnerMaximalMapsInverse_of_mapsTo
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {x y : ℂ} (hx : x ∈ loewnerUnswallowedDomain W t)
    (hy : y ∈ upperHalfPlane) (hxy : loewnerMaximalMaps W t x = y) :
    x = loewnerMaximalMapsInverse hW ht y := by
  apply loewnerMaximalMaps_injOn hW ht hx
    (loewnerMaximalMapsInverse_mem hW ht hy)
  rw [hxy, loewnerMaximalMaps_inverse hW ht hy]





theorem exists_loewnerMaximalMaps_localRightInverse_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : 0 < y.im) (hlt : t < y.im ^ 2 / 16) :
    ∃ inv : ℂ → ℂ,
      ContinuousOn inv (closedBall y (y.im / 4)) ∧
        MapsTo inv (closedBall y (y.im / 4))
          (loewnerUnswallowedDomain W t) ∧
        ∀ v ∈ closedBall y (y.im / 4),
          loewnerMaximalMaps W t (inv v) = v := by
  let E : ℝ := y.im ^ 2 / 16
  have hE : 0 < E := by dsimp [E]; positivity
  have hltE : t < E := by simpa [E] using hlt
  obtain ⟨α, hα, C, hC⟩ := loewner_local_flow_chart hW hy t
  let inv : ℂ → ℂ := fun v ↦ α v 0
  have hinterval : Icc (0 : ℝ) (t + E) ⊆ Icc (t - E) (t + E) := by
    intro u hu
    exact ⟨by linarith [hu.1], hu.2⟩
  have hzeroInterval : (0 : ℝ) ∈ Icc (t - E) (t + E) := by
    constructor
    · linarith
    · positivity
  have hsolution :
      ∀ v ∈ closedBall y (y.im / 4),
        {g : LoewnerForwardSolution W (inv v) (t + E) // g.curve = α v} := by
    intro v hv
    obtain ⟨hend, hderiv, hstrip⟩ := hα v hv
    refine ⟨{
      curve := α v
      initial := rfl
      deriv := ?_
      upper := ?_ }, rfl⟩
    · intro u hu
      exact (hderiv u (hinterval hu)).mono hinterval
    · intro u hu
      exact loewnerStrip_subset_upperHalfPlane (by positivity) (hstrip u)
  refine ⟨inv, ?_, ?_, ?_⟩
  · exact (hC 0 hzeroInterval).continuousOn
  · intro v hv
    let g := (hsolution v hv).1
    have htotal : 0 < t + E := by positivity
    have hvUpper : inv v ∈ upperHalfPlane := by
      rw [← g.initial]
      exact g.upper 0 ⟨le_rfl, by positivity⟩
    have hbefore : IsBeforeLoewnerLifetime W (inv v) t :=
      (isBeforeLoewnerLifetime_iff_exists_admissible ht).2
        ⟨t + E, ⟨htotal, ⟨g⟩⟩, by linarith⟩
    exact ⟨hvUpper, hbefore⟩
  · intro v hv
    let g := (hsolution v hv).1
    have htotal : 0 < t + E := by positivity
    calc
      loewnerMaximalMaps W t (inv v) = g.curve t := by
        exact loewnerMaximalCurve_eq_forwardSolution htotal g
          ⟨ht, by linarith⟩
      _ = α v t := congrFun (hsolution v hv).2 t
      _ = v := (hα v hv).1



theorem continuousAt_loewnerMaximalMapsInverse_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : y ∈ upperHalfPlane) (hlt : t < y.im ^ 2 / 16) :
    ContinuousAt (loewnerMaximalMapsInverse hW ht) y := by
  have hypos : 0 < y.im := mem_upperHalfPlane.mp hy
  obtain ⟨inv, hinvContinuous, hinvMaps, hinvRight⟩ :=
    exists_loewnerMaximalMaps_localRightInverse_of_lt_im_sq_div_sixteen
      hW ht hypos hlt
  have hradius : 0 < y.im / 4 := by positivity
  have hball : closedBall y (y.im / 4) ∈ 𝓝 y :=
    closedBall_mem_nhds y hradius
  have hEq : loewnerMaximalMapsInverse hW ht =ᶠ[𝓝 y] inv := by
    filter_upwards [hball, isOpen_upperHalfPlane.mem_nhds hy] with v hvBall hvUpper
    exact (eq_loewnerMaximalMapsInverse_of_mapsTo hW ht
      (hinvMaps hvBall) hvUpper (hinvRight v hvBall)).symm
  exact (hinvContinuous y (mem_closedBall_self hradius.le)).continuousAt hball
    |>.congr_of_eventuallyEq hEq





theorem loewnerMaximalMaps_local_lipschitz_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hlt : t < z₀.im ^ 2 / 16) :
    ∃ C : ℝ≥0,
      closedBall z₀ (z₀.im / 4) ⊆ loewnerUnswallowedDomain W t ∧
        LipschitzOnWith C (loewnerMaximalMaps W t)
          (closedBall z₀ (z₀.im / 4)) := by
  let E : ℝ := z₀.im ^ 2 / 16
  have hE : 0 < E := by dsimp [E]; positivity
  have hδ : 0 < z₀.im / 2 := by positivity
  obtain ⟨α, hα, C, hC⟩ := loewner_local_flow_chart hW hz₀ 0
  have hinterval : Icc (0 : ℝ) (z₀.im ^ 2 / 16) ⊆
      Icc (0 - z₀.im ^ 2 / 16) (0 + z₀.im ^ 2 / 16) := by
    intro u hu
    exact ⟨by linarith [hu.1], by simpa using hu.2⟩
  let hsolution :
      ∀ w ∈ closedBall z₀ (z₀.im / 4),
        {g : LoewnerForwardSolution W w (z₀.im ^ 2 / 16) //
          g.curve = α w} := by
    intro w hw
    obtain ⟨hinit, hderiv, hstrip⟩ := hα w hw
    refine ⟨{
      curve := α w
      initial := by simpa using hinit
      deriv := ?_
      upper := ?_ }, rfl⟩
    · intro u hu
      exact (hderiv u (hinterval hu)).mono hinterval
    · intro u hu
      exact loewnerStrip_subset_upperHalfPlane hδ (hstrip u)
  have heq : EqOn (loewnerMaximalMaps W t) (fun w ↦ α w t)
      (closedBall z₀ (z₀.im / 4)) := by
    intro w hw
    calc
      loewnerMaximalMaps W t w =
          (hsolution w hw).1.curve t := by
        simpa only [loewnerMaximalMaps] using
          loewnerMaximalCurve_eq_forwardSolution (by simpa [E] using hE)
            (hsolution w hw).1 ⟨ht, hlt⟩
      _ = α w t := congrFun (hsolution w hw).2 t
  have hsub : closedBall z₀ (z₀.im / 4) ⊆ loewnerUnswallowedDomain W t := by
    intro w hw
    let g := (hsolution w hw).1
    have hwupper : w ∈ upperHalfPlane := by
      rw [← g.initial]
      exact g.upper 0 ⟨le_rfl, hE.le⟩
    have hbefore : IsBeforeLoewnerLifetime W w t :=
      (isBeforeLoewnerLifetime_iff_exists_admissible ht).2
        ⟨E, ⟨hE, ⟨g⟩⟩, by simpa [E] using hlt⟩
    exact ⟨hwupper, hbefore⟩
  refine ⟨C, hsub, ?_⟩
  have htchart : t ∈ Icc (-E) E := ⟨by linarith, by simpa [E] using hlt.le⟩
  have hslice := hC t (by simpa [E] using htchart)
  intro x hx y hy
  rw [heq hx, heq hy]
  exact hslice hx hy



theorem continuousAt_loewnerMaximalMaps_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hlt : t < z₀.im ^ 2 / 16) :
    ContinuousAt (loewnerMaximalMaps W t) z₀ := by
  obtain ⟨C, _, hC⟩ :=
    loewnerMaximalMaps_local_lipschitz_of_lt_im_sq_div_sixteen hW ht hz₀ hlt
  apply (hC.continuousOn z₀ (mem_closedBall_self (by positivity))).continuousAt
  exact closedBall_mem_nhds z₀ (by positivity)


theorem loewnerUnswallowedDomain_zero {W : ℝ → ℝ} (hW : Continuous W) :
    loewnerUnswallowedDomain W 0 = upperHalfPlane := by
  ext z
  constructor
  · exact fun hz ↦ hz.1
  · exact fun hz ↦ mem_loewnerUnswallowedDomain_zero hW hz



theorem loewnerMaximalMaps_satisfiesMaximalLoewnerEquation
    {W : ℝ → ℝ} (hW : Continuous W) :
    SatisfiesMaximalLoewnerEquation W (loewnerUnswallowedDomain W)
      (loewnerMaximalMaps W) := by
  refine ⟨loewnerUnswallowedDomain_zero hW, ?_, ?_, ?_⟩
  · intro z hz
    exact loewnerMaximalMaps_zero hW hz.1
  · intro z hz
    exact loewnerMaximalMaps_hasDerivWithinAt_zero hW hz.1
  · intro t ht z hz
    exact loewnerMaximalMaps_hasDerivAt ht hz



theorem loewnerMaximalMaps_regularAt_zero {W : ℝ → ℝ} (hW : Continuous W)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    loewnerUnswallowedDomain W 0 ∈ 𝓝 z ∧
      ContinuousAt (loewnerMaximalMaps W 0) z := by
  have hdomain : loewnerUnswallowedDomain W 0 ∈ 𝓝 z := by
    rw [loewnerUnswallowedDomain_zero hW]
    exact isOpen_upperHalfPlane.mem_nhds hz
  refine ⟨hdomain, continuousAt_id.congr_of_eventuallyEq ?_⟩
  filter_upwards [hdomain] with w hw
  simpa only [id_eq] using loewnerMaximalMaps_zero hW hw.1


theorem loewnerUnswallowedDomain_antitoneOn (W : ℝ → ℝ) :
    AntitoneOn (loewnerUnswallowedDomain W) (Ici (0 : ℝ)) := by
  intro s hs t ht hst z hz
  refine ⟨hz.1, hs, ?_⟩
  exact (ENNReal.ofReal_le_ofReal hst).trans_lt hz.2.2



theorem loewnerUnswallowedDomain_add_subset
    (W : ℝ → ℝ) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) :
    loewnerUnswallowedDomain W (s + u) ⊆
      loewnerUnswallowedDomain W s ∩
        loewnerMaximalMaps W s ⁻¹'
          loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := by
  intro z hz
  refine ⟨loewnerUnswallowedDomain_antitoneOn W hs (add_nonneg hs hu)
    (le_add_of_nonneg_right hu) hz, ?_⟩
  exact loewnerMaximalMaps_mem_shiftedUnswallowedDomain hs hu hz



theorem loewnerUnswallowedDomain_add_eq
    (W : ℝ → ℝ) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) :
    loewnerUnswallowedDomain W (s + u) =
      loewnerUnswallowedDomain W s ∩
        loewnerMaximalMaps W s ⁻¹'
          loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := by
  apply Subset.antisymm (loewnerUnswallowedDomain_add_subset W hs hu)
  rintro z ⟨hzs, hzu⟩
  let g := selectedLoewnerSolution hzs.2
  let A := selectedLoewnerDuration hzs.2
  have hA : 0 < A := (selectedLoewnerDuration_spec hzs.2).1.1
  have hsA : s < A := (selectedLoewnerDuration_spec hzs.2).2
  let gS : LoewnerForwardSolution W z s := g.restrict hsA.le
  let h₀ := selectedLoewnerSolution hzu.2
  let B := selectedLoewnerDuration hzu.2
  have hB : 0 < B := (selectedLoewnerDuration_spec hzu.2).1.1
  have huB : u < B := (selectedLoewnerDuration_spec hzu.2).2
  have hmax : loewnerMaximalMaps W s z = g.curve s := by
    exact loewnerMaximalCurve_eq_forwardSolution hA g ⟨hs, hsA⟩
  let h : LoewnerForwardSolution (fun r ↦ W (s + r)) (g.curve s) B := by
    rw [← hmax]
    exact h₀
  let gh : LoewnerForwardSolution W z (s + B) := gS.append h hs hB.le
  have hadmissible : IsLoewnerAdmissibleDuration W z (s + B) :=
    ⟨by linarith, ⟨gh⟩⟩
  have hbefore : IsBeforeLoewnerLifetime W z (s + u) :=
    (isBeforeLoewnerLifetime_iff_exists_admissible (add_nonneg hs hu)).2
      ⟨s + B, hadmissible, by linarith⟩
  exact ⟨hzs.1, hbefore⟩



theorem continuous_loewnerDriver_shift
    {W : ℝ → ℝ} (hW : Continuous W) (s : ℝ) :
    Continuous (fun r ↦ W (s + r)) :=
  hW.comp (continuous_const.add continuous_id)



theorem loewnerMaximalMapsInverse_add
    {W : ℝ → ℝ} (hW : Continuous W) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    {y : ℂ} (hy : y ∈ upperHalfPlane) :
    loewnerMaximalMapsInverse hW (add_nonneg hs hu) y =
      loewnerMaximalMapsInverse hW hs
        (loewnerMaximalMapsInverse
          (continuous_loewnerDriver_shift hW s) hu y) := by
  let Ws : ℝ → ℝ := fun r ↦ W (s + r)
  have hWs : Continuous Ws := hW.comp (continuous_const.add continuous_id)
  let a : ℂ := loewnerMaximalMapsInverse hWs hu y
  have haShift : a ∈ loewnerUnswallowedDomain Ws u :=
    loewnerMaximalMapsInverse_mem hWs hu hy
  have haUpper : a ∈ upperHalfPlane := haShift.1
  let x : ℂ := loewnerMaximalMapsInverse hW hs a
  have hxInitial : x ∈ loewnerUnswallowedDomain W s :=
    loewnerMaximalMapsInverse_mem hW hs haUpper
  have hxTotal : x ∈ loewnerUnswallowedDomain W (s + u) := by
    rw [loewnerUnswallowedDomain_add_eq W hs hu]
    refine ⟨hxInitial, ?_⟩
    change loewnerMaximalMaps W s x ∈ loewnerUnswallowedDomain Ws u
    rw [loewnerMaximalMaps_inverse hW hs haUpper]
    exact haShift
  have hxMap : loewnerMaximalMaps W (s + u) x = y := by
    rw [loewnerMaximalMaps_flow hs hu hxTotal,
      loewnerMaximalMaps_inverse hW hs haUpper,
      loewnerMaximalMaps_inverse hWs hu hy]
  exact (eq_loewnerMaximalMapsInverse_of_mapsTo hW (add_nonneg hs hu)
    hxTotal hy hxMap).symm


theorem continuousAt_loewnerMaximalMapsInverse_add
    {W : ℝ → ℝ} (hW : Continuous W) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    {y : ℂ} (hy : y ∈ upperHalfPlane)
    (hfirst : ContinuousAt (loewnerMaximalMapsInverse hW hs)
      (loewnerMaximalMapsInverse
        (continuous_loewnerDriver_shift hW s) hu y))
    (hsecond : ContinuousAt
      (loewnerMaximalMapsInverse
        (continuous_loewnerDriver_shift hW s) hu) y) :
    ContinuousAt (loewnerMaximalMapsInverse hW (add_nonneg hs hu)) y := by
  have hcomp : ContinuousAt
      (fun v ↦ loewnerMaximalMapsInverse hW hs
        (loewnerMaximalMapsInverse
          (continuous_loewnerDriver_shift hW s) hu v)) y :=
    hfirst.comp' hsecond
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlane.mem_nhds hy] with v hv
  exact loewnerMaximalMapsInverse_add hW hs hu hv




theorem continuousAt_loewnerMaximalMapsInverse_steps
    {W : ℝ → ℝ} (hW : Continuous W) {u : ℝ} (hu : 0 ≤ u)
    (n : ℕ) {y : ℂ} (hy : y ∈ upperHalfPlane)
    (hshort : u < y.im ^ 2 / 16) :
    ContinuousAt
      (loewnerMaximalMapsInverse hW
        (mul_nonneg (Nat.cast_nonneg n) hu)) y := by
  induction n generalizing y with
  | zero =>
      have hypos : 0 < y.im := mem_upperHalfPlane.mp hy
      let hzero : 0 ≤ (0 : ℝ) * u := by simp
      have hbase :=
        continuousAt_loewnerMaximalMapsInverse_of_lt_im_sq_div_sixteen
          hW hzero hy (by simpa using (show 0 < y.im ^ 2 / 16 by positivity))
      rw [loewnerMaximalMapsInverse_congr_time hW hzero
        (mul_nonneg (Nat.cast_nonneg 0) hu) (by norm_num)] at hbase
      exact hbase
  | succ n ih =>
      let s : ℝ := (n : ℝ) * u
      have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg n) hu
      let Ws : ℝ → ℝ := fun r ↦ W (s + r)
      have hWs : Continuous Ws := hW.comp (continuous_const.add continuous_id)
      let a : ℂ := loewnerMaximalMapsInverse hWs hu y
      have haShift : a ∈ loewnerUnswallowedDomain Ws u :=
        loewnerMaximalMapsInverse_mem hWs hu hy
      have haUpper : a ∈ upperHalfPlane := haShift.1
      have haZero : a ∈ loewnerUnswallowedDomain Ws 0 :=
        loewnerUnswallowedDomain_antitoneOn Ws
          (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
          (show u ∈ Ici 0 from mem_Ici.mpr hu) hu haShift
      have him : y.im ≤ a.im := by
        have hant := loewnerMaximalCurve_im_antitoneOn haZero.2 haShift.2 hu
        change (loewnerMaximalMaps Ws u a).im ≤
          (loewnerMaximalMaps Ws 0 a).im at hant
        rw [loewnerMaximalMaps_inverse hWs hu hy,
          loewnerMaximalMaps_zero hWs haUpper] at hant
        exact hant
      have hshortA : u < a.im ^ 2 / 16 := by
        have hy0 : 0 ≤ y.im := (mem_upperHalfPlane.mp hy).le
        calc
          u < y.im ^ 2 / 16 := hshort
          _ ≤ a.im ^ 2 / 16 := by nlinarith
      have hfirst : ContinuousAt (loewnerMaximalMapsInverse hW hs) a :=
        ih haUpper hshortA
      have hsecond : ContinuousAt (loewnerMaximalMapsInverse hWs hu) y :=
        continuousAt_loewnerMaximalMapsInverse_of_lt_im_sq_div_sixteen
          hWs hu hy hshort
      have hadd := continuousAt_loewnerMaximalMapsInverse_add hW hs hu hy
        (by simpa [Ws] using hfirst) (by simpa [Ws] using hsecond)
      have htime : (((n + 1 : ℕ) : ℝ) * u) = s + u := by
        simp only [s, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [loewnerMaximalMapsInverse_congr_time hW
        (mul_nonneg (Nat.cast_nonneg (n + 1)) hu) (add_nonneg hs hu) htime]
      exact hadd




theorem continuousAt_loewnerMaximalMapsInverse
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {y : ℂ} (hy : y ∈ upperHalfPlane) :
    ContinuousAt (loewnerMaximalMapsInverse hW ht) y := by
  have hypos : 0 < y.im := mem_upperHalfPlane.mp hy
  obtain ⟨n, hn⟩ := exists_nat_gt (16 * t / y.im ^ 2)
  have hquot : 0 ≤ 16 * t / y.im ^ 2 := by positivity
  have hn0 : 0 < (n : ℝ) := hquot.trans_lt hn
  let u : ℝ := t / (n : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hnu : (n : ℝ) * u = t := by
    dsimp [u]
    field_simp
  have hshort : u < y.im ^ 2 / 16 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 16 * t < (n : ℝ) * y.im ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hypos)).mp hn
    nlinarith
  have hcont := continuousAt_loewnerMaximalMapsInverse_steps
    hW hu n hy hshort
  rw [← loewnerMaximalMapsInverse_congr_time hW
    (mul_nonneg (Nat.cast_nonneg n) hu) ht hnu]
  exact hcont





theorem loewnerMaximalMaps_regularAt_add_of_lt_im_sq_div_sixteen
    {W : ℝ → ℝ} (hW : Continuous W) {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    {z : ℂ} (hz : z ∈ loewnerUnswallowedDomain W (s + u))
    (hregular : loewnerUnswallowedDomain W s ∈ 𝓝 z ∧
      ContinuousAt (loewnerMaximalMaps W s) z)
    (hshort : u < (loewnerMaximalMaps W s z).im ^ 2 / 16) :
    loewnerUnswallowedDomain W (s + u) ∈ 𝓝 z ∧
      ContinuousAt (loewnerMaximalMaps W (s + u)) z := by
  let Ws : ℝ → ℝ := fun r ↦ W (s + r)
  have hWs : Continuous Ws :=
    hW.comp (continuous_const.add continuous_id)
  have hzs : z ∈ loewnerUnswallowedDomain W s :=
    loewnerUnswallowedDomain_antitoneOn W hs (add_nonneg hs hu)
      (le_add_of_nonneg_right hu) hz
  let y : ℂ := loewnerMaximalMaps W s z
  have hy : 0 < y.im :=
    mem_upperHalfPlane.mp (loewnerMaximalMaps_mem_upperHalfPlane hzs)
  obtain ⟨C, hball, hLip⟩ :=
    loewnerMaximalMaps_local_lipschitz_of_lt_im_sq_div_sixteen
      hWs hu hy hshort
  let B : Set ℂ := closedBall y (y.im / 4)
  have hB : B ∈ 𝓝 y := closedBall_mem_nhds y (by positivity)
  have hpre : loewnerMaximalMaps W s ⁻¹' B ∈ 𝓝 z :=
    hregular.2 hB
  have hdomain : loewnerUnswallowedDomain W (s + u) ∈ 𝓝 z := by
    apply mem_of_superset (inter_mem hregular.1 hpre)
    intro w hw
    rw [loewnerUnswallowedDomain_add_eq W hs hu]
    exact ⟨hw.1, hball hw.2⟩
  refine ⟨hdomain, ?_⟩
  have hshiftContinuous :
      ContinuousAt (loewnerMaximalMaps Ws u) y :=
    (hLip.continuousOn y (mem_closedBall_self (by positivity))).continuousAt hB
  have hcomp : ContinuousAt
      (fun w ↦ loewnerMaximalMaps Ws u (loewnerMaximalMaps W s w)) z := by
    simpa only [Function.comp_def] using
      Filter.Tendsto.comp hshiftContinuous hregular.2
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hdomain] with w hw
  exact loewnerMaximalMaps_flow hs hu hw






theorem loewnerMaximalMaps_regularAt
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ loewnerUnswallowedDomain W t) :
    loewnerUnswallowedDomain W t ∈ 𝓝 z ∧
      ContinuousAt (loewnerMaximalMaps W t) z := by
  let δ : ℝ := (loewnerMaximalMaps W t z).im
  have hδ : 0 < δ :=
    mem_upperHalfPlane.mp (loewnerMaximalMaps_mem_upperHalfPlane hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (16 * t / δ ^ 2)
  have hquot : 0 ≤ 16 * t / δ ^ 2 := by positivity
  have hn0 : 0 < (n : ℝ) := hquot.trans_lt hn
  let u : ℝ := t / (n : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hnu : (n : ℝ) * u = t := by
    dsimp [u]
    field_simp
  have hushort : u < δ ^ 2 / 16 := by
    rw [div_lt_iff₀ hn0]
    have hmul : 16 * t < (n : ℝ) * δ ^ 2 :=
      (div_lt_iff₀ (sq_pos_of_pos hδ)).mp hn
    nlinarith
  have htime (k : ℕ) (hk : k ≤ n) :
      0 ≤ (k : ℝ) * u ∧ (k : ℝ) * u ≤ t := by
    refine ⟨mul_nonneg (Nat.cast_nonneg k) hu, ?_⟩
    rw [← hnu]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hu
  have hsurvives (k : ℕ) (hk : k ≤ n) :
      z ∈ loewnerUnswallowedDomain W ((k : ℝ) * u) := by
    exact loewnerUnswallowedDomain_antitoneOn W (htime k hk).1 ht
      (htime k hk).2 hz
  have hind : ∀ k : ℕ, k ≤ n →
      loewnerUnswallowedDomain W ((k : ℝ) * u) ∈ 𝓝 z ∧
        ContinuousAt (loewnerMaximalMaps W ((k : ℝ) * u)) z := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using loewnerMaximalMaps_regularAt_zero hW hz.1
    | succ k ih =>
        intro hkn
        have hk : k ≤ n := (Nat.le_succ k).trans hkn
        have hs := (htime k hk).1
        have hznext := hsurvives (k + 1) hkn
        have hstepTime :
            ((k + 1 : ℕ) : ℝ) * u = (k : ℝ) * u + u := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
        have hzadd :
            z ∈ loewnerUnswallowedDomain W ((k : ℝ) * u + u) := by
          rw [hstepTime] at hznext
          exact hznext
        have him : δ ≤ (loewnerMaximalMaps W ((k : ℝ) * u) z).im := by
          exact loewnerMaximalCurve_im_antitoneOn
            (hsurvives k hk).2 hz.2 (htime k hk).2
        have hshort :
            u < (loewnerMaximalMaps W ((k : ℝ) * u) z).im ^ 2 / 16 := by
          calc
            u < δ ^ 2 / 16 := hushort
            _ ≤ (loewnerMaximalMaps W ((k : ℝ) * u) z).im ^ 2 / 16 := by
              gcongr
        have hregadd :=
          loewnerMaximalMaps_regularAt_add_of_lt_im_sq_div_sixteen
            hW hs hu hzadd (ih hk) hshort
        rw [← hstepTime] at hregadd
        exact hregadd
  have hnreg := hind n le_rfl
  rwa [hnu] at hnreg


theorem isOpen_loewnerUnswallowedDomain
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsOpen (loewnerUnswallowedDomain W t) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  exact (loewnerMaximalMaps_regularAt hW ht hz).1



theorem continuousOn_loewnerMaximalMaps
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (loewnerMaximalMaps W t) (loewnerUnswallowedDomain W t) := by
  intro z hz
  exact (loewnerMaximalMaps_regularAt hW ht hz).2.continuousWithinAt


theorem continuousOn_loewnerMaximalMapsInverse
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (loewnerMaximalMapsInverse hW ht) upperHalfPlane := by
  intro y hy
  exact (continuousAt_loewnerMaximalMapsInverse hW ht hy).continuousWithinAt



noncomputable def loewnerMaximalMapsHomeomorph
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    loewnerUnswallowedDomain W t ≃ₜ upperHalfPlane where
  toFun := MapsTo.restrict (loewnerMaximalMaps W t)
    (loewnerUnswallowedDomain W t) upperHalfPlane
    (loewnerMaximalMaps_bijOn_upperHalfPlane hW ht).1
  invFun := MapsTo.restrict (loewnerMaximalMapsInverse hW ht)
    upperHalfPlane (loewnerUnswallowedDomain W t)
    (fun _ hy ↦ loewnerMaximalMapsInverse_mem hW ht hy)
  left_inv := by
    intro x
    apply Subtype.ext
    exact (eq_loewnerMaximalMapsInverse_of_mapsTo hW ht x.2
      (loewnerMaximalMaps_mem_upperHalfPlane x.2) rfl).symm
  right_inv := by
    intro y
    apply Subtype.ext
    exact loewnerMaximalMaps_inverse hW ht y.2
  continuous_toFun :=
    (continuousOn_loewnerMaximalMaps hW ht).mapsToRestrict
      (loewnerMaximalMaps_bijOn_upperHalfPlane hW ht).1
  continuous_invFun :=
    (continuousOn_loewnerMaximalMapsInverse hW ht).mapsToRestrict
      (fun _ hy ↦ loewnerMaximalMapsInverse_mem hW ht hy)



theorem isConnected_loewnerUnswallowedDomain
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsConnected (loewnerUnswallowedDomain W t) := by
  have hH : IsConnected upperHalfPlane := by
    have h : upperHalfPlane = {c : ℂ | (0 : ℝ) < c.im} := rfl
    rw [h]
    exact (convex_halfSpace_im_gt 0).isConnected
      ⟨(0 + 1) * Complex.I, by simp⟩
  have himage := hH.image (loewnerMaximalMapsInverse hW ht)
    (continuousOn_loewnerMaximalMapsInverse hW ht)
  have heq : loewnerMaximalMapsInverse hW ht '' upperHalfPlane =
      loewnerUnswallowedDomain W t := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact loewnerMaximalMapsInverse_mem hW ht hy
    · intro x hx
      let y := loewnerMaximalMaps W t x
      have hy : y ∈ upperHalfPlane := loewnerMaximalMaps_mem_upperHalfPlane hx
      refine ⟨y, hy, ?_⟩
      exact (eq_loewnerMaximalMapsInverse_of_mapsTo hW ht hx hy rfl).symm
  rwa [heq] at himage




theorem isBeforeLoewnerLifetime_add_iff_shifted
    {W : ℝ → ℝ} {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) {z : ℂ}
    (hzs : z ∈ loewnerUnswallowedDomain W s) :
    IsBeforeLoewnerLifetime W z (s + u) ↔
      IsBeforeLoewnerLifetime (fun r ↦ W (s + r))
        (loewnerMaximalMaps W s z) u := by
  constructor
  · intro hz
    have hadd : z ∈ loewnerUnswallowedDomain W (s + u) := ⟨hzs.1, hz⟩
    have hrhs := (Set.ext_iff.mp (loewnerUnswallowedDomain_add_eq W hs hu) z).mp hadd
    exact hrhs.2.2
  · intro hz
    have hshift : loewnerMaximalMaps W s z ∈
        loewnerUnswallowedDomain (fun r ↦ W (s + r)) u :=
      ⟨loewnerMaximalMaps_mem_upperHalfPlane hzs, hz⟩
    have hrhs : z ∈ loewnerUnswallowedDomain W s ∩
        loewnerMaximalMaps W s ⁻¹'
          loewnerUnswallowedDomain (fun r ↦ W (s + r)) u := ⟨hzs, hshift⟩
    exact ((Set.ext_iff.mp (loewnerUnswallowedDomain_add_eq W hs hu) z).mpr hrhs).2



def loewnerSwallowedSet (W : ℝ → ℝ) (t : ℝ) : Set ℂ :=
  upperHalfPlane \ loewnerUnswallowedDomain W t


theorem loewnerSwallowedSet_subset_upperHalfPlane
    (W : ℝ → ℝ) (t : ℝ) :
    loewnerSwallowedSet W t ⊆ upperHalfPlane :=
  fun _ hz ↦ hz.1



theorem loewnerSwallowedSet_relClosed
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : Set ℂ, IsClosed C ∧
      loewnerSwallowedSet W t = C ∩ upperHalfPlane := by
  refine ⟨(loewnerUnswallowedDomain W t)ᶜ,
    (isOpen_loewnerUnswallowedDomain hW ht).isClosed_compl, ?_⟩
  ext z
  simp only [loewnerSwallowedSet, mem_diff, mem_compl_iff, mem_inter_iff]
  tauto



theorem upperHalfPlane_diff_loewnerSwallowedSet
    (W : ℝ → ℝ) (t : ℝ) :
    upperHalfPlane \ loewnerSwallowedSet W t =
      loewnerUnswallowedDomain W t := by
  ext z
  simp only [loewnerSwallowedSet, mem_diff]
  constructor
  · rintro ⟨hzH, hz⟩
    by_contra hnot
    exact hz ⟨hzH, hnot⟩
  · intro hz
    exact ⟨hz.1, fun hswallowed ↦ hswallowed.2 hz⟩


theorem isOpen_upperHalfPlane_diff_loewnerSwallowedSet
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsOpen (upperHalfPlane \ loewnerSwallowedSet W t) := by
  rw [upperHalfPlane_diff_loewnerSwallowedSet]
  exact isOpen_loewnerUnswallowedDomain hW ht


theorem isConnected_upperHalfPlane_diff_loewnerSwallowedSet
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsConnected (upperHalfPlane \ loewnerSwallowedSet W t) := by
  rw [upperHalfPlane_diff_loewnerSwallowedSet]
  exact isConnected_loewnerUnswallowedDomain hW ht



theorem loewnerSwallowedSet_im_sq_le
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ loewnerSwallowedSet W t) :
    z.im ^ 2 ≤ 8 * t := by
  by_contra hnot
  have hlt : t < z.im ^ 2 / 8 := by
    have : 8 * t < z.im ^ 2 := lt_of_not_ge hnot
    linarith
  exact hz.2 (mem_loewnerUnswallowedDomain_of_lt_im_sq_div_eight
    hW ht hz.1 hlt)



theorem exists_loewnerSwallowedSet_re_bound
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    ∃ R : ℝ, ∀ z ∈ loewnerSwallowedSet W t, |z.re| ≤ R := by
  have hcompact : IsCompact (W '' Icc (0 : ℝ) t) :=
    isCompact_Icc.image_of_continuousOn hW.continuousOn
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hcompact.isBounded
  refine ⟨R + 1, ?_⟩
  intro z hz
  apply abs_le.mpr
  constructor
  · by_contra hnot
    have hzleft : z.re ≤ -R - 1 := by linarith
    have hWlower : ∀ s ∈ Icc (0 : ℝ) t, -R ≤ W s := by
      intro s hs
      have hnorm := hR (W s) ⟨s, hs, rfl⟩
      rw [Real.norm_eq_abs] at hnorm
      linarith [neg_abs_le (W s)]
    exact hz.2 (mem_loewnerUnswallowedDomain_of_driverLowerBarrier
      hW ht (by norm_num) hz.1 hzleft hWlower)
  · by_contra hnot
    have hzright : R + 1 ≤ z.re := by linarith
    have hWupper : ∀ s ∈ Icc (0 : ℝ) t, W s ≤ R := by
      intro s hs
      have hnorm := hR (W s) ⟨s, hs, rfl⟩
      rw [Real.norm_eq_abs] at hnorm
      exact (le_abs_self (W s)).trans hnorm
    exact hz.2 (mem_loewnerUnswallowedDomain_of_driverBarrier
      hW ht (by norm_num) hz.1 hzright hWupper)



theorem loewnerSwallowedSet_isBounded_of_re_bound
    {W : ℝ → ℝ} (hW : Continuous W) {t R : ℝ} (ht : 0 ≤ t)
    (hre : ∀ z ∈ loewnerSwallowedSet W t, |z.re| ≤ R) :
    Bornology.IsBounded (loewnerSwallowedSet W t) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨Real.sqrt (R ^ 2 + 8 * t), ?_⟩
  intro z hz
  have him := loewnerSwallowedSet_im_sq_le hW ht hz
  have hre' := abs_le.mp (hre z hz)
  have hrad : 0 ≤ R ^ 2 + 8 * t := by positivity
  have hsq : ‖z‖ ^ 2 ≤ R ^ 2 + 8 * t := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have hsqrt : Real.sqrt (R ^ 2 + 8 * t) ^ 2 = R ^ 2 + 8 * t :=
    Real.sq_sqrt hrad
  have hnorm : 0 ≤ ‖z‖ := norm_nonneg z
  have hsqrtNonneg : 0 ≤ Real.sqrt (R ^ 2 + 8 * t) := Real.sqrt_nonneg _
  nlinarith


theorem loewnerSwallowedSet_isBounded
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    Bornology.IsBounded (loewnerSwallowedSet W t) := by
  obtain ⟨R, hR⟩ := exists_loewnerSwallowedSet_re_bound hW ht
  exact loewnerSwallowedSet_isBounded_of_re_bound hW ht hR



theorem loewnerSwallowedSet_isCompactHull_of_bounded
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    (hbounded : Bornology.IsBounded (loewnerSwallowedSet W t)) :
    IsCompactHull (loewnerSwallowedSet W t) where
  subset := loewnerSwallowedSet_subset_upperHalfPlane W t
  bounded := hbounded
  relClosed := loewnerSwallowedSet_relClosed hW ht
  complement_open := isOpen_upperHalfPlane_diff_loewnerSwallowedSet hW ht
  complement_connected :=
    isConnected_upperHalfPlane_diff_loewnerSwallowedSet hW ht



theorem loewnerSwallowedSet_isCompactHull_of_re_bound
    {W : ℝ → ℝ} (hW : Continuous W) {t R : ℝ} (ht : 0 ≤ t)
    (hre : ∀ z ∈ loewnerSwallowedSet W t, |z.re| ≤ R) :
    IsCompactHull (loewnerSwallowedSet W t) :=
  loewnerSwallowedSet_isCompactHull_of_bounded hW ht
    (loewnerSwallowedSet_isBounded_of_re_bound hW ht hre)



theorem loewnerSwallowedSet_isCompactHull
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsCompactHull (loewnerSwallowedSet W t) :=
  loewnerSwallowedSet_isCompactHull_of_bounded hW ht
    (loewnerSwallowedSet_isBounded hW ht)


theorem loewnerSwallowedSet_zero {W : ℝ → ℝ} (hW : Continuous W) :
    loewnerSwallowedSet W 0 = ∅ := by
  ext z
  constructor
  · intro hz
    exact False.elim (hz.2 (mem_loewnerUnswallowedDomain_zero hW hz.1))
  · simp


theorem loewnerSwallowedSet_monotoneOn (W : ℝ → ℝ) :
    MonotoneOn (loewnerSwallowedSet W) (Ici (0 : ℝ)) := by
  intro s hs t ht hst z hz
  refine ⟨hz.1, ?_⟩
  intro hzt
  exact hz.2 (loewnerUnswallowedDomain_antitoneOn W hs ht hst hzt)

end StatMech.SLE
