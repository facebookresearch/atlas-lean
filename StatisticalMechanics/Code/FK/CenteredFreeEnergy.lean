/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.FK.FKUniqPerEdge
import Code.FK.WiredPressureDeriv
import Code.FK.FKDensityDeriv
import Code.FK.QuadrantPartition

open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace StatMech

namespace FK

open StatMech.Lattice



variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]




noncomputable def cfe_centered (q : ℝ) (t : ℝ) : ℝ :=
  ivp2_tiltFreeEnergy G q t - ivp2_tiltFreeEnergy G q 0

@[simp] theorem cfe_centered_zero (q : ℝ) : cfe_centered G q 0 = 0 := by
  unfold cfe_centered; ring


theorem cfe_centered_convexOn (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) :
    ConvexOn ℝ univ (cfe_centered G q) := by
  have hconv : ConvexOn ℝ univ (ivp2_tiltFreeEnergy G q) :=
    ivp2_tiltFreeEnergy_convexOn G q hq hE
  have heq : cfe_centered G q
      = (fun t => ivp2_tiltFreeEnergy G q t + (- ivp2_tiltFreeEnergy G q 0)) := by
    funext t; unfold cfe_centered; ring
  rw [heq]
  exact hconv.add_const _



theorem cfe_centered_hasDerivAt (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    HasDerivAt (cfe_centered G 2) (fpd_avgDensity G t) t := by
  have hbase : HasDerivAt (ivp2_tiltFreeEnergy G 2) (fpd_avgDensity G t) t := by
    have h := fpd_tiltFreeEnergy_deriv_eq_avgDensity G hE t
    rwa [show (1 / (G.edgeFinset.card : ℝ)) * fkExpect G (fsc_logistic t) 2
        (fun ω => (openCount G ω : ℝ)) = fpd_avgDensity G t from rfl] at h
  exact hbase.sub_const (ivp2_tiltFreeEnergy G 2 0)









theorem cfe_avgDensity_mem_Icc (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    0 ≤ fpd_avgDensity G t ∧ fpd_avgDensity G t ≤ 1 := by
  have hp0 : (0:ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  set p := fsc_logistic t with hp
  have hEr : (0:ℝ) < (G.edgeFinset.card : ℝ) := by exact_mod_cast hE
  
  have hsum1 : ∑ ω : ConfigSpace (Sym2 V), fkProb G p 2 ω = 1 :=
    fkProb_sum_eq_one G hp0 hp1 (by norm_num)
  have hnn : 0 ≤ fkExpect G p 2 (fun ω => (openCount G ω : ℝ)) := by
    unfold fkExpect
    apply Finset.sum_nonneg
    intro ω _
    exact mul_nonneg (fkProb_nonneg G hp0 hp1 (by norm_num) ω) (by positivity)
  have hle : fkExpect G p 2 (fun ω => (openCount G ω : ℝ)) ≤ (G.edgeFinset.card : ℝ) := by
    unfold fkExpect
    calc ∑ ω : ConfigSpace (Sym2 V), fkProb G p 2 ω * (openCount G ω : ℝ)
        ≤ ∑ ω : ConfigSpace (Sym2 V), fkProb G p 2 ω * (G.edgeFinset.card : ℝ) := by
          apply Finset.sum_le_sum
          intro ω _
          apply mul_le_mul_of_nonneg_left _ (fkProb_nonneg G hp0 hp1 (by norm_num) ω)
          have : openCount G ω ≤ G.edgeFinset.card := by
            unfold openCount; exact Finset.card_filter_le _ _
          exact_mod_cast this
      _ = (∑ ω : ConfigSpace (Sym2 V), fkProb G p 2 ω) * (G.edgeFinset.card : ℝ) := by
          rw [← Finset.sum_mul]
      _ = (G.edgeFinset.card : ℝ) := by rw [hsum1, one_mul]
  refine ⟨?_, ?_⟩
  · unfold fpd_avgDensity; positivity
  · unfold fpd_avgDensity
    rw [div_mul_eq_mul_div, one_mul, div_le_one hEr]
    exact hle


theorem cfe_centered_monotone (hE : 0 < G.edgeFinset.card) :
    Monotone (cfe_centered G 2) :=
  monotone_of_hasDerivAt_nonneg (fun x => cfe_centered_hasDerivAt G hE x)
    (fun x => (cfe_avgDensity_mem_Icc G hE x).1)


theorem cfe_id_sub_centered_monotone (hE : 0 < G.edgeFinset.card) :
    Monotone (fun t => t - cfe_centered G 2 t) := by
  refine monotone_of_hasDerivAt_nonneg
    (f' := fun x => 1 - fpd_avgDensity G x) (fun x => ?_) (fun x => ?_)
  · exact (hasDerivAt_id x).sub (cfe_centered_hasDerivAt G hE x)
  · have := (cfe_avgDensity_mem_Icc G hE x).2
    change (0 : ℝ) ≤ 1 - fpd_avgDensity G x
    linarith






theorem cfe_centered_abs_le (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    |cfe_centered G 2 t| ≤ |t| := by
  have hmono := cfe_centered_monotone G hE
  have hmono2 := cfe_id_sub_centered_monotone G hE
  have h0 : cfe_centered G 2 0 = 0 := cfe_centered_zero G 2
  rcases le_or_gt 0 t with ht | ht
  · 
    have hge : 0 ≤ cfe_centered G 2 t := by
      have := hmono ht; rw [h0] at this; exact this
    have hle : cfe_centered G 2 t ≤ t := by
      have := hmono2 ht; simp only at this; rw [h0] at this; linarith
    rw [abs_of_nonneg hge, abs_of_nonneg ht]; exact hle
  · 
    have hle : cfe_centered G 2 t ≤ 0 := by
      have := hmono ht.le; rw [h0] at this; exact this
    have hge : t ≤ cfe_centered G 2 t := by
      have := hmono2 ht.le; simp only at this; rw [h0] at this; linarith
    rw [abs_of_nonpos hle, abs_of_nonpos ht.le]; linarith










section Wired

variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def cfe_wiredCentered (q : ℝ) (t : ℝ) : ℝ :=
  wpd_wiredTiltFreeEnergy G bdry q t - wpd_wiredTiltFreeEnergy G bdry q 0

@[simp] theorem cfe_wiredCentered_zero (q : ℝ) : cfe_wiredCentered G bdry q 0 = 0 := by
  unfold cfe_wiredCentered; ring


theorem cfe_wiredCentered_convexOn (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) :
    ConvexOn ℝ univ (cfe_wiredCentered G bdry q) := by
  have hconv : ConvexOn ℝ univ (wpd_wiredTiltFreeEnergy G bdry q) :=
    wpd_wiredTiltFreeEnergy_convexOn G bdry q hq hE
  have heq : cfe_wiredCentered G bdry q
      = (fun t => wpd_wiredTiltFreeEnergy G bdry q t + (- wpd_wiredTiltFreeEnergy G bdry q 0)) := by
    funext t; unfold cfe_wiredCentered; ring
  rw [heq]; exact hconv.add_const _



theorem cfe_wiredCentered_hasDerivAt (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    HasDerivAt (cfe_wiredCentered G bdry 2) (wpd_avgWiredDensity G bdry 2 t) t := by
  have hbase : HasDerivAt (wpd_wiredTiltFreeEnergy G bdry 2) (wpd_avgWiredDensity G bdry 2 t) t := by
    have h := wpd_wiredTiltFreeEnergy_hasDerivAt G bdry 2 (by norm_num) hE t
    rwa [show (1 / (G.edgeFinset.card : ℝ))
        * wpd_wiredFkExpect G bdry (fsc_logistic t) 2 (fun ω => (openCount G ω : ℝ))
        = wpd_avgWiredDensity G bdry 2 t from rfl] at h
  exact hbase.sub_const (wpd_wiredTiltFreeEnergy G bdry 2 0)

end Wired








variable {d : ℕ}




def cfe_CenteredConvergence (d : ℕ) (G : ℝ → ℝ) : Prop :=
  (∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) ∧ G 0 = 0



theorem cfe_centered_limit_convexOn (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hconv : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
    ConvexOn ℝ univ G :=
  ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
    (fun n => cfe_centered (boxGraph d n) 2) G
    (fun n => cfe_centered_convexOn (boxGraph d n) 2 (by norm_num) (hE n))
    hconv









theorem cfe_wiredCentered_tendsto (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (t : ℝ)
    (hfree : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hsv : Tendsto (fun n =>
        ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 (G t)) := by
  
  have hdiff : ∀ s : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 s
        - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 s) atTop (𝓝 0) := by
    intro s
    have hbound : ∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 s
          - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 s|
        ≤ ((Finset.univ.filter (boxBoundary d n)).card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ) * Real.log 2 := fun n =>
      wpd_tiltFreeEnergy_sub_le (boxGraph d n) (boxBoundary d n) (by norm_num) (hE n) s
    have hsvlog : Tendsto (fun n =>
        ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)
          * Real.log 2) atTop (𝓝 0) := by
      have := hsv.mul_const (Real.log 2); simpa using this
    refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
    exact squeeze_zero (fun n => abs_nonneg _) hbound hsvlog
  
  have hcdiff : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t
        - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 0) := by
    have heq : (fun n => cfe_centered (boxGraph d n) 2 t
          - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t)
        = (fun n => (ivp2_tiltFreeEnergy (boxGraph d n) 2 t
            - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t)
          - (ivp2_tiltFreeEnergy (boxGraph d n) 2 0
            - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 0)) := by
      funext n; unfold cfe_centered cfe_wiredCentered; ring
    rw [heq]
    have := (hdiff t).sub (hdiff 0)
    simpa using this
  
  have hwired : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t
        - (cfe_centered (boxGraph d n) 2 t
          - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t)) atTop (𝓝 (G t - 0)) :=
    hfree.sub hcdiff
  simpa using hwired















theorem cfe_genuineFreeIsLeftDeriv (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hcol : fpe2_GenuineFreeCollapse d N) :
    fpe2_GenuineFreeIsLeftDeriv d N G := by
  intro e' he' t
  have hbL : ∀ s, pressureLeftDeriv G s
      ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    exact fdd_leftDeriv_le_avgLimit
      (fun n => cfe_centered (boxGraph d n) 2) G
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => cfe_centered_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d n) (hEbox n) u)
      hboxfree s _ hG (hcol e' he' s)
  have hbR : ∀ s, freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv G s := by
    intro s
    exact fdd_avgLimit_le_rightDeriv
      (fun n => cfe_centered (boxGraph d n) 2) G
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => cfe_centered_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d n) (hEbox n) u)
      hboxfree s _ hG (hcol e' he' s)
  exact fdd_eq_leftDeriv_of_bracket_leftContinuous hG hbL hbR
    (osc_freeEdgeDensity_left_continuous d N e' t)





theorem cfe_genuineWiredIsRightDeriv (hd : 1 ≤ d) (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    fpe2_GenuineWiredIsRightDeriv d N G := by
  have hsv := fup_surfaceVolume_tendsto_zero d hd
  have hwiredlim : ∀ t,
      Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t)
        atTop (𝓝 (G t)) :=
    fun t => cfe_wiredCentered_tendsto hEbox t (hboxfree t) hsv
  intro e' he' t
  have hbL : ∀ s, pressureLeftDeriv G s
      ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    refine (?_ : pressureLeftDeriv G s
        ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)).trans
      (freeEdgeDensity_q2_le_wiredEdgeDensity d N e' (fsc_logistic_pos s) (fsc_logistic_lt_one s))
    exact fdd_leftDeriv_le_avgLimit
      (fun n => cfe_centered (boxGraph d n) 2) G
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => cfe_centered_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d n) (hEbox n) u)
      hboxfree s _ hG (hcolfree e' he' s)
  have hbR : ∀ s, wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv G s := by
    intro s
    exact fdd_avgLimit_le_rightDeriv
      (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2) G
      (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2)
      (fun n => cfe_wiredCentered_convexOn (boxGraph d n) (boxBoundary d n) 2 (by norm_num) (hEbox n))
      (fun n u => cfe_wiredCentered_hasDerivAt (boxGraph d n) (boxBoundary d n) (hEbox n) u)
      hwiredlim s _ hG (hcolwired e' he' s)
  exact fdd_eq_rightDeriv_of_bracket_rightContinuous hG hbL hbR
    (osc_wiredEdgeDensity_right_continuous d N e' t)



















theorem cfe_fk_uniqueness_of_centeredConvergence (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fpe2_fk_uniqueness_of_genuine (lt_of_lt_of_le one_pos hd) N eb heb hG
    (cfe_genuineFreeIsLeftDeriv N hEbox hG hboxfree hcolfree)
    (cfe_genuineWiredIsRightDeriv hd N hEbox hG hboxfree hcolfree hcolwired)













theorem cfe_fk_uniqueness_of_centeredData (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  cfe_fk_uniqueness_of_centeredConvergence hd N eb heb hEbox hG hboxfree
    (gec_GenuineFreeCollapse hd N hEbox)
    (gec_GenuineWiredCollapse hd N hEbox)














theorem cfe_centeredConvergence_satisfiable :
    ∃ (gn : ℕ → ℝ → ℝ) (G : ℝ → ℝ),
      (∀ t, Tendsto (fun n => gn n t) atTop (𝓝 (G t))) ∧ G 0 = 0 ∧ ConvexOn ℝ univ G := by
  refine ⟨fun _ _ => 0, fun _ => 0, fun t => tendsto_const_nhds, rfl, ?_⟩
  exact convexOn_const 0 convex_univ















































theorem cfe_residue_remark : True := trivial

end FK

end StatMech
