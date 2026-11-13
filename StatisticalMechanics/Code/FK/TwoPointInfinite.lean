/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Code.FK.InfiniteVolume
import Code.FK.TwoPoint
import Code.FK.Limits
import Code.Foundations.MonotoneLimit

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators NNReal Topology

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice










variable {E : Type*} [Countable E]


theorem bddAbove_range_apply (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) : BddAbove (Set.range (fun n => (μ n) A)) :=
  ⟨1, by rintro x ⟨n, rfl⟩; exact apply_le_one _ _⟩






noncomputable def ivTwoPointSup (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) : NNReal :=
  ⨆ n, (μ n) A





noncomputable def ivTwoPointInf (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) : NNReal :=
  ⨅ n, (μ n) A


theorem le_ivTwoPointSup (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) (n : ℕ) : (μ n) A ≤ ivTwoPointSup μ A :=
  le_ciSup (bddAbove_range_apply μ A) n


theorem ivTwoPointInf_le (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) (n : ℕ) : ivTwoPointInf μ A ≤ (μ n) A :=
  ciInf_le (OrderBot.bddBelow _) n





theorem ivTwoPointSup_pos (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) {n : ℕ} (hn : 0 < (μ n) A) : 0 < ivTwoPointSup μ A :=
  lt_of_lt_of_le hn (le_ivTwoPointSup μ A n)




theorem ivTwoPointInf_pos_of_uniform (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) {c : NNReal} (hc : 0 < c) (hbound : ∀ n, c ≤ (μ n) A) :
    0 < ivTwoPointInf μ A :=
  lt_of_lt_of_le hc (le_ciInf hbound)







theorem ivTwoPointSup_isLimit (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (hchain : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ (μ (n + 1) : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    Tendsto (fun n => (μ n) A) atTop (𝓝 (ivTwoPointSup μ A)) :=
  tendsto_NNReal_of_monotone_isIncreasing hchain hAclopen hAinc







theorem ivTwoPointInf_isLimit (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (hchain : ∀ n, (μ (n + 1) : Measure (ConfigSpace E)) ≼ (μ n : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    Tendsto (fun n => (μ n) A) atTop (𝓝 (ivTwoPointInf μ A)) := by
  have hAmeas := IsClopen.measurableSet_configSpace hAclopen
  have hanti : Antitone (fun n => (μ n) A) := by
    apply antitone_nat_of_succ_le
    intro n
    have hreal : (μ (n + 1) : Measure (ConfigSpace E)).real A
        ≤ (μ n : Measure (ConfigSpace E)).real A := hchain n A hAmeas hAinc
    rw [← ProbabilityMeasure.coe_apply_eq_real, ← ProbabilityMeasure.coe_apply_eq_real] at hreal
    exact_mod_cast hreal
  exact tendsto_atTop_ciInf hanti (OrderBot.bddBelow _)











def boxRestrict (d n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    ConfigSpace (Sym2 (boxVerts d n)) :=
  fun eb => ω (edgeIncl d n eb)



theorem continuous_boxRestrict (d n : ℕ) : Continuous (boxRestrict d n) :=
  continuous_pi (fun eb => continuous_apply (edgeIncl d n eb))



theorem monotone_boxRestrict (d n : ℕ) : Monotone (boxRestrict d n) :=
  fun _ _ hab eb => hab (edgeIncl d n eb)





def boxConnEvent (d n : ℕ) (x y : boxVerts d n) : Set (ConfigSpace (Sym2 (Site d))) :=
  boxRestrict d n ⁻¹' (connEvent (boxGraph d n) x y)





theorem isClopen_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    IsClopen (boxConnEvent d n x y) :=
  IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩ (continuous_boxRestrict d n)


theorem measurableSet_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    MeasurableSet (boxConnEvent d n x y) :=
  (isClopen_boxConnEvent d n x y).isOpen.measurableSet





theorem isIncreasing_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    IsIncreasing (boxConnEvent d n x y) :=
  fun _ _ hab ha => connEvent_isIncreasing (boxGraph d n) x y (monotone_boxRestrict d n hab) ha




theorem boxRestrict_extendEdge (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    boxRestrict d n (extendEdge d n ω) = ω := by
  funext eb
  unfold boxRestrict extendEdge
  have hmem : edgeIncl d n eb ∈ Set.range (edgeIncl d n) := ⟨eb, rfl⟩
  rw [dif_pos hmem]
  congr 1
  exact edgeIncl_injective d n hmem.choose_spec




theorem extendEdge_preimage_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    extendEdge d n ⁻¹' (boxConnEvent d n x y) = connEvent (boxGraph d n) x y := by
  ext ω
  simp only [boxConnEvent, Set.mem_preimage, boxRestrict_extendEdge]






theorem freeFiniteMeasure_real_boxConnEvent (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d n) :
    (freeFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxConnEvent d n x y)
      = twoPointFun (boxGraph d n) p q x y := by
  have hA : MeasurableSet (boxConnEvent d n x y) := measurableSet_boxConnEvent d n x y
  have hfree : (freeFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y)
      = ((fkPMF (boxGraph d n) hp hp1 hq).toMeasure
          (extendEdge d n ⁻¹' (boxConnEvent d n x y))).toReal := by
    unfold freeFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hfree, extendEdge_preimage_boxConnEvent, fkPMF_toMeasure_toReal]
  unfold twoPointFun
  exact Finset.sum_congr rfl fun ω _ => mul_comm _ _




theorem wiredFkProb_pos {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) :
    0 < wiredFkProb G bdry p q ω :=
  div_pos (wiredFkWeight_pos G bdry hp hp1 hq ω) (wiredFkZ_pos G bdry hp hp1 hq)




theorem wiredFiniteMeasure_real_boxConnEvent (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d n) :
    (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxConnEvent d n x y)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (connEvent (boxGraph d n) x y).indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hA : MeasurableSet (boxConnEvent d n x y) := measurableSet_boxConnEvent d n x y
  have hw : (wiredFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y)
      = ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure
          (extendEdge d n ⁻¹' (boxConnEvent d n x y))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hw, extendEdge_preimage_boxConnEvent, wiredFkPMF_toMeasure_toReal]






theorem freeFiniteMeasure_apply_boxConnEvent_pos (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d n}
    (h : (boxGraph d n).Reachable x y) :
    0 < (freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d n x y) := by
  have hreal : 0 < (freeFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y) := by
    rw [freeFiniteMeasure_real_boxConnEvent]
    exact twoPointFun_pos_of_reachable (boxGraph d n) hp hp1 hq h
  rw [← ProbabilityMeasure.coe_apply_eq_real] at hreal
  exact_mod_cast hreal



theorem wiredFiniteMeasure_apply_boxConnEvent_pos (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d n}
    (h : (boxGraph d n).Reachable x y) :
    0 < (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d n x y) := by
  have hreal : 0 < (wiredFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y) := by
    rw [wiredFiniteMeasure_real_boxConnEvent]
    apply Finset.sum_pos'
    · intro ω _
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
        (wiredFkProb_pos (boxGraph d n) (boxBoundary d n) hp hp1 hq ω).le
    · refine ⟨fun _ => true, Finset.mem_univ _, ?_⟩
      rw [Set.indicator_of_mem (allOpen_mem_connEvent (boxGraph d n) h), one_mul]
      exact wiredFkProb_pos (boxGraph d n) (boxBoundary d n) hp hp1 hq _
  rw [← ProbabilityMeasure.coe_apply_eq_real] at hreal
  exact_mod_cast hreal

















noncomputable def freeIvTwoPoint (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d N) : NNReal :=
  ivTwoPointSup (fun n => freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)










noncomputable def wiredIvTwoPoint (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d N) : NNReal :=
  ivTwoPointInf (fun n => wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)












theorem freeIvTwoPoint_pos (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d N}
    (h : (boxGraph d N).Reachable x y) :
    0 < freeIvTwoPoint d N hp hp1 hq x y :=
  ivTwoPointSup_pos _ _ (freeFiniteMeasure_apply_boxConnEvent_pos d N hp hp1 hq h)



theorem freeIvTwoPoint_self_pos (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x : boxVerts d N) :
    0 < freeIvTwoPoint d N hp hp1 hq x x :=
  freeIvTwoPoint_pos d N hp hp1 hq (SimpleGraph.Reachable.refl x)













theorem wiredIvTwoPoint_pos_of_uniform (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d N} {c : NNReal} (hc : 0 < c)
    (hbound : ∀ n, c ≤ (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) :
    0 < wiredIvTwoPoint d N hp hp1 hq x y :=
  ivTwoPointInf_pos_of_uniform _ _ hc hbound










theorem freeIvTwoPoint_isLimit (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hchain : ∀ n, (freeFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
        ≼ (freeFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
    (x y : boxVerts d N) :
    Tendsto (fun n => (freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) atTop
      (𝓝 (freeIvTwoPoint d N hp hp1 hq x y)) :=
  ivTwoPointSup_isLimit _ hchain (isClopen_boxConnEvent d N x y) (isIncreasing_boxConnEvent d N x y)










theorem wiredIvTwoPoint_isLimit (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hchain : ∀ n, (wiredFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
        ≼ (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
    (x y : boxVerts d N) :
    Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) atTop
      (𝓝 (wiredIvTwoPoint d N hp hp1 hq x y)) :=
  ivTwoPointInf_isLimit _ hchain (isClopen_boxConnEvent d N x y) (isIncreasing_boxConnEvent d N x y)

end FK

end StatMech
