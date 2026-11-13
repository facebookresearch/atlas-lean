/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Code.FK.CriticalPoint
import Code.FK.OrderTransition
import Code.Percolation.Sharpness
import Code.Percolation.BurtonKeaneMerge
import Code.Foundations.StochasticDomination

open MeasureTheory
open scoped NNReal

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation











theorem frp_fkSubcriticalSet_bddAbove (d : ℕ) (q : ℝ) :
    BddAbove (fkSubcriticalSet d q) := by
  refine ⟨1, ?_⟩
  rintro p ⟨_, hp1, _, _⟩
  exact le_of_lt hp1











theorem frp_fkTheta_pos_of_gt_fkPc (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hpc : fkPc d q < p) :
    0 < fkTheta d hp hp1 hq (q := q) := by
  rcases (fkTheta_nonneg d hp hp1 hq (q := q)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hmem : p ∈ fkSubcriticalSet d q := ⟨hp, hp1, hq, h.symm⟩
    have hle : p ≤ fkPc d q := le_csSup (frp_fkSubcriticalSet_bddAbove d q) hmem
    exact absurd hle (not_le.mpr hpc)










theorem frp_measurableSet_percolationEvent (d : ℕ) :
    MeasurableSet (Percolation.percolationEvent d) := by
  rw [Percolation.percolationEvent_eq_iInter]
  exact MeasurableSet.iInter (fun n => Percolation.measurableSet_crossingEvent' (n + 1))




theorem frp_isIncreasing_percolationEvent (d : ℕ) :
    IsIncreasing (Percolation.percolationEvent d) := by
  intro ω ω' h hω
  rw [Percolation.mem_percolationEvent] at hω ⊢
  exact hω.mono (Percolation.cluster_mono h (Percolation.origin d))


























theorem frp_free_percolation_above_pc (d : ℕ) {p p' q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hp' : 0 < p') (hp1' : p' < 1)
    (hpc' : fkPc d q < p')
    (hmono : (freeInfiniteVolume d hp' hp1' hq : Measure (ConfigSpace (Sym2 (Site d))))
        ≼ (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
    (huniq : fkThetaFree d hp' hp1' hq (q := q) = fkTheta d hp' hp1' hq (q := q)) :
    0 < fkThetaFree d hp hp1 hq (q := q) := by
  
  have hwired : 0 < fkTheta d hp' hp1' hq (q := q) :=
    frp_fkTheta_pos_of_gt_fkPc d hp' hp1' hq hpc'
  
  have hfree' : 0 < fkThetaFree d hp' hp1' hq (q := q) := huniq ▸ hwired
  
  
  have hmono' : fkThetaFree d hp' hp1' hq (q := q) ≤ fkThetaFree d hp hp1 hq (q := q) :=
    hmono (Percolation.percolationEvent d) (frp_measurableSet_percolationEvent d)
      (frp_isIncreasing_percolationEvent d)
  exact lt_of_lt_of_le hfree' hmono'





theorem frp_free_percolation_above_pc_of_countable_agreement
    (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hpc : fkPc d q < p) (bad : Set ℝ) (hbad : bad.Countable)
    (hmono : ∀ {p' : ℝ} (hp' : 0 < p') (hp1' : p' < 1), fkPc d q < p' →
      (freeInfiniteVolume d hp' hp1' hq : Measure (ConfigSpace (Sym2 (Site d))))
        ≼ (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
    (hagree : ∀ {p' : ℝ} (hp' : 0 < p') (hp1' : p' < 1), fkPc d q < p' →
      p' ∉ bad →
      fkThetaFree d hp' hp1' hq (q := q) = fkTheta d hp' hp1' hq (q := q)) :
    0 < fkThetaFree d hp hp1 hq (q := q) := by
  let a := max (fkPc d q) 0
  have hap : a < p := max_lt hpc hp
  have hI : (Set.Ioo a p).Nonempty := Set.nonempty_Ioo.mpr hap
  obtain ⟨p', hp'bad, hp'I⟩ :=
    (hbad.dense_compl ℝ).exists_mem_open isOpen_Ioo hI
  have hp' : 0 < p' := lt_of_le_of_lt (le_max_right _ _) hp'I.1
  have hp1' : p' < 1 := hp'I.2.trans hp1
  have hpc' : fkPc d q < p' := lt_of_le_of_lt (le_max_left _ _) hp'I.1
  exact frp_free_percolation_above_pc d hp hp1 hq hp' hp1' hpc'
    (hmono hp' hp1' hpc') (hagree hp' hp1' hpc' hp'bad)

end FK

end StatMech
