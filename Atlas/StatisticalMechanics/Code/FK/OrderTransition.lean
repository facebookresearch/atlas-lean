/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Code.FK.CriticalPoint
import Code.FK.IvProperties
import Code.FK.DlrSandwich
import Code.BeffaraDC.SelfDualValue

open MeasureTheory
open scoped NNReal

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation














noncomputable def fkThetaFree (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : ℝ :=
  ((freeInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d)


theorem fkThetaFree_nonneg (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 ≤ fkThetaFree d hp hp1 hq (q := q) :=
  ENNReal.toReal_nonneg


theorem fkThetaFree_le_one (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkThetaFree d hp hp1 hq (q := q) ≤ 1 := by
  unfold fkThetaFree
  rw [Measure.real]
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one















def IsFirstOrderTransition (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : Prop :=
  fkThetaFree d hp hp1 hq (q := q) = 0 ∧ 0 < fkTheta d hp hp1 hq (q := q)

















theorem firstOrderTransition_of_contour (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hFree : fkThetaFree d hp hp1 hq (q := q) = 0)
    (hWired : 0 < fkTheta d hp hp1 hq (q := q)) :
    IsFirstOrderTransition d hp hp1 hq :=
  ⟨hFree, hWired⟩




theorem fkThetaFree_ne_fkTheta_of_firstOrder (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (h : IsFirstOrderTransition d hp hp1 hq) :
    fkThetaFree d hp hp1 hq (q := q) ≠ fkTheta d hp hp1 hq (q := q) := by
  obtain ⟨hFree, hWired⟩ := h
  rw [hFree]
  exact ne_of_lt hWired






theorem freeInfiniteVolume_ne_wiredInfiniteVolume_of_firstOrder (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (h : IsFirstOrderTransition d hp hp1 hq) :
    freeInfiniteVolume d hp hp1 hq ≠ wiredInfiniteVolume d hp hp1 hq := by
  intro heq
  refine fkThetaFree_ne_fkTheta_of_firstOrder d hp hp1 hq h ?_
  unfold fkThetaFree fkTheta
  rw [heq]























theorem order_transition_q_large {q : ℝ} (hq : 4 < q)
    (hpos : 0 < BeffaraDC.selfDualPoint q)
    (hlt : BeffaraDC.selfDualPoint q < 1)
    (hFree : fkThetaFree 2 hpos hlt (by linarith : (0 : ℝ) < q) (q := q) = 0)
    (hWired : 0 < fkTheta 2 hpos hlt (by linarith : (0 : ℝ) < q) (q := q)) :
    IsFirstOrderTransition 2 hpos hlt (by linarith : (0 : ℝ) < q)
      ∧ freeInfiniteVolume 2 hpos hlt (by linarith : (0 : ℝ) < q)
          ≠ wiredInfiniteVolume 2 hpos hlt (by linarith : (0 : ℝ) < q) := by
  have hfo : IsFirstOrderTransition 2 hpos hlt (by linarith : (0 : ℝ) < q) :=
    firstOrderTransition_of_contour 2 hpos hlt _ hFree hWired
  exact ⟨hfo, freeInfiniteVolume_ne_wiredInfiniteVolume_of_firstOrder 2 hpos hlt _ hfo⟩







theorem order_transition_q_large_selfDual {q : ℝ} (hq : 4 < q)
    (hFree : fkThetaFree 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2
        (by linarith : (0 : ℝ) < q) (q := q) = 0)
    (hWired : 0 < fkTheta 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2
        (by linarith : (0 : ℝ) < q) (q := q)) :
    IsFirstOrderTransition 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2
        (by linarith : (0 : ℝ) < q)
      ∧ freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
          (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2
          (by linarith : (0 : ℝ) < q)
        ≠ wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
            (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2
            (by linarith : (0 : ℝ) < q) :=
  order_transition_q_large hq
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
    (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2 hFree hWired

end FK

end StatMech
