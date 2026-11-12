/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































import Code.FK.InfiniteVolume
import Code.Percolation.Theta

open MeasureTheory
open scoped NNReal

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation







noncomputable def fkTheta (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : ℝ :=
  ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (percolationEvent d)



theorem fkTheta_nonneg (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 ≤ fkTheta d hp hp1 hq (q := q) :=
  ENNReal.toReal_nonneg



theorem fkTheta_le_one (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkTheta d hp hp1 hq (q := q) ≤ 1 := by
  unfold fkTheta
  rw [Measure.real]
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one





def fkSubcriticalSet (d : ℕ) (q : ℝ) : Set ℝ :=
  {p : ℝ | ∃ (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q), fkTheta d hp hp1 hq (q := q) = 0}

@[simp]
theorem mem_fkSubcriticalSet {d : ℕ} {q : ℝ} {p : ℝ} :
    p ∈ fkSubcriticalSet d q ↔
      ∃ (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q), fkTheta d hp hp1 hq (q := q) = 0 :=
  Iff.rfl






noncomputable def fkPc (d : ℕ) (q : ℝ) : ℝ :=
  sSup (fkSubcriticalSet d q)

end FK

end StatMech
