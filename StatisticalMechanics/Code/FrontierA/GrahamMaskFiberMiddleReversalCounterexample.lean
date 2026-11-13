/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamMaskFiberMiddleReversal
import Code.FrontierA.GrahamThreeGateBoundaryCounterexample









open Finset

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent



def canonicalGateCounterColoring :
    ↑canonicalGateCounterSupport → Fin 4 :=
  coloringOfRowData canonicalGateCounterSupport canonicalGateCounterK
    canonicalGateCounterC0 canonicalGateCounterC2

theorem canonicalGateCounterColoring_leftSourcePattern :
    LeftSourcePattern canonicalGateCounterEnds canonicalGateCounterSupport
      {0, 1} {1, 2} canonicalGateCounterColoring := by
  have hc := colorClasses_coloringOfRowData
    (m := canonicalGateCounterSupport) (K := canonicalGateCounterK)
    (P := canonicalGateCounterC0) (Q := canonicalGateCounterC2)
    (by decide) (by decide) (by decide)
  rw [LeftSourcePattern]
  simp only [canonicalGateCounterColoring]
  rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  exact canonicalGateCounter_cell_sources


def canonicalGateCounterMaskProfile : Finset (Fin 21) × Finset (Fin 21) :=
  fourColorMaskProfile canonicalGateCounterSupport canonicalGateCounterColoring


def canonicalGateCounterSourcePoint :
    leftSourceMaskFiber canonicalGateCounterEnds canonicalGateCounterSupport
      0 1 2 3 canonicalGateCounterMaskProfile :=
  ⟨canonicalGateCounterColoring,
    canonicalGateCounterColoring_leftSourcePattern, rfl⟩

theorem canonicalGateCounterColoring_rows :
    rowClass canonicalGateCounterSupport canonicalGateCounterColoring 0 =
        canonicalGateCounterK ∧
      rowClass canonicalGateCounterSupport canonicalGateCounterColoring 1 =
        canonicalGateCounterL := by
  have hr := rowClasses_coloringOfRowData
    (m := canonicalGateCounterSupport) (K := canonicalGateCounterK)
    (P := canonicalGateCounterC0) (Q := canonicalGateCounterC2)
    (by decide) (by decide) (by decide)
  exact ⟨hr.1, hr.2.trans canonicalGateCounter_rows_partition.1⟩

theorem canonicalGateCounterColoring_middleSwap_rows :
    rowClass canonicalGateCounterSupport
        (middleSwap canonicalGateCounterSupport canonicalGateCounterColoring) 0 =
        canonicalGateCounterA ∧
      rowClass canonicalGateCounterSupport
        (middleSwap canonicalGateCounterSupport canonicalGateCounterColoring) 1 =
        canonicalGateCounterB := by
  have hc := colorClasses_coloringOfRowData
    (m := canonicalGateCounterSupport) (K := canonicalGateCounterK)
    (P := canonicalGateCounterC0) (Q := canonicalGateCounterC2)
    (by decide) (by decide) (by decide)
  constructor
  · rw [rowClass_zero, colorClass_middleSwap, colorClass_middleSwap]
    have h0 : Equiv.swap (1 : Fin 4) 2 0 = 0 := by decide
    have h1 : Equiv.swap (1 : Fin 4) 2 1 = 2 := by decide
    rw [h0, h1]
    change colorClass canonicalGateCounterSupport
        (coloringOfRowData canonicalGateCounterSupport canonicalGateCounterK
          canonicalGateCounterC0 canonicalGateCounterC2) 0 ∪
      colorClass canonicalGateCounterSupport
        (coloringOfRowData canonicalGateCounterSupport canonicalGateCounterK
          canonicalGateCounterC0 canonicalGateCounterC2) 2 = _
    rw [hc.1, hc.2.2.1]
    decide
  · rw [rowClass_one, colorClass_middleSwap, colorClass_middleSwap]
    have h2 : Equiv.swap (1 : Fin 4) 2 2 = 1 := by decide
    have h3 : Equiv.swap (1 : Fin 4) 2 3 = 3 := by decide
    rw [h2, h3]
    change colorClass canonicalGateCounterSupport
        (coloringOfRowData canonicalGateCounterSupport canonicalGateCounterK
          canonicalGateCounterC0 canonicalGateCounterC2) 1 ∪
      colorClass canonicalGateCounterSupport
        (coloringOfRowData canonicalGateCounterSupport canonicalGateCounterK
          canonicalGateCounterC0 canonicalGateCounterC2) 3 = _
    rw [hc.2.1, hc.2.2.2]
    decide

private theorem canonicalGateCounterA_conn :
    connK canonicalGateCounterEnds canonicalGateCounterA 1 3 := by
  have h12 : connK canonicalGateCounterEnds canonicalGateCounterA 1 2 :=
    Relation.ReflTransGen.single ⟨6, by simp [canonicalGateCounterA],
      by simp [canonicalGateCounterEnds], by simp [canonicalGateCounterEnds], by decide⟩
  have h25 : adjStep canonicalGateCounterEnds canonicalGateCounterA 2 5 :=
    ⟨13, by simp [canonicalGateCounterA], by simp [canonicalGateCounterEnds],
      by simp [canonicalGateCounterEnds], by decide⟩
  have h53 : adjStep canonicalGateCounterEnds canonicalGateCounterA 5 3 :=
    ⟨16, by simp [canonicalGateCounterA], by simp [canonicalGateCounterEnds],
      by simp [canonicalGateCounterEnds], by decide⟩
  exact (h12.tail h25).tail h53



theorem middleSwap_rowsDisconnect_implication_false :
    RowsDisconnect canonicalGateCounterEnds canonicalGateCounterSupport
        canonicalGateCounterColoring 1 3 ∧
      ¬ RowsDisconnect canonicalGateCounterEnds canonicalGateCounterSupport
        (middleSwap canonicalGateCounterSupport canonicalGateCounterColoring) 1 3 := by
  constructor
  · rw [RowsDisconnect, canonicalGateCounterColoring_rows.1,
      canonicalGateCounterColoring_rows.2]
    simpa [CanonicalGateCounterGated,
      canonicalGateCounter_rows_partition.1] using
        canonicalGateCounter_KL_gated
  · intro h
    rw [RowsDisconnect,
      canonicalGateCounterColoring_middleSwap_rows.1,
      canonicalGateCounterColoring_middleSwap_rows.2] at h
    exact h.1 canonicalGateCounterA_conn



theorem sourceMaskFiber_gate_implication_false :
    ∃ c : leftSourceMaskFiber canonicalGateCounterEnds
        canonicalGateCounterSupport 0 1 2 3 canonicalGateCounterMaskProfile,
      RowsDisconnect canonicalGateCounterEnds canonicalGateCounterSupport
          c.1 1 3 ∧
        ¬ RowsDisconnect canonicalGateCounterEnds canonicalGateCounterSupport
          (middleSwap canonicalGateCounterSupport c.1) 1 3 :=
  ⟨canonicalGateCounterSourcePoint,
    middleSwap_rowsDisconnect_implication_false⟩

end StatMech.GrahamGHS.FourColor
