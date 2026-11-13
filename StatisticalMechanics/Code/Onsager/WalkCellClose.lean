/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Onsager.CellEulerFaithful
import Code.Onsager.CellGaussBonnetGlobal









namespace StatMech.Onsager.WalkCellClose

open Finset
open StatMech.Onsager.BaseCase StatMech.Onsager.CellEuler
  StatMech.Onsager.CellGaussBonnetGlobal StatMech.Onsager.CellPinch
  StatMech.Onsager.WalkCellRegion StatMech.Onsager.WalkCellLocal
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.CellEulerFaithful


theorem base_cc_eq_four {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d = 4 := by
  let S := interiorCells d hclosed hsimple hreflexfree
  have hgb := cornerDiff_eq S
  have hcorners := cornerDiff_interiorCells_eq_cc d hclosed hsimple hreflexfree
  have hpinch := pinchCount_interiorCells_eq_zero d hclosed hsimple hreflexfree
  have heuler := eulerChar_interiorCells_le_one d hclosed hsimple hreflexfree
  have hlower := four_le_cc d hclosed hreflexfree
  change cornerDiff S = (cc d : ℤ) at hcorners
  change pinchCount S = 0 at hpinch
  change eulerChar S ≤ 1 at heuler
  rw [hcorners, hpinch] at hgb
  norm_num at hgb
  have hlowerZ : (4 : ℤ) ≤ cc d := by exact_mod_cast hlower
  omega


theorem cc_lt_eight {m : ℕ} (d : Fin (m + 3) → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d < 8 := by
  rw [base_cc_eq_four d hclosed hsimple hreflexfree]
  decide


theorem base_cc_eq_four' {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d = 4 := by
  have hlower : 4 ≤ cc d := four_le_cc d hclosed hreflexfree
  have hcard : cc d ≤ n := by
    unfold cc
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun i : Fin n => d (i + 1) - d i = 1)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := by
    use n - 3
    omega
  exact base_cc_eq_four d hclosed hsimple hreflexfree


theorem cc_lt_eight' {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hclosed : ∑ i, stepOf (d i) = 0) (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    cc d < 8 := by
  rw [base_cc_eq_four' d hclosed hsimple hreflexfree]
  decide

end StatMech.Onsager.WalkCellClose
