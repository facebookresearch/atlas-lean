/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Chemistry.Separations.BatchLangmuirBalance
import Mathlib.Tactic.NormNum

/-!
# Tests for the batch Langmuir balance
-/

open Chemistry.Separations

-- With positive parameters the unique root is interior, with occupancy 2/3.
example :
    let q : ℝ → ℝ := fun c => 4 * (2 * c / (1 + 2 * c))
    (∀ c ∈ Set.Icc 0 5, 2 * (5 - c) = 3 * q c ↔ c = 1) ∧
      q 1 / 4 = 2 / 3 ∧ q 1 / 4 ∈ Set.Ico 0 1 := by
  intro q
  obtain ⟨c, _, _, huniq, hocc, _⟩ :=
    batchLangmuirBalance (V := 2) (c₀ := 5) (m := 3) (qMax := 4) (K := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hroot : 2 * ((5 : ℝ) - 1) = 3 * q 1 := by norm_num [q]
  have hc : (1 : ℝ) = c := huniq 1 (by norm_num [Set.mem_Icc]) hroot
  subst c
  refine ⟨?_, by norm_num [q], hocc⟩
  intro d hd
  refine ⟨huniq d hd, ?_⟩
  rintro rfl
  exact hroot

-- Zero adsorbent mass gives zero total, although the per-unit loading formula is positive.
example :
    let q : ℝ → ℝ := fun c => 4 * (2 * c / (1 + 2 * c))
    ∃ c, c = 5 ∧ 0 * q c = 0 ∧ 0 < q c := by
  intro q
  obtain ⟨c, _, _, _, _, hzero⟩ :=
    batchLangmuirBalance (V := 2) (c₀ := 5) (m := 0) (qMax := 4) (K := 2)
      (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
  obtain ⟨hc, htotal⟩ := hzero (Or.inr rfl)
  exact ⟨c, hc, htotal, by norm_num [q, hc]⟩

-- Zero affinity gives zero total with positive adsorbent mass.
example :
    let q : ℝ → ℝ := fun c => 4 * (0 * c / (1 + 0 * c))
    ∃ c, c = 5 ∧ 3 * q c = 0 ∧ q c / 4 = 0 := by
  intro q
  obtain ⟨c, _, _, _, _, hzero⟩ :=
    batchLangmuirBalance (V := 2) (c₀ := 5) (m := 3) (qMax := 4) (K := 0)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl
  obtain ⟨hc, htotal⟩ := hzero (Or.inl rfl)
  exact ⟨c, hc, htotal, by simp [q]⟩

#print axioms Chemistry.Separations.batchLangmuirBalance
