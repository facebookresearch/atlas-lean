/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CoveringSystem.MirskyNewman
import Mathlib.Tactic.NormNum

namespace MirskyNewmanTest

private def classes : Finset (ℤ × ℕ) := {(0, 2), (0, 3), (1, 4), (-1, 6), (-5, 12)}

-- The cover has period twelve and includes negative representatives.
example : (1 : ℚ) < ∑ c ∈ classes, (1 : ℚ) / c.2 := by
  apply MetaMathlibExt.one_lt_sum_inv_moduli_of_distinct_covering
  · intro z
    have hperiod : ∀ n : Fin 12, ∃ c ∈ classes, (n : ℤ) ≡ c.1 [ZMOD c.2] := by decide
    obtain ⟨c, hc, hz⟩ := hperiod ⟨(z % 12).toNat, by omega⟩
    have hd : ∀ c ∈ classes, (c.2 : ℤ) ∣ 12 := by decide
    refine ⟨c, hc, ((Int.mod_modEq z 12).symm.of_dvd (hd c hc)).trans ?_⟩
    simpa [Int.toNat_of_nonneg (Int.emod_nonneg z (by decide : (12 : ℤ) ≠ 0))] using hz
  · intro c hc d hd heq
    exact (show ∀ c ∈ classes, ∀ d ∈ classes, c.2 = d.2 → c = d by decide) c hc d hd heq
  · decide

-- The two classes modulo two cover exactly once and attain equality.
example : Int.IsCoveringSystem {(0, 2), (1, 2)} ∧
    (∑ c ∈ ({(0, 2), (1, 2)} : Finset (ℤ × ℕ)), (1 : ℚ) / c.2) = 1 := by
  constructor
  · intro z
    by_cases hz : z % 2 = 0
    · exact ⟨(0, 2), by simp, hz⟩
    · exact ⟨(1, 2), by simp, by change z % 2 = 1; omega⟩
  · norm_num [Finset.sum_insert]

end MirskyNewmanTest
