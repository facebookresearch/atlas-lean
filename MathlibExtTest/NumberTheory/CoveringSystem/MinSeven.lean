/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CoveringSystem.MinSeven

/-! # Tests for the covering system with minimum modulus seven -/

namespace MathlibExtTest.CoveringSystem.MinSeven

-- The minimum is attained by exactly one class.
example : ∃ C : Finset (ℤ × ℕ), Int.IsCoveringSystem C ∧ ∃! c, c ∈ C ∧ c.2 = 7 := by
  obtain ⟨C, hcov, hinj, _, ⟨c, hc, hseven⟩, _⟩ :=
    MetaMathlibExt.exists_distinct_covering_min_seven_lcm_15120
  exact ⟨C, hcov, c, ⟨hc, hseven⟩, fun d hd => hinj hd.1 hc (hd.2.trans hseven.symm)⟩

-- A single class covers both the last residue of the period and its negative representative.
example : ∃ C : Finset (ℤ × ℕ), Int.IsCoveringSystem C ∧ ∃ c ∈ C,
    7 ≤ c.2 ∧ (-1 : ℤ) ≡ c.1 [ZMOD c.2] ∧ (15119 : ℤ) ≡ c.1 [ZMOD c.2] := by
  obtain ⟨C, hcov, _, hmin, _, hlcm⟩ :=
    MetaMathlibExt.exists_distinct_covering_min_seven_lcm_15120
  obtain ⟨c, hc, hneg⟩ := hcov (-1)
  have hdvd : c.2 ∣ 15120 := hlcm ▸ Finset.dvd_lcm (f := Prod.snd) hc
  have hperiod : (15119 : ℤ) ≡ -1 [ZMOD 15120] := by decide
  exact ⟨C, hcov, c, hc, hmin c hc, hneg,
    ((hperiod.of_dvd (Int.natCast_dvd_natCast.mpr hdvd)).trans hneg)⟩

end MathlibExtTest.CoveringSystem.MinSeven
