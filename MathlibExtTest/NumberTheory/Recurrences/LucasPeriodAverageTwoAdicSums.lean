/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.LucasPeriodAverageTwoAdicSums

/-! # Regression tests for nondivisibility of Lucas sums -/

namespace MetaMathlibExt

private def pZero : LucasSequenceParams := ⟨4, -1, by decide⟩
private def pTwo : LucasSequenceParams := ⟨6, 1, by decide⟩

-- The length-two block must already give a nonzero residue.
example (hnd : IsNondegenerateLucasPair pZero.p pZero.q) :
    ¬ (2 : ℤ) ∣ ∑ i ∈ Finset.Icc 1 2, lucasU pZero i :=
  (lucasU_sum_not_dvd_of_p_zero_mod_four pZero hnd (by decide) (by decide)).1
    2 1 (by decide) (by decide) (by decide)

-- Three blocks of length four must retain the nonzero residue modulo four.
example (hnd : IsNondegenerateLucasPair pTwo.p pTwo.q) :
    ¬ (4 : ℤ) ∣ ∑ i ∈ Finset.Icc 1 12, lucasU pTwo i :=
  (lucasU_sum_not_dvd_of_p_two_mod_four pTwo hnd (by decide) (by decide)).1
    12 2 (by decide) (by decide) (by decide)

example (hnd : IsNondegenerateLucasPair pZero.p pZero.q) :
    ¬ ∃ x : ℕ, 6 ∣ x ∧ x ∈ lucasAverageSet pZero :=
  (lucasU_sum_not_dvd_of_p_zero_mod_four pZero hnd (by decide) (by decide)).2.1
    6 (by decide) ⟨3, rfl⟩

example (hnd : IsNondegenerateLucasPair pTwo.p pTwo.q)
    (hd : (8 : ℤ) ∣ ∑ i ∈ Finset.Icc 1 8, lucasU pTwo i) : False := by
  have h := (lucasU_sum_not_dvd_of_p_two_mod_four pTwo hnd (by decide) (by decide)).2.2
    8 (by decide) hd
  exact (by decide : ¬ 8 % 2 = 1) (Nat.odd_iff.mp h)

end MetaMathlibExt
