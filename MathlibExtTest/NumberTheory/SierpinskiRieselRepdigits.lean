/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SierpinskiRieselRepdigits

namespace MetaMathlibExt

-- The one-digit and three-digit binary repunits both fall under the obstruction.
example (S : Finset (ℕ × ℕ × ℕ)) : ¬ IsSierpinskiCoveringData 1 S :=
  not_isSierpinskiCoveringData_two_pow_sub_one (t := 1) (by decide) S

example (S : Finset (ℕ × ℕ × ℕ)) : ¬ IsSierpinskiCoveringData (repstring 2 1 0 3) S := by
  rw [repstring_two_one_zero_three]
  exact not_isSierpinskiCoveringData_two_pow_sub_one (t := 3) (by decide) S

-- Two copies of the two-digit block 12 with one zero between them.
example : repstring 10 12 1 2 = 12012 := by
  norm_num [repstring]

-- A genuine covering for 78557, with 2 representing the zero class modulo 2.
private def covering78557 : Finset (ℕ × ℕ × ℕ) :=
  {(2, 2, 3), (1, 4, 5), (1, 3, 7), (11, 12, 13), (15, 18, 19), (27, 36, 37), (3, 9, 73)}

private theorem covering78557_valid : IsSierpinskiCoveringData 78557 covering78557 := by
  refine ⟨?_, Finset.injOn_of_card_image_eq (by decide), by decide⟩
  intro z
  -- It suffices to check one period of 36 consecutive residues.
  have hcover : ∀ i : Fin 36, ∃ s ∈ covering78557,
      (s.2.1 : ℤ) ∣ 36 ∧ (i : ℤ) ≡ s.1 [ZMOD s.2.1] := by decide
  let i : Fin 36 := ⟨(z % 36).toNat, by omega⟩
  obtain ⟨s, hs, hm, hi⟩ := hcover i
  refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
  have hrep : (i : ℤ) = z % 36 := Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))
  rw [hrep] at hi
  exact ((Int.mod_modEq z 36).symm.of_dvd hm).trans hi

-- At k = 0, truncated subtraction makes the Riesel divisibility condition automatic.
example : IsRieselCoveringData 0 covering78557 := by
  obtain ⟨hcover, hinj, hdata⟩ := covering78557_valid
  refine ⟨hcover, hinj, fun s hs => ?_⟩
  obtain ⟨hm, hp, hperiod, _⟩ := hdata s hs
  exact ⟨hm, hp, hperiod, by simp⟩

end MetaMathlibExt
