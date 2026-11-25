/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CoveringSystem.DiscardPrimePower

/-! # Tests for discarding prime-power multiples in a distinct covering system -/

namespace MetaMathlibExt.isCoveringSystem_filter_not_dvd_of_lt

private def cover : Finset (ℤ × ℕ) := {(0, 2), (0, 3), (1, 4), (1, 6), (11, 12)}

private theorem cover_isCoveringSystem : Int.IsCoveringSystem cover := by
  have hres : ∀ r : Fin 12, ∃ c ∈ cover, (r : ℤ) ≡ c.1 [ZMOD c.2] := by decide
  have hdvd : ∀ c ∈ cover, (c.2 : ℤ) ∣ 12 := by decide
  intro z
  let r : Fin 12 := ⟨(z % 12).toNat, by omega⟩
  obtain ⟨c, hc, hrc⟩ := hres r
  have hr : (r : ℤ) = z % 12 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  rw [hr] at hrc
  exact ⟨c, hc, ((Int.mod_modEq z 12).symm.of_dvd (hdvd c hc)).trans hrc⟩

-- Discard the singleton of modulus zero and all three possible positive multiples of 9.
-- The moduli 3, 6 and 12 survive even though they share the prime factor 3.
example : Int.IsCoveringSystem cover := by
  let C : Finset (ℤ × ℕ) := {(11, 0), (2, 9), (3, 18), (4, 27)} ∪ cover
  have hcov : Int.IsCoveringSystem C := by
    intro z
    obtain ⟨c, hc, hz⟩ := cover_isCoveringSystem z
    exact ⟨c, Finset.mem_union_right _ hc, hz⟩
  have h := isCoveringSystem_filter_not_dvd_of_lt C hcov (by decide) 27 (by decide)
    (p := 3) (a := 2) (by decide) (by decide) (by decide)
  exact (show C.filter (fun c => ¬ 3 ^ 2 ∣ c.2) = cover by decide) ▸ h

-- At equality, 12 = 2 ^ 2 * (2 + 1), removing the multiples of 4 leaves -1 uncovered.
example : ¬ Int.IsCoveringSystem (cover.filter fun c => ¬ 2 ^ 2 ∣ c.2) := by
  intro h
  have := h (-1)
  revert this
  decide

end MetaMathlibExt.isCoveringSystem_filter_not_dvd_of_lt
