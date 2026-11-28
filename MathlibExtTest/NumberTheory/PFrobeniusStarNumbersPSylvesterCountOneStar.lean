/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PFrobeniusStarNumbersPSylvesterCountOneStar

/-!
# Tests for the Frobenius numbers and one-Sylvester counts of consecutive star numbers

Concrete instances of the one-Sylvester formula and independent count checks at starting index ten
for `p = 0, 1, 2`.
-/

namespace MathlibExtTest.NumberTheory.PFrobeniusStarNumbersPSylvesterCountOneStar

open MathlibExt.NumberTheory.PFrobeniusStarNumbersWanted

example : pSylvesterStarCount 1 6 = 6313 := by
  simpa using pSylvesterCount_one_star 6 (by decide)

example : pSylvesterStarCount 1 10 = 27441 := by
  simpa using pSylvesterCount_one_star 10 (by decide)

-- Check the count at `g` and above it in every residue modulo 541. Adding further
-- copies of 541 preserves those representations, so the check covers every `N > g`.
private theorem checkedFrobeniusAtTen (p g : ℕ) (hbound : g + 541 < 541 * 661)
    (hcount : starRepCountCandidates 10 g = p)
    (hwindow : (List.range 541).all
      (fun i => decide (p < starRepCountCandidates 10 (g + i + 1))) = true) :
    IsPFrobeniusStarNumber p 10 g := by
  apply isPFrobeniusStarNumber_iff.mpr
  refine ⟨?_, ?_⟩
  · have hg : g < 541 * 661 := by omega
    rw [starRepCount_eq_starRepCountCandidates 10 g hg, hcount]
  intro N hN
  let i := (N - (g + 1)) % 541
  let k := (N - (g + 1)) / 541
  have hi : i < 541 := Nat.mod_lt _ (by decide)
  have hle : g + i + 1 < 541 * 661 := by omega
  have hsplit : g + i + 1 + k * 541 = N := by
    have h := Nat.mod_add_div (N - (g + 1)) 541
    rw [Nat.mul_comm 541] at h
    dsimp [i, k]
    omega
  have hhere := of_decide_eq_true (List.all_eq_true.mp hwindow i (List.mem_range.mpr hi))
  rw [← starRepCount_eq_starRepCountCandidates 10 _ hle] at hhere
  exact hhere.trans_le (hsplit ▸ starRepCount_le_add_mul 10 (g + i + 1) k)

-- The formula and both count conditions are checked without the general theorem.
private def tenCase (p g : ℕ) : Prop :=
  (g : ℤ) = ((2 : ℤ) * 10 - 11) * (star 11 : ℤ) +
    ((p : ℤ) + 3) * 10 * (star 12 : ℤ) - (star 10 : ℤ) ∧
    IsPFrobeniusStarNumber p 10 g

example : tenCase 0 29198 :=
  ⟨by decide +kernel, checkedFrobeniusAtTen 0 29198 (by decide) (by decide +kernel)
    (by decide +kernel)⟩

example : tenCase 1 37128 :=
  ⟨by decide +kernel, checkedFrobeniusAtTen 1 37128 (by decide) (by decide +kernel)
    (by decide +kernel)⟩

example : tenCase 2 45058 :=
  ⟨by decide +kernel, checkedFrobeniusAtTen 2 45058 (by decide) (by decide +kernel)
    (by decide +kernel)⟩

-- A client of the general theorem recovers the last numerical value above.
example : IsPFrobeniusStarNumber 2 10 45058 := by
  obtain ⟨g, hg, hformula⟩ := exists_isPFrobeniusNumber_star_of_ten_le 10 2
    (by decide) (Or.inr (Or.inr rfl))
  have hvalue : (g : ℤ) = 45058 := hformula
  have heq : g = 45058 := by omega
  simpa only [heq] using hg

end MathlibExtTest.NumberTheory.PFrobeniusStarNumbersPSylvesterCountOneStar
