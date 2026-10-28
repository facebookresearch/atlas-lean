/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCoordinates

/-! The four possible absolute-coordinate shapes at physical Leech norm six. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Multiplicities of absolute values 0 through 8 for the two even and two odd shapes. -/
def leechNormSixShapeCounts : Fin 4 → Fin 9 → ℕ :=
  ![![12, 0, 12, 0, 0, 0, 0, 0, 0],
    ![15, 0, 8, 0, 1, 0, 0, 0, 0],
    ![0, 23, 0, 0, 0, 1, 0, 0, 0],
    ![0, 21, 0, 3, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 1000000 in
-- The finite arithmetic branches determine every absolute-coordinate multiplicity.
private theorem nat_normSix_shapes (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℕ)
    (ht : a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 = 24)
    (hs : a1 + 4 * a2 + 9 * a3 + 16 * a4 + 25 * a5 + 36 * a6 + 49 * a7 + 64 * a8 = 48)
    (hparity : (a1 = 0 ∧ a3 = 0 ∧ a5 = 0 ∧ a7 = 0) ∨
      (a0 = 0 ∧ a2 = 0 ∧ a4 = 0 ∧ a6 = 0 ∧ a8 = 0))
    (hcode : a2 + a6 = 0 ∨ a2 + a6 = 8 ∨ a2 + a6 = 12 ∨
      a2 + a6 = 16 ∨ a2 + a6 = 24)
    (hheight : ¬ (a2 = 0 ∧ a4 = 3)) :
    ∃ s : Fin 4, ![a0, a1, a2, a3, a4, a5, a6, a7, a8] = leechNormSixShapeCounts s := by
  rcases hparity with ⟨h1, h3, h5, h7⟩ | ⟨h0, h2, h4, h6, h8⟩
  · have h8 : a8 = 0 := by omega
    have h6 : a6 = 0 := by
      rcases hcode with h | h | h | h | h <;> omega
    have h4cases : a4 = 0 ∨ a4 = 1 ∨ a4 = 3 := by
      rcases hcode with h | h | h | h | h <;> omega
    rcases h4cases with h4 | h4 | h4
    · refine ⟨0, ?_⟩
      have h0 : a0 = 12 := by omega
      have h2 : a2 = 12 := by omega
      simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
      rfl
    · refine ⟨1, ?_⟩
      have h0 : a0 = 15 := by omega
      have h2 : a2 = 8 := by omega
      simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
      rfl
    · exact False.elim (hheight ⟨by omega, h4⟩)
  · clear hcode hheight
    have hbalance : 8 * a3 + 24 * a5 + 48 * a7 = 24 := by omega
    clear hs
    have h7 : a7 = 0 := by omega
    have h5cases : a5 = 0 ∨ a5 = 1 := by omega
    rcases h5cases with h5 | h5
    · refine ⟨3, ?_⟩
      have h1 : a1 = 21 := by omega
      have h3 : a3 = 3 := by omega
      simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
      rfl
    · refine ⟨2, ?_⟩
      have h1 : a1 = 23 := by omega
      have h3 : a3 = 0 := by omega
      simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
      rfl

/-- Source parity, Golay weights, and the height congruence determine all four shapes. -/
theorem leechNormSix_shape_of_multiplicities (n : Fin 9 → ℕ)
    (htotal : ∑ k, n k = 24) (hsquare : ∑ k, k.val ^ 2 * n k = 48)
    (hparity : (n 1 = 0 ∧ n 3 = 0 ∧ n 5 = 0 ∧ n 7 = 0) ∨
      (n 0 = 0 ∧ n 2 = 0 ∧ n 4 = 0 ∧ n 6 = 0 ∧ n 8 = 0))
    (hcode : n 2 + n 6 = 0 ∨ n 2 + n 6 = 8 ∨ n 2 + n 6 = 12 ∨
      n 2 + n 6 = 16 ∨ n 2 + n 6 = 24)
    (hheight : ¬ (n 2 = 0 ∧ n 4 = 3)) :
    ∃ s : Fin 4, n = leechNormSixShapeCounts s := by
  have ht : n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 + n 8 = 24 := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using htotal
  have hs : n 1 + 4 * n 2 + 9 * n 3 + 16 * n 4 + 25 * n 5 + 36 * n 6 +
      49 * n 7 + 64 * n 8 = 48 := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsquare
  obtain ⟨s, he⟩ := nat_normSix_shapes (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6)
    (n 7) (n 8) ht hs hparity hcode hheight
  refine ⟨s, ?_⟩
  have hv : n = ![n 0, n 1, n 2, n 3, n 4, n 5, n 6, n 7, n 8] := by
    funext k
    fin_cases k <;> rfl
  exact hv.trans he

set_option maxHeartbeats 2000000 in
-- Transport the complete finite coordinate square sum through the integer cast.
/-- Physical norm six has original integer square sum 48. -/
theorem leechNormSix_natSquareSum (u : Fin 24 → ℤ) (h : leechSquareSum u = 48) :
    ∑ i, (u i).natAbs ^ 2 = 48 := by
  have hc : ((∑ i, (u i).natAbs ^ 2 : ℕ) : ℤ) = leechSquareSum u := by
    simp only [Nat.cast_sum, Nat.cast_pow, Int.natCast_natAbs, leechSquareSum, sq_abs]
  exact_mod_cast hc.trans h

/-- Every actual norm-six coordinate has absolute value at most six. -/
theorem leechNormSix_natAbs_le (u : Fin 24 → ℤ) (h : leechSquareSum u = 48)
    (i : Fin 24) : (u i).natAbs ≤ 6 := by
  have hi : (u i).natAbs ^ 2 ≤ ∑ j, (u j).natAbs ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 24 => (u j).natAbs ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [leechNormSix_natSquareSum u h] at hi
  nlinarith

/-- The existing absolute-value multiplicities recover every original norm-six coordinate. -/
theorem leechNormSixMultiplicity_square (u : Fin 24 → ℤ)
    (hb : ∀ i, (u i).natAbs ≤ 8) (hs : leechSquareSum u = 48) :
    ∑ k : Fin 9, k.val ^ 2 * leechNormEightMultiplicity u k = 48 := by
  let f : Fin 24 → Fin 9 := fun i => ⟨(u i).natAbs, Nat.lt_succ_of_le (hb i)⟩
  have h := Finset.sum_fiberwise' (Finset.univ : Finset (Fin 24)) f
    (fun k : Fin 9 => k.val ^ 2)
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  have h' : (∑ k : Fin 9, k.val ^ 2 * leechNormEightMultiplicity u k) =
      ∑ i, (u i).natAbs ^ 2 := by
    simpa [leechNormEightMultiplicity, f, Fin.ext_iff, mul_comm] using h
  exact h'.trans (leechNormSix_natSquareSum u hs)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
