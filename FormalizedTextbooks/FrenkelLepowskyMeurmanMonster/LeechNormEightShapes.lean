/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Absolute-coordinate shapes of norm-eight vectors in the integral Leech model.
The coordinate square sum is 64 because the physical embedding divides by√8. -/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fin.VecNotation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Multiplicities of absolute coordinate values 0, ..., 8 for the eight possible shapes. -/
def leechNormEightShapeCounts : Fin 8 → Fin 9 → ℕ :=
  ![![23, 0, 0, 0, 0, 0, 0, 0, 1],
    ![16, 0, 7, 0, 0, 0, 1, 0, 0],
    ![20, 0, 0, 0, 4, 0, 0, 0, 0],
    ![14, 0, 8, 0, 2, 0, 0, 0, 0],
    ![11, 0, 12, 0, 1, 0, 0, 0, 0],
    ![8, 0, 16, 0, 0, 0, 0, 0, 0],
    ![0, 21, 0, 2, 0, 1, 0, 0, 0],
    ![0, 19, 0, 5, 0, 0, 0, 0, 0]]

set_option maxHeartbeats 1000000 in
-- Six scalar arithmetic branches reconstruct their nine coordinate counts.
private theorem nat_normEight_even (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℕ)
    (htotal : a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 = 24)
    (hsquare : a1 + 4 * a2 + 9 * a3 + 16 * a4 + 25 * a5 + 36 * a6 + 49 * a7 + 64 * a8 = 64)
    (he : a1 = 0 ∧ a3 = 0 ∧ a5 = 0 ∧ a7 = 0)
    (hcode : a2 + a6 = 0 ∨ a2 + a6 = 8 ∨ a2 + a6 = 12 ∨ a2 + a6 = 16 ∨ a2 + a6 = 24) :
    ∃ s : Fin 8, ![a0, a1, a2, a3, a4, a5, a6, a7, a8] = leechNormEightShapeCounts s := by
  obtain ⟨h1, h3, h5, h7⟩ := he
  have h8bound : a8 ≤ 1 := by omega
  by_cases h8 : a8 = 1
  · clear hcode
    have ha0 : a0 = 23 := by omega
    have ha1 : a1 = 0 := by omega
    have ha2 : a2 = 0 := by omega
    have ha3 : a3 = 0 := by omega
    have ha4 : a4 = 0 := by omega
    have ha5 : a5 = 0 := by omega
    have ha6 : a6 = 0 := by omega
    have ha7 : a7 = 0 := by omega
    have ha8 : a8 = 1 := by omega
    refine ⟨0, ?_⟩
    simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
    rfl
  · have h8zero : a8 = 0 := by omega
    have h6bound : a6 ≤ 1 := by omega
    by_cases h6 : a6 = 1
    · have h4zero : a4 = 0 := by
        rcases hcode with hc | hc | hc | hc | hc <;> omega
      clear hcode
      have ha0 : a0 = 16 := by omega
      have ha1 : a1 = 0 := by omega
      have ha2 : a2 = 7 := by omega
      have ha3 : a3 = 0 := by omega
      have ha4 : a4 = 0 := by omega
      have ha5 : a5 = 0 := by omega
      have ha6 : a6 = 1 := by omega
      have ha7 : a7 = 0 := by omega
      have ha8 : a8 = 0 := by omega
      refine ⟨1, ?_⟩
      simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
      rfl
    · have h6zero : a6 = 0 := by omega
      have h4cases : a4 = 0 ∨ a4 = 1 ∨ a4 = 2 ∨ a4 = 3 ∨ a4 = 4 := by omega
      rcases h4cases with h4 | h4 | h4 | h4 | h4
      · clear hcode
        have ha0 : a0 = 8 := by omega
        have ha1 : a1 = 0 := by omega
        have ha2 : a2 = 16 := by omega
        have ha3 : a3 = 0 := by omega
        have ha4 : a4 = 0 := by omega
        have ha5 : a5 = 0 := by omega
        have ha6 : a6 = 0 := by omega
        have ha7 : a7 = 0 := by omega
        have ha8 : a8 = 0 := by omega
        refine ⟨5, ?_⟩
        simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
        rfl
      · clear hcode
        have ha0 : a0 = 11 := by omega
        have ha1 : a1 = 0 := by omega
        have ha2 : a2 = 12 := by omega
        have ha3 : a3 = 0 := by omega
        have ha4 : a4 = 1 := by omega
        have ha5 : a5 = 0 := by omega
        have ha6 : a6 = 0 := by omega
        have ha7 : a7 = 0 := by omega
        have ha8 : a8 = 0 := by omega
        refine ⟨4, ?_⟩
        simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
        rfl
      · clear hcode
        have ha0 : a0 = 14 := by omega
        have ha1 : a1 = 0 := by omega
        have ha2 : a2 = 8 := by omega
        have ha3 : a3 = 0 := by omega
        have ha4 : a4 = 2 := by omega
        have ha5 : a5 = 0 := by omega
        have ha6 : a6 = 0 := by omega
        have ha7 : a7 = 0 := by omega
        have ha8 : a8 = 0 := by omega
        refine ⟨3, ?_⟩
        simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
        rfl
      · exfalso
        rcases hcode with hc | hc | hc | hc | hc <;> omega
      · clear hcode
        have ha0 : a0 = 20 := by omega
        have ha1 : a1 = 0 := by omega
        have ha2 : a2 = 0 := by omega
        have ha3 : a3 = 0 := by omega
        have ha4 : a4 = 4 := by omega
        have ha5 : a5 = 0 := by omega
        have ha6 : a6 = 0 := by omega
        have ha7 : a7 = 0 := by omega
        have ha8 : a8 = 0 := by omega
        refine ⟨2, ?_⟩
        simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
        rfl

private theorem nat_normEight_odd (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℕ)
    (htotal : a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 = 24)
    (hsquare : a1 + 4 * a2 + 9 * a3 + 16 * a4 + 25 * a5 + 36 * a6 + 49 * a7 + 64 * a8 = 64)
    (ho : a0 = 0 ∧ a2 = 0 ∧ a4 = 0 ∧ a6 = 0 ∧ a8 = 0) :
    ∃ s : Fin 8, ![a0, a1, a2, a3, a4, a5, a6, a7, a8] = leechNormEightShapeCounts s := by
  obtain ⟨h0, h2, h4, h6, h8⟩ := ho
  have hbalance : 8 * a3 + 24 * a5 + 48 * a7 = 40 := by omega
  clear hsquare
  have h7zero : a7 = 0 := by omega
  have h5bound : a5 ≤ 1 := by omega
  by_cases h5 : a5 = 1
  · have ha0 : a0 = 0 := by omega
    have ha1 : a1 = 21 := by omega
    have ha2 : a2 = 0 := by omega
    have ha3 : a3 = 2 := by omega
    have ha4 : a4 = 0 := by omega
    have ha5 : a5 = 1 := by omega
    have ha6 : a6 = 0 := by omega
    have ha7 : a7 = 0 := by omega
    have ha8 : a8 = 0 := by omega
    refine ⟨6, ?_⟩
    simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
    rfl
  · have h5zero : a5 = 0 := by omega
    have ha0 : a0 = 0 := by omega
    have ha1 : a1 = 19 := by omega
    have ha2 : a2 = 0 := by omega
    have ha3 : a3 = 5 := by omega
    have ha4 : a4 = 0 := by omega
    have ha5 : a5 = 0 := by omega
    have ha6 : a6 = 0 := by omega
    have ha7 : a7 = 0 := by omega
    have ha8 : a8 = 0 := by omega
    refine ⟨7, ?_⟩
    simp only [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
    rfl


private theorem nat_normEight_shapes (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℕ)
    (htotal : a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 = 24)
    (hsquare : a1 + 4 * a2 + 9 * a3 + 16 * a4 + 25 * a5 + 36 * a6 + 49 * a7 + 64 * a8 = 64)
    (hparity : (a1 = 0 ∧ a3 = 0 ∧ a5 = 0 ∧ a7 = 0) ∨
      (a0 = 0 ∧ a2 = 0 ∧ a4 = 0 ∧ a6 = 0 ∧ a8 = 0))
    (hcode : a2 + a6 = 0 ∨ a2 + a6 = 8 ∨ a2 + a6 = 12 ∨ a2 + a6 = 16 ∨ a2 + a6 = 24) :
    ∃ s : Fin 8, ![a0, a1, a2, a3, a4, a5, a6, a7, a8] = leechNormEightShapeCounts s := by
  rcases hparity with he | ho
  · exact nat_normEight_even _ _ _ _ _ _ _ _ _ htotal hsquare he hcode
  · exact nat_normEight_odd _ _ _ _ _ _ _ _ _ htotal hsquare ho

/-- Elementary arithmetic classification after parity and Golay weights have
been established. It excludes the two spurious even shapes of code weight 4. -/
theorem leechNormEight_shape_of_multiplicities (n : Fin 9 → ℕ)
    (htotal : ∑ k, n k = 24)
    (hsquare : ∑ k : Fin 9, k.val ^ 2 * n k = 64)
    (hparity : (n 1 = 0 ∧ n 3 = 0 ∧ n 5 = 0 ∧ n 7 = 0) ∨
      (n 0 = 0 ∧ n 2 = 0 ∧ n 4 = 0 ∧ n 6 = 0 ∧ n 8 = 0))
    (hcode : n 2 + n 6 = 0 ∨ n 2 + n 6 = 8 ∨ n 2 + n 6 = 12 ∨
      n 2 + n 6 = 16 ∨ n 2 + n 6 = 24) :
    ∃ s : Fin 8, n = leechNormEightShapeCounts s := by
  have ht : n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 + n 8 = 24 := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using htotal
  have hs : n 1 + 4 * n 2 + 9 * n 3 + 16 * n 4 + 25 * n 5 + 36 * n 6 +
      49 * n 7 + 64 * n 8 = 64 := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsquare
  obtain ⟨s, he⟩ := nat_normEight_shapes (n 0) (n 1) (n 2) (n 3) (n 4)
    (n 5) (n 6) (n 7) (n 8) ht hs hparity hcode
  refine ⟨s, ?_⟩
  have hn : n = ![n 0, n 1, n 2, n 3, n 4, n 5, n 6, n 7, n 8] := by
    funext k
    fin_cases k <;> rfl
  exact hn.trans he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
