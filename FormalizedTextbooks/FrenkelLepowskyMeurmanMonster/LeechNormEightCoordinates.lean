/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Coordinate multiplicities and residues for the norm-eight classification. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Count coordinates having a given absolute integer value. -/
def leechNormEightMultiplicity (u : Fin 24 → ℤ) (k : Fin 9) : ℕ :=
  (Finset.univ.filter fun i => (u i).natAbs = k.val).card

/-- The physical norm-eight condition has integer coordinate square sum 64. -/
theorem leechNormEight_natSquareSum (u : Fin 24 → ℤ) (h : leechSquareSum u = 64) :
    ∑ i, (u i).natAbs ^ 2 = 64 := by
  have hc : ((∑ i, (u i).natAbs ^ 2 : ℕ) : ℤ) = leechSquareSum u := by
    simp only [Nat.cast_sum, Nat.cast_pow, Int.natCast_natAbs, leechSquareSum, sq_abs]
  exact_mod_cast hc.trans h

private theorem nat_coordinate_square_bound (w : Fin 24 → ℕ)
    (h : ∑ i, w i ^ 2 = 64) (i : Fin 24) : w i ≤ 8 := by
  have hi : w i ^ 2 ≤ ∑ j, w j ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 24 => w j ^ 2)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [h] at hi
  nlinarith

/-- Every coordinate has absolute value at most 8. -/
theorem leechNormEight_natAbs_le (u : Fin 24 → ℤ) (h : leechSquareSum u = 64)
    (i : Fin 24) : (u i).natAbs ≤ 8 :=
  nat_coordinate_square_bound (fun j => (u j).natAbs) (leechNormEight_natSquareSum u h) i

/-- The nine absolute-value multiplicities cover all 24 coordinates. -/
theorem leechNormEightMultiplicity_total (u : Fin 24 → ℤ)
    (hb : ∀ i, (u i).natAbs ≤ 8) : ∑ k, leechNormEightMultiplicity u k = 24 := by
  let f : Fin 24 → Fin 9 := fun i => ⟨(u i).natAbs, Nat.lt_succ_of_le (hb i)⟩
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin 24)) (Finset.univ : Finset (Fin 9)) f
  simpa [leechNormEightMultiplicity, f, Fin.ext_iff] using h

/-- The weighted multiplicities recover the integer coordinate norm. -/
theorem leechNormEightMultiplicity_square (u : Fin 24 → ℤ)
    (hb : ∀ i, (u i).natAbs ≤ 8) (hs : leechSquareSum u = 64) :
    ∑ k : Fin 9, k.val ^ 2 * leechNormEightMultiplicity u k = 64 := by
  let f : Fin 24 → Fin 9 := fun i => ⟨(u i).natAbs, Nat.lt_succ_of_le (hb i)⟩
  have h := Finset.sum_fiberwise' (Finset.univ : Finset (Fin 24)) f
    (fun k : Fin 9 => k.val ^ 2)
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  have h' : (∑ k : Fin 9, k.val ^ 2 * leechNormEightMultiplicity u k) =
      ∑ i, (u i).natAbs ^ 2 := by
    simpa [leechNormEightMultiplicity, f, Fin.ext_iff, mul_comm] using h
  exact h'.trans (leechNormEight_natSquareSum u hs)

/-- The even source residue determines its binary code bit by the absolute
coordinate: only 2 and 6 represent the nonzero bit modulo four. -/
theorem leechNormEight_even_scalar (x : ℤ) (b : ZMod 2) (hb : x.natAbs ≤ 8)
    (hr : (x : ZMod 4) = 2 * ((b.val : ℕ) : ZMod 4)) :
    (x.natAbs = 0 ∨ x.natAbs = 2 ∨ x.natAbs = 4 ∨ x.natAbs = 6 ∨ x.natAbs = 8) ∧
    (b.val = if x.natAbs = 2 ∨ x.natAbs = 6 then 1 else 0) := by
  have ha : |x| ≤ (8 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hb
  obtain ⟨hl, hh⟩ := abs_le.mp ha
  have hcheck : ∀ a : Fin 17, ∀ b : ZMod 2,
      let y : ℤ := (a.val : ℤ) - 8
      (y : ZMod 4) = 2 * ((b.val : ℕ) : ZMod 4) →
      (y.natAbs = 0 ∨ y.natAbs = 2 ∨ y.natAbs = 4 ∨ y.natAbs = 6 ∨ y.natAbs = 8) ∧
      (b.val = if y.natAbs = 2 ∨ y.natAbs = 6 then 1 else 0) := by
    decide +kernel
  let a : Fin 17 := ⟨(x + 8).toNat, by omega⟩
  have hx : (a.val : ℤ) - 8 = x := by dsimp [a]; omega
  have hh := hcheck a b
  dsimp only at hh
  rw [hx] at hh
  exact hh hr

/-- The odd source residue restricts the absolute coordinate to 1,3,5,7. -/
theorem leechNormEight_odd_scalar (x : ℤ) (b : ZMod 2) (hb : x.natAbs ≤ 8)
    (hr : (x : ZMod 4) = 1 + 2 * ((b.val : ℕ) : ZMod 4)) :
    x.natAbs = 1 ∨ x.natAbs = 3 ∨ x.natAbs = 5 ∨ x.natAbs = 7 := by
  have ha : |x| ≤ (8 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hb
  obtain ⟨hl, hh⟩ := abs_le.mp ha
  have hcheck : ∀ a : Fin 17, ∀ b : ZMod 2,
      let y : ℤ := (a.val : ℤ) - 8
      (y : ZMod 4) = 1 + 2 * ((b.val : ℕ) : ZMod 4) →
      y.natAbs = 1 ∨ y.natAbs = 3 ∨ y.natAbs = 5 ∨ y.natAbs = 7 := by
    decide +kernel
  let a : Fin 17 := ⟨(x + 8).toNat, by omega⟩
  have hx : (a.val : ℤ) - 8 = x := by dsimp [a]; omega
  have hh := hcheck a b
  dsimp only at hh
  rw [hx] at hh
  exact hh hr

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
