/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWAsm

/-! # Tight checked bounds of packed tensors (factory)

The bounds produced by the packed word actions grow by the crude letter growth factors.  A cheap
kernel check (`colsLtB`, one mask per column) certifies a power-of-two bound of the actual fields
(`tbnd_tight`), so that the multiplicative packed dot products can be used for the self dot of the
target (`ident_forward_selfM` / `ident_inverse_selfM`), which needs much less kernel memory than
the field-by-field loop. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open scoped BigOperators

/-! ## Tight field bounds of packed tensors -/

/-- The bits `k ≤ b < w` of a field, replicated over `2^12` fields. -/
def hiMaskT (w k : ℕ) : ℕ := dblM w (2 ^ w - 2 ^ k) 1 12

theorem fld_hiMaskT (w k t : ℕ) (ht : t < 2 ^ 12) :
    fld w (hiMaskT w k) t = 2 ^ w - 2 ^ k := by
  have hB : 2 ^ w - 2 ^ k < 2 ^ (w * 1) := by
    rw [mul_one]
    exact Nat.sub_lt (by positivity) (by positivity)
  rw [hiMaskT, fld_dblM w _ 1 (by norm_num) hB 12 t (by simpa using ht), Nat.mod_one,
    fld_zero_right]
  exact Nat.mod_eq_of_lt (by rw [mul_one] at hB; exact hB)

theorem lt_of_and_hi (x w k : ℕ) (hx : x < 2 ^ w) (hk : k ≤ w) (h : x &&& (2 ^ w - 2 ^ k) = 0) :
    x < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  by_cases hbw : b < w
  · have h1 : (2 ^ w - 2 ^ k).testBit b = true := by
      have e : 2 ^ w - 2 ^ k = (2 ^ (w - k) - 1) <<< k := by
        rw [Nat.shiftLeft_eq, Nat.sub_mul, one_mul, ← pow_add, Nat.sub_add_cancel hk]
      rw [e, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    have h2 := congrArg (fun y => y.testBit b) h
    simp only [Nat.testBit_and, h1, Bool.and_true, Nat.zero_testBit] at h2
    exact h2
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
      (by omega)))

/-- All fields of all 24 columns are below `2^k`. -/
def colsLtB (w k : ℕ) (Y : List SVec) : Bool :=
  (List.range 24).all (fun i => ((tcol Y i).1 &&& hiMaskT w k) == 0 &&
    ((tcol Y i).2 &&& hiMaskT w k) == 0)

/-- A checked tight bound of a packed tensor. -/
theorem tbnd_tight (w k C : ℕ) (Y : List SVec) (hY : TBnd w C Y) (hk : k ≤ w)
    (h : colsLtB w k Y = true) : TBnd w (2 ^ k - 1) Y := by
  intro i hi
  simp only [colsLtB, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h i hi
  obtain ⟨s1, s2, s3⟩ := hY i hi
  refine ⟨s1, s2, fun t ht => ?_⟩
  have f1 : fld w (tcol Y i).1 t &&& (2 ^ w - 2 ^ k) = 0 := by
    rw [← fld_hiMaskT w k t ht, ← fld_land, h1, fld_zero_right_zero]
  have f2 : fld w (tcol Y i).2 t &&& (2 ^ w - 2 ^ k) = 0 := by
    rw [← fld_hiMaskT w k t ht, ← fld_land, h2, fld_zero_right_zero]
  have l1 := lt_of_and_hi _ w k (fld_lt _ _ _) hk f1
  have l2 := lt_of_and_hi _ w k (fld_lt _ _ _) hk f2
  constructor <;> omega

/-! ## Assembly with the multiplicative self dot under tight bounds -/

/-- Forward identification from self pairings, with tight checked bounds of both tensors. -/
theorem ident_forward_selfM (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hCC : 2 * (2 * 4096 * (C * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hok : octPackOk wo L = true)
    (hm : triMatF true L W = selfMatQ W)
    (hp : pairSumQ true L W = W.sden * (selfPairsZ W : ℚ))
    (hn : L.sden * (octSumZ wo true L W : ℚ) / 8 = W.sden * (selfOctP W : ℚ))
    (ha : (oddWZ w true X W : ℚ) / (2 * D) = W.sden * (selfOddP W : ℚ))
    (ht : L.sden * (oddLZ w true Y L : ℚ) / E +
      (tdotM w (trialityTensorT w (!true) X) Y : ℚ) / (2 * D * E) =
        (tdotM w Y Y : ℚ) / (E * E)) :
    sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_forward_self i j h g L W hL hW hLt hWt hX hY hB hBC hCC hx hy hok hm hp hn ha ht

/-- Inverse identification from self pairings, with tight checked bounds of both tensors. -/
theorem ident_inverse_selfM (i j : Fin 12) (h g : H) (L W : IdentVec) {wo w B C : ℕ}
    {X Y : List SVec} {D E : ℚ} (hL : L.sh.ok = true) (hW : W.sh.ok = true)
    (hLt : L.ten = tensorRat w X D) (hWt : W.ten = tensorRat w Y E) (hX : TBnd w B X)
    (hY : TBnd w C Y) (hB : 4 * B < 2 ^ w) (hBC : 2 * (2 * 4096 * (4 * B * C)) < 2 ^ w)
    (hCC : 2 * (2 * 4096 * (C * C)) < 2 ^ w)
    (hx : griessConwayEncode (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) = L.real)
    (hy : griessConwayEncode (rhoLocal g (generatedAxisGlobalTwelveRepresentative j)) = W.real)
    (hok : octPackOk wo L = true)
    (hm : triMatF false L W = selfMatQ W)
    (hp : pairSumQ false L W = W.sden * (selfPairsZ W : ℚ))
    (hn : L.sden * (octSumZ wo false L W : ℚ) / 8 = W.sden * (selfOctP W : ℚ))
    (ha : (oddWZ w false X W : ℚ) / (2 * D) = W.sden * (selfOddP W : ℚ))
    (ht : L.sden * (oddLZ w false Y L : ℚ) / E +
      (tdotM w (trialityTensorT w (!false) X) Y : ℚ) / (2 * D * E) =
        (tdotM w Y Y : ℚ) / (E * E)) :
    sExtra.symm (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) =
      rhoLocal g (generatedAxisGlobalTwelveRepresentative j) :=
  ident_inverse_self i j h g L W hL hW hLt hWt hX hY hB hBC hCC hx hy hok hm hp hn ha ht
end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
