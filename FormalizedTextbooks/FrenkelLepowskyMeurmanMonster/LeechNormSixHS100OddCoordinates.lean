/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100Flag

/-! Exact original odd shortest-vector points of the canonical genuine lattice flag. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- The complete original odd shortest vector with its sole coefficient minus three at j. -/
def leechNormSixHS100Odd (j : Fin 24) : leechIntegral :=
  griessShortLatticeVector (Sum.inr (Sum.inr (0, j)))

/-- Every physical coordinate of the original zero-code odd vector is retained. -/
theorem leechNormSixHS100Odd_coordinate (j i : Fin 24) :
    (leechNormSixHS100Odd j).val i = 1 - 4 * (if i = j then 1 else 0) := by
  have hz : golayEncodedMask 0 = 0 := by decide +kernel
  simp only [leechNormSixHS100Odd, griessShortLatticeVector, griessShortIntegral,
    Fin.val_zero, hz, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte, one_mul]
  by_cases hi : i = j <;> simp [hi]

/-- Every complete original odd candidate has actual integer square sum thirty-two. -/
theorem leechNormSixHS100Odd_square (j : Fin 24) :
    leechSquareSum (leechNormSixHS100Odd j).val = 32 :=
  griessShortIntegral_squareSum (Sum.inr (Sum.inr (0, j)))

/-- The complete zero-code odd vector has actual coordinate sum twenty. -/
theorem leechNormSixHS100Odd_sum (j : Fin 24) :
    (∑ i, (leechNormSixHS100Odd j).val i) = 20 := by
  simp_rw [leechNormSixHS100Odd_coordinate]
  simp [Finset.sum_sub_distrib]

/-- Every original odd candidate outside the two root coordinates is a genuine flag point. -/
theorem leechNormSixHS100Odd_point (j : Fin 24) (h0 : j ≠ 0) (h1 : j ≠ 1) :
    LeechNormSixHS100PointCondition leechNormSixHS100Root leechNormSixHS100Companion
      (leechNormSixHS100Odd j) := by
  rw [leechNormSixHS100PointCondition_coordinates]
  refine ⟨leechNormSixHS100Odd_square j, ?_, ?_⟩
  · simp [leechNormSixHS100Odd_coordinate, Ne.symm h0, Ne.symm h1]
  · rw [leechNormSixHS100Odd_sum, leechNormSixHS100Odd_coordinate]
    simp [Ne.symm h0]

/-- The exact complete coordinate sum of an odd original Golay sign vector. -/
theorem leechNormSixHS100Odd_signed_sum (c : Fin 24 → ZMod 2) (j : Fin 24) :
    (∑ i, (1 - 2 * ((c i).val : ℤ)) * (if i = j then -3 else 1)) =
      24 - 2 * ((∑ i, (c i).val : ℕ) : ℤ) - 4 * (1 - 2 * ((c j).val : ℤ)) := by
  have ht (i : Fin 24) :
      (1 - 2 * ((c i).val : ℤ)) * (if i = j then -3 else 1) =
        (1 - 2 * ((c i).val : ℤ)) -
          (if i = j then 4 * (1 - 2 * ((c j).val : ℤ)) else 0) := by
    by_cases hi : i = j <;> simp [hi]
    ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib]
  have hfirst : (∑ i, (1 - 2 * ((c i).val : ℤ))) =
      24 - 2 * ((∑ i, (c i).val : ℕ) : ℤ) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sum]
    norm_num
  rw [hfirst]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]


/-- Golay weights force every actual odd flag point to have zero codeword and an outside root position. -/
theorem leechNormSixHS100Odd_classification (z : leechIntegral)
    (c : Fin 24 → ZMod 2) (hc : c ∈ golayCode) (j : Fin 24)
    (hv : ∀ i, z.val i = (1 - 2 * ((c i).val : ℤ)) * (if i = j then -3 else 1))
    (hz : LeechNormSixHS100PointCondition leechNormSixHS100Root
      leechNormSixHS100Companion z) :
    j ≠ 0 ∧ j ≠ 1 ∧ c = 0 ∧ z = leechNormSixHS100Odd j := by
  obtain ⟨_, h01, hyp⟩ := (leechNormSixHS100PointCondition_coordinates z).mp hz
  have hcv (i : Fin 24) : (c i).val < 2 := ZMod.val_lt _
  have h0 : j ≠ 0 := by
    intro hj
    have h0 := hv 0
    have h1 := hv 1
    rw [hj] at h0 h1
    have hc0 : (c 0).val = 0 ∨ (c 0).val = 1 := by have h := hcv 0; omega
    have hc1 : (c 1).val = 0 ∨ (c 1).val = 1 := by have h := hcv 1; omega
    rcases hc0 with hc0 | hc0 <;> rcases hc1 with hc1 | hc1
    all_goals
      rw [hc0] at h0
      rw [hc1] at h1
      norm_num at h0 h1
      omega
  have h1 : j ≠ 1 := by
    intro hj
    have h0 := hv 0
    have h1 := hv 1
    rw [hj] at h0 h1
    have hc0 : (c 0).val = 0 ∨ (c 0).val = 1 := by have h := hcv 0; omega
    have hc1 : (c 1).val = 0 ∨ (c 1).val = 1 := by have h := hcv 1; omega
    rcases hc0 with hc0 | hc0 <;> rcases hc1 with hc1 | hc1
    all_goals
      rw [hc0] at h0
      rw [hc1] at h1
      norm_num at h0 h1
      omega
  have hsum : (∑ i, z.val i) =
      24 - 2 * ((∑ i, (c i).val : ℕ) : ℤ) - 4 * (1 - 2 * ((c j).val : ℤ)) := by
    simp_rw [hv]
    exact leechNormSixHS100Odd_signed_sum c j
  have hz0 : z.val 0 = 1 - 2 * ((c 0).val : ℤ) := by
    rw [hv]
    simp [Ne.symm h0]
  rw [hsum, hz0] at hyp
  have hw := golayCode_weights c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have hw0 : (∑ i, (c i).val : ℕ) = 0 := by
    have hc0 := hcv 0
    have hcj := hcv j
    rcases hw with hw | hw | hw | hw | hw <;> omega
  have hc0 : c = 0 := by
    funext i
    apply (ZMod.val_eq_zero _).mp
    have h := Finset.single_le_sum (f := fun k : Fin 24 => (c k).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hw0] at h
    omega
  refine ⟨h0, h1, hc0, Subtype.ext (funext fun i => ?_)⟩
  rw [hv, hc0, leechNormSixHS100Odd_coordinate]
  simp only [Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero, one_mul]
  by_cases hi : i = j <;> simp [hi]

/-- Adding the genuine all-one codeword reverses every original odd coordinate sign. -/
theorem leechNormSixHS100Odd_sign_complement (t : ZMod 2) :
    -(1 - 2 * (t.val : ℤ)) = 1 - 2 * ((t + 1).val : ℤ) := by
  fin_cases t <;> decide

/-- Both original preferred odd-vector signs have precisely the outside zero-code classification. -/
theorem leechNormSixHS100Odd_catalog (z : leechIntegral) (d : Fin 2048) (j : Fin 24)
    (hp : z.val = griessShortIntegral (Sum.inr (Sum.inr (d, j))) ∨
      z.val = -griessShortIntegral (Sum.inr (Sum.inr (d, j))))
    (hz : LeechNormSixHS100PointCondition leechNormSixHS100Root
      leechNormSixHS100Companion z) : j ≠ 0 ∧ j ≠ 1 ∧ z = leechNormSixHS100Odd j := by
  let dl : Fin 4096 := ⟨d.val, by omega⟩
  let c : Fin 24 → ZMod 2 := golayEncoder (golayLabelCoefficients dl)
  have hc : c ∈ golayCode := ⟨_, rfl⟩
  have hsign (i : Fin 24) : (if (golayEncodedMask d.val).testBit i.val then (-1 : ℤ) else 1) =
      1 - 2 * ((c i).val : ℤ) := by
    change _ = 1 - 2 * ((golayEncoder (golayLabelCoefficients dl) i).val : ℤ)
    rw [golayLabelEncoder_match]
    change _ = 1 - 2 * ((if (golayEncodedMask d.val).testBit i.val then 1 else 0 : ℕ) : ℤ)
    cases hb : (golayEncodedMask d.val).testBit i.val <;> norm_num [hb]
  rcases hp with hp | hp
  · have h := leechNormSixHS100Odd_classification z c hc j (fun i => by
      rw [hp]
      change (if (golayEncodedMask d.val).testBit i.val then (-1 : ℤ) else 1) *
        (if i = j then -3 else 1) = _
      rw [hsign]) hz
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  · have hone : (fun _ : Fin 24 => (1 : ZMod 2)) ∈ golayCode :=
      ⟨Pi.single 11 1, golay_all_one⟩
    have h := leechNormSixHS100Odd_classification z (c + fun _ => 1)
      (golayCode.add_mem hc hone) j (fun i => by
        rw [hp]
        change -((if (golayEncodedMask d.val).testBit i.val then (-1 : ℤ) else 1) *
          (if i = j then -3 else 1)) =
            (1 - 2 * ((c i + 1).val : ℤ)) * (if i = j then -3 else 1)
        rw [← leechNormSixHS100Odd_sign_complement, hsign]
        ring) hz
    exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- Different original distinguished positions give different complete odd lattice vectors. -/
theorem leechNormSixHS100Odd_injective : Function.Injective leechNormSixHS100Odd := by
  intro i j h
  have he := congrArg (fun z : leechIntegral => z.val i) h
  rw [leechNormSixHS100Odd_coordinate, leechNormSixHS100Odd_coordinate] at he
  by_contra hij
  simp [hij] at he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
