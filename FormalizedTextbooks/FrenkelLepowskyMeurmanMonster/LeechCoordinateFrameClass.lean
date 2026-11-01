/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The norm-eight representatives of the distinguished coordinate-frame class. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCatalog

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The integral coordinate-frame vector has physical squared norm eight. -/
def leechCoordinateFrameVector (i : Fin 24) : Fin 24 → ℤ := Pi.single i 8

/-- Every coordinate-frame vector is an actual lattice vector. -/
theorem leechCoordinateFrameVector_mem (i : Fin 24) :
    leechCoordinateFrameVector i ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, 0, golayCode.zero_mem, ?_, ?_⟩
  · intro j
    by_cases h : j = i
    · norm_num [leechCoordinateFrameVector, h]
      decide
    · simp [leechCoordinateFrameVector, h]
  · norm_num [leechCoordinateFrameVector, Pi.single_apply]
    decide

/-- The integral square sum of each coordinate-frame vector is 64. -/
theorem leechCoordinateFrameVector_square (i : Fin 24) :
    leechSquareSum (leechCoordinateFrameVector i) = 64 := by
  simp [leechSquareSum, leechCoordinateFrameVector, Pi.single_apply, ite_pow]

private theorem frameClass_scalar (x : ℤ) (m : Fin 2) (b : ZMod 2)
    (hb : x.natAbs ≤ 8)
    (hr : (x : ZMod 8) = 2 * (m.val : ZMod 8) + 4 * (b.val : ZMod 8)) :
    (m.val = 0 → (x.natAbs = 0 ∨ x.natAbs = 4 ∨ x.natAbs = 8) ∧
      b.val = if x.natAbs = 4 then 1 else 0) ∧
    (m.val = 1 → 2 ≤ x.natAbs) := by
  have ht : ∀ a : Fin 17, ∀ m : Fin 2, ∀ b : ZMod 2,
      let x : ℤ := (a.val : ℤ) - 8
      (x : ZMod 8) = 2 * (m.val : ZMod 8) + 4 * (b.val : ZMod 8) →
      (m.val = 0 → (x.natAbs = 0 ∨ x.natAbs = 4 ∨ x.natAbs = 8) ∧
        b.val = if x.natAbs = 4 then 1 else 0) ∧
      (m.val = 1 → 2 ≤ x.natAbs) := by decide +kernel
  have ha : |x| ≤ (8 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hb
  let a : Fin 17 := ⟨(x + 8).toNat, by omega⟩
  have hx : (a.val : ℤ) - 8 = x := by dsimp [a]; omega
  have hh := ht a m b
  dsimp only at hh
  rw [hx] at hh
  exact hh hr

private theorem frameClass_double_residue (u w : Fin 24 → ℤ) (m : ℤ)
    (c : Fin 24 → ZMod 2)
    (hw : ∀ i, (w i : ZMod 4) = (m : ZMod 4) + 2 * ((c i).val : ZMod 4))
    (hu : u = fun i => 2 * w i + leechCoordinateFrameVector 0 i) (i : Fin 24) :
    (u i : ZMod 8) = 2 * (m : ZMod 8) + 4 * ((c i).val : ZMod 8) := by
  have hd : (4 : ℤ) ∣ m + 2 * ((c i).val : ℤ) - w i := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 4).mp
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hw i
  obtain ⟨k, hk⟩ := hd
  suffices hh : (u i : ZMod 8) = ((2 * m + 4 * ((c i).val : ℤ) : ℤ) : ZMod 8) by
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hh
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 8).mpr
  have hi := congrFun hu i
  by_cases hz : i = 0
  · subst i
    refine ⟨k - 1, ?_⟩
    simp [leechCoordinateFrameVector] at hi
    linear_combination 2 * hk - hi
  · refine ⟨k, ?_⟩
    simp [leechCoordinateFrameVector, hz] at hi
    linear_combination 2 * hk - hi

private theorem frameClass_even (u w : leechIntegral) (hs : leechSquareSum u.val = 64)
    (hu : u.val = fun i => 2 * w.val i + leechCoordinateFrameVector 0 i) :
    ∃ c ∈ golayCode, ∀ i,
      ((u.val i).natAbs = 0 ∨ (u.val i).natAbs = 4 ∨ (u.val i).natAbs = 8) ∧
      (c i).val = if (u.val i).natAbs = 4 then 1 else 0 := by
  obtain ⟨m, hm, c, hc, hr, _⟩ := (mem_leechIntegral_iff_source w.val).mp w.property
  have hb := leechNormEight_natAbs_le u.val hs
  rcases hm with hm | hm
  · subst m
    refine ⟨c, hc, fun i => ?_⟩
    exact (frameClass_scalar (u.val i) 0 (c i) (hb i)
      (by simpa using frameClass_double_residue u.val w.val 0 c hr hu i)).1 rfl
  · subst m
    have hl (i : Fin 24) : 2 ≤ (u.val i).natAbs :=
      (frameClass_scalar (u.val i) 1 (c i) (hb i)
        (by simpa using frameClass_double_residue u.val w.val 1 c hr hu i)).2 rfl
    have hsum : (96 : ℕ) ≤ ∑ i, (u.val i).natAbs ^ 2 := by
      calc
        96 = ∑ _i : Fin 24, (4 : ℕ) := by simp
        _ ≤ ∑ i, (u.val i).natAbs ^ 2 := Finset.sum_le_sum fun i _ => by
          have hi := hl i
          nlinarith
    rw [leechNormEight_natSquareSum u.val hs] at hsum
    omega

private theorem frameClass_eight_count (u w : leechIntegral) (hs : leechSquareSum u.val = 64)
    (hu : u.val = fun i => 2 * w.val i + leechCoordinateFrameVector 0 i) :
    leechNormEightMultiplicity u.val 8 = 1 := by
  classical
  obtain ⟨c, hc, hr⟩ := frameClass_even u w hs hu
  have hzero (k : Fin 9) (hk : k.val ≠ 0 ∧ k.val ≠ 4 ∧ k.val ≠ 8) :
      leechNormEightMultiplicity u.val k = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    rcases (hr i).1 with h | h | h <;> omega
  have h1 := hzero 1 (by decide)
  have h2 := hzero 2 (by decide)
  have h6 := hzero 6 (by decide)
  have hcweight : (∑ i, (c i).val) = leechNormEightMultiplicity u.val 4 := by
    simp_rw [(hr _).2]
    simp [leechNormEightMultiplicity]
  have hfour : leechNormEightMultiplicity u.val 4 ≠ 4 := by
    have hw := golayCode_weights c hc
    rw [hcweight] at hw
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using
      (show leechNormEightMultiplicity u.val 4 ≠ 4 from by
        intro he
        norm_num [he] at hw)
  obtain ⟨s, he⟩ := leechNormEight_catalog u hs
  rw [he] at h1 h2 h6 hfour ⊢
  fin_cases s <;> simp_all [leechNormEightShapeCounts]

/-- A norm-eight vector in the distinguished class modulo twice the lattice
is precisely a positive or negative coordinate-frame vector. -/
theorem leechNormEight_coordinate_frame_class (u w : leechIntegral)
    (hs : leechSquareSum u.val = 64)
    (hu : u.val = fun i => 2 * w.val i + leechCoordinateFrameVector 0 i) :
    ∃ i : Fin 24, u.val = leechCoordinateFrameVector i ∨
      u.val = -leechCoordinateFrameVector i := by
  classical
  have hn := leechNormEight_natSquareSum u.val hs
  have h8 := frameClass_eight_count u w hs hu
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h8
  rw [show (8 : Fin 9).val = 8 by decide] at hi
  have habs : (u.val i).natAbs = 8 := by
    have hm : i ∈ Finset.univ.filter fun j => (u.val j).natAbs = 8 := by rw [hi]; simp
    exact (Finset.mem_filter.mp hm).2
  have hrest : ∀ j, j ≠ i → u.val j = 0 := by
    intro j hj
    have he : ∑ k ∈ Finset.univ.erase i, (u.val k).natAbs ^ 2 = 0 := by
      have hh := Finset.sum_erase_add (Finset.univ : Finset (Fin 24))
        (fun k => (u.val k).natAbs ^ 2) (Finset.mem_univ i)
      rw [habs, hn] at hh
      omega
    have hjb := Finset.single_le_sum (f := fun k => (u.val k).natAbs ^ 2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
    rw [he] at hjb
    have hz : (u.val j).natAbs = 0 := by nlinarith
    exact Int.natAbs_eq_zero.mp hz
  have hi8 : u.val i = 8 ∨ u.val i = -8 := by
    have ha : |u.val i| = (8 : ℤ) := by
      rw [← Int.natCast_natAbs, habs]
      norm_num
    rcases abs_cases (u.val i) with h | h <;> omega
  refine ⟨i, ?_⟩
  rcases hi8 with hi8 | hi8
  · left
    funext j
    by_cases hj : j = i
    · subst j
      simp [leechCoordinateFrameVector, hi8]
    · simp [leechCoordinateFrameVector, hj, hrest j hj]
  · right
    funext j
    by_cases hj : j = i
    · subst j
      simp [leechCoordinateFrameVector, hi8]
    · simp [leechCoordinateFrameVector, hj, hrest j hj]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
