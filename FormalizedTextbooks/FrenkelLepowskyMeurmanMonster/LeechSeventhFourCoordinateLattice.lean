/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

/-! Actual lattice membership for coordinates divisible by four
and exact half-difference classes. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

private theorem parity_one_impossible : ∀ c : ZMod 2,
    (0 : ZMod 4) ≠ 1 + 2 * (c.val : ZMod 4) := by decide +kernel

/-- Four times an integral coordinate vector is in the actual Leech lattice exactly at even sum. -/
theorem leechSeventh_four_coordinate_mem_iff (v : Fin 24 → ℤ) :
    (4 : ℤ) • v ∈ leechIntegral ↔ Even (∑ i, v i) := by
  rw [mem_leechIntegral_iff_source]
  constructor
  · rintro ⟨m, hm, c, _, hc, hs⟩
    have hm0 : m = 0 := by
      rcases hm with h0 | h1
      · exact h0
      · have h := hc 0
        rw [h1] at h
        have he : (0 : ZMod 4) = 1 + 2 * ((c 0).val : ZMod 4) := by
          norm_num [Pi.smul_apply, smul_eq_mul] at h
          rw [show (4 : ZMod 4) = 0 from by decide, zero_mul] at h
          exact h
        exact False.elim (parity_one_impossible (c 0) he)
    rw [hm0] at hs
    have he : ((4 * ∑ i, v i : ℤ) : ZMod 8) = 0 := by
      simpa only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
        Int.cast_zero, mul_zero] using hs
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp he
    apply even_iff_two_dvd.mpr
    refine ⟨k, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    refine ⟨0, Or.inl rfl, 0, golayCode.zero_mem, ?_, ?_⟩
    · intro i
      norm_num [Pi.smul_apply, smul_eq_mul]
      rw [show (4 : ZMod 4) = 0 from by decide, zero_mul]
    · have he : (∑ i, (4 : ℤ) * v i) = 8 * k := by
        rw [← Finset.mul_sum, hk]
        ring
      change ((∑ i, 4 * v i : ℤ) : ZMod 8) = 4 * (0 : ZMod 8)
      rw [he]
      norm_num
      rw [show (8 : ZMod 8) = 0 from by decide, zero_mul]

/-- Equality of actual quotient classes is exactly membership
of a specified integral half-difference. -/
theorem leechSeventh_reduction_eq_iff_half (u v : leechIntegral) (w : Fin 24 → ℤ)
    (hw : u.val - v.val = (2 : ℤ) • w) :
    leechReduction u = leechReduction v ↔ w ∈ leechIntegral := by
  have hq : leechReduction u = leechReduction v ↔ u - v ∈ twiceLeechIntegral :=
    QuotientAddGroup.eq_iff_sub_mem
  rw [hq]
  constructor
  · rintro ⟨z, hz⟩
    have he : z.val = w := by
      funext i
      have h := congrArg (fun x : leechIntegral => x.val i) hz
      have hwi := congrArg (fun x : Fin 24 → ℤ => x i) hw
      change 2 * z.val i = u.val i - v.val i at h
      change u.val i - v.val i = 2 * w i at hwi
      omega
    exact he ▸ z.property
  · intro hm
    refine ⟨⟨w, hm⟩, ?_⟩
    apply Subtype.ext
    change (2 : ℤ) • w = u.val - v.val
    exact hw.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
