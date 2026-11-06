/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete absolute-coordinate classification of actual norm-eight Leech vectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightShapes
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem normEightMultiplicity_eq_zero (u : Fin 24 → ℤ) (k : Fin 9)
    (h : ∀ i, (u i).natAbs ≠ k.val) : leechNormEightMultiplicity u k = 0 := by
  rw [leechNormEightMultiplicity, Finset.card_eq_zero]
  exact Finset.filter_eq_empty_iff.mpr fun i _ => h i

private theorem normEightCodeWeight_eq_multiplicities (u : Fin 24 → ℤ)
    (c : Fin 24 → ZMod 2) (hb : ∀ i, (u i).natAbs ≤ 8)
    (hr : ∀ i, (u i : ZMod 4) = 2 * ((c i).val : ZMod 4)) :
    (∑ i, (c i).val) = leechNormEightMultiplicity u 2 + leechNormEightMultiplicity u 6 := by
  have hbit (i : Fin 24) : (c i).val =
      (if (u i).natAbs = 2 then 1 else 0) + (if (u i).natAbs = 6 then 1 else 0) := by
    rw [(leechNormEight_even_scalar (u i) (c i) (hb i) (hr i)).2]
    by_cases h2 : (u i).natAbs = 2
    · simp [h2]
    · by_cases h6 : (u i).natAbs = 6 <;> simp [h2, h6]
  simp_rw [hbit]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_boole, leechNormEightMultiplicity]
  norm_num

/-- Every actual integral Leech vector of physical norm eight has one of the
six even or two odd coordinate shapes. This is a complete classification,
using the actual source congruences and the proved Golay weight distribution. -/
theorem leechNormEight_catalog (u : leechIntegral) (hs : leechSquareSum u.val = 64) :
    ∃ s : Fin 8, leechNormEightMultiplicity u.val = leechNormEightShapeCounts s := by
  have hb := leechNormEight_natAbs_le u.val hs
  have ht := leechNormEightMultiplicity_total u.val hb
  have hn := leechNormEightMultiplicity_square u.val hb hs
  obtain ⟨m, hm, c, hc, hr, hsum⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  rcases hm with hm | hm
  · subst m
    have hr0 : ∀ i, (u.val i : ZMod 4) = 2 * ((c i).val : ZMod 4) := by
      simpa only [Int.cast_zero, zero_add] using hr
    have he (i : Fin 24) := (leechNormEight_even_scalar (u.val i) (c i) (hb i) (hr0 i)).1
    have hz (k : Fin 9) (hk : k.val = 1 ∨ k.val = 3 ∨ k.val = 5 ∨ k.val = 7) :
        leechNormEightMultiplicity u.val k = 0 := by
      apply normEightMultiplicity_eq_zero
      intro i
      rcases he i with hi | hi | hi | hi | hi <;> omega
    have hp : (leechNormEightMultiplicity u.val 1 = 0 ∧
        leechNormEightMultiplicity u.val 3 = 0 ∧ leechNormEightMultiplicity u.val 5 = 0 ∧
        leechNormEightMultiplicity u.val 7 = 0) :=
      ⟨hz 1 (by decide), hz 3 (by decide), hz 5 (by decide), hz 7 (by decide)⟩
    have hw := golayCode_weights c hc
    rw [normEightCodeWeight_eq_multiplicities u.val c hb hr0] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    exact leechNormEight_shape_of_multiplicities _ ht hn (Or.inl hp) hw
  · subst m
    have hr1 : ∀ i, (u.val i : ZMod 4) = 1 + 2 * ((c i).val : ZMod 4) := by
      simpa only [Int.cast_one] using hr
    have ho (i : Fin 24) := leechNormEight_odd_scalar (u.val i) (c i) (hb i) (hr1 i)
    have hz (k : Fin 9)
        (hk : k.val = 0 ∨ k.val = 2 ∨ k.val = 4 ∨ k.val = 6 ∨ k.val = 8) :
        leechNormEightMultiplicity u.val k = 0 := by
      apply normEightMultiplicity_eq_zero
      intro i
      rcases ho i with hi | hi | hi | hi <;> omega
    have hp : (leechNormEightMultiplicity u.val 0 = 0 ∧
        leechNormEightMultiplicity u.val 2 = 0 ∧ leechNormEightMultiplicity u.val 4 = 0 ∧
        leechNormEightMultiplicity u.val 6 = 0 ∧ leechNormEightMultiplicity u.val 8 = 0) :=
      ⟨hz 0 (by decide), hz 2 (by decide), hz 4 (by decide), hz 6 (by decide), hz 8 (by decide)⟩
    apply leechNormEight_shape_of_multiplicities _ ht hn (Or.inr hp)
    left
    rw [hp.2.1, hp.2.2.2.1]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
