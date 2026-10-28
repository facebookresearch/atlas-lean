/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixShapes

/-! Complete absolute-coordinate classification of actual physical norm-six Leech vectors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem multiplicity_zero (u : Fin 24 → ℤ) (k : Fin 9)
    (h : ∀ i, (u i).natAbs ≠ k.val) : leechNormEightMultiplicity u k = 0 := by
  rw [leechNormEightMultiplicity, Finset.card_eq_zero]
  exact Finset.filter_eq_empty_iff.mpr fun i _ => h i

private theorem coordinate_not_of_zero (u : Fin 24 → ℤ) (k : Fin 9)
    (h : leechNormEightMultiplicity u k = 0) (i : Fin 24) : (u i).natAbs ≠ k.val := by
  intro hi
  have he : (Finset.univ.filter fun j => (u j).natAbs = k.val) = ∅ :=
    Finset.card_eq_zero.mp h
  have hm : i ∈ Finset.univ.filter fun j => (u j).natAbs = k.val := by simp [hi]
  rw [he] at hm
  simp at hm

private theorem code_weight (u : Fin 24 → ℤ) (c : Fin 24 → ZMod 2)
    (hb : ∀ i, (u i).natAbs ≤ 8)
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

private theorem four_coordinate_mod_eight (x : ℤ) (h : x.natAbs = 0 ∨ x.natAbs = 4) :
    (x : ZMod 8) = 4 * (if x.natAbs = 4 then (1 : ZMod 8) else 0) := by
  rcases h with h | h
  · have hx : x = 0 := Int.natAbs_eq_zero.mp h
    subst x
    norm_num
  · have ha : |x| = |(4 : ℤ)| := by
      rw [← Int.natCast_natAbs]
      simp [h]
    rcases abs_eq_abs.mp ha with hx | hx <;> subst x <;> decide

private theorem height_excludes_three_four (u : Fin 24 → ℤ)
    (hcoord : ∀ i, (u i).natAbs = 0 ∨ (u i).natAbs = 4)
    (hsum : ((∑ i, u i : ℤ) : ZMod 8) = 0) : leechNormEightMultiplicity u 4 ≠ 3 := by
  intro h3
  have hb : (∑ i : Fin 24, if (u i).natAbs = 4 then (1 : ZMod 8) else 0) =
      (leechNormEightMultiplicity u 4 : ZMod 8) := by
    simp [leechNormEightMultiplicity]
  have h : ((∑ i, u i : ℤ) : ZMod 8) =
      (4 : ZMod 8) * (leechNormEightMultiplicity u 4 : ZMod 8) := by
    rw [Int.cast_sum]
    simp_rw [four_coordinate_mod_eight _ (hcoord _)]
    rw [← Finset.mul_sum, hb]
  rw [hsum, h3] at h
  exact (by decide : (0 : ZMod 8) ≠ 12) h

/-- Every actual norm-six lattice vector has one of the four complete original coordinate shapes. -/
theorem leechNormSix_catalog (u : leechIntegral) (hs : leechSquareSum u.val = 48) :
    ∃ s : Fin 4, leechNormEightMultiplicity u.val = leechNormSixShapeCounts s := by
  have hb : ∀ i, (u.val i).natAbs ≤ 8 := fun i =>
    (leechNormSix_natAbs_le u.val hs i).trans (by decide)
  have ht := leechNormEightMultiplicity_total u.val hb
  have hn := leechNormSixMultiplicity_square u.val hb hs
  obtain ⟨m, hm, c, hc, hr, hsum⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  rcases hm with hm | hm
  · subst m
    have hr0 : ∀ i, (u.val i : ZMod 4) = 2 * ((c i).val : ZMod 4) := by
      simpa only [Int.cast_zero, zero_add] using hr
    have he (i : Fin 24) := (leechNormEight_even_scalar (u.val i) (c i) (hb i) (hr0 i)).1
    have hz (k : Fin 9) (hk : k.val = 1 ∨ k.val = 3 ∨ k.val = 5 ∨ k.val = 7) :
        leechNormEightMultiplicity u.val k = 0 := by
      apply multiplicity_zero
      intro i
      rcases he i with hi | hi | hi | hi | hi <;> omega
    have hp : (leechNormEightMultiplicity u.val 1 = 0 ∧
        leechNormEightMultiplicity u.val 3 = 0 ∧ leechNormEightMultiplicity u.val 5 = 0 ∧
        leechNormEightMultiplicity u.val 7 = 0) :=
      ⟨hz 1 (by decide), hz 3 (by decide), hz 5 (by decide), hz 7 (by decide)⟩
    have hw := golayCode_weights c hc
    rw [code_weight u.val c hb hr0] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    apply leechNormSix_shape_of_multiplicities _ ht hn (Or.inl hp) hw
    rintro ⟨h2, h4⟩
    have hn' : leechNormEightMultiplicity u.val 1 + 4 * leechNormEightMultiplicity u.val 2 +
        9 * leechNormEightMultiplicity u.val 3 + 16 * leechNormEightMultiplicity u.val 4 +
        25 * leechNormEightMultiplicity u.val 5 + 36 * leechNormEightMultiplicity u.val 6 +
        49 * leechNormEightMultiplicity u.val 7 + 64 * leechNormEightMultiplicity u.val 8 = 48 := by
      simpa [Fin.sum_univ_succ, Nat.add_assoc] using hn
    have h6 : leechNormEightMultiplicity u.val 6 = 0 := by omega
    have h8 : leechNormEightMultiplicity u.val 8 = 0 := by omega
    have hcoord (i : Fin 24) : (u.val i).natAbs = 0 ∨ (u.val i).natAbs = 4 := by
      rcases he i with hi | hi | hi | hi | hi
      · exact Or.inl hi
      · exact False.elim (coordinate_not_of_zero _ 2 h2 i hi)
      · exact Or.inr hi
      · exact False.elim (coordinate_not_of_zero _ 6 h6 i hi)
      · exact False.elim (coordinate_not_of_zero _ 8 h8 i hi)
    exact height_excludes_three_four u.val hcoord (by simpa using hsum) h4
  · subst m
    have hr1 : ∀ i, (u.val i : ZMod 4) = 1 + 2 * ((c i).val : ZMod 4) := by
      simpa only [Int.cast_one] using hr
    have ho (i : Fin 24) := leechNormEight_odd_scalar (u.val i) (c i) (hb i) (hr1 i)
    have hz (k : Fin 9)
        (hk : k.val = 0 ∨ k.val = 2 ∨ k.val = 4 ∨ k.val = 6 ∨ k.val = 8) :
        leechNormEightMultiplicity u.val k = 0 := by
      apply multiplicity_zero
      intro i
      rcases ho i with hi | hi | hi | hi <;> omega
    have hp : (leechNormEightMultiplicity u.val 0 = 0 ∧
        leechNormEightMultiplicity u.val 2 = 0 ∧ leechNormEightMultiplicity u.val 4 = 0 ∧
        leechNormEightMultiplicity u.val 6 = 0 ∧ leechNormEightMultiplicity u.val 8 = 0) :=
      ⟨hz 0 (by decide), hz 2 (by decide), hz 4 (by decide), hz 6 (by decide), hz 8 (by decide)⟩
    apply leechNormSix_shape_of_multiplicities _ ht hn (Or.inr hp)
    · left
      rw [hp.2.1, hp.2.2.2.1]
    · rintro ⟨_, h⟩
      omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
