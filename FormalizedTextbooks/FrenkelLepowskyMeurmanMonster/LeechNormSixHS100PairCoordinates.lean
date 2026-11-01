/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100Flag

/-! Exact original coordinate-pair points of the canonical norm-four/norm-six flag. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false

/-- The complete positive coordinate pair occurring in the canonical actual point set. -/
def leechNormSixHS100PairIntegral (i : Fin 24) : ℤ :=
  if i = 0 ∨ i = 1 then 4 else 0

/-- The complete positive pair satisfies the original integral Leech congruences. -/
theorem leechNormSixHS100PairIntegral_mem : leechNormSixHS100PairIntegral ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨0, Or.inl rfl, 0, ⟨0, map_zero golayEncoder⟩, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0 ∨ i = 1 <;> norm_num [leechNormSixHS100PairIntegral, hi]
    decide
  · norm_num [leechNormSixHS100PairIntegral, Fin.sum_univ_succ]
    decide

/-- The genuine original positive pair lattice point. -/
def leechNormSixHS100Pair : leechIntegral :=
  ⟨leechNormSixHS100PairIntegral, leechNormSixHS100PairIntegral_mem⟩

/-- The complete positive pair has every required original physical point condition. -/
theorem leechNormSixHS100Pair_point :
    LeechNormSixHS100PointCondition leechNormSixHS100Root leechNormSixHS100Companion
      leechNormSixHS100Pair := by
  rw [leechNormSixHS100PointCondition_coordinates]
  norm_num [leechNormSixHS100Pair, leechNormSixHS100PairIntegral,
    leechSquareSum, Fin.sum_univ_succ]

/-- Every complete signed coordinate-pair vector meeting the physical flag conditions is this pair. -/
theorem leechNormSixHS100Pair_classification (z : leechIntegral)
    (a b : Fin 24) (hab : a ≠ b) (ε η : ℤ)
    (hε : ε = 4 ∨ ε = -4) (hη : η = 4 ∨ η = -4)
    (hv : ∀ i, z.val i = ε * (if i = a then 1 else 0) + η * (if i = b then 1 else 0))
    (hz : LeechNormSixHS100PointCondition leechNormSixHS100Root
      leechNormSixHS100Companion z) : z = leechNormSixHS100Pair := by
  obtain ⟨_, h01, hyp⟩ := (leechNormSixHS100PointCondition_coordinates z).mp hz
  have hsum : (∑ i, z.val i) = ε + η := by
    simp_rw [hv]
    simp [Finset.sum_add_distrib]
  have hz0 : z.val 0 = 0 ∨ z.val 0 = 4 ∨ z.val 0 = -4 := by
    rw [hv]
    by_cases ha : (0 : Fin 24) = a
    · simp only [ha, hab, ↓reduceIte, mul_one, mul_zero, add_zero]
      rcases hε with hε | hε <;> omega
    · by_cases hb : (0 : Fin 24) = b
      · simp only [hb, Ne.symm hab, ↓reduceIte, mul_one, mul_zero, zero_add]
        rcases hη with hη | hη <;> omega
      · simp [ha, hb]
  rw [hsum] at hyp
  have hpos : ε = 4 ∧ η = 4 ∧ z.val 0 = 4 := by
    rcases hε with hε | hε <;> rcases hη with hη | hη <;>
      rcases hz0 with hz0 | hz0 | hz0 <;> omega
  obtain ⟨rfl, rfl, hz0⟩ := hpos
  have ha0 : (0 : Fin 24) = a ∨ (0 : Fin 24) = b := by
    by_contra h
    push Not at h
    have h0 := hv 0
    simp only [h.1, h.2, ↓reduceIte, mul_zero, zero_add] at h0
    omega
  have ha1 : (1 : Fin 24) = a ∨ (1 : Fin 24) = b := by
    by_contra h
    push Not at h
    have h1 := hv 1
    simp only [h.1, h.2, ↓reduceIte, mul_zero, zero_add] at h1
    omega
  have hor : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    have hne : (0 : Fin 24) ≠ 1 := by decide
    rcases ha0 with ha0 | ha0 <;> rcases ha1 with ha1 | ha1
    · exact False.elim (hne (ha0.trans ha1.symm))
    · exact Or.inl ⟨ha0.symm, ha1.symm⟩
    · exact Or.inr ⟨ha1.symm, ha0.symm⟩
    · exact False.elim (hne (ha0.trans ha1.symm))
  apply Subtype.ext
  funext i
  rw [hv]
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
    simp [leechNormSixHS100Pair, leechNormSixHS100PairIntegral, h0, h1]

/-- Both signs of every original preferred pair label have precisely the one actual flag destination. -/
theorem leechNormSixHS100Pair_catalog (z : leechIntegral) (s : Fin 2) (p : Fin 276)
    (hp : z.val = griessShortIntegral (Sum.inl (s, p)) ∨
      z.val = -griessShortIntegral (Sum.inl (s, p)))
    (hz : LeechNormSixHS100PointCondition leechNormSixHS100Root
      leechNormSixHS100Companion z) : z = leechNormSixHS100Pair := by
  rcases hp with hp | hp
  · refine leechNormSixHS100Pair_classification z (griessCoordinatePair p).1
      (griessCoordinatePair p).2 (griessCoordinatePair_ne p) 4
      (if s = 0 then -4 else 4) (Or.inl rfl) ?_ ?_ hz
    · split_ifs <;> simp
    · intro i
      rw [hp]
      rfl
  · refine leechNormSixHS100Pair_classification z (griessCoordinatePair p).1
      (griessCoordinatePair p).2 (griessCoordinatePair_ne p) (-4)
      (-(if s = 0 then -4 else 4)) (Or.inr rfl) ?_ ?_ hz
    · split_ifs <;> norm_num
    · intro i
      rw [hp]
      simp only [Pi.neg_apply, griessShortIntegral]
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
