/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismTransitivity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOctads

/-! Actual odd norm-eight pentad vectors and source-sign normalization. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The odd norm-eight vector with negative threes on a prescribed pentad. -/
def monsterCo1PolarPentadVector (P : Finset (Fin 24)) : Fin 24 → ℤ :=
  fun i => if i ∈ P then -3 else 1

/-- Every pentad vector satisfies the genuine source Leech congruences. -/
theorem monsterCo1PolarPentadVector_mem (P : Finset (Fin 24)) (hP : P.card = 5) :
    monsterCo1PolarPentadVector P ∈ leechIntegral := by
  apply (mem_leechIntegral_iff_source _).mpr
  refine ⟨1, Or.inr rfl, 0, golayCode.zero_mem, ?_, ?_⟩
  · intro i
    simp only [monsterCo1PolarPentadVector]
    simp only [Pi.zero_apply, ZMod.val_zero, Nat.cast_zero, mul_zero, add_zero]
    split_ifs <;> decide +kernel
  · have hsum : ∑ i, monsterCo1PolarPentadVector P i = 24 - 4 * (P.card : ℤ) := by
      have hpoint (i : Fin 24) : monsterCo1PolarPentadVector P i =
          1 - 4 * (if i ∈ P then 1 else 0 : ℤ) := by
        simp only [monsterCo1PolarPentadVector]
        split_ifs <;> ring
      simp_rw [hpoint]
      simp [Finset.sum_sub_distrib, mul_comm]
    rw [hsum, hP]
    decide +kernel

/-- Pentad vectors have actual integer square sum 64. -/
theorem monsterCo1PolarPentadVector_square (P : Finset (Fin 24)) (hP : P.card = 5) :
    leechSquareSum (monsterCo1PolarPentadVector P) = 64 := by
  have hpoint (i : Fin 24) : monsterCo1PolarPentadVector P i ^ 2 =
      1 + 8 * (if i ∈ P then 1 else 0 : ℤ) := by
    simp only [monsterCo1PolarPentadVector]
    split_ifs <;> ring
  simp only [leechSquareSum, hpoint, Finset.sum_add_distrib]
  simp [hP]

/-- Any actual odd lattice vector can be normalized to physical residue one by a genuine sign. -/
theorem monsterCo1PolarLocal_source_sign (u : leechIntegral)
    (hodd : (u.val 0 : ZMod 2) = 1) :
    ∃ d : golayCode, ∀ i : Fin 24,
      ((leechIntegralAction (golaySignIsometry d) u).val i : ZMod 4) = 1 := by
  obtain ⟨m, hm, c, hc, hr, _⟩ := (mem_leechIntegral_iff_source u.val).mp u.property
  have hm1 : m = 1 := by
    rcases hm with hm | hm
    · subst m
      have h := congrArg (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) (hr 0)
      have htwo : (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) (2 : ZMod 4) = 0 := by
        decide +kernel
      simp only [map_add, map_mul, htwo, zero_mul, map_intCast] at h
      rw [hodd] at h
      exact False.elim (one_ne_zero h)
    · exact hm
  subst m
  refine ⟨⟨c, hc⟩, ?_⟩
  intro i
  rw [leechIntegralAction_golaySign]
  change ((if c i = 0 then u.val i else -u.val i : ℤ) : ZMod 4) = 1
  by_cases hi : c i = 0
  · simp only [hi, ite_true, hr]
    decide +kernel
  · simp only [hi, ite_false, Int.cast_neg, hr]
    have hscalar : ∀ b : ZMod 2, b ≠ 0 → -(1 + 2 * (b.val : ZMod 4)) = 1 := by
      decide +kernel
    exact hscalar (c i) hi

/-- Residue-one norm-eight vectors have precisely one of the two genuine odd shapes. -/
theorem monsterCo1PolarLocal_residue_shapes (u : leechIntegral)
    (hn : leechSquareSum u.val = 64) (hr : ∀ i, (u.val i : ZMod 4) = 1) :
    leechNormEightMultiplicity u.val = leechNormEightShapeCounts 6 ∨
      leechNormEightMultiplicity u.val = leechNormEightShapeCounts 7 := by
  have hz : leechNormEightMultiplicity u.val 0 = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    have hu : u.val i = 0 := Int.natAbs_eq_zero.mp hi
    have hh := hr i
    rw [hu] at hh
    change (0 : ZMod 4) = 1 at hh
    exact (by decide : (0 : ZMod 4) ≠ 1) hh
  obtain ⟨s, hs⟩ := leechNormEight_catalog u hn
  have hsz := congrFun hs 0
  rw [hz] at hsz
  fin_cases s
  all_goals first
    | exact Or.inl hs
    | exact Or.inr hs
    | norm_num [leechNormEightShapeCounts] at hsz

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
