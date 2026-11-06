/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairOddThreePositions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairOddFiveOrbits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairPermutationMultiplicity

/-! Genuine positive-root stabilizer transitivity on the entire odd three-coordinate family. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every original odd three-coordinate paired vector has one of two forced root orientations. -/
theorem leechNormSixPair_odd_three_root_pattern (u : LeechNormSixPair)
    (hs : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts 3) :
    (u.val.val 0 = 3 ∧ u.val.val 1 = 1) ∨
      (u.val.val 0 = 1 ∧ u.val.val 1 = 3) := by
  obtain ⟨s, hshape, hpat⟩ := leechNormSix_pair_catalog u.val u.property.1 0 1 u.property.2
  have hs3 : s = 3 := by
    have h3 : leechNormSixShapeCounts s 3 = 3 := by
      simpa [leechNormSixShapeCounts] using congrFun (hshape.symm.trans hs) 3
    fin_cases s <;> simp_all [leechNormSixShapeCounts]
  subst s
  exact hpat

/-- A genuine root-pair swap normalizes the orientation without changing the original shape. -/
theorem leechNormSixPair_odd_three_normalize (u : LeechNormSixPair)
    (hs : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts 3) :
    ∃ a : leechRootedA2PositiveRootSubgroup,
      leechNormEightMultiplicity (a • u).val.val = leechNormSixShapeCounts 3 ∧
        (a • u).val.val 0 = 3 ∧ (a • u).val.val 1 = 1 := by
  rcases leechNormSixPair_odd_three_root_pattern u hs with ⟨hu0, hu1⟩ | ⟨hu0, hu1⟩
  · exact ⟨1, by simpa only [one_smul] using hs,
      by simpa only [one_smul] using hu0, by simpa only [one_smul] using hu1⟩
  · obtain ⟨p, hp0, hp1⟩ := leechNormSixPair_root_swap_exists
    have hr := leechRootedA2Root_permutation_swap p hp0 hp1
    let a : leechRootedA2PositiveRootSubgroup :=
      ⟨⟨golayPermutationIsometry p,
        (leechRootedA2RootLineSubgroup_mem _).mpr (Or.inl hr)⟩, hr⟩
    have ha (i : Fin 24) : (a • u).val.val i = u.val.val (p.val.symm i) := by
      rw [leechNormSixPair_smul_val, leechIntegralAction_golayPermutation]
      rfl
    refine ⟨a, ?_, ?_, ?_⟩
    · rw [leechNormSixPair_smul_val]
      exact (leechNormSixPair_permutation_multiplicity p u.val).trans hs
    · have h0 : p.val.symm 0 = 1 := p.val.symm_apply_eq.mpr hp1.symm
      rw [ha, h0, hu1]
    · have h1 : p.val.symm 1 = 0 := p.val.symm_apply_eq.mpr hp0.symm
      rw [ha, h1, hu0]

/-- All actual odd three-coordinate paired vectors lie in one genuine positive-root
stabilizer orbit, including both root orientations and every original sign pattern. -/
theorem leechNormSixPair_odd_three_transitive (u v : LeechNormSixPair)
    (hu : leechNormEightMultiplicity u.val.val = leechNormSixShapeCounts 3)
    (hv : leechNormEightMultiplicity v.val.val = leechNormSixShapeCounts 3) :
    ∃ e : leechRootedA2PositiveRootSubgroup, e • u = v := by
  obtain ⟨a, ha, ha0, ha1⟩ := leechNormSixPair_odd_three_normalize u hu
  obtain ⟨b, hb, hb0, hb1⟩ := leechNormSixPair_odd_three_normalize v hv
  obtain ⟨c, hc⟩ := leechNormSixPair_odd_three_positive_transitive
    (a • u) (b • v) ha hb ha0 ha1 hb0 hb1
  refine ⟨b⁻¹ * c * a, ?_⟩
  rw [mul_smul, mul_smul, hc, inv_smul_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
