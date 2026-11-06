/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismStabilizer

/-! A genuine signed image of any coordinate frame vector forces monomiality. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine Golay coordinate permutation is in the actual monomial group. -/
theorem generatedTenth_e7_permutation_mem_monomial (p : golayAutomorphismSubgroup) :
    golayPermutationIsometry p ∈ golayMonomialSubgroup := by
  apply leechFrame_mem_monomial
  intro i
  refine ⟨p.val i, 0, ?_⟩
  ext j
  simp [golayPermutationIsometry, golayRealPermute_apply, Pi.single_apply,
    qSign_zero, Equiv.symm_apply_eq]

/-- The actual original integral frame action retains the full coordinate image. -/
theorem generatedTenth_e7_permutation_frame (p : golayAutomorphismSubgroup) (i : Fin 24) :
    leechIntegralAction (golayPermutationIsometry p) (leechCoordinateFrameLattice i) =
      leechCoordinateFrameLattice (p.val i) := by
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding]
  ext j
  change (leechCoordinateFrameVector i (p.val.symm j) : ℝ) / Real.sqrt 8 =
    (leechCoordinateFrameVector (p.val i) j : ℝ) / Real.sqrt 8
  simp only [leechCoordinateFrameVector, Pi.single_apply, Equiv.symm_apply_eq]

/-- A signed image of the distinguished frame gives actual monomiality. -/
theorem generatedTenth_e7_frame_zero_monomial (g : leechIsomSubgroup)
    (h : leechIntegralAction g (leechCoordinateFrameLattice 0) =
        leechCoordinateFrameLattice 0 ∨
      leechIntegralAction g (leechCoordinateFrameLattice 0) =
        -leechCoordinateFrameLattice 0) : g ∈ golayMonomialSubgroup := by
  rcases h with hp | hn
  · exact leech_fix_frame_mem_monomial g hp
  · have hc : leechNegativeIdentity * g ∈ golayMonomialSubgroup := by
      apply leech_fix_frame_mem_monomial
      rw [map_mul]
      change leechIntegralAction leechNegativeIdentity
        (leechIntegralAction g (leechCoordinateFrameLattice 0)) = _
      rw [hn, generatedNormEight_negative_integral, neg_neg]
    have h := golayMonomialSubgroup.mul_mem
      (golayMonomialSubgroup.inv_mem generatedNormEight_negative_mem_monomial) hc
    simpa only [inv_mul_cancel_left] using h

/-- Every coordinate frame is the actual image of the distinguished frame
under a genuine Golay permutation. -/
theorem generatedTenth_e7_frame_from_zero (i : Fin 24) :
    ∃ p : golayAutomorphismSubgroup,
      leechIntegralAction (golayPermutationIsometry p) (leechCoordinateFrameLattice 0) =
        leechCoordinateFrameLattice i := by
  obtain ⟨p, hp⟩ := golayPointStabilizer_reaches (0 : Fin 7) i
    (by simp [golayStabilizerOrbitEligible])
  refine ⟨p.val, ?_⟩
  rw [generatedTenth_e7_permutation_frame]
  exact congrArg leechCoordinateFrameLattice hp

/-- Mapping any actual coordinate frame to any signed coordinate frame
forces membership in the whole actual Golay monomial subgroup. -/
theorem generatedTenth_e7_signed_frame_monomial (g : leechIsomSubgroup) (i j : Fin 24)
    (h : leechIntegralAction g (leechCoordinateFrameLattice i) =
        leechCoordinateFrameLattice j ∨
      leechIntegralAction g (leechCoordinateFrameLattice i) =
        -leechCoordinateFrameLattice j) : g ∈ golayMonomialSubgroup := by
  obtain ⟨p, hp⟩ := generatedTenth_e7_frame_from_zero i
  obtain ⟨q, hq⟩ := generatedTenth_e7_frame_from_zero j
  let a := golayPermutationIsometry p
  let b := golayPermutationIsometry q
  have hb : leechIntegralAction b⁻¹ (leechCoordinateFrameLattice j) =
      leechCoordinateFrameLattice 0 := by
    rw [← hq, map_inv]
    exact LinearEquiv.symm_apply_apply _ _
  have hc : b⁻¹ * g * a ∈ golayMonomialSubgroup := by
    apply generatedTenth_e7_frame_zero_monomial
    rw [map_mul, map_mul]
    change leechIntegralAction b⁻¹
      (leechIntegralAction g (leechIntegralAction a (leechCoordinateFrameLattice 0))) =
        leechCoordinateFrameLattice 0 ∨
      leechIntegralAction b⁻¹
        (leechIntegralAction g (leechIntegralAction a (leechCoordinateFrameLattice 0))) =
          -leechCoordinateFrameLattice 0
    rw [hp]
    rcases h with h | h
    · exact Or.inl (by rw [h, hb])
    · exact Or.inr (by rw [h, map_neg, hb])
  have hd := golayMonomialSubgroup.mul_mem
    (golayMonomialSubgroup.mul_mem (generatedTenth_e7_permutation_mem_monomial q) hc)
    (golayMonomialSubgroup.inv_mem (generatedTenth_e7_permutation_mem_monomial p))
  convert hd using 1
  dsimp [a, b]
  group

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
