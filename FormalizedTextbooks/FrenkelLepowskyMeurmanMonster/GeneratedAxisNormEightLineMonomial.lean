/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineStabilizer

/-! The full actual norm-eight line stabilizer preserves the signed coordinate frame. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

theorem generatedNormEight_negative_mem_monomial :
    leechNegativeIdentity ∈ golayMonomialSubgroup := by
  apply leechFrame_mem_monomial
  intro i
  exact ⟨i, 1, by simp [leechNegativeIdentity_apply, qSign_one]⟩

theorem generatedNormEight_negative_integral (u : leechIntegral) :
    leechIntegralAction leechNegativeIdentity u = -u := by
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  rw [leechIntegralAction_embedding, leechNegativeIdentity_apply]
  exact (leechCoordinateEmbedding.map_neg u.val).symm

/-- Preserving the genuine unoriented coordinate line forces an actual signed Golay permutation. -/
theorem generatedNormEightLineStabilizer_le_monomial :
    generatedNormEightLineStabilizer ≤ golayMonomialSubgroup := by
  intro g hg
  have hm := (generatedNormEightLineStabilizer_mem g).mp hg
  rw [← generatedNormEightLineMatrix_action] at hm
  rcases (generatedNormEightLineMatrix_eq_iff leechNormEightAxis (g • leechNormEightAxis)).mp
      hm.symm with hp | hn
  · apply leech_fix_frame_mem_monomial
    exact congrArg Subtype.val hp
  · have he : leechIntegralAction g (leechCoordinateFrameLattice 0) =
        -leechCoordinateFrameLattice 0 := congrArg Subtype.val hn
    have hc : leechNegativeIdentity * g ∈ golayMonomialSubgroup := by
      apply leech_fix_frame_mem_monomial
      rw [map_mul]
      change leechIntegralAction leechNegativeIdentity
        (leechIntegralAction g (leechCoordinateFrameLattice 0)) = leechCoordinateFrameLattice 0
      rw [he, generatedNormEight_negative_integral, neg_neg]
    have h := golayMonomialSubgroup.mul_mem
      (golayMonomialSubgroup.inv_mem generatedNormEight_negative_mem_monomial) hc
    simpa only [inv_mul_cancel_left] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
