/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionPairLift

/-! Actual pair-family preservation inside the local Ω centralizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

/-- Fixing the actual binary Ω class forces the actual isometry to be monomial. -/
theorem generatedAxis_omega_fixed_monomial (e : leechIsomSubgroup)
    (he : leechBinaryAction e (toAdd (qQuotHom sourceOmegaQ)) =
      toAdd (qQuotHom sourceOmegaQ)) : e ∈ golayMonomialSubgroup := by
  rw [← leechFrameClass_stabilizer_eq_monomial]
  change leechModTwoAction e (leechReduction (leechCoordinateFrameLattice 0)) =
    leechReduction (leechCoordinateFrameLattice 0)
  apply leechHyperbolicCoordinates.injective
  rw [sourceOmegaQ_eq_frame_class, leechBinaryAction_coordinates] at he
  exact he

/-- An actual monomial isometry sends a pair-short label to another pair-short label. -/
theorem generatedAxis_monomial_preserves_pair (e : leechIsomSubgroup)
    (he : e ∈ golayMonomialSubgroup) (s : Fin 2) (p : Fin 276) :
    ∃ t : Fin 2, ∃ q : Fin 276,
      griessShortPermutation e (Sum.inl (s, p)) = Sum.inl (t, q) := by
  let u := leechIntegralAction e (griessShortLatticeVector (Sum.inl (s, p)))
  have hs : leechSquareSum u.val = 32 := by
    rw [leechIntegralAction_squareSum]
    simpa only [griessShortLatticeVector] using griessShortIntegral_squareSum (Sum.inl (s, p))
  have hdiv (i : Fin 24) : 4 ∣ griessShortIntegral (Sum.inl (s, p)) i := by
    simp only [griessShortIntegral]
    split_ifs <;> norm_num
  have hf : ∀ i, 4 ∣ u.val i := by
    obtain ⟨d, a, rfl⟩ := he
    intro i
    change 4 ∣ (leechIntegralAction (golaySignIsometry d * golayPermutationIsometry a)
      (griessShortLatticeVector (Sum.inl (s, p)))).val i
    rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
      leechIntegralAction_golayPermutation]
    simp only [golayIntegerSign, golayIntegerPermute, griessShortLatticeVector]
    split_ifs
    · exact hdiv _
    · exact dvd_neg.mpr (hdiv _)
  obtain ⟨t, q, hi⟩ := four_short_pair u.val hs hf
  have hv : e.val (griessShortVector (Sum.inl (s, p))) =
      griessShortVector (Sum.inl (t, q)) ∨
      e.val (griessShortVector (Sum.inl (s, p))) =
        -griessShortVector (Sum.inl (t, q)) := by
    rcases hi with hi | hi
    · left
      have h := congrArg leechCoordinateEmbedding hi
      rw [leechIntegralAction_embedding] at h
      exact h
    · right
      have h := congrArg leechCoordinateEmbedding hi
      rw [leechIntegralAction_embedding, map_neg] at h
      exact h
  refine ⟨t, q, ?_⟩
  apply centralizer_shortVector_sign_unique
  rcases griessShortPermutation_vector e (Sum.inl (s, p)) with hp | hp
  · rcases hv with hv | hv
    · exact Or.inl (hp.symm.trans hv)
    · exact Or.inr (hp.symm.trans hv)
  · rcases hv with hv | hv
    · exact Or.inr (by
        have h := congrArg Neg.neg (hp.symm.trans hv)
        simpa only [neg_neg] using h)
    · exact Or.inl (by
        have h := congrArg Neg.neg (hp.symm.trans hv)
        simpa only [neg_neg] using h)

/-- The actual local Ω centralizer preserves the signed pair-axis family. -/
theorem generatedAxis_localOmega_pair_image (h : localOmegaStabilizer)
    (s : Fin 2) (p : Fin 276) (c : ZMod 2) :
    ∃ t : Fin 2, ∃ q : Fin 276, ∃ d : ZMod 2,
      rhoLocal h.val (conwayShortAxis (Sum.inl (s, p)) c) =
        conwayShortAxis (Sum.inl (t, q)) d := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h.val
  change localFiberIntoH f = h.val at hf
  have hc := localOmegaStabilizer_projection_mem h
  rw [← hf] at hc
  change leechBinaryAction f.val.2 (toAdd (qQuotHom sourceOmegaQ)) =
    toAdd (qQuotHom sourceOmegaQ) at hc
  obtain ⟨t, q, hp⟩ := generatedAxis_monomial_preserves_pair f.val.2
    (generatedAxis_omega_fixed_monomial f.val.2 hc) s p
  refine ⟨t, q, localShortPhase f (Sum.inl (s, p)) + c, ?_⟩
  rw [← hf]
  change localGriessRepresentation f _ = _
  rw [generatedAxis_localFiber_image, hp]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
