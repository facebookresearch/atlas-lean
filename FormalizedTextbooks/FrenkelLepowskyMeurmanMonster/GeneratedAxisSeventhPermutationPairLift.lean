/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhPermutationCocode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisTransitionOmegaProjection

/-! Actual unsigned permutation lifts fixing Ω and both preferred pair phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual binary permutation has zero canonical correction on either pair family. -/
theorem generatedSeventh_permutation_pair_correction (p : golayAutomorphismSubgroup)
    (s : Fin 2) (k : Fin 276) :
    qCentralCorrection (leechBinaryAction (golayPermutationIsometry p))
      (leechHyperbolicCoordinates (griessShortClass (Sum.inl (s, k)))) = 0 := by
  let R := leechBinaryAction (golayPermutationIsometry p)
  have hc : qCentralCorrection R (binaryCocodeEmbedding (griessPairSyndrome k)) = 0 :=
    generatedSeventh_cocode_correction_zero R
      (generatedSeventh_permutation_cocode_space p) _ (binaryCocodeEmbedding_left _)
  have hw : qCentralCorrection R (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1) = 0 :=
    generatedSeventh_correction_single_zero R _
  have hb : qBeta (R (binaryCocodeEmbedding (griessPairSyndrome k)))
      (R (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1)) = 0 := by
    have hleft : ∀ i : Fin 12,
        R (binaryCocodeEmbedding (griessPairSyndrome k)) (Fin.castAdd 12 i) = 0 :=
      generatedSeventh_permutation_cocode_space p _ (binaryCocodeEmbedding_left _)
    simp only [qBeta, hleft, zero_mul, Finset.sum_const_zero]
  have hb' : qBeta (binaryCocodeEmbedding (griessPairSyndrome k))
      (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1) = 0 := by
    simp only [qBeta, binaryCocodeEmbedding_left, zero_mul, Finset.sum_const_zero]
  fin_cases s
  · change qCentralCorrection R
      (leechHyperbolicCoordinates (griessShortClass (Sum.inl (0, k)))) = 0
    rw [griessPairMinus_coordinates]
    exact hc
  · change qCentralCorrection R
      (leechHyperbolicCoordinates (griessShortClass (Sum.inl (1, k)))) = 0
    rw [griessPairPlus_coordinates, qCentralCorrection_add R
      (leechBinaryAction_squareQuad (golayPermutationIsometry p)), hc, hw, hb, hb']
    rfl

/-- The canonical permutation automorphism fixes the actual Ω element, including its phase. -/
theorem generatedSeventh_permutation_automorphism_omega (p : golayAutomorphismSubgroup) :
    qBinaryIsometryLift (leechBinaryAction (golayPermutationIsometry p))
      (leechBinaryAction_squareQuad (golayPermutationIsometry p)) sourceOmegaQ =
      sourceOmegaQ := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change leechBinaryAction (golayPermutationIsometry p)
      (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1) = _
    exact generatedSeventh_permutation_omega p
  · apply toAdd.injective
    change 0 + qCentralCorrection (leechBinaryAction (golayPermutationIsometry p))
      (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1) = 0
    rw [generatedSeventh_correction_single_zero, add_zero]

/-- Every actual unsigned Golay permutation has a genuine local lift fixing Ω and
with zero preferred-Q phase on both actual pair-short families. -/
theorem generatedSeventh_permutation_pair_lift (p : golayAutomorphismSubgroup) :
    ∃ f : localFiberSubgroup,
      f.val.2 = golayPermutationIsometry p ∧
      spinConjugation f.val.1 sourceOmegaQ = sourceOmegaQ ∧
      ∀ s : Fin 2, ∀ k : Fin 276, localShortPhase f (Sum.inl (s, k)) = 0 := by
  let R := leechBinaryAction (golayPermutationIsometry p)
  let a := qBinaryIsometryLift R (leechBinaryAction_squareQuad (golayPermutationIsometry p))
  obtain ⟨u, hu⟩ := exists_spinHolomorph_lift a
    (qBinaryIsometryLift_central R (leechBinaryAction_squareQuad (golayPermutationIsometry p)))
  have hf : (u, golayPermutationIsometry p) ∈ localFiberSubgroup := by
    change qBinaryAction (spinConjugation u) = R
    rw [hu]
    exact qBinaryAction_isometryLift R _
  let f : localFiberSubgroup := ⟨(u, golayPermutationIsometry p), hf⟩
  refine ⟨f, rfl, ?_, ?_⟩
  · change spinConjugation u sourceOmegaQ = sourceOmegaQ
    rw [hu]
    exact generatedSeventh_permutation_automorphism_omega p
  · intro s k
    change toAdd (spinConjugation u (griessShortQ (Sum.inl (s, k)))).coeff = 0
    rw [hu]
    change 0 + qCentralCorrection R
      (leechHyperbolicCoordinates (griessShortClass (Sum.inl (s, k)))) = 0
    rw [generatedSeventh_permutation_pair_correction, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
