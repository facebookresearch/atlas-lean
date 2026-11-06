/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthDestinationEqualities
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTrialityPhaseMerge
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveRootPairs
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue

/-! Two Odd-class Fourth transition vectors, by reversing the proved Odd-to-Fourth transports.

The root words at Fourth roots fifteen and twelve are the inverted letter parts of the original
Odd-Fourth comparison words zero and two. The comparison words carry an extra extraspecial
correction `q`; conjugated by the root word it lies in the actual Ω stabilizer exactly when its
commutator pairing with the binary root is even. The pairing is even at root fifteen and odd at
root twelve, so the inverse image at root fifteen and the forward image at root twelve have the
class of the listed Odd representative. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An even actual root pairing puts the conjugated extraspecial element in the Ω stabilizer. -/
theorem generatedAxisGlobalTwelveFourth_root_even_normalizer (r : H) (q : Q)
    (hphase : qBeta (toAdd q.base) (generatedAxisGlobalBinaryRoot r).val +
      qBeta (generatedAxisGlobalBinaryRoot r).val (toAdd q.base) = 0) :
    r * inclQ q * r⁻¹ ∈ localOmegaStabilizer := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup r
  change localFiberIntoH f = r at hf
  have hb := qBinaryAction_apply (spinConjugation (f⁻¹).val.1) sourceOmegaQ
  change spinBinaryAction (f⁻¹).val.1 (toAdd (qQuotHom sourceOmegaQ)) =
    toAdd (spinConjugation (f⁻¹).val.1 sourceOmegaQ).base at hb
  rw [(f⁻¹).property] at hb
  have hb' : (generatedAxisGlobalBinaryRoot r).val =
      toAdd (spinConjugation (f⁻¹).val.1 sourceOmegaQ).base := by
    rw [← hf]
    exact hb
  have hqp : q * spinConjugation (f⁻¹).val.1 sourceOmegaQ * q⁻¹ =
      spinConjugation (f⁻¹).val.1 sourceOmegaQ := by
    rw [q_conjugation_central_phase]
    rw [hb'] at hphase
    rw [hphase]
    exact one_mul _
  change q * spinConjugation f.val.1⁻¹ sourceOmegaQ * q⁻¹ =
    spinConjugation f.val.1⁻¹ sourceOmegaQ at hqp
  rw [← hf]
  change localFiberIntoH (f * localFiberIncl q * f⁻¹) ∈ localOmegaStabilizer
  apply (localOmegaStabilizer_fiber_iff _).mpr
  change spinConjugation (f.val.1 * spinHolomorphIncl q * f.val.1⁻¹) sourceOmegaQ = sourceOmegaQ
  rw [map_mul, map_mul]
  change spinConjugation f.val.1
    (spinConjugation (spinHolomorphIncl q)
      (spinConjugation f.val.1⁻¹ sourceOmegaQ)) = _
  rw [spinConjugation_incl, hqp]
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The inverse code of each of the ten original signed source letters. -/
def generatedAxisGlobalTwelveFourthLetterInverse : Fin 10 → Fin 10 :=
  ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8]

/-- Inverses of the ten original signed source letters. -/
theorem generatedAxisGlobalTwelveFourth_letter_inv (l : Fin 10) :
    (generatedAxisGlobalOddSourceLocalLetter l)⁻¹ =
      generatedAxisGlobalOddSourceLocalLetter (generatedAxisGlobalTwelveFourthLetterInverse l) := by
  fin_cases l <;> simp [generatedAxisGlobalOddSourceLocalLetter,
    generatedAxisGlobalTwelveFourthLetterInverse]

/-- The letter product of an original comparison word. -/
def generatedAxisGlobalTwelveFourthComparisonProduct (k : Fin 4) : H :=
  ((generatedAxisGlobalOddFourthComparisonLetters k).map
    generatedAxisGlobalOddSourceLocalLetter).prod

/-- Each comparison word is its extraspecial correction times its letter product. -/
theorem generatedAxisGlobalTwelveFourth_comparison_split (k : Fin 4) :
    generatedAxisGlobalOddFourthComparisonLocal k =
      inclQ (generatedAxisGlobalOddFourthComparisonQ k) *
        generatedAxisGlobalTwelveFourthComparisonProduct k := by
  change localFiberIntoH (localFiberIncl _ * _) = _
  rw [map_mul]
  refine congrArg (fun x => inclQ (generatedAxisGlobalOddFourthComparisonQ k) * x) ?_
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro l _
  exact generatedAxisGlobalOddSourceFiberLetter_local l

/-- Root fifteen is the inverse of the letter product of comparison word zero. -/
theorem generatedAxisGlobalTwelveFourth_root15_word :
    generatedAxisGlobalTwelveFourthRootLocal 15 =
      (generatedAxisGlobalTwelveFourthComparisonProduct 0)⁻¹ := by
  simp only [generatedAxisGlobalTwelveFourthRootLocal, generatedAxisGlobalTwelveFourthRootWords,
    generatedAxisGlobalTwelveFourthComparisonProduct, generatedAxisGlobalOddFourthComparisonLetters,
    Matrix.cons_val, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_inv_rev, generatedAxisGlobalTwelveFourth_letter_inv,
    generatedAxisGlobalTwelveFourthLetterInverse, mul_assoc]

/-- Root twelve is the inverse of the letter product of comparison word two. -/
theorem generatedAxisGlobalTwelveFourth_root12_word :
    generatedAxisGlobalTwelveFourthRootLocal 12 =
      (generatedAxisGlobalTwelveFourthComparisonProduct 2)⁻¹ := by
  simp only [generatedAxisGlobalTwelveFourthRootLocal, generatedAxisGlobalTwelveFourthRootWords,
    generatedAxisGlobalTwelveFourthComparisonProduct, generatedAxisGlobalOddFourthComparisonLetters,
    Matrix.cons_val, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_inv_rev, generatedAxisGlobalTwelveFourth_letter_inv,
    generatedAxisGlobalTwelveFourthLetterInverse, mul_assoc]

/-- The root word is the conjugated correction times the inverse comparison word. -/
private theorem root_split (r P : H) (q : Q) (hr : r = P⁻¹) :
    r = (r * inclQ q * r⁻¹) * (inclQ q * P)⁻¹ := by
  rw [hr]
  group

set_option maxHeartbeats 1000000 in
-- Two complete 24-coordinate commutator pairings.
/-- The comparison corrections pair evenly with root fifteen and oddly with root twelve. -/
theorem generatedAxisGlobalTwelveFourth_comparison_pairings :
    (qBeta (toAdd (generatedAxisGlobalOddFourthComparisonQ 0).base)
        (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveFourthRootMask 15)) +
      qBeta (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveFourthRootMask 15))
        (toAdd (generatedAxisGlobalOddFourthComparisonQ 0).base) = 0) ∧
    (qBeta (toAdd (generatedAxisGlobalOddFourthComparisonQ 2).base)
        (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveFourthRootMask 12)) +
      qBeta (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalTwelveFourthRootMask 12))
        (toAdd (generatedAxisGlobalOddFourthComparisonQ 2).base) = 1) := by
  decide +kernel

/-- The inverse triality image at root fifteen has the class of the listed Odd representative. -/
theorem generatedAxisGlobalTwelveFourth_root15_negative :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  set r := generatedAxisGlobalTwelveFourthRootLocal 15
  set q := generatedAxisGlobalOddFourthComparisonQ 0
  have ht : sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis) =
      rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 0)⁻¹ generatedFourthAxis :=
    generatedAxisGlobalOddFourth_transporter 0
  have hn : r * inclQ q * r⁻¹ ∈ localOmegaStabilizer := by
    apply generatedAxisGlobalTwelveFourth_root_even_normalizer
    change qBeta _ (generatedAxisGlobalTwelveFourthRoot 15).val +
      qBeta (generatedAxisGlobalTwelveFourthRoot 15).val _ = 0
    rw [generatedAxisGlobalTwelveFourthRoot_val]
    exact generatedAxisGlobalTwelveFourth_comparison_pairings.1
  have hs := root_split r (generatedAxisGlobalTwelveFourthComparisonProduct 0) q
    generatedAxisGlobalTwelveFourth_root15_word
  rw [← generatedAxisGlobalTwelveFourth_comparison_split 0] at hs
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelve_omega_inverse_orbit ⟨_, hn⟩
    (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 0)⁻¹ generatedFourthAxis)
  have hz : sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 0)⁻¹
      generatedFourthAxis) =
      rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis := by
    rw [← ht, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have he : sExtra⁻¹ (rhoLocal r generatedFourthAxis) =
      rhoLocal k (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis) := by
    rw [hs, map_mul, LinearEquiv.mul_apply, ← hk, hz]
  rw [he]
  exact generatedLocalOrbitUnion_local _ k
    (generatedAxisGlobalTwelve_mem_of_transport 2 _ rfl)

/-- The forward triality image at root twelve has the class of the listed Odd representative. -/
theorem generatedAxisGlobalTwelveFourth_root12_positive :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  set r := generatedAxisGlobalTwelveFourthRootLocal 12
  set q := generatedAxisGlobalOddFourthComparisonQ 2
  have ht : sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis) =
      rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹ generatedFourthAxis :=
    generatedAxisGlobalOddFourth_transporter 2
  have hn : (r * inclQ q * r⁻¹) * inclQ singletonCocodeQ ∈ localOmegaStabilizer := by
    apply generatedAxisGlobal_root_phase_normalizer
    change qBeta _ (generatedAxisGlobalTwelveFourthRoot 12).val +
      qBeta (generatedAxisGlobalTwelveFourthRoot 12).val _ = 1
    rw [generatedAxisGlobalTwelveFourthRoot_val]
    exact generatedAxisGlobalTwelveFourth_comparison_pairings.2
  have hs := root_split r (generatedAxisGlobalTwelveFourthComparisonProduct 2) q
    generatedAxisGlobalTwelveFourth_root12_word
  rw [← generatedAxisGlobalTwelveFourth_comparison_split 2] at hs
  have hsq : inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
    rw [← map_mul]
    change inclQ (cocodeQ _ * cocodeQ _) = 1
    rw [cocodeQ_square, map_one]
  have hs' : r = ((r * inclQ q * r⁻¹) * inclQ singletonCocodeQ) *
      (inclQ singletonCocodeQ * (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹) := by
    calc r = (r * inclQ q * r⁻¹) * (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹ := hs
      _ = (r * inclQ q * r⁻¹) * (inclQ singletonCocodeQ * inclQ singletonCocodeQ) *
          (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹ := by rw [hsq, mul_one]
      _ = _ := by group
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨_, hn⟩
    (rhoLocal (inclQ singletonCocodeQ * (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹)
      generatedFourthAxis)
  have hz : sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹
      generatedFourthAxis) =
      rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis := by
    rw [← ht, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have he : sExtra (rhoLocal r generatedFourthAxis) =
      rhoLocal k (rhoLocal (inclQ singletonCocodeQ)
        (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis)) := by
    rw [hs', map_mul, LinearEquiv.mul_apply, ← hk, map_mul, LinearEquiv.mul_apply,
      generatedAxisGlobal_singleton_triality_exchange, hz]
  rw [he]
  exact generatedLocalOrbitUnion_local _ k (generatedLocalOrbitUnion_local _ _
    (generatedAxisGlobalTwelve_mem_of_transport 2 _ rfl))


/-- The inverse triality image at root fifteen lies in the Odd local orbit. -/
theorem generatedAxisGlobalTwelveFourth_root15_negative_odd :
    sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 15) generatedFourthAxis) ∈
      MulAction.orbit H generatedOddAxis := by
  set r := generatedAxisGlobalTwelveFourthRootLocal 15
  set q := generatedAxisGlobalOddFourthComparisonQ 0
  have ht : sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis) =
      rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 0)⁻¹ generatedFourthAxis :=
    generatedAxisGlobalOddFourth_transporter 0
  have hn : r * inclQ q * r⁻¹ ∈ localOmegaStabilizer := by
    apply generatedAxisGlobalTwelveFourth_root_even_normalizer
    change qBeta _ (generatedAxisGlobalTwelveFourthRoot 15).val +
      qBeta (generatedAxisGlobalTwelveFourthRoot 15).val _ = 0
    rw [generatedAxisGlobalTwelveFourthRoot_val]
    exact generatedAxisGlobalTwelveFourth_comparison_pairings.1
  have hs := root_split r (generatedAxisGlobalTwelveFourthComparisonProduct 0) q
    generatedAxisGlobalTwelveFourth_root15_word
  rw [← generatedAxisGlobalTwelveFourth_comparison_split 0] at hs
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelve_omega_inverse_orbit ⟨_, hn⟩
    (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 0)⁻¹ generatedFourthAxis)
  have hz : sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 0)⁻¹
      generatedFourthAxis) =
      rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis := by
    rw [← ht, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have he : sExtra⁻¹ (rhoLocal r generatedFourthAxis) =
      rhoLocal k (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 2) generatedOddAxis) := by
    rw [hs, map_mul, LinearEquiv.mul_apply, ← hk, hz]
  rw [he]
  exact ⟨k * generatedAxisGlobalOddSourceRootLocalWord 2, mul_smul _ _ _⟩

/-- The forward triality image at root twelve lies in the Odd local orbit. -/
theorem generatedAxisGlobalTwelveFourth_root12_positive_odd :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 12) generatedFourthAxis) ∈
      MulAction.orbit H generatedOddAxis := by
  set r := generatedAxisGlobalTwelveFourthRootLocal 12
  set q := generatedAxisGlobalOddFourthComparisonQ 2
  have ht : sExtra (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis) =
      rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹ generatedFourthAxis :=
    generatedAxisGlobalOddFourth_transporter 2
  have hn : (r * inclQ q * r⁻¹) * inclQ singletonCocodeQ ∈ localOmegaStabilizer := by
    apply generatedAxisGlobal_root_phase_normalizer
    change qBeta _ (generatedAxisGlobalTwelveFourthRoot 12).val +
      qBeta (generatedAxisGlobalTwelveFourthRoot 12).val _ = 1
    rw [generatedAxisGlobalTwelveFourthRoot_val]
    exact generatedAxisGlobalTwelveFourth_comparison_pairings.2
  have hs := root_split r (generatedAxisGlobalTwelveFourthComparisonProduct 2) q
    generatedAxisGlobalTwelveFourth_root12_word
  rw [← generatedAxisGlobalTwelveFourth_comparison_split 2] at hs
  have hsq : inclQ singletonCocodeQ * inclQ singletonCocodeQ = (1 : H) := by
    rw [← map_mul]
    change inclQ (cocodeQ _ * cocodeQ _) = 1
    rw [cocodeQ_square, map_one]
  have hs' : r = ((r * inclQ q * r⁻¹) * inclQ singletonCocodeQ) *
      (inclQ singletonCocodeQ * (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹) := by
    calc r = (r * inclQ q * r⁻¹) * (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹ := hs
      _ = (r * inclQ q * r⁻¹) * (inclQ singletonCocodeQ * inclQ singletonCocodeQ) *
          (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹ := by rw [hsq, mul_one]
      _ = _ := by group
  obtain ⟨k, hk⟩ := localOmegaStabilizer_triality_orbit ⟨_, hn⟩
    (rhoLocal (inclQ singletonCocodeQ * (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹)
      generatedFourthAxis)
  have hz : sExtra⁻¹ (rhoLocal (generatedAxisGlobalOddFourthComparisonLocal 2)⁻¹
      generatedFourthAxis) =
      rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis := by
    rw [← ht, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  have he : sExtra (rhoLocal r generatedFourthAxis) =
      rhoLocal k (rhoLocal (inclQ singletonCocodeQ)
        (rhoLocal (generatedAxisGlobalOddSourceRootLocalWord 4) generatedOddAxis)) := by
    rw [hs', map_mul, LinearEquiv.mul_apply, ← hk, map_mul, LinearEquiv.mul_apply,
      generatedAxisGlobal_singleton_triality_exchange, hz]
  rw [he]
  refine ⟨k * (inclQ singletonCocodeQ * generatedAxisGlobalOddSourceRootLocalWord 4), ?_⟩
  change (k * (inclQ singletonCocodeQ * generatedAxisGlobalOddSourceRootLocalWord 4)) •
    generatedOddAxis = _
  rw [mul_smul, mul_smul]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
