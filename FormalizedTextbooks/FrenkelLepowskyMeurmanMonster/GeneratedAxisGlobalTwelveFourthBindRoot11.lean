/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFifthBindRoot11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestRoots
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLocalWord

/-! The positive root-eleven Fourth transition has the actual Fourth class.

Root eleven is the empty word. The Fourth axis is the triality image of the literal
octad-family word `generatedFourthLocalFiber` applied to the octad-image axis of
`generatedFourthOctad`. The extraspecial lift of the lattice vector `4e₀ + 4e₄`, whose support is
disjoint from that octad, fixes the whole octad-image axis and pairs oddly with the actual binary
root of the literal word. Hence both triality signs of that octad-family transition have one
local class, and the forward triality image of the Fourth axis is a local image of the Fourth axis
itself. The commutator pairing is computed from the genuine lattice inner product
(`generatedAxisGlobalTwelveFifthBind_polar`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The lattice vector `4e₀ + 4e₄`, the fourth actual integral basis column. -/
def generatedAxisGlobalTwelveFourthBindPairVector : leechIntegral :=
  leechExplicitCoordinateMap (Pi.single 4 1)

/-- Its physical coordinates. -/
theorem generatedAxisGlobalTwelveFourthBindPairVector_val (i : Fin 24) :
    generatedAxisGlobalTwelveFourthBindPairVector.val i = if i = 0 ∨ i = 4 then 4 else 0 := by
  change (leechBasisMatrix *ᵥ Pi.single 4 1) i = _
  revert i
  decide +kernel

/-- Its actual integral-basis coordinates. -/
theorem generatedAxisGlobalTwelveFourthBindPairVector_coordinates :
    leechExplicitCoordinates generatedAxisGlobalTwelveFourthBindPairVector = Pi.single 4 1 :=
  (LinearEquiv.ofBijective leechExplicitCoordinateMap
    leechExplicitCoordinateMap_bijective).symm_apply_apply _

/-- The extraspecial lift of the lattice class of `4e₀ + 4e₄`. -/
def generatedAxisGlobalTwelveFourthBindQ : Q :=
  ⟨ofAdd (leechHyperbolicCoordinates
    (leechReduction generatedAxisGlobalTwelveFourthBindPairVector)), 1⟩

/-- Its exact hyperbolic binary coordinates. -/
theorem generatedAxisGlobalTwelveFourthBindQ_base :
    toAdd generatedAxisGlobalTwelveFourthBindQ.base =
      monsterCo1GeometryBinaryMaskDecode 4257792 := by
  change leechHyperbolicCoordinates
    (leechReduction generatedAxisGlobalTwelveFourthBindPairVector) = _
  rw [leechHyperbolicCoordinates_explicit,
    generatedAxisGlobalTwelveFourthBindPairVector_coordinates]
  funext i
  revert i
  decide +kernel

/-- Every short vector supported on the Fourth octad vanishes at coordinates 0 and 4. -/
theorem generatedAxisGlobalTwelveFourthBind_support_zero (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedFourthOctad r) (i : Fin 24)
    (hi : i = 0 ∨ i = 4) : griessShortIntegral r i = 0 := by
  have hb : (0xcccc00 : ℕ).testBit i.val = false := by
    rcases hi with rfl | rfl <;> decide
  rcases r with ⟨s, p⟩ | (⟨d, e⟩ | ⟨d, j⟩)
  · change generatedOctadPairSupport generatedFourthOctad p at hr
    rw [generatedOctadPairSupport, generatedFourthOctad_mask] at hr
    have h1 : i ≠ (griessCoordinatePair p).1 := by
      intro h
      rw [← h, hb] at hr
      exact Bool.false_ne_true hr.1
    have h2 : i ≠ (griessCoordinatePair p).2 := by
      intro h
      rw [← h, hb] at hr
      exact Bool.false_ne_true hr.2
    simp only [griessShortIntegral, h1, h2, ite_false, mul_zero, add_zero]
  · change d = generatedFourthOctad at hr
    subst d
    simp only [griessShortIntegral, generatedFourthOctad_mask, hb, Bool.false_eq_true, ite_false]
  · exact False.elim hr

/-- The lift has zero phase at all short coordinates supported on the Fourth octad. -/
theorem generatedAxisGlobalTwelveFourthBindQ_phase (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedFourthOctad r) :
    localAxisQPhase r generatedAxisGlobalTwelveFourthBindQ = 1 := by
  have hs : ∑ i, generatedAxisGlobalTwelveFourthBindPairVector.val i *
      (griessShortLatticeVector r).val i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [generatedAxisGlobalTwelveFourthBindPairVector_val]
    by_cases hi : i = 0 ∨ i = 4
    · change (if i = 0 ∨ i = 4 then (4 : ℤ) else 0) * griessShortIntegral r i = 0
      rw [generatedAxisGlobalTwelveFourthBind_support_zero r hr i hi, mul_zero]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hi), zero_mul]
  apply toAdd.injective
  change qBeta (leechHyperbolicCoordinates
        (leechReduction generatedAxisGlobalTwelveFourthBindPairVector))
      (leechHyperbolicCoordinates (leechReduction (griessShortLatticeVector r))) +
    qBeta (leechHyperbolicCoordinates (leechReduction (griessShortLatticeVector r)))
      (leechHyperbolicCoordinates
        (leechReduction generatedAxisGlobalTwelveFourthBindPairVector)) = 0
  rw [generatedAxisGlobalTwelveFifthBind_polar, hs]
  rfl

/-- The lift fixes the whole octad-image axis: matrix, short and tensor coordinates. -/
theorem generatedAxisGlobalTwelveFourthBindQ_fixed :
    rhoLocal (inclQ generatedAxisGlobalTwelveFourthBindQ)
      generatedAxisGlobalTwelveFifthBindOctadAxis =
        generatedAxisGlobalTwelveFifthBindOctadAxis := by
  unfold generatedAxisGlobalTwelveFifthBindOctadAxis
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode
    (localGriessRepresentation (localFiberIncl generatedAxisGlobalTwelveFourthBindQ) _) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  apply Prod.ext
  · change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  · apply Prod.ext
    · ext r
      have hd := localShortOperator_image (localFiberIncl generatedAxisGlobalTwelveFourthBindQ)
        (griessConwayEncode (sExtra
          (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 r
      change localShortOperator (localFiberIncl generatedAxisGlobalTwelveFourthBindQ) _
        (griessShortPermutation 1 r) = _ at hd
      rw [map_one, Equiv.Perm.one_apply] at hd
      change localShortOperator (localFiberIncl generatedAxisGlobalTwelveFourthBindQ) _ r = _
      rw [hd]
      by_cases hr : generatedOctadShortSupport generatedFourthOctad r
      · have hp := generatedAxisGlobalTwelveFourthBindQ_phase r hr
        have hz : localShortPhase (localFiberIncl generatedAxisGlobalTwelveFourthBindQ) r =
            0 := by
          rw [localAxisQPhase_eq_short_phase, hp]
          rfl
        rw [hz, qSign_zero, one_mul]
      · have hz := not_ne_iff.mp
          (mt (generatedAxis_triality_octad_support_iff generatedFourthOctad 0 0 r).mp hr)
        rw [hz, mul_zero]
    · rw [generatedAxis_triality_octad_tensor_zero_all, map_zero]

private theorem fourthXiBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction co1XiIsometry v = omegaOrbitBinaryMatrices 0 *ᵥ v :=
  omegaOrbitIsometry_binary 0 v

private theorem fourthPermutationZeroBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 0) v = omegaOrbitBinaryMatrices 3 *ᵥ v :=
  omegaOrbitIsometry_binary 3 v

/-- The inverse literal Fourth word has the original three-factor spatial part. -/
theorem generatedAxisGlobalTwelveFourthBind_fiber_inv_spatial :
    (generatedFourthLocalFiber⁻¹).val.2 =
      co1XiIsometry * omegaOrbitPermutationIsometry 0 * co1XiIsometry := by
  have h : (generatedFourthLocalFiber⁻¹).val.2 =
      (co1XiIsometry⁻¹ * (omegaOrbitPermutationIsometry 0)⁻¹ * co1XiIsometry⁻¹)⁻¹ := rfl
  rw [h]
  group

set_option maxHeartbeats 10000000 in
-- Three actual binary matrix actions, checked on all 24 coordinates.
/-- The exact binary root of the literal octad-family Fourth word. -/
theorem generatedAxisGlobalTwelveFourthBind_fiber_root :
    (generatedAxisGlobalBinaryRoot (localFiberIntoH generatedFourthLocalFiber)).val =
      monsterCo1GeometryBinaryMaskDecode 5183502 := by
  change co1BinaryAction (projH (localFiberIntoH generatedFourthLocalFiber)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [← map_inv]
  change leechBinaryAction (generatedFourthLocalFiber⁻¹).val.2 _ = _
  rw [generatedAxisGlobalTwelveFourthBind_fiber_inv_spatial]
  simp only [map_mul, LinearEquiv.mul_apply]
  simp_rw [fourthXiBinary, fourthPermutationZeroBinary]
  decide +kernel

set_option maxHeartbeats 1000000 in
-- One complete 24-coordinate pairing.
/-- The lift pairs oddly with the actual binary root of the literal word. -/
theorem generatedAxisGlobalTwelveFourthBindQ_pairing :
    qBeta (toAdd generatedAxisGlobalTwelveFourthBindQ.base)
        (generatedAxisGlobalBinaryRoot (localFiberIntoH generatedFourthLocalFiber)).val +
      qBeta (generatedAxisGlobalBinaryRoot (localFiberIntoH generatedFourthLocalFiber)).val
        (toAdd generatedAxisGlobalTwelveFourthBindQ.base) = 1 := by
  rw [generatedAxisGlobalTwelveFourthBindQ_base, generatedAxisGlobalTwelveFourthBind_fiber_root]
  decide +kernel

/-- The forward triality image of the Fourth axis is a local image of the Fourth axis. -/
theorem generatedAxisGlobalTwelveFourthBind_triality_fourth :
    ∃ k : H, sExtra generatedFourthAxis = rhoLocal k generatedFourthAxis := by
  obtain ⟨k, hk⟩ := generatedAxisGlobal_triality_phase_merge
    generatedAxisGlobalTwelveFifthBindOctadAxis (localFiberIntoH generatedFourthLocalFiber)
    generatedAxisGlobalTwelveFourthBindQ generatedAxisGlobalTwelveFourthBindQ_fixed
    generatedAxisGlobalTwelveFourthBindQ_pairing
  have hv : generatedFourthAxis = sExtra (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
      generatedAxisGlobalTwelveFifthBindOctadAxis) := generatedFourthAxis_local_expression
  have h3 : sExtra generatedFourthAxis =
      sExtra⁻¹ (rhoLocal (localFiberIntoH generatedFourthLocalFiber)
        generatedAxisGlobalTwelveFifthBindOctadAxis) := by
    rw [hv]
    apply sExtra.injective
    rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  refine ⟨k⁻¹, ?_⟩
  rw [h3, hv, hk, map_inv]
  simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- The positive root-eleven Fourth transition lies in the twelve-family union (Fourth class). -/
theorem generatedAxisGlobalTwelveFourth_root11_positive :
    sExtra (rhoLocal (generatedAxisGlobalTwelveFourthRootLocal 11) generatedFourthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelveFourthBind_triality_fourth
  apply generatedAxisGlobalTwelve_mem_of_transport 3 k
  rw [generatedAxisGlobalTwelveFourthRootLocal_eleven, map_one, LinearEquiv.coe_one, id_eq]
  exact hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
