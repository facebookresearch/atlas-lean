/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveCatalogue
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTrialityPhaseMerge
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhaseExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthRoot11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitActions

/-! The positive root-eleven Fifth transition has the actual Fifth class.

Root eleven is the identity coset. The Fifth axis is the triality image of the literal
octad-family word `generatedFifthLocalFiber` applied to the octad-image axis of
`generatedFourthOctad`. The extraspecial lift of the lattice vector `4e₀ + 4e₁₆`, whose support
is disjoint from that octad, fixes the whole octad-image axis and pairs oddly with the actual
binary root of the literal word. Hence both triality signs of that octad-family transition have
one local class, and the forward triality image of the Fifth axis is a local image of the Fifth
axis itself. The commutator pairing is computed from the genuine lattice inner product, by
polarizing the proved half-norm identity of the hyperbolic coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The octad-image axis of the Fourth octad, the source of the literal Fifth word. -/
def generatedAxisGlobalTwelveFifthBindOctadAxis : GriessSpace :=
  sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)

/-- Every actual integral Leech vector has square sum divisible by sixteen. -/
theorem generatedAxisGlobalTwelveFifthBind_squareSum_dvd (u : leechIntegral) :
    (16 : ℤ) ∣ leechSquareSum u.val := by
  rw [← leechExplicitCoordinates_vector u, leechBasis_squareSum]
  exact dvd_mul_right _ _

/-- The binary commutator pairing of two lattice classes is half their inner product, mod 2. -/
theorem generatedAxisGlobalTwelveFifthBind_polar (u w : leechIntegral) :
    qBeta (leechHyperbolicCoordinates (leechReduction u))
        (leechHyperbolicCoordinates (leechReduction w)) +
      qBeta (leechHyperbolicCoordinates (leechReduction w))
        (leechHyperbolicCoordinates (leechReduction u)) =
      (((∑ i, u.val i * w.val i) / 8 : ℤ) : ZMod 2) := by
  set a := leechHyperbolicCoordinates (leechReduction u)
  set b := leechHyperbolicCoordinates (leechReduction w)
  have hab : leechHyperbolicCoordinates (leechReduction (u + w)) = a + b := by
    rw [map_add, map_add]
  have hu := leechHyperbolicCoordinates_halfNorm u
  have hw := leechHyperbolicCoordinates_halfNorm w
  have huw := leechHyperbolicCoordinates_halfNorm (u + w)
  rw [hab] at huw
  have hq : squareQuad (a + b) = squareQuad a + squareQuad b + (qBeta a b + qBeta b a) := by
    change qBeta (a + b) (a + b) = qBeta a a + qBeta b b + (qBeta a b + qBeta b a)
    rw [qBeta_add_left, qBeta_add_right, qBeta_add_right]
    ring
  obtain ⟨x, hx⟩ := generatedAxisGlobalTwelveFifthBind_squareSum_dvd u
  obtain ⟨y, hy⟩ := generatedAxisGlobalTwelveFifthBind_squareSum_dvd w
  obtain ⟨t, ht⟩ := generatedAxisGlobalTwelveFifthBind_squareSum_dvd (u + w)
  have hexp : leechSquareSum (u + w).val =
      leechSquareSum u.val + leechSquareSum w.val + 2 * ∑ i, u.val i * w.val i := by
    simp only [leechSquareSum, Submodule.coe_add, Pi.add_apply, add_sq, Finset.sum_add_distrib,
      Finset.mul_sum]
    ring_nf
  have hdot : ∑ i, u.val i * w.val i = 8 * (t - x - y) := by
    rw [hx, hy, ht] at hexp
    linarith
  rw [hx] at hu
  rw [hy] at hw
  rw [ht] at huw
  rw [Int.mul_ediv_cancel_left _ (by decide)] at hu hw huw
  rw [hdot, Int.mul_ediv_cancel_left _ (by decide)]
  have hz : ((t - x - y : ℤ) : ZMod 2) = (t : ZMod 2) - x - y := by push_cast; ring
  rw [hz, huw, hu, hw, hq]
  ring

/-- The lattice vector `4e₀ + 4e₁₆`, the sixteenth actual integral basis column. -/
def generatedAxisGlobalTwelveFifthBindPairVector : leechIntegral :=
  leechExplicitCoordinateMap (Pi.single 16 1)

/-- Its physical coordinates. -/
theorem generatedAxisGlobalTwelveFifthBindPairVector_val (i : Fin 24) :
    generatedAxisGlobalTwelveFifthBindPairVector.val i = if i = 0 ∨ i = 16 then 4 else 0 := by
  change (leechBasisMatrix *ᵥ Pi.single 16 1) i = _
  revert i
  decide +kernel

/-- Its actual integral-basis coordinates. -/
theorem generatedAxisGlobalTwelveFifthBindPairVector_coordinates :
    leechExplicitCoordinates generatedAxisGlobalTwelveFifthBindPairVector = Pi.single 16 1 :=
  (LinearEquiv.ofBijective leechExplicitCoordinateMap
    leechExplicitCoordinateMap_bijective).symm_apply_apply _

/-- The extraspecial lift of the lattice class of `4e₀ + 4e₁₆`. -/
def generatedAxisGlobalTwelveFifthBindQ : Q :=
  ⟨ofAdd (leechHyperbolicCoordinates (leechReduction generatedAxisGlobalTwelveFifthBindPairVector)),
    1⟩

/-- Its exact hyperbolic binary coordinates. -/
theorem generatedAxisGlobalTwelveFifthBindQ_base :
    toAdd generatedAxisGlobalTwelveFifthBindQ.base = monsterCo1GeometryBinaryMaskDecode 4241408 := by
  change leechHyperbolicCoordinates (leechReduction generatedAxisGlobalTwelveFifthBindPairVector) = _
  rw [leechHyperbolicCoordinates_explicit, generatedAxisGlobalTwelveFifthBindPairVector_coordinates]
  funext i
  revert i
  decide +kernel

/-- Every short vector supported on the Fourth octad vanishes at coordinates 0 and 16. -/
theorem generatedAxisGlobalTwelveFifthBind_support_zero (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedFourthOctad r) (i : Fin 24)
    (hi : i = 0 ∨ i = 16) : griessShortIntegral r i = 0 := by
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

/-- The lift has zero phase at all 120 short coordinates supported on the Fourth octad. -/
theorem generatedAxisGlobalTwelveFifthBindQ_phase (r : GriessShortIndex)
    (hr : generatedOctadShortSupport generatedFourthOctad r) :
    localAxisQPhase r generatedAxisGlobalTwelveFifthBindQ = 1 := by
  have hs : ∑ i, generatedAxisGlobalTwelveFifthBindPairVector.val i *
      (griessShortLatticeVector r).val i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [generatedAxisGlobalTwelveFifthBindPairVector_val]
    by_cases hi : i = 0 ∨ i = 16
    · change (if i = 0 ∨ i = 16 then (4 : ℤ) else 0) * griessShortIntegral r i = 0
      rw [generatedAxisGlobalTwelveFifthBind_support_zero r hr i hi, mul_zero]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hi), zero_mul]
  apply toAdd.injective
  change qBeta (leechHyperbolicCoordinates
        (leechReduction generatedAxisGlobalTwelveFifthBindPairVector))
      (leechHyperbolicCoordinates (leechReduction (griessShortLatticeVector r))) +
    qBeta (leechHyperbolicCoordinates (leechReduction (griessShortLatticeVector r)))
      (leechHyperbolicCoordinates
        (leechReduction generatedAxisGlobalTwelveFifthBindPairVector)) = 0
  rw [generatedAxisGlobalTwelveFifthBind_polar, hs]
  rfl

/-- The lift fixes the whole octad-image axis: matrix, short and tensor coordinates. -/
theorem generatedAxisGlobalTwelveFifthBindQ_fixed :
    rhoLocal (inclQ generatedAxisGlobalTwelveFifthBindQ)
      generatedAxisGlobalTwelveFifthBindOctadAxis = generatedAxisGlobalTwelveFifthBindOctadAxis := by
  unfold generatedAxisGlobalTwelveFifthBindOctadAxis
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  change griessConwayEncode
    (localGriessRepresentation (localFiberIncl generatedAxisGlobalTwelveFifthBindQ) _) = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  apply Prod.ext
  · change conwayMatrixAction 1 _ = _
    rw [map_one]
    rfl
  · apply Prod.ext
    · ext r
      have hd := localShortOperator_image (localFiberIncl generatedAxisGlobalTwelveFifthBindQ)
        (griessConwayEncode (sExtra
          (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1 r
      change localShortOperator (localFiberIncl generatedAxisGlobalTwelveFifthBindQ) _
        (griessShortPermutation 1 r) = _ at hd
      rw [map_one, Equiv.Perm.one_apply] at hd
      change localShortOperator (localFiberIncl generatedAxisGlobalTwelveFifthBindQ) _ r = _
      rw [hd]
      by_cases hr : generatedOctadShortSupport generatedFourthOctad r
      · have hp := generatedAxisGlobalTwelveFifthBindQ_phase r hr
        have hz : localShortPhase (localFiberIncl generatedAxisGlobalTwelveFifthBindQ) r = 0 := by
          rw [localAxisQPhase_eq_short_phase, hp]
          rfl
        rw [hz, qSign_zero, one_mul]
      · have hz := not_ne_iff.mp
          (mt (generatedAxis_triality_octad_support_iff generatedFourthOctad 0 0 r).mp hr)
        rw [hz, mul_zero]
    · rw [generatedAxis_triality_octad_tensor_zero_all, map_zero]

private theorem xiBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction co1XiIsometry v = omegaOrbitBinaryMatrices 0 *ᵥ v :=
  omegaOrbitIsometry_binary 0 v

private theorem permutationZeroBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 0) v = omegaOrbitBinaryMatrices 3 *ᵥ v :=
  omegaOrbitIsometry_binary 3 v

private theorem permutationOneBinary (v : Fin 24 → ZMod 2) :
    leechBinaryAction (omegaOrbitPermutationIsometry 1) v = omegaOrbitBinaryMatrices 4 *ᵥ v :=
  omegaOrbitIsometry_binary 4 v

/-- The inverse literal Fifth word has the original four-factor spatial part. -/
theorem generatedAxisGlobalTwelveFifthBind_fiber_inv_spatial :
    (generatedFifthLocalFiber⁻¹).val.2 =
      co1XiIsometry * omegaOrbitPermutationIsometry 1 * omegaOrbitPermutationIsometry 0 *
        co1XiIsometry := by
  have h : (generatedFifthLocalFiber⁻¹).val.2 =
      (co1XiIsometry⁻¹ * (omegaOrbitPermutationIsometry 0)⁻¹ *
        (omegaOrbitPermutationIsometry 1)⁻¹ * co1XiIsometry⁻¹)⁻¹ := rfl
  rw [h]
  group

set_option maxHeartbeats 10000000 in
-- Four actual binary matrix actions, checked on all 24 coordinates.
/-- The exact binary root of the literal octad-family Fifth word. -/
theorem generatedAxisGlobalTwelveFifthBind_fiber_root :
    (generatedAxisGlobalBinaryRoot (localFiberIntoH generatedFifthLocalFiber)).val =
      monsterCo1GeometryBinaryMaskDecode 8374284 := by
  change co1BinaryAction (projH (localFiberIntoH generatedFifthLocalFiber)⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [← map_inv]
  change leechBinaryAction (generatedFifthLocalFiber⁻¹).val.2 _ = _
  rw [generatedAxisGlobalTwelveFifthBind_fiber_inv_spatial]
  simp only [map_mul, LinearEquiv.mul_apply]
  simp_rw [xiBinary, permutationZeroBinary, permutationOneBinary]
  decide +kernel

set_option maxHeartbeats 1000000 in
-- One complete 24-coordinate pairing.
/-- The lift pairs oddly with the actual binary root of the literal word. -/
theorem generatedAxisGlobalTwelveFifthBindQ_pairing :
    qBeta (toAdd generatedAxisGlobalTwelveFifthBindQ.base)
        (generatedAxisGlobalBinaryRoot (localFiberIntoH generatedFifthLocalFiber)).val +
      qBeta (generatedAxisGlobalBinaryRoot (localFiberIntoH generatedFifthLocalFiber)).val
        (toAdd generatedAxisGlobalTwelveFifthBindQ.base) = 1 := by
  rw [generatedAxisGlobalTwelveFifthBindQ_base, generatedAxisGlobalTwelveFifthBind_fiber_root]
  decide +kernel

/-- The forward triality image of the Fifth axis is a local image of the Fifth axis. -/
theorem generatedAxisGlobalTwelveFifthBind_triality_fifth :
    ∃ k : H, sExtra generatedFifthAxis = rhoLocal k generatedFifthAxis := by
  obtain ⟨k, hk⟩ := generatedAxisGlobal_triality_phase_merge
    generatedAxisGlobalTwelveFifthBindOctadAxis (localFiberIntoH generatedFifthLocalFiber)
    generatedAxisGlobalTwelveFifthBindQ generatedAxisGlobalTwelveFifthBindQ_fixed
    generatedAxisGlobalTwelveFifthBindQ_pairing
  have hv : generatedFifthAxis = sExtra (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      generatedAxisGlobalTwelveFifthBindOctadAxis) := generatedFifthAxis_local_expression
  have h3 : sExtra generatedFifthAxis = sExtra⁻¹ (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      generatedAxisGlobalTwelveFifthBindOctadAxis) := by
    rw [hv]
    apply sExtra.injective
    rw [sExtra_triple, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  refine ⟨k⁻¹, ?_⟩
  rw [h3, hv, hk, map_inv]
  simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

/-- The positive root-eleven Fifth transition lies in the twelve-family union (Fifth class). -/
theorem generatedAxisGlobalTwelveFifthBind_root11_positive :
    sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord 11) generatedFifthAxis) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  obtain ⟨k, hk⟩ := generatedAxisGlobalTwelveFifthBind_triality_fifth
  apply generatedAxisGlobalTwelve_mem_of_transport 4 k
  rw [generatedAxisGlobalFifthRoot11_localWord, map_one, LinearEquiv.coe_one, id_eq]
  exact hk

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
