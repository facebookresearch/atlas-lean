/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenClassSourceFlags

/-! A genuine reverse feasible transition identifies the one-quarter destination class. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Original local words relate the entire odd and containing vectors by actual triality,
while fixing the original positive first axis. -/
theorem generatedFeasibleSixteenOddContaining_transition :
    ∃ k l : localAxisStabilizer generatedFeasiblePhysicalRootPair,
      sExtra (rhoLocal k.val generatedFeasibleSecondaryOddDestination) =
        rhoLocal l.val generatedFeasibleContainingOctadDestination := by
  obtain ⟨r, hrx, hrf⟩ := generatedFeasibleSixteenOdd_source_flag
  obtain ⟨q, hqx, hqf⟩ := generatedFeasibleSixteenOctad_source_flag
  obtain ⟨h, hx, hf⟩ := generatedFeasibleSixteenOddOctad_rooted_transporter
  obtain ⟨p, hp⟩ := generatedAxis_pair_localOmega_transitive 0 0
    generatedFeasibleSixteenOddMiddlePair generatedFeasiblePhysicalRootPair 0 0
  obtain ⟨p', hconj⟩ := localOmegaStabilizer_triality_conjugate p
  have hcomm (x : GriessSpace) : rhoLocal p'.val (sExtra x) =
      sExtra (rhoLocal p.val x) := by
    have hw : extraIntoGenerated * localIntoGenerated p.val =
        localIntoGenerated p'.val * extraIntoGenerated := by
      calc
        _ = (extraIntoGenerated * localIntoGenerated p.val * extraIntoGenerated⁻¹) *
            extraIntoGenerated := by group
        _ = _ := by rw [hconj]
    exact (congrArg (fun g : G => g.val x) hw).symm
  have hp' : rhoLocal p'.val
      (conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddMiddlePair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
    have he := hcomm (conwayShortAxis (Sum.inl (0, generatedFeasibleSixteenOddMiddlePair)) 0)
    rw [generatedAxis_triality_pair_exact, hp, generatedAxis_triality_pair_exact] at he
    exact he
  let w := generatedAxisGlobalOddSourceRootLocalWord 6
  have hk : rhoLocal (p.val * w * r)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hrf]
    rw [generatedFeasibleSixteenOddRootWord_first, hp]
  let k : localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    ⟨p.val * w * r, by
      change rhoLocal (p.val * w * r) (conwayAxis generatedFeasiblePhysicalRootPair) = _
      simpa only [conwayShortAxis_pair_zero] using hk⟩
  have hl : rhoLocal (p'.val * h⁻¹ * q)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hqf,
      generatedFeasibleContaining_inverse_transports _ _ _ hf, hp']
  let l : localAxisStabilizer generatedFeasiblePhysicalRootPair :=
    ⟨p'.val * h⁻¹ * q, by
      change rhoLocal (p'.val * h⁻¹ * q) (conwayAxis generatedFeasiblePhysicalRootPair) = _
      simpa only [conwayShortAxis_pair_zero] using hl⟩
  refine ⟨k, l, ?_⟩
  change sExtra (rhoLocal (p.val * w * r) _) = rhoLocal (p'.val * h⁻¹ * q) _
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hrx,
    ← hcomm, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hqx]
  exact congrArg (rhoLocal p'.val) (generatedFeasibleContaining_inverse_transports h _ _ hx).symm

/-- An actual outgoing one-quarter coefficient forces the original selected-sixteen input. -/
theorem generatedFeasibleSixteen_quarter_input
    (h : localAxisStabilizer generatedFeasiblePhysicalRootPair)
    (hq : (griessConwayEncode (sExtra
      (rhoLocal h.val generatedFeasibleContainingOctadDestination))).2.1
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 / 4) :
    generatedFeasibleContainingSelectedShortSquare
      (generatedFeasibleContainingInverseSecondaryAddresses
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 = 16 := by
  let x := rhoLocal h.val generatedFeasibleContainingOctadDestination
  have hx : x ∈ MulAction.orbit (localAxisStabilizer generatedFeasiblePhysicalRootPair)
      generatedFeasibleContainingOctadDestination := ⟨h, rfl⟩
  have hm : (griessConwayEncode x).2.1 generatedFeasibleMateLabel = 0 := by
    by_contra hn
    have hc := generatedFeasibleContaining_mate_nonzero_coordinate ⟨x, hx⟩ hn
    change x ∈ generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingOctadDestination ∪
      generatedFeasibleContainingCoordinateNOrbit generatedFeasibleContainingTrialitySquare at hc
    rcases hc with hc | hc
    · have ht := (generatedFeasibleContainingCoordinateFirst_self_return hc).2
      have hi := generatedFeasibleContaining_first_coordinate (sExtra x) ht
      change (griessConwayEncode (sExtra x)).2.1 _ = 1 / 4 at hq
      linarith
    · have ht := (generatedFeasibleContainingCoordinateSecond_secondary_return hc).2
      obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp ht
      change rhoLocal a.val (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair) =
        sExtra x at ha
      have hi := generatedFeasibleContaining_first_coordinate_invariant
        generatedFeasiblePhysicalRootPair a
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)
      have hz : (griessConwayEncode
          (generatedFeasibleSecondaryAxis generatedFeasiblePhysicalRootPair)).2.1
            (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 0 := by
        exact generatedFeasibleContainingEstablishedDestinationSource_first 1
      rw [ha, hz] at hi
      change (griessConwayEncode (sExtra x)).2.1 _ = 1 / 4 at hq
      linarith
  have hs := generatedFeasibleContainingInputFirst_word_square h hm
  rw [generatedFeasibleContainingInputFirst_apply, hq] at hs
  have hi : (generatedFeasibleContainingSelectedShortSquare
      (generatedFeasibleContainingInverseSecondaryAddresses
        (Quotient.mk (QuotientGroup.rightRel
          (localFeasibleTransitionSubgroup generatedFeasiblePhysicalRootPair)) h)).val.1 : ℝ) = 16 := by
    linarith
  exact_mod_cast hi

/-- The new one-quarter representative has exactly the existing actual odd feasible A class. -/
theorem generatedFeasibleContainingSixteen_class_eq_odd :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingSixteenDestination =
      generatedFeasibleSecondaryAClass generatedFeasibleSecondaryOddDestination := by
  obtain ⟨k, l, hkl⟩ := generatedFeasibleSixteenOddContaining_transition
  let x := rhoLocal k.val generatedFeasibleSecondaryOddDestination
  have hx : x ∈ generatedFeasibleTransitionVectors generatedFeasiblePhysicalRootPair
      generatedFeasibleSecondaryOddDestination generatedFeasibleContainingOctadDestination := by
    refine ⟨⟨k, rfl⟩, ?_⟩
    rw [hkl]
    exact ⟨l, rfl⟩
  have hy := generatedFeasibleTransition_reflection_mem generatedFeasiblePhysicalRootPair
    generatedFeasibleSecondaryOddDestination generatedFeasibleContainingOctadDestination x hx
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp hy.1
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hy.2
  change rhoLocal h.val generatedFeasibleContainingOctadDestination =
    generatedAxisTransitionReflection x at hh
  change rhoLocal a.val generatedFeasibleSecondaryOddDestination =
    sExtra (generatedAxisTransitionReflection x) at ha
  have hq : (griessConwayEncode (sExtra
      (rhoLocal h.val generatedFeasibleContainingOctadDestination))).2.1
        (Sum.inl (0, generatedFeasiblePhysicalRootPair)) = 1 / 4 := by
    rw [hh, ← ha, generatedFeasibleContaining_first_coordinate_invariant]
    exact generatedFeasibleContainingEstablishedDestinationSource_first 4
  have hc := generatedFeasibleContaining_sixteen_word_recognition h
    (generatedFeasibleSixteen_quarter_input h hq)
  change generatedFeasibleSecondaryAClass
    (sExtra (rhoLocal h.val generatedFeasibleContainingOctadDestination)) = _ at hc
  have ho : generatedFeasibleSecondaryAClass
      (sExtra (rhoLocal h.val generatedFeasibleContainingOctadDestination)) =
        generatedFeasibleSecondaryAClass generatedFeasibleSecondaryOddDestination := by
    apply (generatedFeasibleSecondaryAClass_eq_iff _ _).mpr
    refine ⟨a⁻¹, ?_⟩
    rw [hh]
    exact generatedFeasibleContaining_inverse_transports a.val _ _ ha
  exact hc.symm.trans ho

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
