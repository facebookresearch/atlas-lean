/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorSourceFlags
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingZeroOutsideAnchorClassRecognition

/-! The full original outside-to-containing transition identifies the entire actual zero orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Original local words relate the entire outside and containing vectors by actual triality,
while fixing the original positive first axis. -/
theorem generatedFeasibleContainingZeroOutsideAnchorOutsideContaining_transition :
    ∃ k l : localAxisStabilizer generatedFeasiblePhysicalRootPair,
      sExtra (rhoLocal k.val generatedFeasibleOutsideOctadDestination) =
        rhoLocal l.val generatedFeasibleContainingOctadDestination := by
  obtain ⟨r, hrx, hrf⟩ := generatedFeasibleContainingZeroOutsideAnchorOutside_source_flag
  obtain ⟨q, hqx, hqf⟩ := generatedFeasibleContainingZeroOutsideAnchorContaining_source_flag
  let h := localFiberIntoH (generatedFeasibleContainingZeroOutsideAnchorStep 1)
  have hx := generatedFeasibleContainingZeroOutsideAnchorWhole_axis
  have hf := generatedFeasibleContainingZeroOutsideAnchorStep_first 1
  obtain ⟨p, hp⟩ := generatedAxis_pair_localOmega_transitive 0 0
    (23 : Fin 276) generatedFeasiblePhysicalRootPair 0 0
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
      (conwayShortAxis (Sum.inl (0, (23 : Fin 276))) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
    have he := hcomm (conwayShortAxis (Sum.inl (0, (23 : Fin 276))) 0)
    rw [generatedAxis_triality_pair_exact, hp, generatedAxis_triality_pair_exact] at he
    exact he
  let w := localFiberIntoH (generatedFeasibleContainingZeroOutsideAnchorStep 0)
  have hk : rhoLocal (p.val * w * r)
      (conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0) =
        conwayShortAxis (Sum.inl (0, generatedFeasiblePhysicalRootPair)) 0 := by
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hrf]
    rw [generatedFeasibleContainingZeroOutsideAnchorStep_first 0, hp]
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

/-- All actual zero-coefficient inputs reach exactly the established outside-octad A class. -/
theorem generatedFeasibleContaining_zero_class_eq_outside :
    generatedFeasibleSecondaryAClass generatedFeasibleContainingZeroDestination =
      generatedFeasibleSecondaryAClass generatedFeasibleOutsideOctadDestination := by
  obtain ⟨k, l, hkl⟩ := generatedFeasibleContainingZeroOutsideAnchorOutsideContaining_transition
  exact generatedFeasibleContainingZeroOutsideAnchor_class_of_actual_transition k l hkl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
