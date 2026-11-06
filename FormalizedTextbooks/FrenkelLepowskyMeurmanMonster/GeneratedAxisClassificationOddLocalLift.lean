/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddLocalFixed
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineMonomial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineSignedUnit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerLocalLift

/-! Every actual spatial norm-eight line stabilizer lifts, after an actual
extraspecial correction, to the full original odd-axis stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine Co0 line stabilizer has a compatible fiber lift fixing the
full actual odd axis, with its original spatial component unchanged. -/
theorem generatedOddAxis_projected_stabilizer_lift (g : leechIsomSubgroup)
    (hg : g ∈ generatedNormEightLineStabilizer) :
    ∃ f : localFiberSubgroup, f.val.2 = g ∧
      rhoLocal (localFiberIntoH f) generatedOddAxis = generatedOddAxis := by
  obtain ⟨f, hfg⟩ := generatedCentral_localFiber_lift g
  have hmono : f.val.2 ∈ golayMonomialSubgroup := by
    rw [hfg]
    exact generatedNormEightLineStabilizer_le_monomial hg
  obtain ⟨q, hq⟩ := generatedOddSpin_monomial_Q_orbit f hmono
  obtain ⟨b, hb⟩ := generatedNormEightLineStabilizer_signed_unit g hg
  let k : Q := qCentral b * q⁻¹
  let f' : localFiberSubgroup := localFiberIncl k * f
  have hspatial : f'.val.2 = g := by
    change (1 : leechIsomSubgroup) * f.val.2 = g
    rw [one_mul, hfg]
  have hspin : f'.val.1.val (generatedOddSpinState 0 1 0) =
      qSign b • generatedOddSpinState 0 1 0 := by
    change spinRepresentation k (f.val.1.val (generatedOddSpinState 0 1 0)) = _
    rw [← hq]
    change spinRepresentation (qCentral b * q⁻¹)
      (spinRepresentation q (generatedOddSpinState 0 1 0)) = _
    rw [map_mul, LinearEquiv.mul_apply, map_inv]
    change spinRepresentation (qCentral b)
      ((spinRepresentation q).symm (spinRepresentation q (generatedOddSpinState 0 1 0))) = _
    rw [LinearEquiv.symm_apply_apply, spinRepresentation_central]
  refine ⟨f', hspatial, ?_⟩
  change localGriessRepresentation f' generatedOddAxis = generatedOddAxis
  apply generatedOddAxis_lift_fixed f' (hspatial ▸ generatedNormEightLineStabilizer_le_monomial hg)
    b hspin
  · rw [hspatial]
    exact hb
  · rw [hspatial]
    exact (generatedNormEightLine_odd_stabilizer_iff g 0 0).mpr hg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
