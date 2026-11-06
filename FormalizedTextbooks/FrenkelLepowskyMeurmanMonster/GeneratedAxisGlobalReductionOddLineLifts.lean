/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddLocalLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddStabilizerProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionBinary

/-! Genuine full odd-axis lifts of coordinate-line-preserving spatial actions.
These supply actual stabilizer elements for third-family binary reduction. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A signed image of the original coordinate unit preserves its genuine norm-eight line. -/
theorem generatedAxisGlobalOdd_signed_unit_line (g : leechIsomSubgroup) (b : ZMod 2)
    (hg : g.val (Pi.single 0 1) = qSign b • (Pi.single 0 1 : Fin 24 → ℝ)) :
    g ∈ generatedNormEightLineStabilizer := by
  rw [generatedNormEightLineStabilizer_mem]
  simp only [generatedNormEightLineMatrix, conwayMatrixAction_vecMulVec,
    generatedNormEightVector_axis_unit, map_smul, hg]
  fin_cases b <;> ext i j <;>
    simp [Matrix.vecMulVec, qSign_zero, qSign_one, Pi.smul_apply]

/-- Every original Golay sign preserves the actual coordinate line. -/
theorem generatedAxisGlobalOdd_sign_line (c : golayCode) :
    golaySignIsometry c ∈ generatedNormEightLineStabilizer := by
  apply generatedAxisGlobalOdd_signed_unit_line _ (c.val 0)
  ext i
  by_cases hi : i = 0
  · subst i
    simp [golaySignIsometry, golayRealSign_apply]
  · simp [golaySignIsometry, golayRealSign_apply, hi]

/-- Every genuine Golay permutation fixing coordinate zero preserves its actual norm-eight line. -/
theorem generatedAxisGlobalOdd_permutation_line (p : golayAutomorphismSubgroup)
    (hp : p.val 0 = 0) :
    golayPermutationIsometry p ∈ generatedNormEightLineStabilizer := by
  apply generatedAxisGlobalOdd_signed_unit_line _ 0
  ext i
  simp [golayPermutationIsometry, golayRealPermute_apply, Pi.single_apply,
    Equiv.symm_apply_eq, hp, qSign_zero]

/-- A true spatial line stabilizer has a genuine full-axis-fixing local lift. -/
def generatedAxisGlobalOddLineLift (g : generatedNormEightLineStabilizer) :
    generatedOddLocalAxisStabilizer :=
  ⟨localFiberIntoH
      (Classical.choose (generatedOddAxis_projected_stabilizer_lift g.val g.property)),
    (Classical.choose_spec
      (generatedOddAxis_projected_stabilizer_lift g.val g.property)).2⟩

/-- The lift retains its original spatial projection in the actual Conway quotient. -/
theorem generatedAxisGlobalOddLineLift_projection (g : generatedNormEightLineStabilizer) :
    projH (generatedAxisGlobalOddLineLift g).val = QuotientGroup.mk' signsSubgroup g.val := by
  change QuotientGroup.mk' signsSubgroup
    (Classical.choose
      (generatedOddAxis_projected_stabilizer_lift g.val g.property)).val.2 = _
  rw [(Classical.choose_spec
    (generatedOddAxis_projected_stabilizer_lift g.val g.property)).1]

/-- Every line lift fixes the entire actual odd axis, including its central phases. -/
theorem generatedAxisGlobalOddLineLift_fixed (g : generatedNormEightLineStabilizer) :
    rhoLocal (generatedAxisGlobalOddLineLift g).val generatedOddAxis = generatedOddAxis :=
  (generatedAxisGlobalOddLineLift g).property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
