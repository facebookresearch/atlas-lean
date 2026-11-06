/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! Complete original inverse-triality coordinates follow from the proved actual order three. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The entire inverse source formula is two applications of the checked real forward formula. -/
def generatedAxisGlobalRawInverseFormula (a : ConwayRawSpace) : ConwayRawSpace :=
  generatedAxisGlobalRawTrialityFormula (generatedAxisGlobalRawTrialityFormula a)

/-- The actual inverse-triality image retains every coordinate of all three constituents. -/
theorem generatedAxisGlobalRawInverseFormula_actual (x : GriessSpace) :
    griessConwayEncode (sExtra.symm x) =
      generatedAxisGlobalRawInverseFormula (griessConwayEncode x) := by
  have h : sExtra (sExtra x) = sExtra.symm x := by
    have h := congrArg (fun e : GriessSpace ≃ₗ[ℝ] GriessSpace => e (sExtra.symm x))
      sExtra_pow_three
    simpa only [pow_succ, pow_zero, LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq,
      LinearEquiv.apply_symm_apply] using h
  rw [← h, generatedAxisGlobalRawTrialityFormula_actual,
    generatedAxisGlobalRawTrialityFormula_actual]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
