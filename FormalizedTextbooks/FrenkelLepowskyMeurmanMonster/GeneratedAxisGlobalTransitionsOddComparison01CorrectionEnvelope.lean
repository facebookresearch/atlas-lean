/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddQEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01TensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData

/-! The original complete comparison correction is checked on a complete sign-and-Q support envelope, with proved zeros outside. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Every possible original source sign contribution. -/
def generatedAxisGlobalOddComparison01SignEnvelope : Fin 4096 → Bool := generatedAxisGlobalOddSpinEnvelope ![
    0x14144141000000000000000000001414000000004141,
    0x414100000000141400000000000000000000414114140000,
    0x414100000000141400000000000000000000414114140000,
    0x14144141000000000000000000001414000000004141,
    0x1414000000004141000000000000000000001414414100000000000000000000,
    0x414114140000000000000000000041410000000014140000000000000000,
    0x414114140000000000000000000041410000000014140000000000000000,
    0x1414000000004141000000000000000000001414414100000000000000000000,
    0x14144141000000000000000000001414000000004141,
    0x414100000000141400000000000000000000414114140000,
    0x414100000000141400000000000000000000414114140000,
    0x14144141000000000000000000001414000000004141,
    0x1414000000004141000000000000000000001414414100000000000000000000,
    0x414114140000000000000000000041410000000014140000000000000000,
    0x414114140000000000000000000041410000000014140000000000000000,
    0x1414000000004141000000000000000000001414414100000000000000000000]

/-- The genuine Q translation of every possible original sign contribution. -/
def generatedAxisGlobalOddComparison01CorrectionEnvelope : Fin 4096 → Bool := generatedAxisGlobalOddSpinEnvelope ![
    0x14144141000000000000000000001414000000004141,
    0x414100000000141400000000000000000000414114140000,
    0x414100000000141400000000000000000000414114140000,
    0x14144141000000000000000000001414000000004141,
    0x1414000000004141000000000000000000001414414100000000000000000000,
    0x414114140000000000000000000041410000000014140000000000000000,
    0x414114140000000000000000000041410000000014140000000000000000,
    0x1414000000004141000000000000000000001414414100000000000000000000,
    0x14144141000000000000000000001414000000004141,
    0x414100000000141400000000000000000000414114140000,
    0x414100000000141400000000000000000000414114140000,
    0x14144141000000000000000000001414000000004141,
    0x1414000000004141000000000000000000001414414100000000000000000000,
    0x414114140000000000000000000041410000000014140000000000000000,
    0x414114140000000000000000000041410000000014140000000000000000,
    0x1414000000004141000000000000000000001414414100000000000000000000]

/-- The entire original source spin correction retains all original coefficients and phases. -/
theorem generatedAxisGlobalOddComparison01EnvelopeSpin_certificate (k : Fin 4096) :
    generatedAxisGlobalOddComparisonSpinInteger 1 generatedAxisGlobalOddRoot00Spin12 k = generatedAxisGlobalOddComparison01Spin k := by
  let S := generatedAxisGlobalOddComparison01SignEnvelope
  let E := generatedAxisGlobalOddComparison01CorrectionEnvelope
  have hcS : ∀ e : Fin 2048,
      (generatedAxisGlobalOddRoot00Spin12 (generatedAxisGlobalTensorLowLabel e) ≠ 0 ∨
       generatedAxisGlobalOddRoot00Spin12 (generatedAxisGlobalTensorHighLabel e) ≠ 0 ∨
       generatedAxisGlobalOddRoot00Spin12 (generatedAxisGlobalTensorLowLabel (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode 6) e)) ≠ 0 ∨
       generatedAxisGlobalOddRoot00Spin12 (generatedAxisGlobalTensorHighLabel (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode 6) e)) ≠ 0) →
       S (generatedAxisGlobalTensorLowLabel e) = true ∧ S (generatedAxisGlobalTensorHighLabel e) = true := by
    apply generatedAxisGlobalOddLowEnvelope_blocked_forall
    decide +kernel
  have hcQ : ∀ m : Fin 4096, S m = true →
      E ((generatedAxisGlobalOddQSpinLabelEquiv (generatedAxisGlobalOddComparisonQ 1)).symm m) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (1 : ℤ) * generatedAxisGlobalOddComparisonSpinInteger 1 generatedAxisGlobalOddRoot00Spin12 k =
        1 * generatedAxisGlobalOddComparison01Spin k := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddComparison01Spin k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hz : ∀ k : Fin 4096, E k = false →
      generatedAxisGlobalOddComparisonSpinInteger 1 generatedAxisGlobalOddRoot00Spin12 k = 0 := by
    intro k hk
    change generatedAxisGlobalOddQSpinInteger (generatedAxisGlobalOddComparisonQ 1)
      (generatedAxisGlobalOddSignSpinInteger 6 generatedAxisGlobalOddRoot00Spin12) k = 0
    exact generatedAxisGlobalOddQSignSpin_zero_outside _ 6 _ S E
      (generatedAxisGlobalOddSignSpin_zero_outside 6 _ S hcS) hcQ k hk
  simpa only [one_mul] using generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 1 1 hi hz hv k

/-- Every physical spatial coefficient has its original source sign. -/
theorem generatedAxisGlobalOddComparison01EnvelopeSpatial_certificate (i : Fin 24) :
    generatedAxisGlobalOddComparisonSpatialInteger 1 generatedAxisGlobalOddRoot00Spatial12 i = generatedAxisGlobalOddComparison01Spatial i := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
