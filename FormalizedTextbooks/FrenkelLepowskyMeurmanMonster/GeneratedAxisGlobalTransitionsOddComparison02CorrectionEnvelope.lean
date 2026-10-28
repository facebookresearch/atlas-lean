/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddQEnvelope
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02TensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStateData

/-! The original complete comparison correction is checked on a complete sign-and-Q support envelope, with proved zeros outside. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

/-- Every possible original source sign contribution. -/
def generatedAxisGlobalOddComparison02SignEnvelope : Fin 4096 → Bool := generatedAxisGlobalOddSpinEnvelope ![
    0x666699990000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x666699990000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x666699990000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x666699990000,
    0x0,
    0x0,
    0x0,
    0x0]

/-- The genuine Q translation of every possible original sign contribution. -/
def generatedAxisGlobalOddComparison02CorrectionEnvelope : Fin 4096 → Bool := generatedAxisGlobalOddSpinEnvelope ![
    0x666699990000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x666699990000,
    0x0,
    0x0,
    0x0,
    0x0,
    0x666699990000000000000000000000000000000000000000000000000000,
    0x0,
    0x0,
    0x666699990000,
    0x0,
    0x0,
    0x0,
    0x0]

/-- The entire original source spin correction retains all original coefficients and phases. -/
theorem generatedAxisGlobalOddComparison02EnvelopeSpin_certificate (k : Fin 4096) :
    generatedAxisGlobalOddComparisonSpinInteger 2 generatedAxisGlobalOddRoot06Spin08 k = generatedAxisGlobalOddComparison02Spin k := by
  let S := generatedAxisGlobalOddComparison02SignEnvelope
  let E := generatedAxisGlobalOddComparison02CorrectionEnvelope
  have hcS : ∀ e : Fin 2048,
      (generatedAxisGlobalOddRoot06Spin08 (generatedAxisGlobalTensorLowLabel e) ≠ 0 ∨
       generatedAxisGlobalOddRoot06Spin08 (generatedAxisGlobalTensorHighLabel e) ≠ 0 ∨
       generatedAxisGlobalOddRoot06Spin08 (generatedAxisGlobalTensorLowLabel (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode 4) e)) ≠ 0 ∨
       generatedAxisGlobalOddRoot06Spin08 (generatedAxisGlobalTensorHighLabel (generatedAxisGlobalSignInputCode (generatedAxisGlobalSignLowCode 4) e)) ≠ 0) →
       S (generatedAxisGlobalTensorLowLabel e) = true ∧ S (generatedAxisGlobalTensorHighLabel e) = true := by
    apply generatedAxisGlobalOddLowEnvelope_blocked_forall
    decide +kernel
  have hcQ : ∀ m : Fin 4096, S m = true →
      E ((generatedAxisGlobalOddQSpinLabelEquiv (generatedAxisGlobalOddComparisonQ 2)).symm m) = true := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hi : ∀ k : Fin 4096, E k = true →
      (1 : ℤ) * generatedAxisGlobalOddComparisonSpinInteger 2 generatedAxisGlobalOddRoot06Spin08 k =
        1 * generatedAxisGlobalOddComparison02Spin k := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hv : ∀ k : Fin 4096, E k = false → generatedAxisGlobalOddComparison02Spin k = 0 := by
    apply generatedAxisGlobalOddSpinEnvelope_blocked_forall
    decide +kernel
  have hz : ∀ k : Fin 4096, E k = false →
      generatedAxisGlobalOddComparisonSpinInteger 2 generatedAxisGlobalOddRoot06Spin08 k = 0 := by
    intro k hk
    change generatedAxisGlobalOddQSpinInteger (generatedAxisGlobalOddComparisonQ 2)
      (generatedAxisGlobalOddSignSpinInteger 4 generatedAxisGlobalOddRoot06Spin08) k = 0
    exact generatedAxisGlobalOddQSignSpin_zero_outside _ 4 _ S E
      (generatedAxisGlobalOddSignSpin_zero_outside 4 _ S hcS) hcQ k hk
  simpa only [one_mul] using generatedAxisGlobalOddSpinEnvelope_certificate E _ _ 1 1 hi hz hv k

/-- Every physical spatial coefficient has its original source sign. -/
theorem generatedAxisGlobalOddComparison02EnvelopeSpatial_certificate (i : Fin 24) :
    generatedAxisGlobalOddComparisonSpatialInteger 2 generatedAxisGlobalOddRoot06Spatial08 i = generatedAxisGlobalOddComparison02Spatial i := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
