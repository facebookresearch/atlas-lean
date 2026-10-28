/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinBlockIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddXiSpinCached

/-! Complete bounded physical spin-output certificates for the original source primitive. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 80000000 in
-- Every one of 256 physical output coordinates is checked with its genuine source formula.
/-- All physical coordinates of this complete source output block are exact. -/
theorem generatedAxisGlobalOddRoot00SpinStep03Block09_certificate (n : Fin 256) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 7 generatedAxisGlobalOddRoot00Spin02
      (generatedAxisGlobalOddSpinOutputBlock 9 n) =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin03 (generatedAxisGlobalOddSpinOutputBlock 9
      n) := by
  have h : ∀ n : Fin 256, (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 7
      generatedAxisGlobalOddRoot00Spin02 (generatedAxisGlobalOddSpinOutputBlock 9 n) =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin03 (generatedAxisGlobalOddSpinOutputBlock 9
      n) := by decide +kernel
  exact h n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
