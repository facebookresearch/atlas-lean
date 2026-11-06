/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpinBlockIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddXiSpinCached
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block06

/-! Complete bounded physical spin-output certificates for the original source primitive. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All physical coordinates of this complete source output block are exact. -/
theorem generatedAxisGlobalOddRoot06SpinStep01Block06_certificate (n : Fin 256) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 0 generatedAxisGlobalOddRoot06Spin00
      (generatedAxisGlobalOddSpinOutputBlock 6 n) =
      8 * (1 : ℤ) * generatedAxisGlobalOddRoot06Spin01 (generatedAxisGlobalOddSpinOutputBlock 6
      n) := by
  exact generatedAxisGlobalOddRoot00SpinStep01Block06_certificate n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
