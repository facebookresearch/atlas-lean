/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFactorPrimitives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddXiSpinCached
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinXi01Batch00

/-! Complete bounded physical spin-output certificates for the original source primitive. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All physical coordinates of this complete source output block are exact. -/
theorem generatedAxisGlobalOddRoot00SpinStep01Block00_certificate (n : Fin 256) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 0 generatedAxisGlobalOddRoot00Spin00 ⟨0 +
      n.val, by have hn := n.isLt; omega⟩ =
      8 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin01 ⟨0 + n.val, by have hn := n.isLt; omega⟩
      := by
  change (1 : ℤ) * generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot00Spin00 ⟨0 +
      n.val, by have hn := n.isLt; omega⟩ =
      8 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin01 ⟨0 + n.val, by have hn := n.isLt; omega⟩
  simpa only [zero_add, one_mul, mul_one] using
    generatedAxisGlobalOddRoot00SpinXi01Batch00_certificate n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
