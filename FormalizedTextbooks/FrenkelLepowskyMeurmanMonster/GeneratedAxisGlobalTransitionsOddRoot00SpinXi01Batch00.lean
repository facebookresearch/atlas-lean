/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddXiSpinCached

/-! Check the original first Gaussian on a complete block of physical spin coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 80000000 in
-- Each of 256 physical output coordinates retains the genuine 64-term source sum.
/-- The first original Gaussian has the exact candidate numerator on this complete block. -/
theorem generatedAxisGlobalOddRoot00SpinXi01Batch00_certificate (j : Fin 256) :
    generatedAxisGlobalOddXiSpinInteger generatedAxisGlobalOddRoot00Spin00
        ⟨j.val, by have hj := j.isLt; omega⟩ =
      8 * generatedAxisGlobalOddRoot00Spin01 ⟨j.val, by have hj := j.isLt; omega⟩ := by
  rw [generatedAxisGlobalOddXiSpinInteger_eq_cached]
  have h : ∀ j : Fin 256,
      generatedSixthIntegerXiCached generatedAxisGlobalOddRoot00Spin00
          ⟨j.val, by have hj := j.isLt; omega⟩ =
        8 * generatedAxisGlobalOddRoot00Spin01 ⟨j.val, by have hj := j.isLt; omega⟩ := by
    decide +kernel
  exact h j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
