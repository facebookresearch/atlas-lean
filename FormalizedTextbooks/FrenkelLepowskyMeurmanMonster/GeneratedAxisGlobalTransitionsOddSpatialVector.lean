/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpatialVectorCertificate

/-! Actual real spatial directions of every original odd-family source root word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All 24 actual spatial coordinates of each original root word equal the checked formula. -/
theorem generatedAxisGlobalOddSpatialRootVector_actual (k : Fin 9) :
    (generatedAxisGlobalOddSourceSpatialWord k).val (Pi.single (0 : Fin 24) (1 : ℝ)) =
      fun i => (generatedAxisGlobalOddSpatialRootVectorQ k i : ℝ) := by
  have h := generatedAxisGlobalOddSpatialVectorWordQ_actual
    (generatedAxisGlobalOddSourceRootWords k) (Pi.single (0 : Fin 24) (1 : ℚ))
  rw [generatedAxisGlobalOddSpatialRootVectorQ_certificate] at h
  have hs : (fun i => ((Pi.single (0 : Fin 24) (1 : ℚ) : Fin 24 → ℚ) i : ℝ)) =
      Pi.single (0 : Fin 24) (1 : ℝ) := by
    ext i
    by_cases hi : i = 0 <;> simp [hi]
  rw [hs] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
