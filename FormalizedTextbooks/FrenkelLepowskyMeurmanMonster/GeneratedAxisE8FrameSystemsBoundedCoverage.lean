/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageBlock00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageBlock01

/-! The two checked first-label blocks cover every greedy first label that can
occur in a sixteen-element subspace, by the independent pigeonhole bound. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every possible first label below32 has an ordinary-kernel coverage certificate. -/
theorem generatedAxisE8FrameCandidateBoundedCoverage_certificate :
    ∀ a : Fin 32, generatedAxisE8FrameCandidateCoverageAt ⟨a.val, by omega⟩ := by
  intro a
  by_cases ha : a.val < 16
  · have h := generatedAxisE8FrameCandidateCoverage_block_00 ⟨a.val, ha⟩
    simpa only [Nat.zero_add] using h
  · have h := generatedAxisE8FrameCandidateCoverage_block_01 ⟨a.val - 16, by omega⟩
    have he : (⟨16 + (a.val - 16), by omega⟩ : Fin 256) = ⟨a.val, by omega⟩ := by
      apply Fin.ext
      change 16 + (a.val - 16) = a.val
      omega
    rwa [he] at h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
