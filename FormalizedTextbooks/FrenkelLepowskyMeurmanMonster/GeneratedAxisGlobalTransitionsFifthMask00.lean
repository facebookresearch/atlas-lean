/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthMaskAction
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache00

/-! Unconditional entire first-root Q transport in the original extraspecial coordinate model. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every mask is transported by the genuine complete first-root local word, including its phase. -/
theorem generatedAxisGlobalFifthMask00_actual (v : ℕ) :
    spinConjugation (generatedAxisGlobalFifthShortWordFiber 0).val.1
        (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedAxisGlobalFifthQCacheBinary 0)
        (generatedAxisGlobalFifthMaskRows 0) (generatedAxisGlobalFifthMaskCoefficients 0) v :=
  generatedAxisGlobalFifthMaskAction_actual 0 generatedAxisGlobalFifthQCache00_actual v

/-- The original first-root Q evaluator equals the complete checked polynomial evaluator. -/
theorem generatedAxisGlobalFifthQFast_mask00 (v : ℕ) :
    generatedAxisGlobalFifthQFast 0 (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedAxisGlobalFifthQCacheBinary 0)
        (generatedAxisGlobalFifthMaskRows 0) (generatedAxisGlobalFifthMaskCoefficients 0) v :=
  generatedAxisGlobalFifthQFast_mask 0 generatedAxisGlobalFifthQCache00_actual v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
