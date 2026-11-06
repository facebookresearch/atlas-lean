/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQFast

/-! The original verified coordinate cache evaluates the complete genuine local source word. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full original word evaluator equals its already checked original coordinate cache. -/
theorem generatedTenth_Q_word_fast (k : Fin 14)
    (hk : ∀ i, generatedAxisGlobalFifthChainQImage k 7 (qCoordinateGenerator i) =
      generatedAxisGlobalFifthQCache k i) (q : Q) :
    generatedTenthQWordImage k 7 q = generatedAxisGlobalFifthQFast k q := by
  rw [← generatedTenth_Q_word_image]
  change spinConjugation (generatedAxisGlobalFifthShortWordFiber k).val.1 q = _
  rw [generatedAxisGlobalFifthShortWord_QImage, generatedAxisGlobalFifthQFast_actual k hk]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
