/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceMonomialCacheData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceMonomialBitModel

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- All original coordinates and phases are checked through the exact bounded binary formulas.
/-- Every complete original pullback and quadratic phase is checked, including all 4096 labels. -/
theorem generatedTwelfth_tensor_source_monomial_cache_check01 : ∀ a : Fin 4096,
    generatedAxisGlobalSpinLabel
        ((generatedTwelfthTensorSourceMonomialModel 1).coordinate *ᵥ golayLabelCoefficients a) =
      generatedTwelfthTensorSourceMonomialPull 1 a ∧
    generatedAxisGlobalIntSign
        (monsterMonomialQuadratic
          (fun i j => (generatedTwelfthTensorSourceMonomialModel 1).phase i j)
          (golayLabelCoefficients a)) = generatedTwelfthTensorSourceMonomialPhaseSign 1 a := by
  have hb : ∀ a : Fin 4096,
      generatedAxisGlobalSpinLabel (generatedTwelfthTensorSourceMonomialBitPull 1 a) =
        generatedTwelfthTensorSourceMonomialPull 1 a ∧
      generatedAxisGlobalIntSign (generatedTwelfthTensorSourceMonomialBitPhase 1 a) =
        generatedTwelfthTensorSourceMonomialPhaseSign 1 a := by
    decide +kernel
  intro a
  simpa only [generatedTwelfthTensorSourceMonomialBitPull_actual,
    generatedTwelfthTensorSourceMonomialBitPhase_actual] using hb a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
