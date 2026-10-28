/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialCacheData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthMonomialBitModel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthBlocks

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 0 to 511 are checked through exact bounded binary formulas.
private theorem packet0 : ∀ a : Fin 512,
    generatedAxisGlobalSpinLabel (generatedFeasibleAmbientTenthMonomialBitPull 2
        (generatedFeasibleAmbientTenthBlockLabel 0 a)) =
        generatedFeasibleAmbientTenthMonomialPull 2 (generatedFeasibleAmbientTenthBlockLabel 0 a) ∧
      generatedAxisGlobalIntSign (generatedFeasibleAmbientTenthMonomialBitPhase 2
          (generatedFeasibleAmbientTenthBlockLabel 0 a)) =
        generatedFeasibleAmbientTenthMonomialPhaseSign 2 (generatedFeasibleAmbientTenthBlockLabel
            0 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 512 to 1023 are checked through exact bounded binary formulas.
private theorem packet1 : ∀ a : Fin 512,
    generatedAxisGlobalSpinLabel (generatedFeasibleAmbientTenthMonomialBitPull 2
        (generatedFeasibleAmbientTenthBlockLabel 1 a)) =
        generatedFeasibleAmbientTenthMonomialPull 2 (generatedFeasibleAmbientTenthBlockLabel 1 a) ∧
      generatedAxisGlobalIntSign (generatedFeasibleAmbientTenthMonomialBitPhase 2
          (generatedFeasibleAmbientTenthBlockLabel 1 a)) =
        generatedFeasibleAmbientTenthMonomialPhaseSign 2 (generatedFeasibleAmbientTenthBlockLabel
            1 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1024 to 1535 are checked through exact bounded binary formulas.
private theorem packet2 : ∀ a : Fin 512,
    generatedAxisGlobalSpinLabel (generatedFeasibleAmbientTenthMonomialBitPull 2
        (generatedFeasibleAmbientTenthBlockLabel 2 a)) =
        generatedFeasibleAmbientTenthMonomialPull 2 (generatedFeasibleAmbientTenthBlockLabel 2 a) ∧
      generatedAxisGlobalIntSign (generatedFeasibleAmbientTenthMonomialBitPhase 2
          (generatedFeasibleAmbientTenthBlockLabel 2 a)) =
        generatedFeasibleAmbientTenthMonomialPhaseSign 2 (generatedFeasibleAmbientTenthBlockLabel
            2 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 1536 to 2047 are checked through exact bounded binary formulas.
private theorem packet3 : ∀ a : Fin 512,
    generatedAxisGlobalSpinLabel (generatedFeasibleAmbientTenthMonomialBitPull 2
        (generatedFeasibleAmbientTenthBlockLabel 3 a)) =
        generatedFeasibleAmbientTenthMonomialPull 2 (generatedFeasibleAmbientTenthBlockLabel 3 a) ∧
      generatedAxisGlobalIntSign (generatedFeasibleAmbientTenthMonomialBitPhase 2
          (generatedFeasibleAmbientTenthBlockLabel 3 a)) =
        generatedFeasibleAmbientTenthMonomialPhaseSign 2 (generatedFeasibleAmbientTenthBlockLabel
            3 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2048 to 2559 are checked through exact bounded binary formulas.
private theorem packet4 : ∀ a : Fin 512,
    generatedAxisGlobalSpinLabel (generatedFeasibleAmbientTenthMonomialBitPull 2
        (generatedFeasibleAmbientTenthBlockLabel 4 a)) =
        generatedFeasibleAmbientTenthMonomialPull 2 (generatedFeasibleAmbientTenthBlockLabel 4 a) ∧
      generatedAxisGlobalIntSign (generatedFeasibleAmbientTenthMonomialBitPhase 2
          (generatedFeasibleAmbientTenthBlockLabel 4 a)) =
        generatedFeasibleAmbientTenthMonomialPhaseSign 2 (generatedFeasibleAmbientTenthBlockLabel
            4 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 2560 to 3071 are checked through exact bounded binary formulas.
private theorem packet5 : ∀ a : Fin 512,
    generatedAxisGlobalSpinLabel (generatedFeasibleAmbientTenthMonomialBitPull 2
        (generatedFeasibleAmbientTenthBlockLabel 5 a)) =
        generatedFeasibleAmbientTenthMonomialPull 2 (generatedFeasibleAmbientTenthBlockLabel 5 a) ∧
      generatedAxisGlobalIntSign (generatedFeasibleAmbientTenthMonomialBitPhase 2
          (generatedFeasibleAmbientTenthBlockLabel 5 a)) =
        generatedFeasibleAmbientTenthMonomialPhaseSign 2 (generatedFeasibleAmbientTenthBlockLabel
            5 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3072 to 3583 are checked through exact bounded binary formulas.
private theorem packet6 : ∀ a : Fin 512,
    generatedAxisGlobalSpinLabel (generatedFeasibleAmbientTenthMonomialBitPull 2
        (generatedFeasibleAmbientTenthBlockLabel 6 a)) =
        generatedFeasibleAmbientTenthMonomialPull 2 (generatedFeasibleAmbientTenthBlockLabel 6 a) ∧
      generatedAxisGlobalIntSign (generatedFeasibleAmbientTenthMonomialBitPhase 2
          (generatedFeasibleAmbientTenthBlockLabel 6 a)) =
        generatedFeasibleAmbientTenthMonomialPhaseSign 2 (generatedFeasibleAmbientTenthBlockLabel
            6 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Labels 3584 to 4095 are checked through exact bounded binary formulas.
private theorem packet7 : ∀ a : Fin 512,
    generatedAxisGlobalSpinLabel (generatedFeasibleAmbientTenthMonomialBitPull 2
        (generatedFeasibleAmbientTenthBlockLabel 7 a)) =
        generatedFeasibleAmbientTenthMonomialPull 2 (generatedFeasibleAmbientTenthBlockLabel 7 a) ∧
      generatedAxisGlobalIntSign (generatedFeasibleAmbientTenthMonomialBitPhase 2
          (generatedFeasibleAmbientTenthBlockLabel 7 a)) =
        generatedFeasibleAmbientTenthMonomialPhaseSign 2 (generatedFeasibleAmbientTenthBlockLabel
            7 a) := by
  decide +kernel

/-- Every root-two pullback and quadratic phase of word 2 is checked at all 4096 labels. -/
theorem generatedFeasibleAmbientTenth_monomial_cache_check02 : ∀ a : Fin 4096,
    generatedAxisGlobalSpinLabel
        ((generatedFeasibleAmbientTenthMonomialModel 2).coordinate *ᵥ golayLabelCoefficients a) =
      generatedFeasibleAmbientTenthMonomialPull 2 a ∧
    generatedAxisGlobalIntSign
        (monsterMonomialQuadratic
          (fun i j => (generatedFeasibleAmbientTenthMonomialModel 2).phase i j)
          (golayLabelCoefficients a)) = generatedFeasibleAmbientTenthMonomialPhaseSign 2 a := by
  have hb : ∀ a : Fin 4096,
      generatedAxisGlobalSpinLabel (generatedFeasibleAmbientTenthMonomialBitPull 2 a) =
        generatedFeasibleAmbientTenthMonomialPull 2 a ∧
      generatedAxisGlobalIntSign (generatedFeasibleAmbientTenthMonomialBitPhase 2 a) =
        generatedFeasibleAmbientTenthMonomialPhaseSign 2 a := by
    apply generatedFeasibleAmbientTenth_fin4096_blocks
    intro q
    fin_cases q
    · exact packet0
    · exact packet1
    · exact packet2
    · exact packet3
    · exact packet4
    · exact packet5
    · exact packet6
    · exact packet7
  intro a
  simpa only [generatedFeasibleAmbientTenthMonomialBitPull_actual,
    generatedFeasibleAmbientTenthMonomialBitPhase_actual] using hb a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
