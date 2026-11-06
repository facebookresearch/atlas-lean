/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthByte00Data
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQFast
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache00

/-! All768 byte lifts retain their complete actual root-word Q action and central phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxHeartbeats 200000000 in
-- Check all18432 actual binary coordinates and all768 genuine central output coefficients.
set_option maxRecDepth 10000 in
/-- Every cached byte is the entire original Q image, with its actual central sign. -/
theorem generatedAxisGlobalFifthByte00Cache_checked (b : Fin 3) (t : Fin 256) :
    generatedAxisGlobalFifthQFast 0 (generatedAxisGlobalQByteFromFin b t) =
      generatedAxisGlobalFifthByte00Cache b t := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    funext j
    have h : ∀ b : Fin 3, ∀ t : Fin 256, ∀ j : Fin 24,
        toAdd (generatedAxisGlobalFifthQFast 0 (generatedAxisGlobalQByteFromFin b t)).base j =
          toAdd (generatedAxisGlobalFifthByte00Cache b t).base j := by
      decide +kernel
    exact h b t j
  · apply toAdd.injective
    have h : ∀ b : Fin 3, ∀ t : Fin 256,
        toAdd (generatedAxisGlobalFifthQFast 0 (generatedAxisGlobalQByteFromFin b t)).coeff =
          toAdd (generatedAxisGlobalFifthByte00Cache b t).coeff := by
      decide +kernel
    exact h b t

/-- Three verified byte images give the complete actual root-word Q evaluator. -/
theorem generatedAxisGlobalFifthByte00Evaluation_actual (q : Q) :
    generatedAxisGlobalFifthQFast 0 q =
      generatedAxisGlobalQByteEvaluation generatedAxisGlobalFifthByte00Cache q := by
  rw [← generatedAxisGlobalFifthQFast_actual 0 generatedAxisGlobalFifthQCache00_actual,
    ← generatedAxisGlobalFifthShortWord_QImage]
  apply generatedAxisGlobalQByteEvaluation_actual
  intro b t
  rw [generatedAxisGlobalFifthShortWord_QImage,
    generatedAxisGlobalFifthQFast_actual 0 generatedAxisGlobalFifthQCache00_actual]
  exact generatedAxisGlobalFifthByte00Cache_checked b t

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
