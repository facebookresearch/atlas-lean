/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQStates09Data

/-! Exact individual source-factor coordinate states for the actual root 9 word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxRecDepth 10000 in
set_option maxHeartbeats 200000000 in
-- Verify every scalar binary coordinate using only a single actual factor at a constant input.
/-- Every candidate binary state follows its genuine individual source-factor Q image. -/
theorem generatedAxisGlobalFifthQStates09_binary (n : Fin 41) (i : Fin 24) :
    (generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor09 n)
      (generatedAxisGlobalFifthQState09 (Fin.castAdd 1 n) i)).base =
        (generatedAxisGlobalFifthQState09 (Fin.natAdd 1 n) i).base := by
  apply toAdd.injective
  funext j
  have h : ∀ n : Fin 41, ∀ i j : Fin 24,
      toAdd (generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor09 n)
        (generatedAxisGlobalFifthQState09 (Fin.castAdd 1 n) i)).base j =
          toAdd (generatedAxisGlobalFifthQState09 (Fin.natAdd 1 n) i).base j := by
    decide +kernel
  exact h n i j

set_option maxRecDepth 10000 in
set_option maxHeartbeats 200000000 in
-- Verify every actual source-factor central correction at the same concrete input lifts.
/-- Every candidate central sign follows its genuine individual source-factor Q image. -/
theorem generatedAxisGlobalFifthQStates09_phase (n : Fin 41) (i : Fin 24) :
    (generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor09 n)
      (generatedAxisGlobalFifthQState09 (Fin.castAdd 1 n) i)).coeff =
        (generatedAxisGlobalFifthQState09 (Fin.natAdd 1 n) i).coeff := by
  apply toAdd.injective
  have h : ∀ n : Fin 41, ∀ i : Fin 24,
      toAdd (generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor09 n)
        (generatedAxisGlobalFifthQState09 (Fin.castAdd 1 n) i)).coeff =
          toAdd (generatedAxisGlobalFifthQState09 (Fin.natAdd 1 n) i).coeff := by
    decide +kernel
  exact h n i

/-- Both finite certificates determine each entire actual source-factor coordinate lift. -/
theorem generatedAxisGlobalFifthQStates09_actual (n : Fin 41) (i : Fin 24) :
    generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor09 n)
      (generatedAxisGlobalFifthQState09 (Fin.castAdd 1 n) i) =
        generatedAxisGlobalFifthQState09 (Fin.natAdd 1 n) i :=
  NormalizedCocycleExtension.Extension.ext
    (generatedAxisGlobalFifthQStates09_binary n i) (generatedAxisGlobalFifthQStates09_phase n i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
