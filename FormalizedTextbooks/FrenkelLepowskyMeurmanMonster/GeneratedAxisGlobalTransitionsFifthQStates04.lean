/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQStates04Data

/-! Exact individual source-factor coordinate states for the actual root 4 word. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

set_option maxRecDepth 10000 in
set_option maxHeartbeats 200000000 in
-- Verify every scalar binary coordinate using only a single actual factor at a constant input.
/-- Every candidate binary state follows its genuine individual source-factor Q image. -/
theorem generatedAxisGlobalFifthQStates04_binary (n : Fin 62) (i : Fin 24) :
    (generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor04 n)
      (generatedAxisGlobalFifthQState04 (Fin.castAdd 1 n) i)).base =
        (generatedAxisGlobalFifthQState04 (Fin.natAdd 1 n) i).base := by
  apply toAdd.injective
  funext j
  have h : ∀ n : Fin 62, ∀ i j : Fin 24,
      toAdd (generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor04 n)
        (generatedAxisGlobalFifthQState04 (Fin.castAdd 1 n) i)).base j =
          toAdd (generatedAxisGlobalFifthQState04 (Fin.natAdd 1 n) i).base j := by
    decide +kernel
  exact h n i j

set_option maxRecDepth 10000 in
set_option maxHeartbeats 200000000 in
-- Verify every actual source-factor central correction at the same concrete input lifts.
/-- Every candidate central sign follows its genuine individual source-factor Q image. -/
theorem generatedAxisGlobalFifthQStates04_phase (n : Fin 62) (i : Fin 24) :
    (generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor04 n)
      (generatedAxisGlobalFifthQState04 (Fin.castAdd 1 n) i)).coeff =
        (generatedAxisGlobalFifthQState04 (Fin.natAdd 1 n) i).coeff := by
  apply toAdd.injective
  have h : ∀ n : Fin 62, ∀ i : Fin 24,
      toAdd (generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor04 n)
        (generatedAxisGlobalFifthQState04 (Fin.castAdd 1 n) i)).coeff =
          toAdd (generatedAxisGlobalFifthQState04 (Fin.natAdd 1 n) i).coeff := by
    decide +kernel
  exact h n i

/-- Both finite certificates determine each entire actual source-factor coordinate lift. -/
theorem generatedAxisGlobalFifthQStates04_actual (n : Fin 62) (i : Fin 24) :
    generatedAxisGlobalQFactorImage (generatedAxisGlobalFifthQFactor04 n)
      (generatedAxisGlobalFifthQState04 (Fin.castAdd 1 n) i) =
        generatedAxisGlobalFifthQState04 (Fin.natAdd 1 n) i :=
  NormalizedCocycleExtension.Extension.ext
    (generatedAxisGlobalFifthQStates04_binary n i) (generatedAxisGlobalFifthQStates04_phase n i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
