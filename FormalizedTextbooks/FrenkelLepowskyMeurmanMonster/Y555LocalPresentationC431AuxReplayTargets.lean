/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal binding of the original C431 cubic and the original-relation loop coefficient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431AuxReplayValid

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The exact positive original-source spelling of the requested longest-word/e1 cube. -/
def y431AuxReplayCubePositiveWord : List (Fin 9) :=
  (List.replicate 3
    ((List.replicate 9 ([0, 1, 5, 8, 2, 6, 3] : List (Fin 9))).flatten ++ [4])).flatten

/-- Encode that literal original-source cube in the finite signed replay alphabet. -/
def y431AuxReplayCubeSignedWord : List (Fin 810 × Bool) :=
  y431AuxReplayCubePositiveWord.map
    (fun v => (y431AuxReplayGeneratorSymbol (y431AuxOriginalLetter v), true))

set_option maxRecDepth 100000 in
/-- The finite replay word has exactly the original free-group cubic's value. -/
theorem y431AuxReplayCubeSignedWord_value :
    y431AuxReplayWordValue y431AuxReplayCubeSignedWord =
      PresentedGroup.mk y431Relations y431LongestCube := by
  have he := (y431AuxReplayWordValue_positive
      (y431AuxReplayCubePositiveWord.map y431AuxOriginalLetter)).trans
    (y431AuxPositiveWord_original y431AuxReplayCubePositiveWord)
  have hv : y431AuxReplayWordValue y431AuxReplayCubeSignedWord =
      y431PositiveWord y431AuxReplayCubePositiveWord := by
    simpa only [y431AuxReplayCubeSignedWord, List.map_map, Function.comp_def] using he
  rw [hv, y431AuxReplayCubePositiveWord, y431PositiveWord_replicate,
    y431PositiveWord_append, y431PositiveWord_replicate]
  simp [y431PositiveWord, y431LongestCube, y431F12, map_pow, map_mul,
    PresentedGroup.of, mul_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- This finite comparison checks the literal cubic and its exact H-coefficient symbol.
/-- The designated checked equation has precisely the original cubic as its left-hand side. -/
theorem y431AuxReplayCube_equation :
    (y431AuxReplayProgram 3660).1.left = y431AuxReplayCubeSignedWord ∧
      (y431AuxReplayProgram 3660).1.right = [(y431AuxReplayHSymbol 584, true)] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- This finite comparison checks the exact original-relation loop coefficient and empty output.
/-- The designated original-relator loop has exactly its declared coefficient and identity sides. -/
theorem y431AuxReplayLoop_equation :
    (y431AuxReplayProgram 3683).1.left = [(y431AuxReplayHSymbol 619, true)] ∧
      (y431AuxReplayProgram 3683).1.right = [] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The two target coefficients have exactly the same verified E8 word spelling. -/
theorem y431AuxReplayHWord_target_eq_loop :
    y431AuxReplayHWord 584 = y431AuxReplayHWord 619 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
