/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.KeyTheorems.BakerGillSolovay

open Cslib.Complexity.Classes
open MetaMathlibExt.Complexity.KeyTheorems.BakerGillSolovay

example :
    (∃ O : List Bool → Bool, PWithOracle O ≠ NPWithOracle O) ∧
      (∃ O : List Bool → Bool, PWithOracle O = NPWithOracle O) :=
  baker_gill_solovay

example :
    ∃ A B : List Bool → Bool, A ≠ B ∧
      PWithOracle A ≠ NPWithOracle A ∧ PWithOracle B = NPWithOracle B := by
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := baker_gill_solovay
  exact ⟨A, B, fun h => hA (h.symm ▸ hB), hA, hB⟩
