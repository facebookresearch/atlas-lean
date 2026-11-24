/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.FastVanDerWaerdenGame
import Mathlib.Tactic.NormNum

/-! # Tests for the fast van der Waerden game -/

namespace MetaMathlibExt.FastVanDerWaerdenGame

-- Translation, dilation, and contraction realize all three types at the smallest allowed size.
example : IsSymmetricOfType {0, 1, 2, 3} ⟨0, by decide⟩ ⟨3, by decide⟩ :=
  ⟨by decide, 1, 1, by norm_num, by
    simp (disch := norm_num) only [Finset.orderEmbOfFin_apply, Finset.sort_insert,
      Finset.sort_singleton]
    decide +kernel⟩

example : IsSymmetricOfType {0, 1, 2, 4} ⟨1, by decide⟩ ⟨3, by decide⟩ :=
  ⟨by decide, 2, 0, by norm_num, by
    simp (disch := norm_num) only [Finset.orderEmbOfFin_apply, Finset.sort_insert,
      Finset.sort_singleton]
    decide +kernel⟩

example : IsSymmetricOfType {0, 2, 3, 4} ⟨0, by decide⟩ ⟨2, by decide⟩ :=
  ⟨by decide, 1 / 2, 2, by norm_num, by
    simp (disch := norm_num) only [Finset.orderEmbOfFin_apply, Finset.sort_insert,
      Finset.sort_singleton]
    decide +kernel⟩

-- Deleting the two interior positions never works in a four-element set.
example (S : Finset ℚ) (hS : S.card = 4) :
    ¬ IsSymmetricOfType S ⟨1, by omega⟩ ⟨2, by omega⟩ := by
  intro h
  have hcases := isSymmetricOfType_cases S (by omega) _ _ h
  simp [hS] at hcases

-- The first selection wins the singleton game regardless of Breaker's reply.
example : MakerWinsWithin {0} 1 ∅ ∅ := by
  right
  refine ⟨0, by simp, by simp, fun _ _ _ _ => ?_⟩
  exact ⟨1, by decide, 0, by simp⟩

end MetaMathlibExt.FastVanDerWaerdenGame
