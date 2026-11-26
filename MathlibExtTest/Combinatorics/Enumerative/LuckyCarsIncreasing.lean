/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LuckyCarsIncreasing

/-! # Tests for lucky cars in weakly increasing parking functions -/

open MetaMathlibExt MathlibExt.Combinatorics.Enumerative.LuckyCarsWanted

-- Car zero is always lucky, and the prefix factor is the Catalan number at zero.
example : qInc 3 0 0 = 5 := by
  rw [qInc_eq, ite_eq_left rfl]
  decide +kernel

-- Both blocks have length two, so both factors are nontrivial.
example : qInc 4 2 2 = 4 := by
  rw [qInc_eq, ite_eq_left rfl]
  decide +kernel

-- Car one can prefer spot zero, but it cannot park there.
example : qInc 3 1 0 = 0 := by
  rw [qInc_eq, ite_eq_right (by decide)]

-- Independently enumerate the diagonal fiber using the greedy parking algorithm.
example : (Finset.univ.filter (fun f : Fin 3 → Fin 3 =>
    IsParkingFunction 3 f ∧ (∀ a b, a ≤ b → f a ≤ f b) ∧ f 1 = 1 ∧
      parkSpots f 1 = f 1)).card = 2 := by decide +kernel
