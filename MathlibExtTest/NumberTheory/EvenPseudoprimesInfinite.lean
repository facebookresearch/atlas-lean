/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EvenPseudoprimesInfinite
import Mathlib.Order.Interval.Finset.Nat

open MathlibExt.NumberTheory

-- Every finite search bound misses an even composite solution to the Fermat congruence.
example (B : ℕ) : ∃ N > B, Even N ∧ ¬ N.Prime ∧ 2 ^ N ≡ 2 [MOD N] := by
  obtain ⟨N, hN, hB⟩ := EvenPseudoprimesWanted.evenPseudoprimes_infinite.exists_gt B
  have h := mem_evenPseudoprimes.mp hN
  exact ⟨N, hB, h.even, h.not_prime, h.modeq⟩
