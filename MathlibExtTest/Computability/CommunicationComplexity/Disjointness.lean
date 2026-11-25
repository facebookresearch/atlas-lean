/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.CommunicationComplexity.Disjointness

/-!
# Tests for randomized communication complexity of set disjointness
-/

namespace MathlibExtTest.Computability.CommunicationComplexity.Disjointness

open MathlibExt.Computability.CommunicationComplexity

example (x y : Fin 0 → Bool) : disjFn 0 x y = false := by simp [disjFn]

example : disjFn 3 ![true, false, true] ![false, true, false] = false := by decide

example : disjFn 3 ![true, false, true] ![false, false, true] = true := by decide

-- At positive length, error one third requires communication.
example {n : ℕ} (hn : 0 < n) : 0 < randComplexity (disjFn n) (1 / 3) := by
  obtain ⟨c, hc, h⟩ := randComplexity_disjFn_ge (1 / 3) (by norm_num) (by norm_num)
  exact_mod_cast (mul_pos hc (by exact_mod_cast hn : 0 < (n : ℝ))).trans_le (h n)

-- A fair public coin attains the excluded endpoint with no communication.
example (n : ℕ) : randComplexity (disjFn n) (1 / 2) = 0 := by
  let P : PublicCoinProtocol (Fin n → Bool) (Fin n → Bool) Bool := ⟨Protocol.output⟩
  apply Nat.eq_zero_of_le_zero
  refine Nat.sInf_le ⟨P.toRandomized, P.cost_toRandomized_le.trans ?_, fun x y => ?_⟩
  · simp [P, PublicCoinProtocol.cost, Protocol.depth]
  · rw [P.error_toRandomized]
    cases h : disjFn n x y <;>
      norm_num [PublicCoinProtocol.errorProb, P, Protocol.eval, h, Finset.filter_insert,
        Finset.filter_singleton]

end MathlibExtTest.Computability.CommunicationComplexity.Disjointness
