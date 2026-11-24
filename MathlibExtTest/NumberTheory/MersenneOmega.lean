/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MersenneOmega
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace MetaMathlibExt.one_lt_gcd_mersenneOmega_of_legendreSym_eq_zero

local instance sevenPrime : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

-- The squarefree parts for seed 5 are 3 and 7. Reduction modulo 7 uses a proper
-- divisor of their product, 21.
private theorem seed_five (n : ℕ) (h : legendreSym 7 (mersenne n) = 0) :
    1 < Nat.gcd n (mersenneOmega 21) :=
  one_lt_gcd_mersenneOmega_of_legendreSym_eq_zero 5 (hs₁ := by decide) 3 7
    ⟨by decide, Nat.prime_three.prime.squarefree, 0, 1, by decide⟩
    ⟨by decide, Nat.prime_seven.prime.squarefree, 0, 1, by decide⟩ 7 (by decide) n h

example : 1 < Nat.gcd 3 (mersenneOmega 21) :=
  seed_five 3 (by norm_num [mersenne])

-- At exponent zero the Mersenne number is zero and the gcd equals the adjusted order.
example : 1 < mersenneOmega 21 := by
  simpa using seed_five 0 (by simp)

-- Two has odd order three modulo seven, so the adjusted order doubles it.
example : mersenneOmega 7 = 6 := by
  have h : orderOf (2 : ZMod 7) = 3 := orderOf_eq_prime (by decide) (by decide)
  rw [mersenneOmega, h]
  decide

end MetaMathlibExt.one_lt_gcd_mersenneOmega_of_legendreSym_eq_zero
