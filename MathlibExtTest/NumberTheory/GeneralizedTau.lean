/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedTau

open MetaMathlibExt

-- The shifted index can itself be a multiple of the prime.
example : generalizedTau 6 3 ≡ 0 [ZMOD 3] :=
  generalizedTau_two_mul_prime_succ_modEq_zero 3 (by decide) ⟨1, rfl⟩ 2 (by decide)

-- At n = 0 the divisibility hypothesis fails and the coefficient is 1 modulo 3.
example : ¬ generalizedTau 6 1 ≡ 0 [ZMOD 3] := by
  rw [generalizedTau_one]
  decide
