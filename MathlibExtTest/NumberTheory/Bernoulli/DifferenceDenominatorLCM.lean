/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Bernoulli.DifferenceDenominatorLCM

open MetaMathlibExt UniqueFactorizationMonoid

-- The power-of-two boundary includes exponent zero.
example : Odd (bernoulliDiffDenominator 1) :=
  (bernoulliDiffDenominator_parity_radical_lcm 1 (by decide)).1.mpr ⟨0, rfl⟩

example : ¬ Odd (bernoulliDiffDenominator 3) := by decide +kernel

-- Both 2 and 3 divide the successor 6, but neither divides the index 5.
example : radical (5 + 1 : ℕ) ∣ bernoulliDiffDenominatorCoprimePart 5 :=
  ((bernoulliDiffDenominator_parity_radical_lcm 5 (by decide)).2.1 (by decide)).2

-- At n = 7, the radical and the next denominator contribute different primes to the lcm.
example : bernoulliDiffDenominator 7 = 6 := by
  rw [(bernoulliDiffDenominator_parity_radical_lcm 7 (by decide)).2.2 (by decide) (by decide),
    Nat.radical_eq_prod_primeFactors]
  decide +kernel
