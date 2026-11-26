/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GenLeonardoGenLeonardoBinomialSteps

/-! # Tests for `MathlibExt.NumberTheory.GenLeonardoGenLeonardoBinomialSteps` -/

namespace MathlibExtTest.NumberTheory.GenLeonardoGenLeonardoBinomialSteps

open MetaMathlibExt

-- Step three for `L` at `k = 1`, `n = 2`, `r = 0`: both sides equal `36`.
example : ∑ i ∈ Finset.range (2 + 1), (Nat.choose 2 i : ℤ) * genLeonardo 1 (3 * i + 0)
    = 2 ^ 2 * genLeonardo 1 (2 * 2 + 0) :=
  (genLeonardo_binomial_steps 1 2 0).1

example : ∑ i ∈ Finset.range (2 + 1), (Nat.choose 2 i : ℤ) * genLeonardo 1 (3 * i + 0) = 36 := by
  rw [(genLeonardo_binomial_steps 1 2 0).1]
  decide

-- Step three for `M` at `k = 1`, `n = 2`, `r = 0`: both sides equal `80`.
example : ∑ i ∈ Finset.range (2 + 1),
    (Nat.choose 2 i : ℤ) * genLeonardoCompanion 1 (3 * i + 0)
    = 2 ^ 2 * genLeonardoCompanion 1 (2 * 2 + 0) :=
  (genLeonardo_binomial_steps 1 2 0).2.1

example : ∑ i ∈ Finset.range (2 + 1),
    (Nat.choose 2 i : ℤ) * genLeonardoCompanion 1 (3 * i + 0) = 80 := by
  rw [(genLeonardo_binomial_steps 1 2 0).2.1]
  decide

-- Step four for `L` at `k = 1`, `n = 1`, `r = 0`: both sides equal `10`.
example : ∑ i ∈ Finset.range (1 + 1), (Nat.choose 1 i : ℤ) * genLeonardo 1 (4 * i + 0)
    = 3 ^ 1 * genLeonardo 1 (2 * 1 + 0) + 1 * (3 ^ 1 - 2 ^ 1) :=
  (genLeonardo_binomial_steps 1 1 0).2.2.1

example : ∑ i ∈ Finset.range (1 + 1), (Nat.choose 1 i : ℤ) * genLeonardo 1 (4 * i + 0) = 10 := by
  rw [(genLeonardo_binomial_steps 1 1 0).2.2.1]
  decide

-- Step four for `M` at `k = 1`, `n = 1`, `r = 0`: both sides equal `20`.
example : ∑ i ∈ Finset.range (1 + 1),
    (Nat.choose 1 i : ℤ) * genLeonardoCompanion 1 (4 * i + 0)
    = 3 ^ 1 * genLeonardoCompanion 1 (2 * 1 + 0) + 2 * 1 * (3 ^ 1 - 2 ^ 1) :=
  (genLeonardo_binomial_steps 1 1 0).2.2.2

example : ∑ i ∈ Finset.range (1 + 1),
    (Nat.choose 1 i : ℤ) * genLeonardoCompanion 1 (4 * i + 0) = 20 := by
  rw [(genLeonardo_binomial_steps 1 1 0).2.2.2]
  decide

end MathlibExtTest.NumberTheory.GenLeonardoGenLeonardoBinomialSteps
