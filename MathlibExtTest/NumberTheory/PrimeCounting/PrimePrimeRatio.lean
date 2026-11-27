/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.PrimePrimeRatio

/-! # Tests for the asymptotic `p_n ~ n log n` of the zero-based `n`-th prime -/

-- The statement is the equivalence of the cast `n`-th prime with `n * log n` along `atTop`.
example : Asymptotics.IsEquivalent Filter.atTop
    (fun n : ℕ => ((Nat.nth Nat.Prime n : ℕ) : ℝ)) (fun n : ℕ => (n : ℝ) * Real.log n) :=
  MetaMathlibExt.nth_prime_isEquivalent_mul_log

-- It bounds the `n`-th prime by a constant multiple of `n * log n` for large `n`.
example : Asymptotics.IsBigO Filter.atTop
    (fun n : ℕ => ((Nat.nth Nat.Prime n : ℕ) : ℝ)) (fun n : ℕ => (n : ℝ) * Real.log n) :=
  MetaMathlibExt.nth_prime_isEquivalent_mul_log.isBigO
