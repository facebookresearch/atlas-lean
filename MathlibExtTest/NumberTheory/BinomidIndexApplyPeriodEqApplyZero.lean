/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomidIndexApplyPeriodEqApplyZero

/-!
# Tests for periodicity of lex-minimal extensions

The zero-index equality extends tail periodicity to every index.
-/

namespace MathlibExtTest.NumberTheory.BinomidIndexApplyPeriodEqApplyZero

open MetaMathlibExt

example {η : ℕ → ℕ} (hη : IsLexMinimalExtension η) {p : ℕ} (hp : 0 < p)
    (hper : ∀ i, 1 ≤ i → η (i + p) = η i) : ∀ i, η (i + p) = η i := by
  intro i
  cases i with
  | zero => simpa using hη.apply_period_eq_apply_zero hp hper
  | succ i => exact hper (i + 1) (Nat.succ_le_succ (Nat.zero_le i))

end MathlibExtTest.NumberTheory.BinomidIndexApplyPeriodEqApplyZero
