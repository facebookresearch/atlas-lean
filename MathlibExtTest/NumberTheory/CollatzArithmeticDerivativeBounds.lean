/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CollatzArithmeticDerivativeBounds
import Mathlib.Tactic.LinearCombination

open MetaMathlibExt

namespace MathlibExtTest.NumberTheory.CollatzArithmeticDerivativeBounds

-- The compatible semiprimes `1609 · 71` and `349 · 491` satisfy the factor bounds.
example : 241 ≤ 349 ∧ 241 ≤ 491 ∧ 3 * 71 < 349 ∧ 3 * 71 < 491 ∧ 349 < 3 * 1609 ∧
    491 < 3 * 1609 := by
  obtain ⟨hp, hq, hr, hs, hsum, hprod⟩ := isCompatibleSemiprimePair_71_1609
  have hswap : IsCompatibleSemiprimePair 1609 71 349 491 :=
    ⟨hq, hp, hr, hs, by omega, by linear_combination hprod⟩
  exact IsCompatibleSemiprimePair.bounds hswap (by decide)

end MathlibExtTest.NumberTheory.CollatzArithmeticDerivativeBounds
