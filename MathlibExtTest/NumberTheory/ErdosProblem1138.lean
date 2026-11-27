/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ErdosProblem1138
import Mathlib.Tactic.NormNum

/-! # Endpoint tests for Vardi's prime-gap asymptotic -/

namespace MathlibExt.NumberTheory.ErdosProblem1138Wanted.Tests

-- The starting prime must be strictly below x.
example : supPrimeGap 2 = 0 := by
  norm_num [supPrimeGap, show Nat.primeCounting' 2 = 0 by decide]

example : supPrimeGap 3 = 1 := by
  norm_num [supPrimeGap, show Nat.primeCounting' 3 = 1 by decide, primeGap]

-- A nonintegral cutoff includes the gap starting at 3 even though it ends at 5.
private theorem gap_at_nine_halves : supPrimeGap (9 / 2) = 2 := by
  have hceil : ⌈(9 / 2 : ℝ)⌉₊ = 5 :=
    (Nat.ceil_eq_iff (by decide)).2 (by norm_num)
  rw [supPrimeGap, hceil, show Nat.primeCounting' 5 = 2 by decide]
  rw [show Finset.range 2 = insert 1 {0} by decide, Finset.sup_insert, Finset.sup_singleton]
  norm_num [primeGap]

-- The first window (3,6] excludes 3. The second window (4,7] includes 7.
example : primeCountIocMulConst (3 / 2) (9 / 2, 3) = 1 := by
  norm_num [primeCountIocMulConst, gap_at_nine_halves,
    show Nat.primeCounting 3 = 2 by decide, show Nat.primeCounting 6 = 3 by decide]

example : primeCountIocMulConst (3 / 2) (9 / 2, 4) = 2 := by
  norm_num [primeCountIocMulConst, gap_at_nine_halves,
    show Nat.primeCounting 4 = 2 by decide, show Nat.primeCounting 7 = 4 by decide]

example : disprovedVardi := vardiAsymptotic_refuted

end MathlibExt.NumberTheory.ErdosProblem1138Wanted.Tests
