/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GenLeonardoCross

/-! # Tests for `MathlibExt.NumberTheory.GenLeonardoCross` -/

namespace MathlibExtTest.GenLeonardoCross

open MetaMathlibExt

/-- The identity of `genLeonardo_cross`, without its hypothesis. -/
private abbrev CrossIdentity (k : ℤ) (n : ℕ) : Prop :=
  genLeonardo k n * genLeonardoCompanion k (n + 1)
      - genLeonardo k (n + 1) * genLeonardoCompanion k (n - 1)
    = (k + 1) * genLeonardo k (2 * n) - k * genLeonardo k n + k

example (k : ℤ) (n : ℕ) (hn : 1 ≤ n) : CrossIdentity k n :=
  genLeonardo_cross k n hn

-- At `k = 1`, `n = 3`, both sides equal `46`.
example : CrossIdentity 1 3 := by decide

-- At `k = -2`, `n = 2`, both sides equal `1`.
example : CrossIdentity (-2) 2 := by decide

-- The boundary case `n = 1`: both sides equal `(k + 1) * (2 + k)`.
example (k : ℤ) : CrossIdentity k 1 := genLeonardo_cross k 1 (by decide)

-- The hypothesis `1 ≤ n` cannot be dropped: at `k = -2`, `n = 0` the two sides are
-- `-2` and `-1`, because `n - 1` truncates to `0`.
example : ¬ CrossIdentity (-2) 0 := by decide

end MathlibExtTest.GenLeonardoCross
