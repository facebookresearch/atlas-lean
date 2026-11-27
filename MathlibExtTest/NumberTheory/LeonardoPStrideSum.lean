/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoPStrideSum

namespace MathlibExt.NumberTheory.LeonardoPWanted

-- The branch with `m < p` starts in the initial block and then adds the term at index four.
example : ∑ i ∈ Finset.range (0 + 1), leonardoPK 2 3 ((2 + 1) * i + 1) = 1 := by
  rw [sum_leonardoPK_stride 2 3 1 0 (by decide) (by decide) (by decide)]
  decide

example : ∑ i ∈ Finset.range (1 + 1), leonardoPK 2 3 ((2 + 1) * i + 1) = 10 := by
  rw [sum_leonardoPK_stride 2 3 1 1 (by decide) (by decide) (by decide)]
  decide

-- At `m = p` the shifted endpoint crosses the initial block even for `n = 0`.
example : ∑ i ∈ Finset.range (0 + 1), leonardoPK 2 3 ((2 + 1) * i + 2) = 1 := by
  rw [sum_leonardoPK_stride 2 3 2 0 (by decide) (by decide) (by decide)]
  decide

example : ∑ i ∈ Finset.range (1 + 1), leonardoPK 2 3 ((2 + 1) * i + 2) = 14 := by
  rw [sum_leonardoPK_stride 2 3 2 1 (by decide) (by decide) (by decide)]
  decide

end MathlibExt.NumberTheory.LeonardoPWanted
