/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.NColorEvenPartsDivisorSum

namespace MetaMathlibExt

-- The smallest positive size has no even parts.
example : (∑ s ∈ nColorPartitions 1, (s.filter fun p => Even p.1).card) = 0 := by
  rw [nColor_evenParts_eq_sum_sigmaEven 1 (by decide)]
  decide

-- At `k = 4`, count one removed part of size 4 or two of size 2 (of the same color).
example : (∑ s ∈ nColorPartitions 4, (s.filter fun p => Even p.1).card) = 12 := by
  rw [nColor_evenParts_eq_sum_sigmaEven 4 (by decide)]
  decide +kernel

-- The odd total size permits even parts, but has no contribution from `k = 5`.
example : (∑ s ∈ nColorPartitions 5, (s.filter fun p => Even p.1).card) = 18 := by
  rw [nColor_evenParts_eq_sum_sigmaEven 5 (by decide)]
  decide +kernel

end MetaMathlibExt
