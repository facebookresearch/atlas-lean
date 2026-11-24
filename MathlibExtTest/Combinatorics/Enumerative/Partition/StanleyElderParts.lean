/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.StanleyElderParts

namespace MetaMathlibExt.nColor_evenParts_generatingFunction

-- The empty partition contributes no even parts.
example : (∑ s ∈ nColorPartitions 0, (s.filter fun p => Even p.1).card) = 0 := by
  decide

-- At size two there is one occurrence of each color.
example : (∑ s ∈ nColorPartitions 2, (s.filter fun p => Even p.1).card) = 2 := by
  decide +kernel

-- At size four, the shapes 4, 2+2 and 2+1+1 contribute 4, 6 and 2 occurrences.
example : (∑ s ∈ nColorPartitions 4, (s.filter fun p => Even p.1).card) = 12 := by
  decide +kernel

end MetaMathlibExt.nColor_evenParts_generatingFunction
