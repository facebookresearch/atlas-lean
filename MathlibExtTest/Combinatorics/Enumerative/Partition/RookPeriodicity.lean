/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.RookPeriodicity

namespace MetaMathlibExt

-- Both parameters attain their lower bounds.
example : maxRookPartitionCount 3 16 ≡ maxRookPartitionCount 3 10 [MOD 2] :=
  maxRookPartitionCount_three_modEq 2 10 (by decide) (by decide)

-- A composite modulus sharing a factor with the step size three.
example : maxRookPartitionCount 3 29 ≡ maxRookPartitionCount 3 11 [MOD 6] :=
  maxRookPartitionCount_three_modEq 6 11 (by decide) (by decide)

end MetaMathlibExt
