/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.VnArrangementCountConsecutive

namespace MetaMathlibExt

-- A single integer has one vn-arrangement.
example : vnArrangementCount 1 (Finset.Ico (0 : ℤ) 1).val = 1 := by
  simpa using vnArrangementCount_consecutive (0 : ℤ) 1 (by decide)

-- Two consecutive integers have two vn-arrangements.
example : vnArrangementCount 1 (Finset.Ico (0 : ℤ) 2).val = 2 := by
  simpa using vnArrangementCount_consecutive (0 : ℤ) 2 (by decide)

-- Four consecutive integers, starting below zero, have eight vn-arrangements.
example : vnArrangementCount 1 (Finset.Ico (-2 : ℤ) 2).val = 8 := by
  simpa using vnArrangementCount_consecutive (-2 : ℤ) 4 (by decide)

-- Five consecutive integers have sixteen vn-arrangements, wherever they start.
example (a : ℤ) :
    vnArrangementCount 1 (Finset.Ico a (a + 5)).val = 16 := by
  simpa using vnArrangementCount_consecutive a 5 (by decide)

end MetaMathlibExt
