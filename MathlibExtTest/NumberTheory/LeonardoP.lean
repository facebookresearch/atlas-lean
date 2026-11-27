/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LeonardoP

namespace MathlibExt.NumberTheory.LeonardoPWanted

-- Cross the initial block and reach the first step with two noninitial summands.
example : leonardoPKSeq 2 3 6 = [1, 1, 1, 5, 9, 13, 21] := by decide

-- The integer extension crosses from −k to 1 at zero and agrees with later natural terms.
example : (leonardoPKZ 2 3 (-1), leonardoPKZ 2 3 0, leonardoPKZ 2 3 3) = (-3, 1, 5) := by
  decide

-- The sum through index four includes the term at index four.
example : ∑ i ∈ Finset.range 5, leonardoPK 2 3 i = 17 := by
  rw [sum_leonardoPK 2 3 4 (by decide) (by decide)]
  decide

end MathlibExt.NumberTheory.LeonardoPWanted
