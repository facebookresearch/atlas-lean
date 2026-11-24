/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.TruncateDiagonalSequences

namespace MetaMathlibExt

-- The shortest admissible tail has two ones after the staircase.
example :
    (diagonalClassOf 5 (diagonalOfList [1, 2, 1, 1])).card =
      (diagonalClassOf 3 (diagonalOfList [1, 1, 1])).card := by
  exact card_diagonalClassOf_truncate 2 1 (fun i => if i = 1 then 2 else 0)
    (by decide) (by decide) (by decide) (by decide)

-- Delete two staircase steps while retaining the lower block of ones.
example :
    (diagonalClassOf 15 (diagonalOfList [1, 2, 3, 4, 2, 2, 1])).card =
      (diagonalClassOf 8 (diagonalOfList [1, 2, 2, 2, 1])).card := by
  exact card_diagonalClassOf_truncate 4 2 (fun i => [0, 1, 2].getD i 0)
    (by decide) (by decide) (by decide) (by decide)

end MetaMathlibExt
