/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.CappedDiagonalSequences

namespace MetaMathlibExt

-- The staircase contributes its own one in addition to the capped copies.
example :
    (diagonalClassOf 4 (diagonalOfList [1, 1, 1, 1])).card =
      (diagonalClassOf 3 (diagonalOfList [1, 1, 1])).card := by
  exact card_diagonalClassOf_min_two 1 (by decide) (fun _ => 3)

-- Cap both the highest and lowest blocks, keeping a singleton block and a missing height.
example :
    (diagonalClassOf 28 (diagonalOfList [1, 2, 3, 4, 4, 4, 4, 2, 1, 1, 1, 1])).card =
      (diagonalClassOf 22 (diagonalOfList [1, 2, 3, 4, 4, 4, 2, 1, 1])).card := by
  exact card_diagonalClassOf_min_two 4 (by decide) (fun i => [0, 4, 1, 0, 3].getD i 0)

end MetaMathlibExt
