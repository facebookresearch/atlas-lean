/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.ColoredPartitionsDifferentColors

open Finset

namespace MetaMathlibExt.card_coloredPartitions_differentColors

-- The empty partition is excluded even when no parts are available.
example :
    (((Icc 1 0 ×ˢ Icc 1 0).filter (fun p : ℕ × ℕ => p.2 ≤ p.1)).powerset.filter
      (fun T => T.Nonempty ∧ (T.image Prod.snd).card = T.card)).card = 0 :=
  card_coloredPartitions_differentColors 0

-- At bound two, sizes may repeat, while colors must be distinct.
example :
    (((Icc 1 2 ×ˢ Icc 1 2).filter (fun p : ℕ × ℕ => p.2 ≤ p.1)).powerset.filter
      (fun T => T.Nonempty ∧ (T.image Prod.snd).card = T.card)) =
      {{(1, 1)}, {(2, 1)}, {(2, 2)}, {(1, 1), (2, 2)}, {(2, 1), (2, 2)}} := by
  decide

end MetaMathlibExt.card_coloredPartitions_differentColors
