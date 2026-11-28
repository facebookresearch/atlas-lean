/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SetPartitionPeaks

open MetaMathlibExt.symmetricPeaks_derivative_generatingFunction

-- The empty alphabet admits exactly the empty word.
example : (partitionWords 0 0).card = 1 ∧ (partitionWords 1 0).card = 0 := by
  simp [card_partitionWords]

-- Of the three two-block words of length three, 001 and 011 end in 1.
-- The last letter is new in the first word and repeated in the second.
example : ∑ w ∈ partitionWords 3 2, (w (Fin.last 2)).val = 2 := by
  rw [sum_partitionWords_snoc 2 1]
  decide
