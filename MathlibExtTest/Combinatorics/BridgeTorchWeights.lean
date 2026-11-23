/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.BridgeTorchWeights

namespace MetaMathlibExt.BridgeTorchGeneralizations

open Finset

example : bridgeWeight 0 = 0 := rfl

-- A two-person crossing incurs one surcharge, with the slower crossing time as the maximum.
example (n : ℕ) (hn : 1 < n) :
    bridgeWeight 1 + bridgeWeight n + 9 / 2 ≤ n + (1 + (n : ℚ)) := by
  have hn0 : 0 ≠ n := by omega
  have h := bridgeWeight_local_inequality {1, n} (insert_nonempty _ _)
    (card_le_two.trans (by decide)) (by simp [hn0])
  simpa [hn.ne, max_eq_right hn.le, show (2 : ℚ) - 1 = 1 by decide +kernel] using h

-- Equality can occur among the exceptional weights and among the first three affine weights.
example :
    (∑ i ∈ ({1, 5, 6} : Finset ℕ), bridgeWeight i) + 9 = 6 + (1 + 5 + 6 : ℚ) := by
  decide +kernel

example :
    (∑ i ∈ ({7, 8, 9} : Finset ℕ), bridgeWeight i) + 9 = 9 + (7 + 8 + 9 : ℚ) := by
  decide +kernel

end MetaMathlibExt.BridgeTorchGeneralizations
