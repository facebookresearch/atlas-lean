/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.ModEq
public import WantedExt.Combinatorics.Enumerative.OverpartitionsOddPartsWanted

namespace MetaMathlibExt

@[expose] public section

/--
For every natural `n`, `ped(225n+43)`, `ped(225n+88)`, `ped(225n+133)`, and
`ped(225n+223)` are each congruent to zero modulo `24`; the four clauses below encode
the four progressions in that order, with `ped` represented by
`distinctEvenPartsCount` and no deviation from the paper.
Source: Hemjyoti Nath, *New Congruences for Partitions Where the Even Parts Are Distinct*, INTEGERS 24 (2024), Article A79, Theorem 1.1.
-/
public theorem_wanted partitionsEvenPartsDistinct_mod24_progressions (n : ℕ) :
    Nat.ModEq 24 (distinctEvenPartsCount (225 * n + 43)) 0 ∧
      Nat.ModEq 24 (distinctEvenPartsCount (225 * n + 88)) 0 ∧
      Nat.ModEq 24 (distinctEvenPartsCount (225 * n + 133)) 0 ∧
      Nat.ModEq 24 (distinctEvenPartsCount (225 * n + 223)) 0

/--
For naturals `k` and `n` with `k ≥ 1`, `ped(9n+7)` is congruent modulo `24` to
`ped(9·5^(2k)n + (57·5^(2k) - 1)/8)`. The formal statement uses natural-number
division; it is exact because `57·5^(2k) - 1` is divisible by `8`.
Source: Hemjyoti Nath, *New Congruences for Partitions Where the Even Parts Are Distinct*, INTEGERS 24 (2024), Article A79, Theorem 1.1.
-/
public theorem_wanted partitionsEvenPartsDistinct_mod24_five_power
    (k n : ℕ) (hk : 1 ≤ k) :
    Nat.ModEq 24 (distinctEvenPartsCount (9 * n + 7))
      (distinctEvenPartsCount
        (9 * 5 ^ (2 * k) * n + (57 * 5 ^ (2 * k) - 1) / 8))

end

end MetaMathlibExt
