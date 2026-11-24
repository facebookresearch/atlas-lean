/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NineRegularPartitionIteration

namespace MetaMathlibExt.card_nine_regular_iterate_modEq

private abbrev regularCount (n : ℕ) : ℤ := (Nat.Partition.restricted n (¬ 9 ∣ ·)).card

-- At s = 1 the three residue classes start with the partitions of 1, 2, and 3.
example : regularCount 1 ≡ 1 [ZMOD 3] ∧ regularCount 2 ≡ 2 [ZMOD 3] ∧
    regularCount 3 ≡ 0 [ZMOD 3] :=
  (card_nine_regular_iterate_modEq (r := 1) (s := 1) (hr := by decide) (hs := by decide)).2

-- Two iterations carry 4 to 69, and the three initial values to 21, 37, and 53.
example : regularCount 69 ≡ regularCount 4 [ZMOD 3] ∧ regularCount 21 ≡ 1 [ZMOD 3] ∧
    regularCount 37 ≡ 2 [ZMOD 3] ∧ regularCount 53 ≡ 0 [ZMOD 3] :=
  card_nine_regular_iterate_modEq (r := 4) (s := 3) (hr := by decide) (hs := by decide)

end MetaMathlibExt.card_nine_regular_iterate_modEq
