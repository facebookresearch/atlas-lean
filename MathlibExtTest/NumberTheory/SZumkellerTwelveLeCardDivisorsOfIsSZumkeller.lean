/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.SZumkellerTwelveLeCardDivisorsOfIsSZumkeller

namespace MathlibExtTest.NumberTheory.SZumkellerTwelveLeCardDivisorsOfIsSZumkeller

-- 60 is an even s-Zumkeller number, so it has at least twelve divisors.
example : 12 ≤ (Nat.divisors 60).card :=
  MetaMathlibExt.twelve_le_card_divisors_of_isSZumkeller 60
    MetaMathlibExt.isSZumkeller_sixty (by decide)

-- The bound is tight at 60, which has exactly twelve divisors.
example : (Nat.divisors 60).card = 12 := by
  have hle := MetaMathlibExt.twelve_le_card_divisors_of_isSZumkeller 60
    MetaMathlibExt.isSZumkeller_sixty (by decide)
  have hge : (Nat.divisors 60).card ≤ 12 := by decide
  exact le_antisymm hge hle

end MathlibExtTest.NumberTheory.SZumkellerTwelveLeCardDivisorsOfIsSZumkeller
