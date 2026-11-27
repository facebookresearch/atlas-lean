/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Digits.ReverseDivisorHasPropertyPStarOfDvd

namespace MathlibExtTest.NumberTheory.Digits.ReverseDivisorHasPropertyPStarOfDvd

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

-- Both `9` and `11` divide `99`, so both have property `P*`.
example : HasPropertyPStar 9 :=
  hasPropertyPStar_of_dvd 9 (by decide)

example : HasPropertyPStar 11 :=
  hasPropertyPStar_of_dvd 11 (by decide)

-- Hence `99` itself has property `P*`.
example : HasPropertyPStar 99 :=
  hasPropertyPStar_of_dvd 99 dvd_rfl

-- So `99` divides the reversal of each of its multiples.
example (m : ℕ) (hm : 99 ∣ m) : 99 ∣ Nat.reverseDigits 10 m :=
  hasPropertyPStar_of_dvd 99 dvd_rfl m hm

end MathlibExtTest.NumberTheory.Digits.ReverseDivisorHasPropertyPStarOfDvd
