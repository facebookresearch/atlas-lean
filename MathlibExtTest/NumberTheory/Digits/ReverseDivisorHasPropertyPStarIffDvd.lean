/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.Digits.ReverseDivisorHasPropertyPStarIffDvd

namespace MathlibExtTest.NumberTheory.Digits.ReverseDivisorHasPropertyPStarIffDvd

open MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

example : HasPropertyPStar 33 :=
  (hasPropertyPStar_iff_dvd 33 (by decide)).mpr (by decide)

example : ¬ HasPropertyPStar 7 := by
  intro h
  have h7 := (hasPropertyPStar_iff_dvd 7 (by decide)).mp h
  exact (by decide : ¬ 7 ∣ 99) h7

example : Nat.reverseDigits 10 330 = 33 ∧ 33 ∣ Nat.reverseDigits 10 330 :=
  ⟨by decide, (hasPropertyPStar_iff_dvd 33 (by decide)).mpr (by decide) 330 (by decide)⟩

example : HasPropertyPStar 0 ∧ ¬ 0 ∣ 99 := by
  refine ⟨?_, by decide⟩
  intro m hm
  obtain rfl := Nat.zero_dvd.mp hm
  decide

end MathlibExtTest.NumberTheory.Digits.ReverseDivisorHasPropertyPStarIffDvd
