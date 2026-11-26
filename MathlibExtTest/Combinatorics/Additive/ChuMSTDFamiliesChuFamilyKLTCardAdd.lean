/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTCardAdd
import Mathlib.Tactic.Linarith

namespace MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTCardAdd

open MetaMathlibExt Pointwise

example : 35 ≤ (chuFamilyKLT 1 1 1 + chuFamilyKLT 1 1 1).card := by
  simpa using chuFamilyKLT_card_add (k := 1) (l := 1) (t := 1)
    (by decide) (by decide) (by decide)

example {k l t : ℕ} (hk : 0 < k) (hl : 0 < l) (ht : 0 < t) :
    11 + 6 * k * l * t + 8 * l * t + 8 * t <
      (chuFamilyKLT k l t + chuFamilyKLT k l t).card := by
  have h := chuFamilyKLT_card_add hk hl ht
  have hlt : 0 < l * t := Nat.mul_pos hl ht
  nlinarith only [h, hlt]

end MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyKLTCardAdd
