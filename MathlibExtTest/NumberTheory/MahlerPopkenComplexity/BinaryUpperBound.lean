/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MahlerPopkenComplexity.BinaryUpperBound

namespace MathlibExt.NumberTheory.MahlerPopkenComplexityWanted

-- The bound is attained at its lower endpoint, the single leaf for two.
example : mahlerPopkenComplexity 2 2 = 1 :=
  le_antisymm (mahlerPopkenComplexity_two_le_log_add_digitCount_sub_one 2 (by decide))
    (mahlerPopkenComplexity_pos (by decide) (by decide))

-- A power of two contributes only its leading one.
example : mahlerPopkenComplexity 2 16 ≤ 4 :=
  mahlerPopkenComplexity_two_le_log_add_digitCount_sub_one 16 (by decide)

-- The binary expansion 1101 contributes two ones after its leading digit.
example : mahlerPopkenComplexity 2 13 ≤ 5 :=
  mahlerPopkenComplexity_two_le_log_add_digitCount_sub_one 13 (by decide)

end MathlibExt.NumberTheory.MahlerPopkenComplexityWanted
