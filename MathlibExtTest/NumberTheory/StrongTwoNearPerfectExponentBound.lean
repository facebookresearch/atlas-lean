/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.StrongTwoNearPerfectExponentBound

namespace MetaMathlibExt

-- The strict bound is sharp: k = 2 * a - 1.
example : (5 : ℕ) < 2 * 3 :=
  lt_two_mul_of_strong_two_near_perfect_form (a := 3) (k := 5) (p := 11)
    (by decide) (by decide) (by decide)

end MetaMathlibExt
