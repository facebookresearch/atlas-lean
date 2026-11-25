/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SingletonSumFreeMod

namespace MetaMathlibExt

-- `a = 2` is divisible by the prime but not by the modulus `2 ^ 2`.
example : IsSumFreeMod (2 ^ 2) 2 {(2 : ℤ)} :=
  isSumFreeMod_singleton_prime_pow 2 2 2 2 (by decide) (by decide) (by decide)
    (by decide) (by decide)

end MetaMathlibExt
