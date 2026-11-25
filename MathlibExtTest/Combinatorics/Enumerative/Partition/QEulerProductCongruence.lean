/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProductCongruence

open PowerSeries

namespace MetaMathlibExt

-- Shifting all prime factors into the index leaves the first power of the prime as modulus.
example (n : ℕ) : coeff n (qEulerProduct 2 ^ 9) ≡ coeff n (qEulerProduct 18) [ZMOD 3] := by
  simpa using qEulerProduct_iterated_primePower_congruence 3 2 2 2 1
    (by decide) (by decide) (by decide) (by decide) (by decide) n

-- A partial shift with multiplier three gives divisibility of the coefficient difference by eight.
example (n : ℕ) :
    (8 : ℤ) ∣ coeff n (qEulerProduct 12 ^ 12) - coeff n (qEulerProduct 3 ^ 48) :=
  (qEulerProduct_iterated_primePower_congruence 2 4 3 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) n).dvd

end MetaMathlibExt
