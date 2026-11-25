/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.Finite.OrderedPartitionCongruence

namespace MetaMathlibExt.OrderedPartitionCongruenceTest

open Finset

-- The largest permitted length for p = 5, with a nonempty sum and 4 ∤ t.
example : 5 ∣ ∑ j ∈ Icc 1 15,
    ∑ ω ∈ (Fintype.piFinset fun _ : Fin 3 => Icc 1 21).filter
        (fun ω => ∑ i, ω i = j * 4), (∏ i, ω i) ^ 3 :=
  prime_dvd_sum_compositions_prod_pow (k := 21) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- For p = 3 and t = 2, the extra divisibility hypothesis holds at k = 19.
example : 3 ∣ ∑ j ∈ Icc 1 9,
    ∑ ω ∈ (Fintype.piFinset fun _ : Fin 1 => Icc 1 19).filter
        (fun ω => ∑ i, ω i = j * 2), (∏ i, ω i) ^ 2 :=
  prime_dvd_sum_compositions_prod_pow (k := 19) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- Without the extra factor of 3 in k - 1, the sum of even squares is 56 ≡ 2 (mod 3).
example : (∑ j ∈ Icc 1 3,
    ∑ ω ∈ (Fintype.piFinset fun _ : Fin 1 => Icc 1 7).filter
        (fun ω => ∑ i, ω i = j * 2), (∏ i, ω i) ^ 2) = 56 := by
  decide

-- At s = p - 1 the single tuple (1, 1) contributes 1 modulo 3.
example : (∑ j ∈ Icc 1 1,
    ∑ ω ∈ (Fintype.piFinset fun _ : Fin 2 => Icc 1 1).filter
        (fun ω => ∑ i, ω i = j * 2), (∏ i, ω i) ^ 1) = 1 := by
  decide

end MetaMathlibExt.OrderedPartitionCongruenceTest
