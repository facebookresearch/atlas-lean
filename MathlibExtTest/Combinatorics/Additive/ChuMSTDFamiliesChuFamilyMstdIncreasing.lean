/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyMstdIncreasing

@[expose] public section

open MetaMathlibExt
open Pointwise

namespace MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyMstdIncreasing

-- Theorem 3 at `k = 1` with tail `(1, 1, 2)`: the set `(0 | 1, 1, 2, M^1, M^2, 1, 1, 2)`
-- is sum-dominated.
example :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock 1 ++ chuBlock 2 ++ [1, 1, 2])
    (A - A).card < (A + A).card :=
  chu_family_mstd_increasing (k := 1) (by decide) (Or.inl rfl)

-- Theorem 3 at `k = 1` with tail `(1, 1, 2, 1)`: the set `(0 | 1, 1, 2, M^1, M^2, 1, 1, 2, 1)`
-- is sum-dominated.
example :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock 1 ++ chuBlock 2 ++ [1, 1, 2, 1])
    (A - A).card < (A + A).card :=
  chu_family_mstd_increasing (k := 1) (by decide) (Or.inr rfl)

-- Theorem 3 at `k = 2` with tail `(1, 1, 2)`: the set `(0 | 1, 1, 2, M^2, M^3, 1, 1, 2)`
-- is sum-dominated.
example :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock 2 ++ chuBlock 3 ++ [1, 1, 2])
    (A - A).card < (A + A).card :=
  chu_family_mstd_increasing (k := 2) (by decide) (Or.inl rfl)

end MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyMstdIncreasing
