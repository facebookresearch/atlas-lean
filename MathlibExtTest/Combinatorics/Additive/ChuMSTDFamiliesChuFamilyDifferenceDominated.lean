/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyDifferenceDominated

namespace MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyDifferenceDominated

open scoped Pointwise
open MetaMathlibExt

example :
    let A : Finset ℤ := {0, 1, 2, 4, 5, 9, 12, 13, 17, 21, 24, 25, 29, 33, 36, 37, 38}
    (A + A).card < (A - A).card := by
  have hA : setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock 1 ++ chuBlock 2 ++ chuBlock 2 ++ [1, 1]) =
        ({0, 1, 2, 4, 5, 9, 12, 13, 17, 21, 24, 25, 29, 33, 36, 37, 38} : Finset ℤ) := by
    decide
  simpa only [hA] using chu_family_difference_dominated (k := 1) (by decide)

example {k : ℕ} (hk : 0 < k) :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock k ++ chuBlock (k + 1) ++ chuBlock (k + 1) ++ [1, 1])
    (A + A).card + 1 ≤ (A - A).card :=
  chu_family_difference_dominated hk

#check @MetaMathlibExt.chu_family_difference_dominated
#print axioms MetaMathlibExt.chu_family_difference_dominated

end MathlibExtTest.Combinatorics.Additive.ChuMSTDFamiliesChuFamilyDifferenceDominated
