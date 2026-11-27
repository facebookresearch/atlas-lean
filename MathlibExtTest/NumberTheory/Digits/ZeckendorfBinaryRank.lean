/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ZeckendorfBinaryRank

namespace MetaMathlibExt

-- The empty support gives an empty range.
example : ((Finset.range 0).filter (fun n => n &&& (n >>> 1) = 0)).card = 0 := by
  calc
    _ = _ := card_zeckendorfBinary_lt_sum_two_pow ∅
    _ = 0 := by decide

-- With no adjacent bits, every set bit contributes a Fibonacci term.
example : ((Finset.range 21).filter (fun n => n &&& (n >>> 1) = 0)).card = 12 := by
  calc
    _ = _ := card_zeckendorfBinary_lt_sum_two_pow {0, 2, 4}
    _ = 12 := by decide

-- The journal example has one adjacent pair: the bit at index 2 contributes nothing.
example : ((Finset.range 100).filter (fun n => n &&& (n >>> 1) = 0)).card = 34 := by
  calc
    _ = _ := card_zeckendorfBinary_lt_sum_two_pow {2, 5, 6}
    _ = 34 := by decide

-- Only the highest adjacent pair sets the cutoff, and a separated higher bit still contributes.
example : ((Finset.range 91).filter (fun n => n &&& (n >>> 1) = 0)).card = 34 := by
  calc
    _ = _ := card_zeckendorfBinary_lt_sum_two_pow {0, 1, 3, 4, 6}
    _ = 34 := by decide

end MetaMathlibExt
