/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FibonacciAlternatingSums

namespace MetaMathlibExt.fibonacciAlternatingSum_tempered

-- The neighboring values at the first index covered by the theorem.
example : fibonacciAlternatingSum 11 = 56 ∧ fibonacciAlternatingSum 12 = 88 ∧
    fibonacciAlternatingSum 13 = 145 := by decide

example : 12 * fibonacciAlternatingSum 12 ^ 2 ≤
      13 * (fibonacciAlternatingSum 11 * fibonacciAlternatingSum 13) ∧
    12 * (fibonacciAlternatingSum 11 * fibonacciAlternatingSum 13) ≤
      13 * fibonacciAlternatingSum 12 ^ 2 :=
  fibonacciAlternatingSum_tempered 12 (by decide)

-- At index 10 the upper bound on the quotient fails.
example : 11 * fibonacciAlternatingSum 10 ^ 2 <
    10 * (fibonacciAlternatingSum 9 * fibonacciAlternatingSum 11) := by decide

end MetaMathlibExt.fibonacciAlternatingSum_tempered
