/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.FibonacciIccanobiF

/-! # Tests for the Fibonacci and iccanobiF iterates of a -/

open MetaMathlibExt

-- At the first admissible index the common words are ababa and baab.
example :
    [true, false] ++ (fibWord 2).map (!·) = [true, false, true, false, true] ∧
      [false, true] ++ (fibWord 1).map (!·) = [false, true, true, false] :=
  fibonacci_iccanobiF_conjugate_a 1 (by decide)

-- At the third iterate the Fibonacci word is abaab and the backward word is baaba.
example : (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[3]
    [true] = [false, true, true, false, true] := by
  apply List.append_cancel_right (bs := [true, false])
  exact (fibonacci_iccanobiF_conjugate_a 2 (by decide)).2.symm
