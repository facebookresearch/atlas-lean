/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.FibonacciIccanobiF

/-! # Tests for the Fibonacci and iccanobiF iterates of a and b -/

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

-- At the first admissible index the iccanobiF iterates of b are aba and ba, so the identities
-- read ababa = aba·ba and baab = ba·ab.
example :
    [true, false] ++ (fibWord 2).map (!·) = [true, false, true] ++ [false, true] ∧
      [false, true] ++ (fibWord 1).map (!·) = [false, true] ++ [true, false] :=
  fibonacci_iccanobiF_conjugate_b 1 (by decide)

-- At n = 2 the fourth iterate of b is baaba, read off from ba·abaab = baaba·ab.
example : (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[4]
    [false] = [false, true, true, false, true] := by
  apply List.append_cancel_right (bs := [true, false])
  exact (fibonacci_iccanobiF_conjugate_b 2 (by decide)).2.symm

-- Together with the identities for a, the (2n + 1)-st iterate of b is the 2n-th iterate of a.
example (n : ℕ) (hn : 1 ≤ n) :
    (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[2 * n + 1]
        [false] =
      (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[2 * n]
        [true] :=
  List.append_cancel_right <|
    (fibonacci_iccanobiF_conjugate_b n hn).1.symm.trans (fibonacci_iccanobiF_conjugate_a n hn).1

-- At n = 3 both identities also hold by evaluation, on words of 23 and 15 letters.
example :
    [true, false] ++ (fibWord 6).map (!·) =
        (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[7]
          [false] ++ [false, true] ∧
      [false, true] ++ (fibWord 5).map (!·) =
        (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[6]
          [false] ++ [true, false] := by
  decide

-- The hypothesis 1 ≤ n is needed: at n = 0, 2 * n - 1 truncates to 0 and the second identity
-- fails, since baa ≠ bab.
example :
    [false, true] ++ (fibWord (2 * 0 - 1)).map (!·) ≠
      (fun u : List Bool => u.flatMap fun x => if x then [false, true] else [true])^[2 * 0]
        [false] ++ [true, false] := by
  decide
