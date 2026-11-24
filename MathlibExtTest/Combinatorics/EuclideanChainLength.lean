/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.EuclideanChainLength
meta import MathlibExt.Combinatorics.EuclideanChainLength

/-!
# Tests for the Euclidean chain function

The two values of `euclideanChainLength_one_left_and_one_right` at small arguments, checked
against the defining recursion and the compiled function, with the edge cases $y = 0$ and $x = 0$.
The tests for `euclideanChainLength_add_mul` exercise zero arguments and addition of a
positive multiple in each position.
-/

open MetaMathlibExt

namespace MathlibExtTest.Combinatorics.EuclideanChainLength

-- The chain `1, 5, 4, 3, 2, 1, 0` has six positive terms.
example : euclideanChainLength 1 5 = 6 :=
  (euclideanChainLength_one_left_and_one_right 5 Nat.one_pos).1

-- The defining recursion alone gives the same value.
example : euclideanChainLength 1 5 = 6 := by
  simp [euclideanChainLength_of_ne_zero, euclideanChainLength_zero]

-- `y = 0` is allowed: the chain `1, 0` has one positive term.
example : euclideanChainLength 1 0 = 1 :=
  (euclideanChainLength_one_left_and_one_right 0 Nat.one_pos).1

-- The chain `7, 1, 0` has two positive terms.
example : euclideanChainLength 7 1 = 2 :=
  (euclideanChainLength_one_left_and_one_right 0 (by decide : 0 < 7)).2

-- The recursion also gives `F(0, 1) = 2`, so the second value does not need `0 < x`.
example : euclideanChainLength 0 1 = 2 := by
  simp [euclideanChainLength_of_ne_zero, euclideanChainLength_zero]

-- The compiled function agrees with both values on small arguments and with `F(13, 60) = 8`.
#guard (List.range 50).all fun y => euclideanChainLength 1 y == y + 1
#guard (List.range 50).all fun x => euclideanChainLength x 1 == 2
#guard euclideanChainLength 13 60 = 8

-- When `y = 0`, the second identity counts `k + 1` terms in `F(x, k * x)`.
example (x k : ℕ) (hx : 0 < x) : euclideanChainLength x (k * x) = 1 + k := by
  simpa only [Nat.add_zero, euclideanChainLength_zero] using
    (euclideanChainLength_add_mul hx 0 k).2

-- A zero multiple leaves both lengths unchanged.
example (x y : ℕ) (hx : 0 < x) :
    euclideanChainLength (x + 0 * y) y = euclideanChainLength x y ∧
      euclideanChainLength x (0 * x + y) = euclideanChainLength x y := by
  simpa only [Nat.zero_mul, Nat.zero_add, Nat.add_zero] using
    euclideanChainLength_add_mul hx y 0

-- With `k = 2`, the chain at `(13, 60)` keeps its length or gains two terms.
example : euclideanChainLength 133 60 = 8 ∧ euclideanChainLength 13 86 = 10 := by
  simpa only [euclideanChainLength_thirteen_sixty] using
    euclideanChainLength_add_mul (x := 13) (by decide) 60 2

#guard euclideanChainLength 133 60 == 8 && euclideanChainLength 13 86 == 10

-- The quotient is one when the arguments are equal, and four for `(3, 12)`.
example : euclideanChainLength 6 6 = 2 := by
  simpa using euclideanChainLength_of_dvd (x := 6) (y := 6) (by decide) (by decide) (by decide)

example : euclideanChainLength 3 12 = 5 := by
  simpa using euclideanChainLength_of_dvd (x := 3) (y := 12) (by decide) (by decide) (by decide)

end MathlibExtTest.Combinatorics.EuclideanChainLength
