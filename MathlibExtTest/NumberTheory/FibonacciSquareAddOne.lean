/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FibonacciSquareAddOne

open MathlibExt.NumberTheory.ShakovTwoRegularWanted

-- The index immediately below the cutoff gives a prime.
example : Nat.Prime (Nat.fib 3 ^ 2 + 1) := by decide

-- The first even and odd indices in the theorem give 10 and 26.
example : Nat.IsComposite 10 := fib_sq_add_one_composite 4 (by decide)

example : Nat.IsComposite 26 := fib_sq_add_one_composite 5 (by decide)
