/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.OddSquareTriangular

namespace MetaMathlibExt

example (x : ℕ) (hx : Odd x) :
    ∃ k : ℕ, (x ^ 2 - 1) / 8 = Nat.polygonalNumber 3 k :=
  sq_sub_one_div_eight_eq_triangular (x := x) (hx := hx)

example : ((1 : ℕ) ^ 2 - 1) / 8 = Nat.polygonalNumber 3 0 := by decide

example : ((7 : ℕ) ^ 2 - 1) / 8 = Nat.polygonalNumber 3 3 := by decide

end MetaMathlibExt
