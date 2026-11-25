/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.SquareTriangularAdditiveUniqueness

-- At the lower endpoint the smaller triangular number has index zero.
example : (2 : ℕ) ^ 2 + 0 = 1 ^ 2 + 3 :=
  MetaMathlibExt.sq_add_triangular_sub_two_eq 2 (by decide)
