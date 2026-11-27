/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Ring.SumsOfSquares

example {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    {p : R} (hp : IsSumSq p) : IsSumSq (f p) := by
  exact hp.map f

#print axioms IsSumSq.map
