/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminMassReversal

/-! # Tests for reversal symmetry of the Gauss–Kuzmin mass -/

open MetaMathlibExt

example (a : List ℕ) (ha : ∀ x ∈ a, 0 < x) :
    gaussKuzminMass a.reverse = gaussKuzminMass a :=
  gaussKuzminMass_reverse a ha

-- The positivity hypothesis is vacuous for the empty string.
example : gaussKuzminMass ([] : List ℕ).reverse = gaussKuzminMass [] :=
  gaussKuzminMass_reverse [] (by decide)

-- Non-palindromes of even and odd length exercise both endpoint orders.
example : gaussKuzminMass [2, 1] = gaussKuzminMass [1, 2] :=
  gaussKuzminMass_reverse [1, 2] (by decide)

example : gaussKuzminMass [3, 1, 2] = gaussKuzminMass [2, 1, 3] :=
  gaussKuzminMass_reverse [2, 1, 3] (by decide)
