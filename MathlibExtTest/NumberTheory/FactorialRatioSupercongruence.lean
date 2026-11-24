/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/OEIS/211417.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import MathlibExt.NumberTheory.FactorialRatioSupercongruence

@[expose] public section

/-!
# Tests for `MathlibExt.NumberTheory.FactorialRatioSupercongruence`

The term tests are the ones carried by `FormalConjectures/OEIS/211417.lean`.
-/

namespace MathlibExtTest.NumberTheory.FactorialRatioSupercongruence

open OeisA211417

-- Source faithfulness: the Formal Conjectures statement `OeisA211417.supercongruence`,
-- verbatim.
example (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ)) :=
  supercongruence p k hp hp5 hk

example : a 0 = 1 := by rfl
example : a 1 = 77636318760 := by rfl

-- A concrete instance of the supercongruence, as a statement about `a 25` and `a 5`
-- (the values themselves are far too large to evaluate here).
example : (5 : ℤ) ^ 6 ∣ ((a (5 ^ 2) : ℤ) - (a (5 ^ 1) : ℤ)) :=
  supercongruence 5 2 (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.NumberTheory.FactorialRatioSupercongruence
