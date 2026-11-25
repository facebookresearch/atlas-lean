/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NarayanaRiesel

/-! Test a representative index and a shifted index at an exponent divisible by 24. -/

open MetaMathlibExt

example : IsRieselNumber (narayanaCowsSequence 3629412) :=
  isRieselNumber_narayanaCowsSequence (by decide)

example : ¬ (narayanaCowsSequence (703725732 + 718391520) * 2 ^ 24 - 1).Prime :=
  (isRieselNumber_narayanaCowsSequence (t := 703725732 + 718391520) (by decide)).2 24 (by decide)
