/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFermatExponents

open MetaMathlibExt

-- All three exponent multipliers can be greater than one in the soluble case.
example : {xyz : ℤ × ℤ × ℤ | xyz.1 ≠ 0 ∧ xyz.2.1 ≠ 0 ∧ xyz.2.2 ≠ 0 ∧
    xyz.1 ^ 15 + xyz.2.1 ^ 12 = xyz.2.2 ^ 14}.Infinite :=
  (generalizedFermat_three_six_two_mul (s := 5) (t := 2) (w := 7)
    (by decide) (by decide) (by decide)).1 (by decide)

-- Each excluded condition can fail while the other conditions hold.
example : ¬ GeneralizedFermatSolvable 6 6 2 :=
  (generalizedFermat_three_six_two_mul (s := 2) (t := 1) (w := 1)
    (by decide) (by decide) (by decide)).2 (by decide)

example : ¬ GeneralizedFermatSolvable 3 6 6 :=
  (generalizedFermat_three_six_two_mul (s := 1) (t := 1) (w := 3)
    (by decide) (by decide) (by decide)).2 (by decide)

example : ¬ GeneralizedFermatSolvable 15 30 2 :=
  (generalizedFermat_three_six_two_mul (s := 5) (t := 5) (w := 1)
    (by decide) (by decide) (by decide)).2 (by decide)

example : ¬ GeneralizedFermatSolvable 15 6 10 :=
  (generalizedFermat_three_six_two_mul (s := 5) (t := 1) (w := 5)
    (by decide) (by decide) (by decide)).2 (by decide)

example : ¬ GeneralizedFermatSolvable 3 30 10 :=
  (generalizedFermat_three_six_two_mul (s := 1) (t := 5) (w := 5)
    (by decide) (by decide) (by decide)).2 (by decide)
