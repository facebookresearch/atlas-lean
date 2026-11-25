/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.HyperLeonardoPRec
import Mathlib.Tactic.NormNum

/-!
# Tests for the recurrence for the hyper Leonardo `p`-numbers
-/

open MetaMathlibExt

-- The recurrence at a triple where `n` is divisible by `p + 1`, the case
-- in which the first sum acquires an extra zero summand.
example : hyperLeonardoP 1 2 1 =
    hyperLeonardoP 1 1 1 + hyperLeonardoP 1 2 0 :=
  (hyperLeonardoP_rec 1 (by decide)).1 2 1 (by decide) (by decide)

-- The recurrence at an ordinary triple.
example : hyperLeonardoP 2 4 2 =
    hyperLeonardoP 2 3 2 + hyperLeonardoP 2 4 1 :=
  (hyperLeonardoP_rec 2 (by decide)).1 4 2 (by decide) (by decide)

-- At order zero the hyper Leonardo `p`-numbers are the Leonardo `p`-numbers.
example : hyperLeonardoP 2 4 0 =
    MathlibExt.NumberTheory.LeonardoPWanted.leonardoPK 2 2 4 :=
  (hyperLeonardoP_rec 2 (by decide)).2 4

-- Concrete values, including the order-zero value above.
example : hyperLeonardoP 2 3 1 = 7 ∧ hyperLeonardoP 1 4 0 = 9 := by
  norm_num [hyperLeonardoP, Finset.sum_range_succ, Nat.choose]
