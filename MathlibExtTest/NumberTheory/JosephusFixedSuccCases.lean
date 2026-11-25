/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusFixedSuccCases

open MetaMathlibExt MathlibExt.NumberTheory.JosephusWanted

-- Each step size has the same fixed point 2.
example : josephus 3 3 = 2 :=
  (josephus_fixed_succ_cases 3 2 (by decide) (by decide) (by decide)).1 (by decide)

example : josephus 7 3 = 3 :=
  (josephus_fixed_succ_cases 7 2 (by decide) (by decide) (by decide)).2.1 2 (by decide) rfl

example : josephus 5 3 = 1 :=
  (josephus_fixed_succ_cases 5 2 (by decide) (by decide) (by decide)).2.2.1 1 2
    (by decide) (by decide) (by decide) rfl

example : josephus 9 3 = 2 :=
  (josephus_fixed_succ_cases 9 2 (by decide) (by decide) (by decide)).2.2.2 2 (by decide) rfl
