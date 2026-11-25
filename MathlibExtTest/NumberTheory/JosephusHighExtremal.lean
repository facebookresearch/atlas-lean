/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusHighExtremal

open MetaMathlibExt MathlibExt.NumberTheory.JosephusWanted

-- At the smallest allowed high extremal point, the final linear step lands on a fixed point.
example : josephus 2 3 = 3 :=
  josephus_add_eq_of_high 2 1 1 (by decide) (by decide) ⟨by decide, by decide⟩ (by decide)

-- Here the starting value is 2 and the floor bound is 9. The next step wraps back to 1.
example : josephus 3 30 = 29 ∧ josephus 3 31 = 1 :=
  ⟨josephus_add_eq_of_high 3 20 9 (by decide) (by decide) ⟨by decide, by decide⟩ (by decide),
    by decide⟩
