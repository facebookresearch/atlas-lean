/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusFixedPointIff

open MetaMathlibExt MathlibExt.NumberTheory.JosephusWanted

-- The converse applies at the lower endpoint `np = k - 1`.
example : josephus 3 2 = 2 :=
  (josephus_eq_self_iff 3 2 (by decide) (by decide)).mpr (by decide)

-- A fixed point strictly beyond the lower endpoint gives the predicted next value.
example : josephus 2 4 = 1 :=
  (josephus_eq_self_iff 2 3 (by decide) (by decide)).mp (by decide)

-- A step that does not wrap around does not give `k - 1`.
example : josephus 2 5 ≠ 1 := by
  intro h
  exact (by decide : josephus 2 4 ≠ 4)
    ((josephus_eq_self_iff 2 4 (by decide) (by decide)).mpr h)
