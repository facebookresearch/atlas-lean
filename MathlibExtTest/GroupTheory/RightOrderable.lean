/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Order.Monoid.TypeTags
import Mathlib.Algebra.Order.Group.Int
import MathlibExt.GroupTheory.RightOrderable

open MathlibExt.GroupTheory.ResiduallyTwoPrimesNotRightOrderableKourovka10Problem30Wanted

-- Translation preserves the usual order on the integers.
example : IsRightOrderable (Multiplicative ℤ) :=
  ⟨inferInstance, fun _ _ c h => Int.add_le_add_right h c.toAdd⟩
