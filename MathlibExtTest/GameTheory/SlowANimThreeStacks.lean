/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.GameTheory.SlowANimThreeStacks

namespace MetaMathlibExt.slowANim_one_two_three_isP_iff

-- The all-even case allows empty stacks.
example : SpragueGrundy.IsP (slowANimGame 3 {1, 2}) ![0, 2, 4] :=
  (slowANim_one_two_three_isP_iff _ (by decide)).2 (Or.inl (by decide))

example : SpragueGrundy.IsP (slowANimGame 3 {1, 2}) ![1, 3, 5] :=
  (slowANim_one_two_three_isP_iff _ (by decide)).2 (Or.inr (by decide))

-- The two-stack move takes this mixed position to zero.
example : ¬ SpragueGrundy.IsP (slowANimGame 3 {1, 2}) ![0, 1, 1] :=
  fun h => (by decide : ¬ ((∀ i, Even (![0, 1, 1] i)) ∨ ∀ i, Odd (![0, 1, 1] i)))
    ((slowANim_one_two_three_isP_iff _ (by decide)).1 h)

end MetaMathlibExt.slowANim_one_two_three_isP_iff
