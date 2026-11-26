/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BeattyDecompositionBeattyFloorFiberCardEqOrEqSucc
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.NumberTheory.BeattyDecompositionBeattyFloorFiberCardEqOrEqSucc

-- At slope `2 / 5` (with `1 / 3 < 2 / 5 < 1 / 2`) every fiber has two or three elements.
example (t : ℕ) :
    {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (2 / 5)⌋ = t}.ncard = 2 ∨
      {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (2 / 5)⌋ = t}.ncard = 2 + 1 :=
  (MetaMathlibExt.beatty_floor_fiber_card_eq_or_eq_succ (k := 2) (α := 2 / 5)
    (by norm_num) (by norm_num)).1 t

-- Both multiplicities occur infinitely often at slope `2 / 5`.
example :
    {t : ℕ | {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (2 / 5)⌋ = t}.ncard = 2}.Infinite ∧
      {t : ℕ | {n : ℕ | 0 < n ∧ ⌊(n : ℝ) * (2 / 5)⌋ = t}.ncard = 2 + 1}.Infinite :=
  (MetaMathlibExt.beatty_floor_fiber_card_eq_or_eq_succ (k := 2) (α := 2 / 5)
    (by norm_num) (by norm_num)).2

end MathlibExtTest.NumberTheory.BeattyDecompositionBeattyFloorFiberCardEqOrEqSucc
