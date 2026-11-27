/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Numerical.VeltkampSplit
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Floor

/-! # Kernel-checked examples of Veltkamp splitting -/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloatingPoint

example : veltkampSplit 3 2 (0 : ℚ) = (0, 0) := by decide +kernel
example : veltkampSplit 3 2 (1 : ℚ) = (1, 0) := by decide +kernel

-- Ties can carry into the next binade in the first operation. The low part can
-- have magnitude `2^(s - 1)` and still fit in `s - 1` bits after normalization.
example : veltkampSplit 3 2 (6 : ℚ) = (8, -2) := by decide +kernel

-- Shewchuk's seven-bit example, and its sign-reversed, rescaled counterpart.
example : veltkampSplit 7 4 (73 : ℚ) = (80, -7) := by decide +kernel
example : veltkampSplit 7 4 (-73 / 8 : ℚ) = (-10, 7 / 8) := by decide +kernel

-- An even precision at the smallest and largest permitted split points.
example : veltkampSplit 4 2 (9 : ℚ) = (8, 1) := by decide +kernel

-- The second rounding is the tie 38 between 36 and 40. Ties toward zero
-- would choose 36 instead of 40 and produce (12, -2).
example : veltkampSplit 4 2 (10 : ℚ) = (8, 2) := by decide +kernel

example : veltkampSplit 8 7 (255 : ℚ) = (256, -1) := by decide +kernel

end Cslib.Algorithms.Lean.FloatingPoint
