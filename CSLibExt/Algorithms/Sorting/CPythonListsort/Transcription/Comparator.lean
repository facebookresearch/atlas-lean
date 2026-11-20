/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

/-!
# Total Boolean comparator model

Version one replaces CPython's fallible and potentially specialized comparison
dispatch with a pure total Boolean function.  Keeping `iflt` as the single
entry point preserves the argument and call order of every transcribed `IFLT`
site while making the deliberate modeling boundary visible in Lean.
-/

namespace CPythonListsort

universe u

/-- The version-one model of CPython's comparison callback. -/
abbrev BoolComparator (α : Type u) := α → α → Bool

/-- The transcription boundary corresponding to CPython's `IFLT(x, y)` macro. -/
@[inline]
def iflt (lt : BoolComparator α) (x y : α) : Bool :=
  lt x y

@[simp]
theorem iflt_eq (lt : BoolComparator α) (x y : α) : iflt lt x y = lt x y := rfl

end CPythonListsort
