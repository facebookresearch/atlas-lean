/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Round

/-!
# Distance to the nearest integer

`distToNearestInt x = |x - round x|` is the distance `‖x‖` from a real number `x` to the nearest
integer.
-/

@[expose] public section

namespace MetaMathlibExt

/-- `‖x‖`, the distance from the real number `x` to the nearest integer. -/
noncomputable def distToNearestInt (x : ℝ) : ℝ :=
  |x - round x|

end MetaMathlibExt
