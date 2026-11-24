/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Height.SchurSiegelSmyth.AbsoluteTrace

/-!
# Sharpness of the absolute trace bound
-/

open MathlibExt.NumberTheory.SchurSiegelSmyth

/-- The absolute traces have a least element, attained by the algebraic integer one. -/
example : IsLeast (absoluteTrace '' {α | IsTotallyPositive α}) 1 := by
  refine ⟨⟨1, isTotallyPositive_one, absoluteTrace_one⟩, ?_⟩
  rintro _ ⟨α, hα, rfl⟩
  exact absoluteTrace_one_le_wanted α hα
