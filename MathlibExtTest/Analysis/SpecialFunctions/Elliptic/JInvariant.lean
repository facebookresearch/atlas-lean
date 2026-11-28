/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Elliptic.JInvariant

open PeriodPair

-- The `j`-invariant is `1728 g₂³ / (g₂³ - 27 g₃²)`, by definition.
example (L : PeriodPair) : L.jInvariant = 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) :=
  rfl

-- If `g₃ = 0` and `g₂ ≠ 0`, the `j`-invariant is `1728`.
example (L : PeriodPair) (h₂ : L.g₂ ≠ 0) (h₃ : L.g₃ = 0) : L.jInvariant = 1728 := by
  rw [jInvariant, h₃]
  field_simp
  ring

-- If `g₂ = 0`, the `j`-invariant is `0`.
example (L : PeriodPair) (h₂ : L.g₂ = 0) : L.jInvariant = 0 := by
  simp [jInvariant, h₂]
