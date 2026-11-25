/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.PVHHCubeMorphicWord

namespace MathlibExt.Combinatorics.PVHHCubeMorphicWordWanted

example : substitutionIterate 4 =
    [.zero, .three, .one, .four, .three, .zero, .one, .one] := rfl

example (w : ℕ → Letter) (hw : IsGeneratedFixedPoint w) : factorSum w 1 3 = 8 := by
  have h₁ : w 1 = .three := hw 4 1 (by decide)
  have h₂ : w 2 = .one := hw 4 2 (by decide)
  have h₃ : w 3 = .four := hw 4 3 (by decide)
  norm_num [factorSum, Finset.sum_range_succ, h₁, h₂, h₃, letterValue]

example : ¬ AvoidsPVHHCubes (fun _ => .three) := by
  intro h
  exact h 0 1 (by decide) ⟨rfl, rfl⟩

end MathlibExt.Combinatorics.PVHHCubeMorphicWordWanted
