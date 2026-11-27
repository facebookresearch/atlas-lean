/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DelannoyHarmonicCongruence
import Mathlib.Tactic.NormNum

open Finset

namespace MathlibExt.NumberTheory.DelannoyTriangleWanted

-- The least allowed prime has Fermat quotient 3, and the weighted sum is 1.
example : (∑ k ∈ Icc 1 4, harmonicMod 5 k * (2 : ZMod 5) ^ k * (k : ZMod 5)⁻¹) = 1 := by
  rw [sum_harmonic_two_pow_div 5 (by decide) (by decide) (by exact ⟨-2, 1, by norm_num⟩)]
  decide

-- The congruence also gives a nonzero residue beyond the boundary case.
example : (∑ k ∈ Icc 1 10, harmonicMod 11 k * (2 : ZMod 11) ^ k * (k : ZMod 11)⁻¹) = 8 := by
  rw [sum_harmonic_two_pow_div 11 (by decide) (by decide) (by exact ⟨-5, 1, by norm_num⟩)]
  decide

end MathlibExt.NumberTheory.DelannoyTriangleWanted
