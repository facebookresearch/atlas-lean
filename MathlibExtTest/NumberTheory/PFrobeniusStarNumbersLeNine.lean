/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PFrobeniusStarNumbersLeNine
import Mathlib.Tactic.NormNum

namespace MathlibExt.NumberTheory.PFrobeniusStarNumbersWanted

example : IsPFrobeniusStarNumber 0 6 6899 := by
  obtain ⟨g, hg, hvalue⟩ :=
    exists_isPFrobeniusNumber_star_of_le_nine 6 0 (by decide) (by decide) (Or.inl rfl)
  norm_num [MetaMathlibExt.StarNumber.star] at hvalue
  obtain rfl : g = 6899 := by omega
  exact hg

example : starRepCount 9 33101 ≤ 2 ∧ 2 < starRepCount 9 33102 := by
  obtain ⟨g, hg, hvalue⟩ :=
    exists_isPFrobeniusNumber_star_of_le_nine 9 2 (by decide) (by decide) (Or.inr (Or.inr rfl))
  norm_num [MetaMathlibExt.StarNumber.star] at hvalue
  obtain rfl : g = 33101 := by omega
  exact ⟨hg.1, hg.2 33102 (by decide)⟩

#print axioms exists_isPFrobeniusNumber_star_of_le_nine

end MathlibExt.NumberTheory.PFrobeniusStarNumbersWanted
