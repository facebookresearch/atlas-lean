/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.NormNum
public import MathlibExt.NumberTheory.OddGreedyChoice

namespace MetaMathlibExtTest

open MetaMathlibExt

example : MetaMathlibExt.IsOddGreedyChoice (1 / 2 : ℚ) 3 := by
  rw [MetaMathlibExt.isOddGreedyChoice_iff]
  refine ⟨by norm_num, ⟨⟨by norm_num, ⟨1, rfl⟩, by norm_num⟩, ?_⟩⟩
  rintro e ⟨he, hodd, hle⟩
  by_cases h3 : 3 ≤ e
  · exact h3
  · obtain ⟨k, hk⟩ := hodd
    have h1 : e = 1 := by omega
    subst h1
    norm_num at hle

example (h : MetaMathlibExt.IsOddGreedyChoice (1 / 2 : ℚ) 3) :
    (1 : ℚ) / 3 ≤ 1 / 2 ∧ Odd 3 :=
  ⟨h.inv_le, h.odd⟩

example (h : MetaMathlibExt.IsOddGreedyChoice (2 / 3 : ℚ) 3)
    (h' : MetaMathlibExt.IsOddGreedyChoice (2 / 3 : ℚ) 5) :
    False :=
  by
  have h35 : 3 ≤ 5 := h.min h'.pos_d h'.odd h'.inv_le
  have h53 : (5 : ℕ) = 3 := h'.unique h
  omega

end MetaMathlibExtTest
