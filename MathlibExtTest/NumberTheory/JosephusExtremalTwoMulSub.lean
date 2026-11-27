/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusExtremalTwoMulSub

namespace MathlibExtTest.NumberTheory.JosephusExtremalTwoMulSub

open MetaMathlibExt MathlibExt.NumberTheory.JosephusWanted

-- J_2 (2 * 2 - 2) = 1 ≤ 1, so 2 is a low extremal point for k = 2.
example : IsLowExtremal 2 2 :=
  ((extremal_two_mul_sub 2 (by decide)).1 (by decide)).2

-- J_4 (2 * 4 - 2) = 5 > 3, so 7 is a low extremal point for k = 4.
example : IsLowExtremal 4 7 :=
  ((extremal_two_mul_sub 4 (by decide)).2 (by decide)).2

-- In particular, 2 * k - 2 is always a low or a high extremal point.
example (k : ℕ) (hk : 2 ≤ k) :
    IsLowExtremal k (2 * k - 2) ∨ IsHighExtremal k (2 * k - 2) := by
  by_cases h : MetaMathlibExt.josephus k (2 * k - 2) ≤ k - 1
  · exact Or.inl ((extremal_two_mul_sub k hk).1 h).2
  · have h' : k - 1 < MetaMathlibExt.josephus k (2 * k - 2) := by omega
    exact Or.inr ((extremal_two_mul_sub k hk).2 h').1

end MathlibExtTest.NumberTheory.JosephusExtremalTwoMulSub
