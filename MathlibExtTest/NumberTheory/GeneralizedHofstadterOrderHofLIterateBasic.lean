/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedHofstadterOrderHofLIterateBasic

/-!
# Tests for basic properties of the Hofstadter image-length iterates

These examples check substitution lengths, the initial-value and recurrence boundary,
zero input, and strict growth of the iterates of `hofL`.

Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized
Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3
(arXiv:2410.00529; TeX source read for the definitions), Proposition 2.3.
-/

namespace MathlibExtTest.NumberTheory.GeneralizedHofstadterOrderHofLIterateBasic

open MetaMathlibExt

example : (hofL 2)^[2] 3 = 8 := by
  rw [(hofL_iterate_basic (by decide : 1 ≤ 2) 2).1 3]
  decide

example (j : ℕ) : (hofL 3)^[j] 0 = 0 :=
  (hofL_iterate_basic (by decide : 1 ≤ 3) j).2.1

example : (hofL 2)^[2] 4 = (hofL 2)^[2] 3 + 3 := by
  have h := (hofL_iterate_basic (by decide : 1 ≤ 2) 2).2.2.1 3
  have hl : ((hofTauList 2)^[2] [hofWord 2 3]).length = 3 := by decide
  simpa only [hl] using h

example : (hofL 3)^[3] 1 = 4 ∧
    (hofL 3)^[3] 1 = (hofL 3)^[2] 1 + (hofL 3)^[0] 1 := by
  obtain ⟨_, _, _, hsmall, hrec, _, _, _⟩ := hofL_iterate_basic (by decide : 1 ≤ 3) 3
  exact ⟨hsmall le_rfl, hrec le_rfl⟩

example : (hofL 1)^[4] 1 = 2 * (hofL 1)^[3] 1 := by
  obtain ⟨_, _, _, _, hrec, _, _, _⟩ := hofL_iterate_basic (by decide : 1 ≤ 1) 4
  have h := hrec (by decide)
  simp only [Nat.reduceSub] at h
  omega

example {m n : ℕ} (h : m < n) : (hofL 3)^[5] m < (hofL 3)^[5] n := by
  obtain ⟨_, _, _, _, _, hmono, _, _⟩ := hofL_iterate_basic (by decide : 1 ≤ 3) 5
  exact hmono h

example (n : ℕ) : (hofL 2)^[3] n = n ↔ n = 0 := by
  obtain ⟨_, _, _, _, _, _, hge, _⟩ := hofL_iterate_basic (by decide : 1 ≤ 2) 3
  simpa using (hge n).2

example (k j n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (hofL k)^[j] n < (hofL k)^[j + 1] n := by
  obtain ⟨_, _, _, _, _, _, _, hindex⟩ := hofL_iterate_basic hk j
  exact hindex n hn (Nat.lt_succ_self j)

end MathlibExtTest.NumberTheory.GeneralizedHofstadterOrderHofLIterateBasic
