/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.NathansonRestrictedSumset

open MetaMathlibExt

-- At the minimum size both allowed orders attain equality, including for a nonunit step.
example (h : ℕ) (hh : h = 2 ∨ h = 3) :
    (({-5, -2, 1, 4, 7} : Finset ℤ) : Set ℤ).IsAPOfLength 5 := by
  let A : Finset ℤ := {-5, -2, 1, 4, 7}
  have hc : A.card = 5 := by decide
  change (A : Set ℤ).IsAPOfLength (↑(5 : ℕ) : ℕ∞)
  rw [← hc]
  apply nathanson_restrictedSumset_inverse A hc.ge h
  all_goals rcases hh with rfl | rfl <;> decide

-- With only four elements the restricted twofold sumset can be minimal for a nonprogression.
example : let A : Finset ℤ := {0, 1, 4, 5}
    (restrictedSumset 2 A).card = 2 * A.card - 2 ^ 2 + 1 ∧ ¬ (A : Set ℤ).IsAPOfLength 4 := by
  dsimp only
  refine ⟨by decide, ?_⟩
  rintro ⟨a, d, _, he⟩
  have term (i : ℕ) (hi : i < 4) : a + i • d ∈ ({0, 1, 4, 5} : Finset ℤ) := by
    change a + i • d ∈ (({0, 1, 4, 5} : Finset ℤ) : Set ℤ)
    rw [he]
    exact ⟨i, by exact_mod_cast hi, rfl⟩
  have h₀ := term 0 (by decide)
  have h₁ := term 1 (by decide)
  have h₂ := term 2 (by decide)
  simp at h₀ h₁ h₂
  have hd : d = 0 := by omega
  subst d
  have constant {x : ℤ} (hx : x ∈ ({0, 1, 4, 5} : Finset ℤ)) : x = a := by
    obtain ⟨i, _, rfl⟩ := he ▸ (show x ∈ (({0, 1, 4, 5} : Finset ℤ) : Set ℤ) from hx)
    simp
  have := constant (x := 0) (by decide)
  have := constant (x := 1) (by decide)
  omega
