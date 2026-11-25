/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SymmetricConvergentDenParity

namespace MetaMathlibExt

-- At length three the cut is at index one, so the second term is q₀.
example : convergentDen (fun _ => 1) 2 = 2 ∧ convergentDen (fun _ => 2) 2 = 5 :=
  ⟨rfl, rfl⟩

example : convergentDen (fun _ => 2) 2 ≡ 3 [MOD 2] :=
  convergentDen_parity_of_odd (l := 3) (hl := ⟨1, rfl⟩) (hl3 := by decide)
    (a := fun _ => 2) (hsymm := by simp)

private def blockFive (x y i : ℕ) : ℕ := if i = 2 ∨ i = 3 then y else x

private theorem blockFive_symm (x y : ℕ) :
    ∀ i, 1 ≤ i → i < 5 → blockFive x y i = blockFive x y (5 - i) := by
  intro i hi hlt
  have h : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

-- All four parity patterns for the first half of the symmetric block x, y, y, x.
-- Check the denominators independently of the theorem.
example : convergentDen (blockFive 1 1) 4 = 5 ∧ convergentDen (blockFive 1 2) 4 = 10 ∧
    convergentDen (blockFive 2 1) 4 = 13 ∧ convergentDen (blockFive 2 2) 4 = 29 :=
  ⟨rfl, rfl, rfl, rfl⟩

example : convergentDen (blockFive 1 2) 4 ≡ 4 [MOD 2] :=
  convergentDen_parity_of_odd (l := 5) (hl := ⟨2, rfl⟩) (hl3 := by decide)
    (a := blockFive 1 2) (hsymm := blockFive_symm 1 2)

example : convergentDen (blockFive 2 1) 4 ≡ 5 [MOD 2] :=
  convergentDen_parity_of_odd (l := 5) (hl := ⟨2, rfl⟩) (hl3 := by decide)
    (a := blockFive 2 1) (hsymm := blockFive_symm 2 1)

end MetaMathlibExt
