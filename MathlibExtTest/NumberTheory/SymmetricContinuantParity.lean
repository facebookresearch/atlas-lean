/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SymmetricContinuantParity

namespace MetaMathlibExt

-- Length two is the base case: the first nontrivial denominator has the parity of the center.
example : convergentDen (fun _ => 5) 1 ≡ 5 [MOD 2] :=
  convergentDen_parity_of_even (l := 2) (hl := ⟨1, rfl⟩) (hl0 := by decide)
    (a := fun _ => 5) (hsymm := by simp)

private def evenCenterTest (i : ℕ) : ℕ := if i = 2 then 3 else 2

-- The symmetric block 2, 3, 2 has final denominator 16 and midpoint product 6.
example : convergentDen evenCenterTest 3 = 16 := rfl

example : convergentDen evenCenterTest 3 % 2 = 0 := by
  have hsymm : ∀ i, 1 ≤ i → i < 4 → evenCenterTest i = evenCenterTest (4 - i) := by
    intro i hi hlt
    have h : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl <;> decide
  have h := convergentDen_parity_of_even (l := 4) (hl := ⟨2, rfl⟩) (hl0 := by decide)
    (a := evenCenterTest) (hsymm := hsymm)
  change convergentDen evenCenterTest 3 % 2 = 6 % 2 at h
  exact h

-- With three unit entries the final denominator is odd instead.
example : convergentDen (fun _ => 1) 3 % 2 = 1 := by
  have h := convergentDen_parity_of_even (l := 4) (hl := ⟨2, rfl⟩) (hl0 := by decide)
    (a := fun _ => 1) (hsymm := by simp)
  exact h

end MetaMathlibExt
