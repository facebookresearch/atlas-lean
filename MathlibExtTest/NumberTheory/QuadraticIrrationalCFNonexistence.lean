/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticIrrationalCFNonexistence

/-! # Tests for shifted convergent denominators and periodic continued fractions -/

open MetaMathlibExt

-- At the minimum length the left half of the shifted continuant is empty.
example (x : ℕ) : convergentDen (fun _ => x) 1 ≡ x [MOD 2] := by
  simpa [convergentDen_zero] using shifted_convergentDen_parity_of_even 4 (by decide) (by decide)
    (fun _ => x) (fun _ _ _ => rfl)

-- The internal coefficients at length eight are 2, 0, 1, 0, 2.
example :
    let a (i : ℕ) := min i (8 - i) % 3
    let d := convergentDen (fun i => a (i + 1))
    d 5 = 5 ∧ a 4 * d 2 = 1 ∧ d 5 ≡ a 4 * d 2 [MOD 2] := by
  intro a d
  refine ⟨rfl, rfl, shifted_convergentDen_parity_of_even 8 (by decide) (by decide) a ?_⟩
  intro i _ hi
  simp only [a, Nat.sub_sub_self hi.le, min_comm]

-- At period length zero every positive position uses its own sequence entry.
example {x : ℝ} {a₀ c : ℕ} {a : ℕ → ℕ} (h : HasPeriodicCF x a₀ a 0 c) (n : ℕ) :
    (GenContFract.of x).partDens.get? n = some (a (n + 1) : ℝ) := by
  simpa using h.2 n
