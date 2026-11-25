/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticIrrationalCFNonexistence

/-! # Tests for convergent denominators and periodic continued fractions -/

open MetaMathlibExt

-- At the shortest split, both predecessor denominators are the empty continuant.
example (x : ℕ) : convergentDen (fun _ => x) 2 = x * x + 1 :=
  convergentDen_symm_split 3 (fun _ => x) (fun _ _ _ => rfl) 1 (by decide) (by decide)

-- Splitting 1, 2, 0, 0, 2, 1 after the second entry gives 3 * 3 + 1 * 1.
example :
    let a (n : ℕ) := min n (7 - n) % 3
    convergentDen a 6 = 3 * 3 + 1 * 1 := by
  intro a
  apply convergentDen_symm_split 7 a _ 2 (by decide) (by decide)
  intro i _ hi
  simp only [a, Nat.sub_sub_self hi.le, min_comm]

-- At the shortest admissible split both shorter correction terms are empty continuants.
example (x : ℕ) : convergentDen (fun _ => x) 2 = x * x + 1 :=
  shifted_convergentDen_symm_split 5 (fun _ => x) (fun _ _ _ => rfl) 2 (by decide) (by decide)

-- At the minimum length the left half of the shifted continuant is empty.
example (x : ℕ) : convergentDen (fun _ => x) 1 ≡ x [MOD 2] := by
  simpa [convergentDen_zero] using shifted_convergentDen_parity_of_even 4 (by decide) (by decide)
    (fun _ => x) (fun _ _ _ => rfl)

-- At odd length five the second summand is the empty continuant.
example (x : ℕ) : x * x + 1 ≡ x + 1 [MOD 2] :=
  shifted_convergentDen_parity_of_odd 5 (by decide) (by decide) (fun _ => x) (fun _ _ _ => rfl)

-- The internal coefficients 2, 0, 0, 2 give 5 on the left and 1 + 2 on the right.
example :
    let a (i : ℕ) := min i (7 - i) % 3
    let d := convergentDen (fun i => a (i + 1))
    d 4 = 5 ∧ d 2 + d 1 = 3 ∧ d 4 ≡ d 2 + d 1 [MOD 2] := by
  intro a d
  have hsymm (i : ℕ) (_ : 1 ≤ i) (hi : i < 7) : a i = a (7 - i) := by
    simp only [a, Nat.sub_sub_self hi.le, min_comm]
  exact ⟨rfl, rfl, shifted_convergentDen_parity_of_odd 7 (by decide) (by decide) a hsymm⟩

-- The internal coefficients are 2, 0, 1, 0, 2. The split after 2, 0 gives 3 + 2.
example :
    let a (i : ℕ) := min i (8 - i) % 3
    let d := convergentDen (fun i => a (i + 1))
    d 5 = 5 ∧ d 5 = d 2 * d 3 + d 1 * d 2 ∧ a 4 * d 2 = 1 ∧ d 5 ≡ a 4 * d 2 [MOD 2] := by
  intro a d
  have hsymm (i : ℕ) (_ : 1 ≤ i) (hi : i < 8) : a i = a (8 - i) := by
    simp only [a, Nat.sub_sub_self hi.le, min_comm]
  exact ⟨rfl, shifted_convergentDen_symm_split 8 a hsymm 3 (by decide) (by decide), rfl,
    shifted_convergentDen_parity_of_even 8 (by decide) (by decide) a hsymm⟩

-- At period length zero every positive position uses its own sequence entry.
example {x : ℝ} {a₀ c : ℕ} {a : ℕ → ℕ} (h : HasPeriodicCF x a₀ a 0 c) (n : ℕ) :
    (GenContFract.of x).partDens.get? n = some (a (n + 1) : ℝ) := by
  simpa using h.2 n
