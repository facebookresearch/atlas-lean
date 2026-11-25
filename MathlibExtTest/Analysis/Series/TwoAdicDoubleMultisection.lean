/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Series.TwoAdicDoubleMultisection

/-!
# Tests for the double two-adic multisection of a double series
-/

namespace MetaMathlibExt.tsum_twoAdic_double_multisection

/-- A unit mass at the index pair `(2, 2)`. -/
private def atom (p q : ℕ) : ℂ := if p = 2 ∧ q = 2 then 1 else 0

private theorem odd_eq_two {j n : ℕ} (h : (2 * n + 1) * 2 ^ j = 2) : j = 1 ∧ n = 0 := by
  rcases j with _ | _ | j
  · simp only [pow_zero, mul_one] at h
    omega
  · simp only [zero_add, pow_one] at h
    exact ⟨rfl, by omega⟩
  · have h' : (2 * n + 1) * 2 ^ j * 4 = 2 := by
      rw [show (2 * n + 1) * 2 ^ j * 4 = (2 * n + 1) * 2 ^ (j + 1 + 1) by ring]
      exact h
    omega

private theorem even_eq_two {j n : ℕ} (h : (2 * n + 2) * 2 ^ j = 2) : j = 0 ∧ n = 0 := by
  rcases j with _ | j
  · simp only [pow_zero, mul_one] at h
    omega
  · have h' : (n + 1) * 2 ^ j * 4 = 2 := by
      rw [show (n + 1) * 2 ^ j * 4 = (2 * n + 2) * 2 ^ (j + 1) by ring]
      exact h
    omega

/-- A family `2 ^ (j + k) * atom (f j n) (g k m)` is summable when the atom is hit at most once. -/
private theorem summable_atom (f g : ℕ → ℕ → ℕ) (x₀ : (ℕ × ℕ) × (ℕ × ℕ))
    (h : ∀ x : (ℕ × ℕ) × (ℕ × ℕ), f x.1.1 x.2.1 = 2 → g x.1.2 x.2.2 = 2 → x = x₀) :
    Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * atom (f x.1.1 x.2.1) (g x.1.2 x.2.2) := by
  refine summable_of_ne_finset_zero (s := {x₀}) fun x hx => ?_
  rw [Finset.mem_singleton] at hx
  simp only [atom]
  rw [ite_eq_right fun h' => hx (h x h'.1 h'.2), mul_zero]

-- A unit mass at `(2, 2)` meets each of the four families at exactly one index:
-- `2 = (2 · 0 + 1) · 2 ^ 1 = (2 · 0 + 2) · 2 ^ 0`. The families contribute `4`, `1`, `2` and
-- `2`, and the double multisection returns the total mass `4 + 1 - 2 - 2 = 1`.
example : ∑' x : (ℕ × ℕ) × (ℕ × ℕ), (2 : ℂ) ^ (x.1.1 + x.1.2)
      * (atom ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2)
        + atom ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2)
        - atom ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2)
        - atom ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2)) = 1 := by
  rw [← tsum_twoAdic_double_multisection atom
    (summable_atom (fun j n => (2 * n + 1) * 2 ^ j) (fun k m => (2 * m + 1) * 2 ^ k)
      ((1, 1), (0, 0)) fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ => by
        obtain ⟨rfl, rfl⟩ := odd_eq_two h₁
        obtain ⟨rfl, rfl⟩ := odd_eq_two h₂
        rfl)
    (summable_atom (fun j n => (2 * n + 2) * 2 ^ j) (fun k m => (2 * m + 2) * 2 ^ k)
      ((0, 0), (0, 0)) fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ => by
        obtain ⟨rfl, rfl⟩ := even_eq_two h₁
        obtain ⟨rfl, rfl⟩ := even_eq_two h₂
        rfl)
    (summable_atom (fun j n => (2 * n + 2) * 2 ^ j) (fun k m => (2 * m + 1) * 2 ^ k)
      ((0, 1), (0, 0)) fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ => by
        obtain ⟨rfl, rfl⟩ := even_eq_two h₁
        obtain ⟨rfl, rfl⟩ := odd_eq_two h₂
        rfl)
    (summable_atom (fun j n => (2 * n + 1) * 2 ^ j) (fun k m => (2 * m + 2) * 2 ^ k)
      ((1, 0), (0, 0)) fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ h₁ h₂ => by
        obtain ⟨rfl, rfl⟩ := odd_eq_two h₁
        obtain ⟨rfl, rfl⟩ := even_eq_two h₂
        rfl)]
  have hsingle (p : ℕ × ℕ) (hp : p ≠ (1, 1)) : atom (p.1 + 1) (p.2 + 1) = 0 :=
    ite_eq_right fun h => hp (Prod.ext (show p.1 = 1 by omega) (show p.2 = 1 by omega))
  rw [tsum_eq_single (1, 1) hsingle]
  simp [atom]

end MetaMathlibExt.tsum_twoAdic_double_multisection
