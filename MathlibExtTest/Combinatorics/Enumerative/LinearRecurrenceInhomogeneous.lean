/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.LinearRecurrenceInhomogeneous
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for inhomogeneous recurrence formulas

The second-difference recurrence has normalized homogeneous solution `f n = n`.
Check its first admissible index and a later index with three distinct forcing terms.
For the convolution identity, check order zero and an order-two recurrence with
zero last coefficient and a nonvanishing second triangular sum.
-/

namespace MetaMathlibExt

example (G w : ℕ → ℂ) (hG : ∀ m, G (m + 2) = 2 * G (m + 1) - G m + w m) :
    G 2 = 2 * G 1 - G 0 + w 0 ∧
    G 4 = 4 * G 1 - 3 * G 0 + (3 * w 0 + 2 * w 1 + w 2) := by
  let A := fun i : ℕ ↦ if i = 1 then (2 : ℂ) else -1
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hf (n : ℕ) (hn : 2 ≤ n) :
      (n : ℂ) = ∑ i ∈ Finset.Icc 1 2, A i * (↑(n - i) : ℂ) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp [hI, A]
    ring
  have hg (n : ℕ) (hn : 2 ≤ n) :
      G n = ∑ i ∈ Finset.Icc 1 2, A i * G (n - i) + w (n - 2) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simpa [hI, A, sub_eq_add_neg] using hG m
  have h (n : ℕ) (hn : 2 ≤ n + 1) :=
    linearRecurrence_inhomogeneous_explicit 2 A (fun n ↦ (n : ℂ)) G w hf hg
      (by intro j hj; simp [show j = 0 by omega]) (by norm_num) hn
  constructor
  · have h₂ := h (n := 1) (by decide)
    norm_num [Finset.sum_range_succ, A] at h₂
    rw [h₂]
    ring
  · have h₄ := h (n := 3) (by decide)
    norm_num [Finset.sum_range_succ, A] at h₄
    rw [h₄]
    ring

example (f w : ℕ → ℂ) (hf : ∀ m, f m = 0) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), f (n - j) * w j) = 0 := by
  have h := linearRecurrence_inhomogeneous_identity 0 (fun _ ↦ 0) f w w
    (by intro m _; simpa using hf m) (by simp) (Nat.zero_le n)
  simpa using h.symm

example (G w : ℕ → ℂ) (hG : ∀ m, G (m + 2) = G (m + 1) + w m) :
    G 4 + G 3 = G 1 + G 3 + (w 0 + w 1 + w 2) := by
  let A := fun i : ℕ ↦ if i = 1 then (1 : ℂ) else 0
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hf (m : ℕ) (_ : 2 ≤ m) :
      (1 : ℂ) = ∑ i ∈ Finset.Icc 1 2, A i * 1 := by
    simp [hI, A]
  have hg (m : ℕ) (hm : 2 ≤ m) :
      G m = ∑ i ∈ Finset.Icc 1 2, A i * G (m - i) + w (m - 2) := by
    obtain ⟨l, rfl⟩ : ∃ l, m = l + 2 := ⟨m - 2, by omega⟩
    simpa [hI, A] using hG l
  simpa [Finset.sum_range_succ, A, add_assoc] using
    linearRecurrence_inhomogeneous_identity 2 A (fun _ ↦ 1) G w hf hg (n := 2) (by decide)

end MetaMathlibExt
