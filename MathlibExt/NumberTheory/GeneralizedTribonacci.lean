/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Basic
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues111

/-!
# Integer-valued generalized Tribonacci sequence

This module formalizes the three-parameter Tribonacci sequence of Ira M. Gessel
and Ishan Kar, *Binomial Convolutions for Rational Power Series*, Journal of
Integer Sequences 27 (2024), Article 24.1.3, lines 700–719:
<https://cs.uwaterloo.ca/journals/JIS/VOL27/Gessel/gessel7.tex>.

For integer initial values `s₀, s₁, s₂`, the source defines `T_n^(s₀,s₁,s₂)` by
`T_0 = s₀`, `T_1 = s₁`, `T_2 = s₂`, and `T_{n+3} = T_{n+2} + T_{n+1} + T_n`.
Unlike the `ℕ`-valued special cases `MetaMathlibExt.tribonacci` (initial values
`0, 0, 1`) and `MetaMathlibExt.tribonacciWithInitialValues111` (initial values
`1, 1, 1`), this sequence takes values in `ℤ`, so it also covers signed initial
data. The bridge theorems below show it is a genuine generalization of both.
-/

@[expose] public section

namespace MetaMathlibExt

/-- The integer-valued generalized Tribonacci sequence `T_n^(s₀,s₁,s₂)`.

Source: Gessel–Kar (2024), JIS 27, Article 24.1.3, lines 700–719:
`T_0 = s₀`, `T_1 = s₁`, `T_2 = s₂`, and `T_{n+3} = T_{n+2} + T_{n+1} + T_n`. -/
def generalizedTribonacci (s₀ s₁ s₂ : ℤ) : ℕ → ℤ
  | 0 => s₀
  | 1 => s₁
  | 2 => s₂
  | n + 3 =>
      generalizedTribonacci s₀ s₁ s₂ (n + 2) +
        generalizedTribonacci s₀ s₁ s₂ (n + 1) + generalizedTribonacci s₀ s₁ s₂ n

/-- Source equation `T_0 = s₀`. -/
@[simp] theorem generalizedTribonacci_zero (s₀ s₁ s₂ : ℤ) :
    generalizedTribonacci s₀ s₁ s₂ 0 = s₀ := rfl

/-- Source equation `T_1 = s₁`. -/
@[simp] theorem generalizedTribonacci_one (s₀ s₁ s₂ : ℤ) :
    generalizedTribonacci s₀ s₁ s₂ 1 = s₁ := rfl

/-- Source equation `T_2 = s₂`. -/
@[simp] theorem generalizedTribonacci_two (s₀ s₁ s₂ : ℤ) :
    generalizedTribonacci s₀ s₁ s₂ 2 = s₂ := rfl

/-- Source recurrence `T_{n+3} = T_{n+2} + T_{n+1} + T_n`. -/
@[simp] theorem generalizedTribonacci_add_three (s₀ s₁ s₂ : ℤ) (n : ℕ) :
    generalizedTribonacci s₀ s₁ s₂ (n + 3) =
      generalizedTribonacci s₀ s₁ s₂ (n + 2) +
        generalizedTribonacci s₀ s₁ s₂ (n + 1) + generalizedTribonacci s₀ s₁ s₂ n :=
  rfl

/-- Initial values `0, 0, 1` recover `MetaMathlibExt.tribonacci`. -/
theorem generalizedTribonacci_zero_zero_one_eq_tribonacci (n : ℕ) :
    generalizedTribonacci 0 0 1 n = (tribonacci n : ℤ) := by
  have h : ∀ m : ℕ, generalizedTribonacci 0 0 1 m = (tribonacci m : ℤ) ∧
      generalizedTribonacci 0 0 1 (m + 1) = (tribonacci (m + 1) : ℤ) ∧
      generalizedTribonacci 0 0 1 (m + 2) = (tribonacci (m + 2) : ℤ) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp [generalizedTribonacci_zero, tribonacci]
      · have h1 : (0 : ℕ) + 1 = 1 := rfl
        rw [h1]
        simp [generalizedTribonacci_one, tribonacci]
      · have h2 : (0 : ℕ) + 2 = 2 := rfl
        rw [h2]
        simp [generalizedTribonacci_two, tribonacci]
    | succ k ih =>
      obtain ⟨ih0, ih1, ih2⟩ := ih
      have e1 : k + 1 + 1 = k + 2 := by omega
      have e2 : k + 1 + 2 = k + 3 := by omega
      refine ⟨ih1, ?_, ?_⟩
      · rw [e1]
        exact ih2
      · rw [e2, generalizedTribonacci_add_three]
        have e3 : tribonacci (k + 3) =
            tribonacci (k + 2) + tribonacci (k + 1) + tribonacci k := rfl
        rw [e3, Int.natCast_add, Int.natCast_add, ih2, ih1, ih0]
  exact (h n).1

/-- Initial values `1, 1, 1` recover
`MetaMathlibExt.tribonacciWithInitialValues111`. -/
theorem generalizedTribonacci_one_one_one_eq_tribonacciWithInitialValues111 (n : ℕ) :
    generalizedTribonacci 1 1 1 n = (tribonacciWithInitialValues111 n : ℤ) := by
  have h : ∀ m : ℕ, generalizedTribonacci 1 1 1 m =
        (tribonacciWithInitialValues111 m : ℤ) ∧
      generalizedTribonacci 1 1 1 (m + 1) =
        (tribonacciWithInitialValues111 (m + 1) : ℤ) ∧
      generalizedTribonacci 1 1 1 (m + 2) =
        (tribonacciWithInitialValues111 (m + 2) : ℤ) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp [generalizedTribonacci_zero, tribonacciWithInitialValues111]
      · have h1 : (0 : ℕ) + 1 = 1 := rfl
        rw [h1]
        simp [generalizedTribonacci_one, tribonacciWithInitialValues111]
      · have h2 : (0 : ℕ) + 2 = 2 := rfl
        rw [h2]
        simp [generalizedTribonacci_two, tribonacciWithInitialValues111]
    | succ k ih =>
      obtain ⟨ih0, ih1, ih2⟩ := ih
      have e1 : k + 1 + 1 = k + 2 := by omega
      have e2 : k + 1 + 2 = k + 3 := by omega
      refine ⟨ih1, ?_, ?_⟩
      · rw [e1]
        exact ih2
      · rw [e2, generalizedTribonacci_add_three]
        have e3 : tribonacciWithInitialValues111 (k + 3) =
            tribonacciWithInitialValues111 (k + 2) +
              tribonacciWithInitialValues111 (k + 1) +
              tribonacciWithInitialValues111 k := rfl
        rw [e3, Int.natCast_add, Int.natCast_add, ih2, ih1, ih0]
  exact (h n).1

/-- Initial values `0, 1, 1` recover `MetaMathlibExt.tribonacci` shifted by one.

This is the ordinary Tribonacci convention stated by Gessel–Kar; since the
repository's `tribonacci` starts `0, 0, 1`, the index shift is essential. -/
theorem generalizedTribonacci_zero_one_one_eq_tribonacci_succ (n : ℕ) :
    generalizedTribonacci 0 1 1 n = (tribonacci (n + 1) : ℤ) := by
  have h : ∀ m : ℕ, generalizedTribonacci 0 1 1 m = (tribonacci (m + 1) : ℤ) ∧
      generalizedTribonacci 0 1 1 (m + 1) = (tribonacci (m + 1 + 1) : ℤ) ∧
      generalizedTribonacci 0 1 1 (m + 2) = (tribonacci (m + 2 + 1) : ℤ) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · have h1 : (0 : ℕ) + 1 = 1 := rfl
        rw [h1]
        simp [generalizedTribonacci_zero, tribonacci]
      · have h1 : (0 : ℕ) + 1 = 1 := rfl
        have h2 : (0 : ℕ) + 1 + 1 = 2 := rfl
        rw [h2, h1]
        simp [generalizedTribonacci_one, tribonacci]
      · have h2 : (0 : ℕ) + 2 = 2 := rfl
        have h3 : (0 : ℕ) + 2 + 1 = 3 := rfl
        rw [h3, h2]
        have e : tribonacci 3 = 1 := rfl
        simp [generalizedTribonacci_two, e]
    | succ k ih =>
      obtain ⟨ih0, ih1, ih2⟩ := ih
      have e1 : k + 1 + 1 = k + 2 := by omega
      have e2 : k + 1 + 2 = k + 3 := by omega
      refine ⟨ih1, ?_, ?_⟩
      · rw [e1]
        exact ih2
      · rw [e2, generalizedTribonacci_add_three]
        have e3 : (tribonacci (k + 3 + 1) : ℤ) = (tribonacci (k + 2 + 1) : ℤ) +
            (tribonacci (k + 1 + 1) : ℤ) + (tribonacci (k + 1) : ℤ) := by
          have r : tribonacci (k + 3 + 1) = tribonacci (k + 2 + 1) +
              tribonacci (k + 1 + 1) + tribonacci (k + 1) := rfl
          rw [r, Int.natCast_add, Int.natCast_add]
        rw [e3, ih2, ih1, ih0]
  exact (h n).1

end MetaMathlibExt
