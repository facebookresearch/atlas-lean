/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.InversionSequenceAvoidSeven
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MetaMathlibExt PowerSeries

private abbrev B₁ : Set (Fin 3 → ℕ) :=
  {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]}

private abbrev B₂ : Set (Fin 3 → ℕ) :=
  {![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}

private abbrev B₃ : Set (Fin 3 → ℕ) :=
  {![0, 1, 0], ![0, 1, 1], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![2, 0, 1], ![2, 1, 0]}

-- Extract the first nontrivial coefficients from the public identity.
private theorem initialCoefficients (B : Set (Fin 3 → ℕ))
    (h : (1 - X) * (1 - 2 * X) ^ 2 * invSeqAvoidGF B =
      X * (1 - 2 * X) ^ 2 + X ^ 2 * (1 - X) ^ 2) :
    coeff 2 (invSeqAvoidGF B) = 2 ∧ coeff 3 (invSeqAvoidGF B) = 4 ∧
      coeff 4 (invSeqAvoidGF B) = 9 := by
  let F := invSeqAvoidGF B
  have h' : F - C (5 : ℚ) * (X ^ 1 * F) + C (8 : ℚ) * (X ^ 2 * F) -
      C (4 : ℚ) * (X ^ 3 * F) = X ^ 1 - C (3 : ℚ) * X ^ 2 + C (2 : ℚ) * X ^ 3 + X ^ 4 := by
    convert h using 1 <;> simp only [F, map_ofNat] <;> ring
  have h0 : coeff 0 F = 0 := (coeff_invSeqAvoidGF B 0).1
  have h1 : coeff 1 F = 1 := by
    rw [(coeff_invSeqAvoidGF B 0).2, invSeqAvoidCount_one, Nat.cast_one]
  have h2 : coeff 2 F = 2 := by
    have he := congrArg (coeff 2) h'
    norm_num [coeff_X_pow_mul', coeff_X_pow, coeff_X, h0, h1] at he
    linarith
  have h3 : coeff 3 F = 4 := by
    have he := congrArg (coeff 3) h'
    norm_num [coeff_X_pow_mul', coeff_X_pow, coeff_X, h0, h1, h2] at he
    linarith
  have h4 : coeff 4 F = 9 := by
    have he := congrArg (coeff 4) h'
    norm_num [coeff_X_pow_mul', coeff_X_pow, coeff_X, h1, h2, h3] at he
    linarith
  exact ⟨h2, h3, h4⟩

-- Length two is below the length of a forbidden pattern.
example : coeff 2 (invSeqAvoidGF B₁) = 2 :=
  (initialCoefficients B₁ (invSeqAvoidGF_010_011_102_201_210_seven B₁ (Or.inl rfl))).1

-- Length three is the first length at which the avoidance condition can remove sequences.
example : coeff 3 (invSeqAvoidGF B₂) = 4 :=
  (initialCoefficients B₂ (invSeqAvoidGF_010_011_102_201_210_seven B₂ (Or.inr (Or.inl rfl)))).2.1

-- At length four a descent into the last position is possible.
example : coeff 4 (invSeqAvoidGF B₃) = 9 :=
  (initialCoefficients B₃ (invSeqAvoidGF_010_011_102_201_210_seven B₃ (Or.inr (Or.inr rfl)))).2.2
