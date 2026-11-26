/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.Finite.PolynomialSumIdentity
import Mathlib.FieldTheory.Finite.GaloisField

open Finset Polynomial
open MathlibExt.Algebra.PermutationPolynomialsWanted

-- The coefficient of degree two survives, but 19 is one modulo nine.
example (c : ZMod 3) : ∑ n ∈ Icc (1 : ℕ) 19, (n : ZMod 3) ^ 2 * c ^ n = c := by
  have h := (finiteField_sum_eval_mul_pow_eq_id_iff (ZMod 3) 3 1 (by decide) (by decide)
    (by simp) (by decide) 19 (by decide) (by decide) (X ^ 2)).mpr
    ⟨by simp, Or.inl (by decide)⟩ c
  simpa using h

-- With the same polynomial and k = 7 the converse detects the nonzero coefficient.
example : ¬∀ c : ZMod 3, ∑ n ∈ Icc (1 : ℕ) 7, (n : ZMod 3) ^ 2 * c ^ n = c := by
  intro hall
  have h := (finiteField_sum_eval_mul_pow_eq_id_iff (ZMod 3) 3 1 (by decide) (by decide)
    (by simp) (by decide) 7 (by decide) (by decide) (X ^ 2)).mp (by simpa using hall)
  simpa [coeff_X_pow] using h.2

-- Over the four-element field, k = 7 fails the congruence modulo four.
-- The constant polynomial has an empty coefficient sum, so the identity still holds.
example (c : GaloisField 2 2) : ∑ n ∈ Icc (1 : ℕ) 7, c ^ n = c := by
  let : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 2) = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
  have h := (finiteField_sum_eval_mul_pow_eq_id_iff (GaloisField 2 2) 2 2 (by decide)
    (by decide) hcard (by decide) 7 (by decide) (by decide) 1).mpr ⟨by simp, Or.inr (by simp)⟩ c
  simpa using h
