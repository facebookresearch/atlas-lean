/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Cyclotomic.ComposedFactorization

open MetaMathlibExt Polynomial

-- Three occurrences of the same prime with exponents 2, 0, 1. The middle block
-- contributes no factor, and the last block starts at the prefix exponent 4.
example : (X ^ 8 - 1 : ℤ[X]) = (X - 1) * (X + 1) * (X ^ 2 + 1) * (X ^ 4 + 1) := by
  have h := X_pow_sub_one_eq_mul_prod_cyclotomic_comp 3 (fun _ => 2)
    (fun i => if i = 1 then 2 else if i = 2 then 0 else 1) (fun _ _ => Nat.prime_two)
  have hIcc₃ : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc₂ : Finset.Icc 1 2 = {1, 2} := by decide
  have hIco₁ : Finset.Ico 1 1 = ∅ := by decide
  have hIco₂ : Finset.Ico 1 2 = {1} := by decide
  have hIco₃ : Finset.Ico 1 3 = {1, 2} := by decide
  norm_num [hIcc₃, hIcc₂, hIco₁, hIco₂, hIco₃, Finset.prod_insert, add_comp] at h
  simpa [mul_assoc] using h

-- An empty index does not require any values of p to be prime.
example (p a : ℕ → ℕ) : (X ^ 1 - 1 : ℤ[X]) = X - 1 := by
  have hEmpty : Finset.Icc (1 : ℕ) 0 = ∅ := by decide
  simpa only [hEmpty, Finset.prod_empty, mul_one] using
    X_pow_sub_one_eq_mul_prod_cyclotomic_comp 0 p a (by simp)
