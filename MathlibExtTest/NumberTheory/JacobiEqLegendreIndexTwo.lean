/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.JacobiEqLegendreIndexTwo

open MetaMathlibExt

-- In `15 = 3 * 5` the prime `5` also has odd exponent. The unit `2` has Jacobi symbol `1`
-- modulo `15` but Legendre symbol `-1` modulo `3`, so it lies outside the subgroup.
example : ∃ H : Subgroup (ZMod 15)ˣ, H.index = 2 ∧
    ZMod.unitOfCoprime 2 (by norm_num) ∉ H := by
  have h15 : (15 : ℕ) = 3 * 5 := rfl
  obtain ⟨H, hH, hidx⟩ := jacobi_eq_legendre_index_two 15 3 (by decide) Nat.prime_three
    (by norm_num) (by
      rintro ⟨-, h⟩
      have h5 := h 5 (by rw [h15, Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.prime_three.primeFactors, Nat.prime_five.primeFactors]; simp)
        (by rw [h15, Nat.factorization_mul (by norm_num) (by norm_num),
          Nat.prime_three.factorization, Nat.prime_five.factorization]; simp)
      omega)
  refine ⟨H, hidx, ?_⟩
  rw [hH]
  have hval : ((ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 15) : (ZMod 15)ˣ) :
      ZMod 15).val = 2 := rfl
  rw [hval]
  norm_num

-- In `9 = 3 ^ 2` the prime `3` has even exponent, so the hypothesis holds.
example : ∃ H : Subgroup (ZMod 9)ˣ,
    (∀ u : (ZMod 9)ˣ, u ∈ H ↔
      jacobiSym (((u : ZMod 9).val : ℕ) : ℤ) 9 = jacobiSym (((u : ZMod 9).val : ℕ) : ℤ) 3) ∧
    H.index = 2 :=
  jacobi_eq_legendre_index_two 9 3 (by decide) Nat.prime_three (by norm_num) (by
    rintro ⟨h, -⟩
    rw [show (9 : ℕ) = 3 ^ 2 from rfl, Nat.prime_three.factorization_pow] at h
    rw [Finsupp.single_eq_same] at h
    exact absurd h (by decide))
