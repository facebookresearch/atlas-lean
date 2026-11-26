/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFrobeniusTriangularIsGenFrobeniusNumberConsMulOfGcd
import Mathlib.Algebra.BigOperators.Fin

/-! # Tests for Beck–Kifer reduction

The reduction sends the Frobenius number of `(3, 1)` to that of `(3, 2)` and gives a
scaling corollary at every representation level.
-/

namespace MathlibExtTest.NumberTheory.GeneralizedFrobeniusTriangularIsGenFrobeniusNumberConsMulOfGcd

open MetaMathlibExt

private theorem base_pair : IsGenFrobeniusNumber ![3, 1] 0 (-1) := by
  constructor
  · rw [frobeniusRepCount_eq_zero_of_neg _ (by decide)]
    exact le_rfl
  · intro m hm
    have hm0 : 0 ≤ m := by omega
    change 0 < {x : Fin 2 → ℕ | ∑ i, (x i : ℤ) * (![3, 1] : Fin 2 → ℕ) i = m}.encard
    apply Set.encard_pos.mpr
    refine ⟨![0, m.toNat], ?_⟩
    simp [Fin.sum_univ_succ, Int.toNat_of_nonneg hm0]

example : IsGenFrobeniusNumber ![3, 2] 0 1 := by
  have hvec : (Fin.cons 3 (fun i => 2 * (![1] : Fin 1 → ℕ) i) : Fin 2 → ℕ) =
      ![3, 2] := by decide
  have hresult := isGenFrobeniusNumber_cons_mul_of_gcd 0 3 2 ![1]
    (by decide) (by decide) (by decide) (by decide) (by decide) 0 (-1) base_pair
  rw [hvec] at hresult
  simpa using hresult

example (s : ℕ) (g : ℤ) (h : IsGenFrobeniusNumber ![3, 1] s g) :
    IsGenFrobeniusNumber ![3, 2] s (2 * g + 3) := by
  have hvec : (Fin.cons 3 (fun i => 2 * (![1] : Fin 1 → ℕ) i) : Fin 2 → ℕ) =
      ![3, 2] := by decide
  have hresult := isGenFrobeniusNumber_cons_mul_of_gcd 0 3 2 ![1]
    (by decide) (by decide) (by decide) (by decide) (by decide) s g h
  rw [hvec] at hresult
  simpa using hresult

end MathlibExtTest.NumberTheory.GeneralizedFrobeniusTriangularIsGenFrobeniusNumberConsMulOfGcd
