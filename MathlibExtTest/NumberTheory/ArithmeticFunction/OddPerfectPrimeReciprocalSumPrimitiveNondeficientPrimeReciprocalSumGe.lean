/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSumPrimitiveNondeficientPrimeReciprocalSumGe
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the prime reciprocal sum lower bound

The bound instantiated at `n = 6` and a numeric upper bound for `log 2` derived from it.
-/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted

-- Six is primitive non-deficient: perfect with all proper divisors deficient.
example : IsPrimitiveNondeficient 6 := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  intro m hm hmn
  have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide +kernel
  rw [hdiv] at hm
  fin_cases hm
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exfalso
    omega

-- At `n = 6` the bound reads `log 2 - 25 / 128 + 1 / 4 ≤ 5 / 6`.
example : Real.log 2 - 25 / 128 + ((3 : ℝ) - 2) / 2 - ((3 : ℝ) - 2) ^ 2 / 4 ≤ 5 / 6 := by
  have h6 : IsPrimitiveNondeficient 6 := by
    refine ⟨⟨by decide, by decide⟩, ?_⟩
    intro m hm hmn
    have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide +kernel
    rw [hdiv] at hm
    fin_cases hm
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exfalso
      omega
  have h := MetaMathlibExt.primitiveNondeficient_primeReciprocalSum_ge 6 h6
  have hmf : Nat.minFac 6 = 2 := by decide +kernel
  have hpf : Nat.primeFactors 6 = {2, 3} := by decide +kernel
  have hH : abundancySup 6 = 3 := by
    unfold abundancySup
    rw [hpf]
    decide +kernel
  rw [hmf, hpf, hH] at h
  norm_num [Finset.sum_insert, Finset.sum_singleton] at h ⊢
  linarith [h]

-- The `n = 6` instance gives a numeric upper bound for `log 2`.
example : Real.log 2 ≤ 0.779 := by
  have h6 : IsPrimitiveNondeficient 6 := by
    refine ⟨⟨by decide, by decide⟩, ?_⟩
    intro m hm hmn
    have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide +kernel
    rw [hdiv] at hm
    fin_cases hm
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exfalso
      omega
  have h := MetaMathlibExt.primitiveNondeficient_primeReciprocalSum_ge 6 h6
  have hmf : Nat.minFac 6 = 2 := by decide +kernel
  have hpf : Nat.primeFactors 6 = {2, 3} := by decide +kernel
  have hH : abundancySup 6 = 3 := by
    unfold abundancySup
    rw [hpf]
    decide +kernel
  rw [hmf, hpf, hH] at h
  norm_num [Finset.sum_insert, Finset.sum_singleton] at h
  linarith [h]

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum
