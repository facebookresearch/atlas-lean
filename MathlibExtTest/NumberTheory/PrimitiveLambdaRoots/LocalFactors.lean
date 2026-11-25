/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimitiveLambdaRoots.LocalFactors
import Mathlib.Tactic.NormNum

open ArithmeticFunction MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted

private theorem delta_two_three : lambdaDelta 2 3 = 1 := by
  have h₃ := carmichael_of_prime Nat.prime_three
  norm_num [lambdaDelta, h₃, Nat.prime_three.primeFactors, Finset.filter_singleton,
    Nat.prime_three.factorization, Nat.prime_two.factorization]

-- At modulus 2 the local factor is 1, and the product has the same count as modulus 3.
example : lambdaH 2 2 * lambdaH 2 3 = lambdaH 2 (2 * 3) := by
  have hprod : carmichael (2 * 3) = 2 := by
    rw [carmichael_mul (by decide), carmichael_two, carmichael_of_prime Nat.prime_three]
    decide
  have h₂ : lambdaDelta 2 2 = 0 := by
    norm_num [lambdaDelta, carmichael_two, Nat.prime_two.factorization]
  have h₆ : lambdaDelta 2 (2 * 3) = 1 := by
    simp only [lambdaDelta, hprod, Nat.primeFactors_mul (by decide : 2 ≠ 0) (by decide : 3 ≠ 0),
      Nat.factorization_mul (by decide : 2 ≠ 0) (by decide : 3 ≠ 0)]
    norm_num [Nat.prime_two.primeFactors, Nat.prime_three.primeFactors, Nat.prime_two.factorization,
      Nat.prime_three.factorization, Finset.filter_insert, Finset.filter_singleton,
      carmichael_of_prime Nat.prime_three]
  obtain ⟨hle, hlt⟩ := lambdaH_mul_ge_and_gt_iff 2 3 2 (by decide) (by decide) (by decide)
    Nat.prime_two (by rw [hprod])
  exact hle.eq_of_not_lt (fun h ↦ by simpa [h₂, delta_two_three, h₆] using hlt.mp h)

-- The exceptional count at 8 grows from two to three after adjoining the odd prime 3.
example : lambdaH 2 8 * lambdaH 2 3 < lambdaH 2 (8 * 3) := by
  have h₈ : carmichael 8 = 2 := carmichael_two_pow_of_ne_two (n := 3) (by decide)
  have hprod : carmichael (8 * 3) = 2 := by
    rw [carmichael_mul (by decide), h₈, carmichael_of_prime Nat.prime_three]
    decide
  apply (lambdaH_mul_ge_and_gt_iff 8 3 2 (by decide) (by decide) (by decide)
    Nat.prime_two (by rw [hprod])).2.mpr
  left
  have hfac : (8 : ℕ).factorization = Finsupp.single 2 3 := by
    rw [show 8 = 2 ^ 3 by decide, Nat.prime_two.factorization_pow]
  have hpf : (8 : ℕ).primeFactors = {2} :=
    Nat.primeFactors_prime_pow (by decide : 3 ≠ 0) Nat.prime_two
  simp only [lambdaDelta, h₈, hprod, Nat.primeFactors_mul (by decide : 8 ≠ 0) (by decide : 3 ≠ 0),
    Nat.factorization_mul (by decide : 8 ≠ 0) (by decide : 3 ≠ 0)]
  norm_num [hfac, hpf, Nat.prime_two.factorization, Nat.prime_three.factorization,
    Nat.prime_three.primeFactors]

-- Both counts are positive and equal the product's count, so only the last disjunct applies.
example : lambdaH 2 3 * lambdaH 2 5 < lambdaH 2 (3 * 5) := by
  have hp : Nat.Prime 5 := by decide
  have h₅ : carmichael 5 = 4 := carmichael_of_prime hp
  have hprod : carmichael (3 * 5) = 4 := by
    rw [carmichael_mul (by decide), carmichael_of_prime Nat.prime_three, h₅]
    decide
  have hv : (4 : ℕ).factorization 2 = 2 := by
    rw [show 4 = 2 ^ 2 by decide, Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
  have hΔ₅ : lambdaDelta 2 5 = 1 := by
    norm_num [lambdaDelta, h₅, hp.primeFactors, hp.factorization, hv, Finset.filter_singleton]
  have hΔ₁₅ : lambdaDelta 2 (3 * 5) = 1 := by
    simp only [lambdaDelta, hprod, Nat.primeFactors_mul (by decide : 3 ≠ 0) (by decide : 5 ≠ 0),
      Nat.factorization_mul (by decide : 3 ≠ 0) (by decide : 5 ≠ 0)]
    norm_num [Nat.prime_three.primeFactors, hp.primeFactors, Nat.prime_three.factorization,
      hp.factorization, hv, Finset.filter_insert, Finset.filter_singleton, h₅,
      carmichael_of_prime Nat.prime_three]
  apply (lambdaH_mul_ge_and_gt_iff 3 5 2 (by decide) (by decide) (by decide) Nat.prime_two
    (by rw [hprod]; decide)).2.mpr
  simp [delta_two_three, hΔ₅, hΔ₁₅]
