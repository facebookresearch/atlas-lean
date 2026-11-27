/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WeightedDirichletConvolutionBFreeCoprimeIndicatorMulMoebius

/-!
# Tests for the twisted B-free convolution

These tests evaluate the convolution at 18 and show that modulus zero gives the
Möbius function.
-/

namespace MathlibExtTest.NumberTheory.WeightedDirichletConvolutionBFreeCoprimeIndicatorMulMoebius

open MetaMathlibExt ArithmeticFunction
open scoped ArithmeticFunction.Moebius

example :
    ∑ d ∈ Nat.divisors 18,
      (if d.Coprime 2 then bFreeIndicator (fun _ => 2) d else 0) * μ (18 / d) = 1 := by
  have h := (bFreeCoprimeIndicator_mul_moebius (κ := fun _ => 2)
    (fun _ _ => by decide) 2).2 2 3 (dvd_refl 2) (by decide) (by decide)
  simpa [Nat.prime_three.factorization, moebius_apply_prime Nat.prime_two,
    moebius_apply_prime Nat.prime_three] using h

example {κ : ℕ → ℕ} (hκ : ∀ p : ℕ, p.Prime → 1 ≤ κ p) (n : ℕ) :
    ∑ d ∈ n.divisors, (if d.Coprime 0 then bFreeIndicator κ d else 0) * μ (n / d) = μ n := by
  simpa using (bFreeCoprimeIndicator_mul_moebius hκ 0).2 n 1
    (dvd_zero n) (by decide) (by decide)

end MathlibExtTest.NumberTheory.WeightedDirichletConvolutionBFreeCoprimeIndicatorMulMoebius
