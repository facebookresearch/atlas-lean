/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Prime.Basic
import MathlibExt.NumberTheory.LaurentCartierCongruence

namespace MetaMathlibExt

open AddMonoidAlgebra

example {r p : ℕ} (hp : p.Prime) (P Q : AddMonoidAlgebra ℤ (Fin r → ℤ)) (k : ℕ) :
    (P ^ k * Q).coeff 0 ≡ (laurentCartier p (P ^ k * Q)).coeff 0 [ZMOD p] := by
  simpa only [Nat.mul_zero, Nat.zero_add, pow_zero, one_mul] using
    constantTerm_pow_mul_modEq_laurentCartier hp P Q 0 k

example {p : ℕ} (hp : p.Prime) (P Q : AddMonoidAlgebra ℤ (Fin 0 → ℤ)) (n : ℕ) :
    (P ^ (p * n) * Q).coeff 0 ≡ (P ^ n * laurentCartier p Q).coeff 0 [ZMOD p] := by
  simpa only [Nat.add_zero, pow_zero, one_mul] using
    constantTerm_pow_mul_modEq_laurentCartier hp P Q n 0

-- With P = x⁻¹ + 1 and Q = x, the two constant terms are 2 and 0.
example :
    let P : AddMonoidAlgebra ℤ (Fin 1 → ℤ) := single (fun _ => -1) 1 + 1
    let Q : AddMonoidAlgebra ℤ (Fin 1 → ℤ) := single (fun _ => 1) 1
    (P ^ (2 * 1 + 0) * Q).coeff 0 ≡
      (P ^ 1 * laurentCartier 2 (P ^ 0 * Q)).coeff 0 [ZMOD 2] :=
  constantTerm_pow_mul_modEq_laurentCartier Nat.prime_two _ _ 1 0

end MetaMathlibExt
