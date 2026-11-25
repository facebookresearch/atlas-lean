/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.SquareTriangularOddPowers
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

open ArithmeticFunction

private def complexId : ArithmeticFunction ℂ := ⟨fun n ↦ (n : ℂ), Nat.cast_zero⟩

-- The identity function at the smallest permitted cutoff and exponent.
example : complexId 2 = 2 := by
  have hf : complexId.IsMultiplicative :=
    ⟨Nat.cast_one, fun {_ _} _ ↦ Nat.cast_mul ..⟩
  have hadd (u v : ℕ) (_ : 0 < u) (_ : 0 < v) :
      complexId (u ^ 2 + v * (v + 1) / 2) = complexId (u ^ 2) + complexId (v * (v + 1) / 2) :=
    Nat.cast_add ..
  have h := multiplicative_sq_triangular_additive_two_pow_odd complexId hf hadd 4 (by decide)
    (fun _ _ _ ↦ rfl) 1 (by decide) (by decide)
  norm_num at h
  exact h

section

variable (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
  (hadd : ∀ u v : ℕ, 0 < u → 0 < v →
    f (u ^ 2 + v * (v + 1) / 2) = f (u ^ 2) + f (v * (v + 1) / 2))

example (hlt : ∀ n : ℕ, 1 ≤ n → n ≤ 5 → f n = n) : f 8 = 8 := by
  have h := multiplicative_sq_triangular_additive_two_pow_odd f hf hadd 6 (by decide) hlt 2
    (by decide) (by decide)
  norm_num at h
  exact h

-- Here 2 * k ≤ N - 2 but 2 ^ k > N - 2, so Lemma 2 alone cannot fix the square 64.
example (hlt : ∀ n : ℕ, 1 ≤ n → n ≤ 7 → f n = n) : f 32 = 32 := by
  have h := multiplicative_sq_triangular_additive_two_pow_odd f hf hadd 8 (by decide) hlt 3
    (by decide) (by decide)
  norm_num at h
  exact h

end

end MetaMathlibExt
