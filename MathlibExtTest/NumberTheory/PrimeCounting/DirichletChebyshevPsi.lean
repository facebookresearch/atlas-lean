/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.DirichletChebyshevPsi

/-!
# Tests for the twisted Chebyshev function `ψ(x, χ)`

Small values of `DirichletCharacter.chebyshevPsi`, the boundary `x < 2`, and agreement with
`Chebyshev.psi` for the character mod `1`.
-/

@[expose] public section

open ArithmeticFunction

namespace DirichletChebyshevPsiTest

/-- `ψ(x, χ) = 0` for `x < 2`, including negative `x`. -/
example {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : x < 2) : χ.chebyshevPsi x = 0 := by
  rw [DirichletCharacter.chebyshevPsi]
  refine Finset.sum_eq_zero fun n hn => ?_
  have hn2 : n < 2 := by
    rw [Finset.mem_Ioc] at hn
    have := hn.2
    have h1 : ⌊x⌋₊ < 2 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hx)
    omega
  have hn1 : n = 0 ∨ n = 1 := by omega
  rcases hn1 with rfl | rfl <;> simp

example {q : ℕ} (χ : DirichletCharacter ℂ q) : χ.chebyshevPsi (-5) = 0 := by
  rw [DirichletCharacter.chebyshevPsi, Nat.floor_of_nonpos (by norm_num)]
  rfl

/-- `ψ(2, χ) = χ(2) log 2`. -/
example {q : ℕ} (χ : DirichletCharacter ℂ q) : χ.chebyshevPsi 2 = χ 2 * Real.log 2 := by
  rw [DirichletCharacter.chebyshevPsi, show ⌊(2 : ℝ)⌋₊ = 2 by simp]
  rw [show Finset.Ioc 0 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)]
  simp [vonMangoldt_apply_prime Nat.prime_two]

/-- For the character mod `1`, `ψ(x, χ) = ψ(x)`. -/
example (χ : DirichletCharacter ℂ 1) (x : ℝ) : χ.chebyshevPsi x = (Chebyshev.psi x : ℂ) := by
  rw [DirichletCharacter.chebyshevPsi, Chebyshev.psi]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [DirichletCharacter.level_one χ, MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

/-- Sums over `Iic` and over `Ioc 0` agree. -/
example {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    χ.chebyshevPsi x = ∑ n ∈ Finset.Iic ⌊x⌋₊, χ n * (vonMangoldt n : ℂ) :=
  DirichletCharacter.chebyshevPsi_eq_sum_Iic χ x

/-- Perron's formula applies at `x = 5/2`, which is not a prime power. -/
example {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Filter.Tendsto (fun R : ℝ => (1 / (2 * Real.pi) : ℂ) * ∫ t in (-R)..R,
        -(deriv (DirichletCharacter.LFunction χ) (2 + t * Complex.I) /
          DirichletCharacter.LFunction χ (2 + t * Complex.I)) *
          (((5 / 2 : ℝ) : ℂ) ^ (2 + t * Complex.I) / (2 + t * Complex.I)))
      Filter.atTop (nhds (χ.chebyshevPsi (5 / 2))) := by
  have := DirichletCharacter.tendsto_truncated_integral_chebyshevPsi χ (x := 5 / 2) (c := 2)
    (by norm_num) (fun n hn => by
      have : (2 * n : ℝ) = 5 := by rw [hn]; norm_num
      have h : 2 * n = 5 := by exact_mod_cast this
      omega) (by norm_num)
  simpa using this

end DirichletChebyshevPsiTest
