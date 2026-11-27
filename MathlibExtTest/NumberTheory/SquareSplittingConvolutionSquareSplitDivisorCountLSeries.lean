/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SquareSplittingConvolutionSquareSplitDivisorCountLSeries

/-! # Tests for the Dirichlet series of the square-splitting divisor function -/

namespace MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitDivisorCountLSeries

open MetaMathlibExt

-- At `s = 2`, the local factor at the prime `2` sums in closed form.
example : HasSum
    (fun k : ℕ => ((squareSplitDivisors (2 ^ k)).card : ℂ) * ((2 : ℂ) ^ (-((k : ℂ) * 2))))
    ((1 + 2 * ((2 : ℂ) ^ (-2 : ℂ))) / (1 - ((2 : ℂ) ^ (-(2 * 2) : ℂ))) ^ 2) := by
  obtain ⟨h, -, -, -⟩ := MetaMathlibExt.squareSplitDivisorCount_LSeries
  have hs2 : (1 : ℝ) < (2 : ℂ).re := by rw [Complex.re_ofNat]; norm_num
  exact (h 2 hs2).1 ⟨2, Nat.prime_two⟩

-- At `s = 2`, the Dirichlet series equals `ζ(2)²ζ(4)²H(2)`.
example : LSeries (fun n => ((squareSplitDivisors n).card : ℂ)) 2 =
    riemannZeta 2 ^ 2 * riemannZeta (2 * 2) ^ 2 *
      ∏' p : Nat.Primes, (1 - 3 * ((p : ℕ) : ℂ) ^ (-(2 * 2) : ℂ) +
        2 * ((p : ℕ) : ℂ) ^ (-(3 * 2) : ℂ)) := by
  obtain ⟨h, -, -, -⟩ := MetaMathlibExt.squareSplitDivisorCount_LSeries
  have hs2 : (1 : ℝ) < (2 : ℂ).re := by rw [Complex.re_ofNat]; norm_num
  exact (h 2 hs2).2.2

-- The `H` factor series converges absolutely at `s = 1`.
example : Summable (fun p : Nat.Primes =>
    ‖-3 * ((p : ℕ) : ℂ) ^ (-(2 * (1 : ℂ))) + 2 * ((p : ℕ) : ℂ) ^ (-(3 * (1 : ℂ)))‖) := by
  obtain ⟨-, h, -, -⟩ := MetaMathlibExt.squareSplitDivisorCount_LSeries
  exact h 1 (by rw [Complex.one_re]; norm_num)

end MathlibExtTest.NumberTheory.SquareSplittingConvolutionSquareSplitDivisorCountLSeries
