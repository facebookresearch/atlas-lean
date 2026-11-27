/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HalfEvenFibonacciSet

/-!
# Tests for the halves of even Fibonacci numbers

The first elements of `halfEvenFibonacciSet`, a value it skips, and the reduction
`not_accessible_four_of_halfEvenFibonacci` combined with monotonicity in the number of colors.
-/

open MetaMathlibExt

namespace MathlibExtTest.Combinatorics.HalfEvenFibonacciSet

-- The elements `F₃ / 2 = 1`, `F₉ / 2 = 17` and `F₁₂ / 2 = 72`, at the indices `n = 0, 2, 3`.
example : 1 ∈ halfEvenFibonacciSet := ⟨0, by decide⟩

example : 17 ∈ halfEvenFibonacciSet := ⟨2, by decide⟩

example : 72 ∈ halfEvenFibonacciSet := ⟨3, by decide⟩

-- `4 = F₆ / 2`, the second element.
example : 4 ∈ halfEvenFibonacciSet := four_mem_halfEvenFibonacciSet

-- The even Fibonacci number `2 = F₃` itself is not a half: the set jumps from `1` to `4`.
example : 2 ∉ halfEvenFibonacciSet := by
  rintro ⟨_ | n, hn⟩
  · exact absurd hn (by decide)
  · dsimp only at hn
    have h6 : Nat.fib 6 = 8 := by decide
    have hle : Nat.fib 6 ≤ Nat.fib (3 * (n + 1 + 1)) := Nat.fib_mono (by omega)
    omega

-- With monotonicity in the number of colors, the reduction rules out every `r ≥ 4`.
example (h : ¬ IsRAccessible 2 halfEvenFibonacciSet) (r : ℕ) (hr : 4 ≤ r) :
    ¬ IsRAccessible r positiveFibonacciSet := fun hF =>
  not_accessible_four_of_halfEvenFibonacci h
    (IsRAccessible.mono positiveFibonacciSet hF (by decide) hr)

-- Contrapositive: a `4`-accessible Fibonacci set would make the halves `2`-accessible.
example (hF : IsRAccessible 4 positiveFibonacciSet) : IsRAccessible 2 halfEvenFibonacciSet :=
  Classical.byContradiction fun h => not_accessible_four_of_halfEvenFibonacci h hF

end MathlibExtTest.Combinatorics.HalfEvenFibonacciSet
