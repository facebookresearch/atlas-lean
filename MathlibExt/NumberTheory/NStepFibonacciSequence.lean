/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# n-step Fibonacci numbers

The `N`-step Fibonacci numbers `F^{(N)}_n` in the Noe and Post convention, used by Bowman,
*Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences
27 (2024), Article 24.3.6, Section 4.4. Compare the `n`-step Lucas numbers `nStepLucas`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- The `N`-step Fibonacci numbers `F^{(N)}_n` (Noe and Post convention): `F^{(N)}_0 = 0`,
`F^{(N)}_1 = 1`, and `F^{(N)}_n = F^{(N)}_{n-1} + ⋯ + F^{(N)}_{n-N}` for `n ≥ 2`, terms with
nonpositive index being `0` (here an index that truncates to `0` contributes `F^{(N)}_0 = 0`).

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 4.4. -/
def nStepFibonacci (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => ∑ i : Fin N, nStepFibonacci N (n + 1 - i)
decreasing_by omega

/-- Recurrence of `F^{(N)}`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 4.4. -/
theorem nStepFibonacci_add_two (N n : ℕ) :
    nStepFibonacci N (n + 2) = ∑ i : Fin N, nStepFibonacci N (n + 1 - i) := by
  rw [nStepFibonacci]

/-- `F^{(N)}_0 = 0`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 4.4. -/
@[simp] theorem nStepFibonacci_zero (N : ℕ) : nStepFibonacci N 0 = 0 := by
  rw [nStepFibonacci]

/-- `F^{(N)}_1 = 1`.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 4.4. -/
@[simp] theorem nStepFibonacci_one (N : ℕ) : nStepFibonacci N 1 = 1 := by
  rw [nStepFibonacci]

/-- `F^{(3)}_5 = 7` (tribonacci numbers `0, 1, 1, 2, 4, 7`).

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 4.4. -/
theorem nStepFibonacci_three_five : nStepFibonacci 3 5 = 7 := by
  simp [nStepFibonacci, Fin.sum_univ_succ]

end MetaMathlibExt
