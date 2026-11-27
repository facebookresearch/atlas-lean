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

/-- **N-step Fibonacci numbers.** For a natural number $N$, the $N$-step Fibonacci numbers
$F^{(N)}_n$ ($n \ge 0$), in the convention of Noe and Post, are defined by $F^{(N)}_0 = 0$,
$F^{(N)}_1 = 1$ and, for $n \ge 2$, $F^{(N)}_n = \sum_{i=1}^{N} F^{(N)}_{n-i}$, where a term
whose index $n - i$ is negative counts as $0$. In particular $F^{(0)}_n = 0$ for $n \ge 2$.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 4.4. -/
def nStepFibonacci (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => ∑ i : Fin N, nStepFibonacci N (n + 1 - i)
decreasing_by omega

/-- **Recurrence for the N-step Fibonacci numbers.** For all natural numbers $N$ and $n$, the
$N$-step Fibonacci numbers $F^{(N)}$ satisfy
$F^{(N)}_{n+2} = \sum_{i=0}^{N-1} F^{(N)}_{\max(n+1-i,\,0)}$.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 4.4. -/
theorem nStepFibonacci_add_two (N n : ℕ) :
    nStepFibonacci N (n + 2) = ∑ i : Fin N, nStepFibonacci N (n + 1 - i) := by
  rw [nStepFibonacci]

/-- **Zeroth N-step Fibonacci number.** For every natural number $N$, the $N$-step Fibonacci
number $F^{(N)}_0$ equals $0$.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 4.4. -/
@[simp] theorem nStepFibonacci_zero (N : ℕ) : nStepFibonacci N 0 = 0 := by
  rw [nStepFibonacci]

/-- **First N-step Fibonacci number.** For every natural number $N$, the $N$-step Fibonacci
number $F^{(N)}_1$ equals $1$.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 4.4. -/
@[simp] theorem nStepFibonacci_one (N : ℕ) : nStepFibonacci N 1 = 1 := by
  rw [nStepFibonacci]

/-- **The tribonacci number with index 5.** The $3$-step Fibonacci number $F^{(3)}_5$ equals $7$.

The tribonacci numbers $F^{(3)}_0, \dots, F^{(3)}_5$ are $0, 1, 1, 2, 4, 7$.

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Section 4.4. -/
theorem nStepFibonacci_three_five : nStepFibonacci 3 5 = 7 := by
  simp [nStepFibonacci, Fin.sum_univ_succ]

end MetaMathlibExt
