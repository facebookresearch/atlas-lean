/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Oppermann prime counts

Asymptotic count of primes in the Oppermann intervals `[n^2 - n, n^2]` and
`[n^2, n^2 + n]`.

Concept ID: `jis_sem_b1c5531b893b694777f2c1c5`.
Source statement: `jis_6984ebbf83b6eb73fb1b156d`.
Source: https://cs.uwaterloo.ca/journals/JIS/VOL28/Cohen/cohen41.tex
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Primes in the lower Oppermann interval.** For a natural number $n$, this is the number of
primes $p$ with $n^2 - n \le p \le n^2$.

Source: concept `jis_sem_b1c5531b893b694777f2c1c5` (counting Oppermann primes), source statement
`jis_6984ebbf83b6eb73fb1b156d`. -/
def oppermannLowerPrimeCount (n : ℕ) : ℕ :=
  ((Finset.Icc (n ^ 2 - n) (n ^ 2)).filter Nat.Prime).card

/-- **Primes in the upper Oppermann interval.** For a natural number $n$, this is the number of
primes $p$ with $n^2 \le p \le n^2 + n$.

Source: concept `jis_sem_b1c5531b893b694777f2c1c5` (counting Oppermann primes), source statement
`jis_6984ebbf83b6eb73fb1b156d`. -/
def oppermannUpperPrimeCount (n : ℕ) : ℕ :=
  ((Finset.Icc (n ^ 2) (n ^ 2 + n)).filter Nat.Prime).card

/-- **Main term for the Oppermann prime counts.** For a natural number $n$, this is the real
number $n / (2 \log n)$, where $\log$ is the natural logarithm. It is used as the asymptotic main
term for the number of primes in each of the intervals $[n^2 - n, n^2]$ and $[n^2, n^2 + n]$.

For $n \le 1$ we have $\log n = 0$, and the value is $0$ by the convention that division by zero
gives zero; this does not affect the asymptotics.

Source: concept `jis_sem_b1c5531b893b694777f2c1c5` (counting Oppermann primes), source statement
`jis_6984ebbf83b6eb73fb1b156d`. -/
noncomputable def oppermannAsymptotic (n : ℕ) : ℝ :=
  (n : ℝ) / (2 * Real.log n)

end

end MetaMathlibExt
