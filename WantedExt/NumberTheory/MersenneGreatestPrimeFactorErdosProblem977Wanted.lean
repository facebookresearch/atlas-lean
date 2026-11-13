/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The greatest prime factor of 2^n - 1 (Erdős Problem 977)

Erdős Problem 977: if `P(m)` is the greatest prime divisor of `m`, then is it true that `P(2^n -
1)/n → ∞` as `n → ∞`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.MaxPrimeFac
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.MersenneGreatestPrimeFactorErdosProblem977Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #977, https://www.erdosproblems.com/977 (status
PROVED). UnsolvedMath record UM-30007106 (`EP-977`), dataset ulamai/UnsolvedMath v1.8.0.

`P(m)` is Mathlib's `Nat.maxPrimeFac m`, the greatest prime factor for `m ≥ 2`. The question about
`P(n! + 1)` mentioned on the page is a different, open problem and is not stated. Compared with the
formal-conjectures statement `ErdosProblems/977.lean` (`erdos_977`, equivalent; no code imported).
-/

/-- Erdős Problem 977: `P(2^n - 1) / n → ∞` as `n → ∞`, where `P(m)` is the greatest prime factor
of `m` (`Nat.maxPrimeFac`). -/
def mersenneGreatestPrimeFactorOverN : Prop :=
  Filter.Tendsto (fun n : ℕ => (Nat.maxPrimeFac (2 ^ n - 1) : ℝ) / n) Filter.atTop Filter.atTop

/--
Resolved true: Stewart proved that `P(a^n - b^n) > n exp(log n / (104 log log n))` for all integers
`a > b > 0` and all large `n`; with `a = 2` and `b = 1` this gives `P(2^n - 1)/n → ∞`, as
erdosproblems.com/977 records. Source: T. F. Bloom, Erdős Problems, Problem #977,
https://www.erdosproblems.com/977 (status PROVED); resolution: C. L. Stewart, On divisors of Lucas
and Lehmer numbers, Acta Math. 211 (2013), 291-314, arXiv:1008.1274, Section 1, (8) (from Theorem
1): if a and b are integers with a > b > 0 then P(a^n - b^n) > n exp(log n / 104 log log n) for n
sufficiently large in terms of the number of distinct prime factors of ab, which 'answers the
question of Schinzel and proves the conjecture of Erdős'; erdosproblems.com/977: 'This was proved in
the affirmative by Stewart', P(2^n - 1) ≫ n^{1 + 1/(104 log log n)} for all large n,
https://arxiv.org/abs/1008.1274.
-/
public theorem_wanted mersenneGreatestPrimeFactorOverN_holds : mersenneGreatestPrimeFactorOverN

end MathlibExt.NumberTheory.MersenneGreatestPrimeFactorErdosProblem977Wanted
