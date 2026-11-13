/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-squarefree central binomial coefficients (Erdős Problem 175)

Erdős Problem 175: show that for every `n ≥ 5` the central binomial coefficient `binom(2n, n)` is
not squarefree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Choose.Central

@[expose] public section

namespace MathlibExt.NumberTheory.CentralBinomialNotSquarefreeErdosProblem175Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #175, https://www.erdosproblems.com/175 (status PROVED
(LEAN)). UnsolvedMath record UM-30006750 (`EP-175`), dataset ulamai/UnsolvedMath v1.8.0.

`Nat.centralBinom n` is `binom(2n, n)`. The bound `n ≥ 5` is the source's: `binom(8, 4) = 70 = 2 · 5
· 7` is squarefree. Compared with the formal-conjectures statement `ErdosProblems/175.lean`
(equivalent; no code imported).
-/

/-- Erdős Problem 175: for every `n ≥ 5` the central binomial coefficient `binom(2n, n)` is not
squarefree. -/
def centralBinomNotSquarefree : Prop :=
  ∀ n : ℕ, 5 ≤ n → ¬ Squarefree (Nat.centralBinom n)

/--
Resolved true: Sárközy proved that `binom(2n, n)` is not squarefree for all large `n`, and Granville
and Ramaré, and independently Velammal, proved it for every `n ≥ 5`; erdosproblems.com/175 lists the
problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #175,
https://www.erdosproblems.com/175 (status PROVED (LEAN)); resolution: A. Granville and O. Ramaré,
Explicit bounds on exponential sums and the scarcity of squarefree binomial coefficients,
Mathematika 43 (1996), 73-107; G. Velammal, Is the binomial coefficient binom(2n, n) squarefree?,
Hardy-Ramanujan J. 18 (1995), 23-45, erdosproblems.com/175: proved by Granville and Ramaré and
independently by Velammal for all n ≥ 5 (Sárközy 1985 for all large n),
https://doi.org/10.1112/S0025579300011608.
-/
public theorem_wanted centralBinomNotSquarefree_holds : centralBinomNotSquarefree

end MathlibExt.NumberTheory.CentralBinomialNotSquarefreeErdosProblem175Wanted
