/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Consecutive integers with equally many divisors (Erdős Problem 946)

Erdős Problem 946: are there infinitely many `n` such that `τ(n) = τ(n + 1)`, where `τ` is the
divisor function?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Divisors

@[expose] public section

namespace MathlibExt.NumberTheory.EqualConsecutiveDivisorCountsErdosProblem946Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #946, https://www.erdosproblems.com/946 (status
PROVED). UnsolvedMath record UM-30007097 (`EP-946`), dataset ulamai/UnsolvedMath v1.8.0.

`τ(n)` is `n.divisors.card`. The longest-run question mentioned on the page as a generalization is
not part of the problem and is not stated. Compared with the formal-conjectures statement
`ErdosProblems/946.lean` (`erdos_946`, equivalent; no code imported).
-/

/-- Erdős Problem 946: there are infinitely many `n` with `τ(n) = τ(n + 1)`, where `τ(n)` is the
number of divisors of `n`. -/
def infinitelyManyEqualConsecutiveDivisorCounts : Prop :=
  {n : ℕ | n.divisors.card = (n + 1).divisors.card}.Infinite

/--
Resolved true: Heath-Brown proved that the number of `n ≤ x` with `τ(n) = τ(n + 1)` is `≫ x / (log
x)⁷`, so there are infinitely many; erdosproblems.com/946 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #946, https://www.erdosproblems.com/946 (status PROVED); resolution:
D. R. Heath-Brown, The divisor function at consecutive integers, Mathematika (1984), 141-149,
erdosproblems.com/946: Heath-Brown proved the claim, with ≫ x/(log x)⁷ such n ≤ x (improved to ≫
x/(log log x)³ by Hildebrand), https://www.erdosproblems.com/946.
-/
public theorem_wanted infinitelyManyEqualConsecutiveDivisorCounts_holds :
    infinitelyManyEqualConsecutiveDivisorCounts

end MathlibExt.NumberTheory.EqualConsecutiveDivisorCountsErdosProblem946Wanted
