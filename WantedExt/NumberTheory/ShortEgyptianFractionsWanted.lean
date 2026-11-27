/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Parts of the statement formulations are adapted from OpenAI's `openai/math`
repository (https://github.com/openai/math), revision
`3344da59991ed94f9ba711217b29c1d760badfa6`:

* `lean/ComparatorChallenges/EgyptianFractions.lean`: prescribed denominator
  occurrence and the pointwise denominator bound.
* `lean/ComparatorChallenges/ShortEgyptianFractions.lean`: existence of an
  expansion of a proper positive rational.

The source's `lean/LICENSE` is the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). The cited Lean files do not name
individual authors or carry a copyright notice. No source proofs are included.
Authors: OpenAI (project attribution in lean/formalization.yaml).
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Fintype.Basic

@[expose] public section

open scoped BigOperators

namespace EgyptianFraction

/-- **Occurrence of a prescribed denominator in an Egyptian expansion of one.**
For every integer $m\ge2$, some finite strictly increasing tuple of positive integer
denominators has reciprocal sum $1$ and contains $m$.

Source: [*Short Egyptian fractions*, occurrence of an exact denominator](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L85-L88). -/
public theorem_wanted exists_expansion_one_with_denominator (m : ℕ) (hm : 2 ≤ m) :
    ∃ k : ℕ, ∃ n : Fin k → ℕ, (∀ i, 1 ≤ n i) ∧ StrictMono n ∧
      (∑ i : Fin k, (1 : ℚ) / n i) = 1 ∧ ∃ i, n i = m

/-- **Every proper positive rational has an Egyptian expansion.** For natural $1\le a<b$,
there is a finite strictly increasing list of denominators, each at least $2$, with sum of
reciprocals equal to $a/b$ in $\mathbb Q$. The input need not be in lowest terms.

Source: [*Short Egyptian fractions*, existence conjunct](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ShortEgyptianFractions.lean#L7-L24). -/
public theorem_wanted exists_expansion_of_proper_rational (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    ∃ ns : List ℕ, ns.Pairwise (· < ·) ∧ (∀ n ∈ ns, 2 ≤ n) ∧
      (ns.map fun n => (1 : ℚ) / n).sum = (a : ℚ) / b

/-- **Pointwise denominator bounds for an Egyptian expansion of one.** Suppose a strictly
increasing $k$-tuple of positive integer denominators has reciprocal sum $1$. The denominator
at index $i$ is at most $k^{2^i}$, with indices starting at $0$.

Source: [*Short Egyptian fractions*, pointwise denominator bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EgyptianFractions.lean#L64-L70). -/
public theorem_wanted denominator_le_pow_in_expansion_one {k : ℕ} {n : Fin k → ℕ}
    (hn : ∀ i, 1 ≤ n i) (hmono : StrictMono n) (hsum : (∑ i : Fin k, (1 : ℚ) / n i) = 1)
    (i : Fin k) : n i ≤ k ^ (2 ^ i.val)

end EgyptianFraction
