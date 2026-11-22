/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Line counts of linear spaces just above a projective plane (Erdős Problem 903)

Erdős Problem 903: let `n = p² + p + 1` for some prime power `p`, and let `A₁, …, A_t ⊆ {1, …, n}`
be a block design (so that every pair `x, y ∈ {1, …, n}` is contained in exactly one `A_i`). Is it
true that if `t > n` then `t ≥ n + p`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MathlibExt.Combinatorics.LinearSpaceLineCountGapErdosProblem903Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #903, https://www.erdosproblems.com/903 (status
PROVED). UnsolvedMath record UM-30007078 (`EP-903`), dataset ulamai/UnsolvedMath v1.8.0.

`{1, …, n}` is `Fin n` and the blocks form an indexed family `Fin t → Finset (Fin n)`. As for Erdős,
Fowler, Sós and Wilson, a block design (`2`-design, pairwise balanced design, linear space) has
blocks of at least two points: blocks with fewer points cover no pair and could be added freely (a
projective plane of order `p` plus one singleton block has `n + 1` blocks), which would make the
question trivially false. Repeated blocks are excluded by the exactly-one condition. The remark 'in
general, one can ask what the possible values of `t` are' is commentary and is not stated. Compared
with the formal-conjectures statement `ErdosProblems/903.lean` (equivalent; no code imported).
-/

/-- A family `A₁, …, A_t` of subsets of `{1, …, v}` (here `Fin v`) is a `2`-design (pairwise
balanced design, linear space): every block has at least two points and every pair of distinct
points lies in exactly one block. -/
def IsTwoDesign {v t : ℕ} (A : Fin t → Finset (Fin v)) : Prop :=
  (∀ i, 2 ≤ (A i).card) ∧ ∀ x y : Fin v, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i

/-- Erdős Problem 903: if `p` is a prime power, `n = p² + p + 1` and `A₁, …, A_t` is a `2`-design on
`{1, …, n}` with more than `n` blocks, then it has at least `n + p` blocks. -/
def lineCountGapAboveProjectivePlane : Prop :=
  ∀ p : ℕ, IsPrimePow p → ∀ (t : ℕ) (A : Fin t → Finset (Fin (p ^ 2 + p + 1))),
    IsTwoDesign A → p ^ 2 + p + 1 < t → p ^ 2 + p + 1 + p ≤ t

/--
Resolved true: Erdős, Fowler, Sós and Wilson (Theorem 2) proved that a `2`-design on `n = p² + p +
1` points (every block of size at least two, every pair of points in exactly one block) has no
number of blocks `b` with `n < b < n + p`, for every `p`; erdosproblems.com/903 lists the problem as
proved. Source: T. F. Bloom, Erdős Problems, Problem #903, https://www.erdosproblems.com/903 (status
PROVED); resolution: P. Erdős, J. C. Fowler, V. T. Sós and R. M. Wilson, On 2-designs, J. Combin.
Theory Ser. A 38 (1985), 131-142, Theorem 2: for v = p² + p + 1 (p not necessarily a prime power)
there is no 2-design with v points and b lines when p² + p + 1 < b < p² + 2p + 1, where a 2-design
has every pair of points in exactly one block and every block of size > 1,
https://users.renyi.hu/~p_erdos/1985-22.pdf.
-/
public theorem_wanted lineCountGapAboveProjectivePlane_holds : lineCountGapAboveProjectivePlane

end MathlibExt.Combinatorics.LinearSpaceLineCountGapErdosProblem903Wanted
