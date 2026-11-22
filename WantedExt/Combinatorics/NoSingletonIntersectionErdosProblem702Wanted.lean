/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Uniform families with no singleton intersection (Erdős Problem 702)

Erdős Problem 702 (Erdős and Sós): let `k ≥ 4`. If `𝓕` is a family of subsets of `{1, …, n}` with
`|A| = k` for all `A ∈ 𝓕` and `|𝓕| > C(n - 2, k - 2)` then there are `A, B ∈ 𝓕` such that `|A ∩ B| =
1`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.NoSingletonIntersectionErdosProblem702Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #702, https://www.erdosproblems.com/702 (status
PROVED). UnsolvedMath record UM-30006985 (`EP-702`), dataset ulamai/UnsolvedMath v1.8.0.

Frankl's theorem is for `n` sufficiently large in terms of `k`, and the target keeps that
hypothesis: for all `n` the statement is false (for `k = 4`, `n = 5` the five `4`-subsets of a
`5`-set pairwise meet in `3` points and `5 > C(3, 2)`). Compared with the formal-conjectures
statement `ErdosProblems/702.lean` (formal-conjectures also proves `erdos_702.variants.all_n_false`
for k = 4, n = 5; no code imported).
-/

/-- Erdős Problem 702, in Frankl's form: for every `k ≥ 4` and every sufficiently large `n`, a
family of more than `C(n - 2, k - 2)` `k`-element subsets of `{1, …, n}` contains two sets
meeting in exactly one element. -/
def noSingletonIntersectionBound : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ᶠ n : ℕ in Filter.atTop, ∀ F : Finset (Finset (Fin n)),
    (∀ A ∈ F, A.card = k) → (n - 2).choose (k - 2) < F.card →
      ∃ A ∈ F, ∃ B ∈ F, (A ∩ B).card = 1

/--
Resolved true: Frankl proved that for `k ≥ 4` and `n` sufficiently large every `k`-uniform family on
`n` points with no two members meeting in exactly one point has at most `C(n - 2, k - 2)` members
(Katona had the case `k = 4`); the hypothesis that `n` is large is needed (`k = 4`, `n = 5`).
erdosproblems.com/702 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#702, https://www.erdosproblems.com/702 (status PROVED); resolution: P. Frankl, On families of
finite sets no two of which intersect in a singleton, Bull. Austral. Math. Soc. 17 (1977), 125-134,
P. Keevash, D. Mubayi and R. M. Wilson, Set systems with no singleton intersection, abstract:
'Frankl showed that |F| ≤ C(n-2, k-2) for k ≥ 4 and n sufficiently large, confirming a conjecture of
Erdős and Sós'; erdosproblems.com/702: Frankl proved this for all k ≥ 4,
https://www.math.cmu.edu/users/mubayi/papers/no-singleton.pdf.
-/
public theorem_wanted noSingletonIntersectionBound_holds : noSingletonIntersectionBound

end MathlibExt.Combinatorics.NoSingletonIntersectionErdosProblem702Wanted
