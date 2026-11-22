/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Families avoiding one intersection size (Erdős Problem 703)

Erdős Problem 703: let `r ≥ 1` and define `T(n, r)` to be maximal such that there exists a family
`𝓕` of subsets of `{1, …, n}` of size `T(n, r)` such that `|A ∩ B| ≠ r` for all `A, B ∈ 𝓕`. Estimate
`T(n, r)` for `r ≥ 2`. In particular, is it true that for every `ε > 0` there exists `δ > 0` such
that for all `εn < r < (1/2 - ε) n` we have `T(n, r) < (2 - δ)^n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MathlibExt.Combinatorics.ForbiddenIntersectionErdosProblem703Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #703, https://www.erdosproblems.com/703 (status PROVED
(LEAN)). UnsolvedMath record UM-30006986 (`EP-703`), dataset ulamai/UnsolvedMath v1.8.0.

`T(n, r) < (2 - δ)^n` is stated as: every family with the property has fewer than `(2 - δ)^n`
members. The condition is read literally for all `A, B ∈ 𝓕` (including `A = B`); with distinct pairs
the bound follows as well, since adding the `r`-sets changes `|𝓕|` by at most `C(n, r)`. The
open-ended 'estimate `T(n, r)`' is not formalized. Compared with the formal-conjectures statement
`ErdosProblems/703.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 703, second question: for every `ε > 0` there is `δ > 0` such that for all
`n` and `εn < r < (1/2 - ε) n`, every family `F` of subsets of `{1, …, n}` with `|A ∩ B| ≠ r` for
all `A, B ∈ F` has `|F| < (2 - δ)^n` (so `T(n, r) < (2 - δ)^n`). -/
def forbiddenIntersectionExponentialGap : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n r : ℕ, ε * n < r → (r : ℝ) < (1 / 2 - ε) * n →
    ∀ F : Finset (Finset (Fin n)), (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ r) →
      (F.card : ℝ) < (2 - δ) ^ n

/--
Resolved true: Frankl and Rödl proved that for every `ε > 0` there is `δ > 0` with `T(n, r) < (2 -
δ)^n` whenever `εn < r < (1/2 - ε) n`; erdosproblems.com/703 lists the problem as proved. Source: T.
F. Bloom, Erdős Problems, Problem #703, https://www.erdosproblems.com/703 (status PROVED (LEAN));
resolution: P. Frankl and V. Rödl, Forbidden intersections, Trans. Amer. Math. Soc. 300 (1987),
259-286, erdosproblems.com/703: 'The answer to the second question is yes, proved by Frankl and
Rödl', https://www.erdosproblems.com/703.
-/
public theorem_wanted forbiddenIntersectionExponentialGap_holds :
    forbiddenIntersectionExponentialGap

end MathlibExt.Combinatorics.ForbiddenIntersectionErdosProblem703Wanted
