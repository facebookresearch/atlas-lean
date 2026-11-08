/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets determined by their multisets of `k`-sums (Erdős Problem 494)

Erdős Problem 494 (Selfridge and Straus): for a finite `A ⊆ ℂ` let `A_k` be the multiset of sums of
`k` distinct elements of `A`. For `k > 2`, do `A_k` and `|A|` determine `A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Powerset

@[expose] public section

namespace MathlibExt.Combinatorics.KSumMultisetDeterminesSetErdosProblem494Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #494, https://www.erdosproblems.com/494 (status
PROVED). UnsolvedMath record UM-30006901 (`EP-494`), dataset ulamai/UnsolvedMath v1.8.0.

Taken with `|A|` large in terms of `k`, as erdosproblems.com/494 does: the literal question fails
for `|A| = k` (rotations about the centroid) and `|A| = 2k` (Tao). `A_k` is a multiset, and `|A| =
|B|` is a hypothesis. Compared with the formal-conjectures statement `ErdosProblems/494.lean` (it
records the k = 2 and k = 3, 4 cases of Selfridge and Straus; no code imported).
-/

/-- `A_k`: the multiset of the sums of `k` distinct elements of the finite set `A ⊆ ℂ`. -/
noncomputable def kSumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => ∑ z ∈ s, z

/-- Erdős Problem 494 (Selfridge and Straus), with `|A|` large: for every `k ≥ 3` there is `n₀`
such that finite sets `A, B ⊆ ℂ` of the same size `≥ n₀` with `A_k = B_k` are equal. -/
def kSumMultisetDeterminesLargeSet : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ n₀ : ℕ, ∀ A B : Finset ℂ, A.card = B.card → n₀ ≤ A.card →
    kSumMultiset A k = kSumMultiset B k → A = B

/--
Resolved true: Gordon, Fraenkel and Straus proved (Section 4) that for `s > 2` two `n`-element
multisets in a torsion-free abelian group with the same multiset of `s`-sums are equal for all but
finitely many `n`; `ℂ` is torsion-free and sets are multisets. Source: T. F. Bloom, Erdős Problems,
Problem #494, https://www.erdosproblems.com/494 (status PROVED); resolution: B. Gordon, A. S.
Fraenkel and E. G. Straus, On the determination of sets by the sets of sums of a certain order,
Pacific J. Math. 12 (1962), 187-196, Section 4: for s > 2, F_s(n) = 1 for all but finitely many n,
for finite multisets in any torsion-free abelian group, https://doi.org/10.2140/pjm.1962.12.187.
-/
public theorem_wanted kSumMultisetDeterminesLargeSet_holds : kSumMultisetDeterminesLargeSet

end MathlibExt.Combinatorics.KSumMultisetDeterminesSetErdosProblem494Wanted
