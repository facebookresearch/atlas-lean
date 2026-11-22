/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Intersections of good subnormal subgroups (Kourovka Notebook Problem 8.74)

Kourovka Notebook, Problem 8.74 (J. G. Thompson), marked solved in the 21st issue: a subnormal
subgroup `H` of a group `G` is good if `⟨H, J⟩` is subnormal in `G` whenever `J` is subnormal in
`G`. Is it true that when `H` and `K` are good subnormal subgroups of `G`, then `H ∩ K` is good?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.IsSubnormal

@[expose] public section

namespace MathlibExt.GroupTheory.GoodSubnormalIntersectionKourovka8Problem74Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 8.74 (J. G. Thompson). UnsolvedMath record
UM-00700522 (`KOU-8.74`), dataset ulamai/UnsolvedMath v1.8.0.

Subnormality is Mathlib's `Subgroup.IsSubnormal` (a finite chain of successively normal subgroups)
and `⟨H, J⟩ = H ⊔ J`. Groups are arbitrary (not necessarily finite) groups in `Type`; in finite
groups every subnormal subgroup is good (Wielandt's join theorem), so a counterexample is infinite.
-/

/-- A subnormal subgroup `H` of `G` is good (Kourovka 8.74) if `⟨H, J⟩` is subnormal in `G` for
every subnormal subgroup `J` of `G`. Subnormality is Mathlib's `Subgroup.IsSubnormal` (a finite
chain of successively normal subgroups). -/
def IsGoodSubnormal {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  H.IsSubnormal ∧ ∀ J : Subgroup G, J.IsSubnormal → (H ⊔ J).IsSubnormal

/-- Kourovka 8.74 (J. G. Thompson): the intersection of two good subnormal subgroups of a group is
good. -/
def goodSubnormalInterGood : Prop :=
  ∀ (G : Type) [Group G] (H K : Subgroup G), IsGoodSubnormal H → IsGoodSubnormal K →
    IsGoodSubnormal (H ⊓ K)

/--
Resolved false: Muliarchyk (Theorem 1) constructs a countable locally finite `2`-group `G` of
derived length at most `3` with good subnormal subgroups `H`, `K` and a subnormal subgroup `J` such
that `⟨H ∩ K, J⟩` is not subnormal, so `H ∩ K` is not good; the Kourovka Notebook (21st issue) marks
8.74 solved: "No, not always". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 8.74 (J. G.
Thompson); resolution: K. Muliarchyk, Intersections of good subnormal subgroups: a counterexample to
Kourovka Notebook Problem 8.74, preprint (14 September 2026), Theorem 1: there is a countable
locally finite 2-group G of derived length at most three with good subnormal subgroups H, K and a
subnormal subgroup J such that ⟨H ∩ K, J⟩ is not subnormal in G; the Kourovka Notebook (21st issue)
marks 8.74 solved: "No, not always",
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_8_74_solution.pdf.
-/
public theorem_wanted goodSubnormalInterGood_refuted : ¬ goodSubnormalInterGood

end MathlibExt.GroupTheory.GoodSubnormalIntersectionKourovka8Problem74Wanted
