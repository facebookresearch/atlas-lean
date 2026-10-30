/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An infinite group without proper nontrivial pronormal subgroups (Kourovka Notebook Problem 19.74)

Kourovka Notebook, Problem 19.74 (D. O. Revin), marked solved in the 21st issue: a subgroup `H` of
`G` is pronormal if `H` and `H^g` are conjugate in `⟨H, H^g⟩` for every `g ∈ G`. Does there exist an
infinite group that does not contain nontrivial proper pronormal subgroups?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import WantedExt.GroupTheory.HallMaximalPronormalSecondMaximalKourovka19Problem109Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.NoProperPronormalSubgroupsKourovka19Problem74Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.74 (D. O. Revin). UnsolvedMath record
UM-00701622 (`KOU-19.74`), dataset ulamai/UnsolvedMath v1.8.0.

Conjugates are images under `MulAut.conj`; `⟨H, H^g⟩` is `H ⊔ H^g`; `G : Type`. Pronormality is
`IsPronormal` of the Kourovka 19.109 entry, reused here: for every `g ∈ G` the subgroups `H` and
`H^g` are conjugate in `⟨H, H^g⟩`.
-/

open MathlibExt.GroupTheory.HallMaximalPronormalSecondMaximalKourovka19Problem109Wanted
  (IsPronormal)

/-- Kourovka 19.74 (D. O. Revin): there is an infinite group whose only pronormal subgroups are the
trivial subgroup and the whole group. -/
def existsInfiniteGroupWithoutProperPronormal : Prop :=
  ∃ (G : Type) (_ : Group G), Infinite G ∧ ∀ H : Subgroup G, IsPronormal H → H = ⊥ ∨ H = ⊤

/--
Resolved true: Corson (Theorem 1) constructs an infinite simple group with no proper abnormal
subgroup, which the problem states is equivalent (the normalizer of a pronormal subgroup is
abnormal); the 21st issue of the Kourovka Notebook marks 19.74 solved ("Yes, it does"). Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 19.74 (D. O. Revin); resolution: S. M. Corson, Infinite
simple groups with no proper abnormal subgroups, Monatsh. Math. (2025),
doi:10.1007/s00605-025-02116-8 (arXiv:2505.07330), Theorem 1: there is an infinite group that is
simple, torsion-free, has no maximal subgroup and has no proper abnormal subgroup, answering Revin's
problem; the Kourovka Notebook (21st issue) marks 19.74 solved: Yes, it does (the problem states the
equivalent form: an infinite simple group without proper abnormal subgroups),
https://arxiv.org/abs/2505.07330.
-/
public theorem_wanted existsInfiniteGroupWithoutProperPronormal_holds :
    existsInfiniteGroupWithoutProperPronormal

end MathlibExt.GroupTheory.NoProperPronormalSubgroupsKourovka19Problem74Wanted
