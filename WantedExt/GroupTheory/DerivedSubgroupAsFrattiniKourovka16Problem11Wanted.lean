/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Derived subgroups as Frattini subgroups of `p`-groups (Kourovka Notebook Problem 16.11)

Kourovka Notebook, Problem 16.11 (Ya. G. Berkovich): let `G` be a finite `p`-group. Does there
always exist a finite `p`-group `H` such that `Φ(H) ≅ [G, G]`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Frattini

@[expose] public section

namespace MathlibExt.GroupTheory.DerivedSubgroupAsFrattiniKourovka16Problem11Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.11 (Ya. G. Berkovich). UnsolvedMath
record UM-00701203 (`KOU-16.11`), dataset ulamai/UnsolvedMath v1.8.0.

`Φ(H)` is Mathlib's `frattini H` (the intersection of the maximal subgroups) and `[G, G]` is
`commutator G`. The prime is universally quantified and `H` must be a `p`-group for the same prime,
as in the problem; groups are taken in `Type`.
-/

/-- Kourovka 16.11 (Ya. G. Berkovich): for every prime `p` and every finite `p`-group `G` there is a
finite `p`-group `H` whose Frattini subgroup `Φ(H)` is isomorphic to the derived subgroup `[G, G]`.
-/
def derivedSubgroupIsFrattini : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∃ (H : Type) (_ : Group H) (_ : Finite H), IsPGroup p H ∧
      Nonempty (frattini H ≃* commutator G)

/--
Resolved false: Ionin and Semidetnov (Answer 3.2) take `p = 2` and `G = SmallGroup(256, 511)`, whose
derived subgroup is the Hall-Senior group 32/40 (Lemma 3.4, a GAP computation); by a theorem of van
der Waall and de Nijs (their Theorem 1.15) that group is not isomorphic to `Φ(H)` for any finite
2-group `H`; the authors state that their solutions were found with the assistance of large language
models and checked by them. The Kourovka Notebook (21st issue) answers 16.11 "No, not always".
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.11 (Ya. G. Berkovich); resolution: V.
Ionin and A. Semidetnov, On some more problems from the Kourovka Notebook, preprint,
arXiv:2608.29219 (2026), Answer 3.2 with Lemma 3.4 and Theorem 3.3 (van der Waall-de Nijs, Theorem
1.15): for p = 2, G = SmallGroup(256, 511) has derived subgroup the Hall-Senior group 32/40, which
is the Frattini subgroup of no finite 2-group; the Kourovka Notebook (21st issue) marks 16.11 solved
(No, not always), https://arxiv.org/abs/2608.29219.
-/
public theorem_wanted derivedSubgroupIsFrattini_refuted : ¬ derivedSubgroupIsFrattini

end MathlibExt.GroupTheory.DerivedSubgroupAsFrattiniKourovka16Problem11Wanted
