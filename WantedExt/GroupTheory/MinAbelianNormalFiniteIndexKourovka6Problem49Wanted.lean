/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Min condition on abelian normal subgroups, finite index (Kourovka Notebook Problem 6.49)

Kourovka Notebook, Archive of Solved Problems, Problem 6.49 (S. A. Chechin): is the minimal
condition for abelian normal subgroups inherited by subgroups of finite index?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.MinAbelianNormalFiniteIndexKourovka6Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.49 (S. A.
Chechin). UnsolvedMath record UM-00700392 (`KOU-6.49`), dataset ulamai/UnsolvedMath v1.8.0.

The minimal condition for abelian normal subgroups is the absence of a strictly descending sequence
of abelian normal subgroups. The Archive's group `G` has all abelian normal subgroups satisfying the
minimal condition for subgroups (which implies this condition), and its subgroup `H` of index `2`
has a strictly descending chain of abelian normal subgroups, so the refutation holds for either
reading of the condition.
-/

/-- Kourovka 6.49 (S. A. Chechin): the minimal condition for abelian normal subgroups (no strictly
descending infinite chain of abelian normal subgroups) is inherited by subgroups of finite
index. -/
def minAbelianNormalInheritedFiniteIndex : Prop :=
  ∀ (G : Type) [Group G],
    (∀ N : ℕ → Subgroup G, (∀ n, (N n).Normal ∧ ∀ a ∈ N n, ∀ b ∈ N n, a * b = b * a) →
      ¬ StrictAnti N) →
    ∀ H : Subgroup G, H.FiniteIndex →
      ∀ N : ℕ → Subgroup H, (∀ n, (N n).Normal ∧ ∀ a ∈ N n, ∀ b ∈ N n, a * b = b * a) →
        ¬ StrictAnti N

/--
Resolved false: the Kourovka Archive answers 6.49 "No, not always" with Chechin's group (1979): a
group `G` all of whose abelian normal subgroups satisfy the minimal condition, with a subgroup `H`
of index `2` containing a strictly decreasing chain of abelian normal subgroups `E_n = A × B × C ×
⟨g^(2^n)⟩`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.49
(S. A. Chechin); resolution: S. A. Chechin, Abstracts of the 15th All-USSR Algebraic Conference,
Krasnoyarsk, 1979; construction given in the Archive, Kourovka Archive, Problem 6.49: No, not
always; G = [(A × B × C × D) ⋊ (⟨g⟩ × ⟨t⟩)] ⋊ (Y × ⟨x⟩) with quasicyclic A, B, C, D, Y; all abelian
normal subgroups of G satisfy min, while in H = [(A × B × C × D) ⋊ (⟨g⟩ × ⟨t⟩)] ⋊ Y the normal
subgroups E_n = A × B × C × ⟨g^(2^n)⟩ form a strictly decreasing chain,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted minAbelianNormalInheritedFiniteIndex_refuted :
    ¬ minAbelianNormalInheritedFiniteIndex

end MathlibExt.GroupTheory.MinAbelianNormalFiniteIndexKourovka6Problem49Wanted
