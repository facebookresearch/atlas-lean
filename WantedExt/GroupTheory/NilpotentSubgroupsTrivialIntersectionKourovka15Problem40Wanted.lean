/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Conjugates of nilpotent subgroups of simple groups (Kourovka Notebook Problem 15.40)

Kourovka Notebook, Problem 15.40 (E. P. Vdovin): let `N` be a nilpotent subgroup of a finite simple
group `G`. Is it true that there exists a subgroup `N₁` conjugate to `N` such that `N ∩ N₁ = 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentSubgroupsTrivialIntersectionKourovka15Problem40Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 15.40 (E. P. Vdovin). UnsolvedMath record
UM-00701128 (`KOU-15.40`), dataset ulamai/UnsolvedMath v1.8.0.

Simple groups are non-abelian, as in the resolution: for `G` of prime order, `N = G` is a
counterexample. The target is the stronger two-subgroup form proved by Burness and Huang (for
nilpotent `A`, `B` there is `x` with `A ∩ B^x = 1`); `A = B = N` is the problem as posed. `B^x` is
the image of `B` under conjugation by `x`; the existential quantifier makes the side of conjugation
irrelevant.
-/

/-- Kourovka 15.40 (E. P. Vdovin), in the two-subgroup form of its resolution: for any nilpotent
subgroups `A` and `B` of a finite non-abelian simple group `G` there is `x ∈ G` with
`A ∩ x B x⁻¹ = 1`; `A = B = N` is the problem as posed. -/
def nilpotentSubgroupsTrivialConjugateIntersection : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ A B : Subgroup G, Group.IsNilpotent A → Group.IsNilpotent B →
      ∃ x : G, A ⊓ B.map (MulAut.conj x).toMonoidHom = ⊥

/--
Resolved true: Burness and Huang prove that if `G` is a finite (non-abelian) simple group and `A`,
`B` are nilpotent subgroups, then `A ∩ B^x = 1` for some `x ∈ G` (for alternating groups via work of
Zenkov); the Kourovka Notebook (21st issue) marks 15.40 solved, "Yes it is true". Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 15.40 (E. P. Vdovin); resolution: T. C. Burness and H. Y.
Huang, On the intersections of nilpotent subgroups in simple groups, arXiv:2508.03479 (2025),
abstract (Vdovin's conjecture and its stronger form: A ∩ B^x = 1 for nilpotent subgroups A, B of a
simple group, combined with work of Kurmazov and Zenkov on alternating groups); the Kourovka
Notebook (21st issue) marks 15.40 solved, https://arxiv.org/abs/2508.03479.
-/
public theorem_wanted nilpotentSubgroupsTrivialConjugateIntersection_holds :
    nilpotentSubgroupsTrivialConjugateIntersection

end MathlibExt.GroupTheory.NilpotentSubgroupsTrivialIntersectionKourovka15Problem40Wanted
