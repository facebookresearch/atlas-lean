/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Automorphism groups transitive on the involutions of a 2-group (Kourovka Notebook Problem 7.31)

Kourovka Notebook, Problem 7.31 (V. D. Mazurov), marked solved in the 21st issue: let `A` be a group
of automorphisms of a finite non-abelian `2`-group `G` acting transitively on the set of involutions
of `G`. Is `A` necessarily soluble?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.InvolutionTransitiveAutomorphismSolubleKourovka7Problem31Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 7.31 (V. D. Mazurov). UnsolvedMath record
UM-00700429 (`KOU-7.31`), dataset ulamai/UnsolvedMath v1.8.0.

`A` is any subgroup of `MulAut G`; transitive on the involutions (elements of order `2`) means every
involution is mapped to every other by some element of `A`. Soluble is `Group.IsSolvable`.
-/

/-- Kourovka 7.31 (V. D. Mazurov): if a group `A` of automorphisms of a finite non-abelian
`2`-group `G` acts transitively on the involutions of `G`, then `A` is soluble. -/
def involutionTransitiveAutomorphismsSoluble : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsPGroup 2 G → (∃ x y : G, x * y ≠ y * x) →
    ∀ A : Subgroup (MulAut G),
      (∀ x y : G, orderOf x = 2 → orderOf y = 2 → ∃ a ∈ A, a x = y) → Group.IsSolvable A

/--
Resolved true: the 21st issue marks 7.31 solved, "Yes, it is", citing Li and Zhu (2024), who confirm
Gross's 1976 conjecture on `2`-automorphic `2`-groups. By their Theorem 1.1 a finite `p`-group `N`
whose automorphism group is transitive on the elements of order `p` is homocyclic, a generalized
quaternion `2`-group, or a Suzuki `2`-group with soluble automorphism group; for a non-abelian
`2`-group the automorphism group is soluble in both remaining cases, hence so is every subgroup `A`.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 7.31 (V. D. Mazurov); resolution: C. H. Li
and Y. Z. Zhu, A proof of Gross' conjecture on 2-automorphic 2-groups, Proc. London Math. Soc. (3)
129, no. 5 (2024), Article e70002, Kourovka Notebook 21st issue, Problem 7.31, marked solved: Yes,
it is; paper, Theorem 1.1 (arXiv:2312.16416): a finite p-group whose automorphism group is
transitive on the elements of order p is homocyclic, generalized quaternion, or a Suzuki 2-group
with soluble automorphism group, https://doi.org/10.1112/plms.70002.
-/
public theorem_wanted involutionTransitiveAutomorphismsSoluble_holds :
    involutionTransitiveAutomorphismsSoluble

end MathlibExt.GroupTheory.InvolutionTransitiveAutomorphismSolubleKourovka7Problem31Wanted
