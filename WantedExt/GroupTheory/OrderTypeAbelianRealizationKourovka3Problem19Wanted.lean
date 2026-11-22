/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Order types of linearly ordered groups (Kourovka Notebook Problem 3.19)

Kourovka Notebook, Archive of Solved Problems, Problem 3.19 (A. I. Mal'cev; A. I. Kokorin): for an
arbitrary linearly ordered group `G`, does there exist a linearly ordered abelian group with the
same order-type as `G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.OrderTypeAbelianRealizationKourovka3Problem19Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.19 (A. I.
Mal'cev; A. I. Kokorin). UnsolvedMath record UM-00700173 (`KOU-3.19`), dataset ulamai/UnsolvedMath
v1.8.0.

Linearly ordered groups carry a linear order invariant under multiplication on both sides
(`MulLeftMono`, `MulRightMono`), linearly ordered abelian groups are `CommGroup` with
`IsOrderedMonoid`, and the same order type means an order isomorphism `G ≃o A`.
-/

/-- Kourovka 3.19 (A. I. Mal'cev; A. I. Kokorin): for every linearly ordered group `G` (with a
bi-invariant linear order) there is a linearly ordered abelian group with the same order type,
i.e. whose underlying order is isomorphic to that of `G`. -/
def orderTypeRealizedByAbelianGroup : Prop :=
  ∀ (G : Type) [Group G] [LinearOrder G] [MulLeftMono G] [MulRightMono G],
    ∃ (A : Type) (_ : CommGroup A) (_ : LinearOrder A) (_ : IsOrderedMonoid A), Nonempty (G ≃o A)

/--
Resolved false: the Kourovka Archive answers 3.19 "No", citing Holland, Mekler and Shelah (Order 1
(1985)): some linearly ordered group has an order type realized by no linearly ordered abelian
group. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.19
(A. I. Mal'cev; A. I. Kokorin); resolution: W. C. Holland, A. H. Mekler and S. Shelah, Order 1
(1985), 383-397, Kourovka Archive, Problem 3.19: No, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted orderTypeRealizedByAbelianGroup_refuted : ¬ orderTypeRealizedByAbelianGroup

end MathlibExt.GroupTheory.OrderTypeAbelianRealizationKourovka3Problem19Wanted
