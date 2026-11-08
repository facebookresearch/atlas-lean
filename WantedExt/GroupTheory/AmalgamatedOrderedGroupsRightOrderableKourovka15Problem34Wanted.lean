/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Right-orderable amalgamated products of ordered groups (Kourovka Notebook Problem 15.34)

Kourovka Notebook, Archive of Solved Problems, Problem 15.34 (V. V. Bludov): is any free product of
linearly ordered groups with an amalgamated subgroup right-orderable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PushoutI

@[expose] public section

namespace MathlibExt.GroupTheory.AmalgamatedOrderedGroupsRightOrderableKourovka15Problem34Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.34 (V. V.
Bludov). UnsolvedMath record UM-00701122 (`KOU-15.34`), dataset ulamai/UnsolvedMath v1.8.0.

Linearly ordered groups are two-sided ordered (`MulLeftMono` and `MulRightMono` for a
`LinearOrder`). The amalgamated subgroup carries the order induced from each factor: it is a
linearly ordered group `H` with order-preserving embeddings `φ i : H → G i`, as in the resolving
theorem, which amalgamates subgroups along an order-preserving isomorphism. Arbitrary families of
factors are allowed, and the amalgam is Mathlib's `Monoid.PushoutI φ`. Right-orderable means a
linear order invariant under right multiplication.
-/

/-- `G` is right-orderable: it admits a linear order invariant under right multiplication. -/
def IsRightOrderable (G : Type*) [Group G] : Prop :=
  ∃ r : LinearOrder G, letI := r; ∀ a b c : G, a ≤ b → a * c ≤ b * c

/-- Kourovka 15.34 (V. V. Bludov): the free product of any family of linearly (two-sided) ordered
groups `G i` with an amalgamated subgroup `H`, embedded in each `G i` by an order-preserving
homomorphism `φ i`, is right-orderable. -/
def amalgamOfOrderedGroupsRightOrderable : Prop :=
  ∀ (ι : Type) (G : ι → Type) [∀ i, Group (G i)] [∀ i, LinearOrder (G i)]
    [∀ i, MulLeftMono (G i)] [∀ i, MulRightMono (G i)] (H : Type) [Group H] [LinearOrder H]
    [MulLeftMono H] [MulRightMono H] (φ : ∀ i, H →* G i),
    (∀ i, StrictMono (φ i)) → IsRightOrderable (Monoid.PushoutI φ)

/--
Resolved true: Bludov and Glass proved that the free product of (two-sided) ordered groups with
subgroups amalgamated along an order-preserving isomorphism is right-orderable, also for arbitrary
families of factors; the Kourovka Archive answers 15.34 "Yes, it is". Source: E. I. Khukhro and V.
D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.34 (V. V. Bludov); resolution: V.
V. Bludov and A. M. W. Glass, On free products of right ordered groups with amalgamated subgroups,
Math. Proc. Cambridge Philos. Soc. 146 (2009), 591-601, main theorem (the free product of ordered
groups G₁, G₂ with subgroups amalgamated via an order-preserving isomorphism is right orderable;
extended to arbitrary families); Kourovka Archive, Problem 15.34 (answer: Yes, it is).
-/
public theorem_wanted amalgamOfOrderedGroupsRightOrderable_holds :
    amalgamOfOrderedGroupsRightOrderable

end MathlibExt.GroupTheory.AmalgamatedOrderedGroupsRightOrderableKourovka15Problem34Wanted
