/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A unique product group that is not left-orderable (Kourovka Notebook Problem 15.49)

Kourovka Notebook, Archive of Solved Problems, Problem 15.49 (P. Linnell): a group `G` is a unique
product group if, for any finite nonempty subsets `X, Y` of `G`, some element of `G` can be written
in exactly one way as `x y` with `x ∈ X` and `y ∈ Y`. Does there exist a unique product group which
is not left-orderable?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.UniqueProds.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.UniqueProductNotLeftOrderableKourovka15Problem49Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.49 (P.
Linnell). UnsolvedMath record UM-00701137 (`KOU-15.49`), dataset ulamai/UnsolvedMath v1.8.0.

The unique product property is Mathlib's `UniqueProds`: for finite nonempty `A, B` some `a₀ ∈ A`,
`b₀ ∈ B` form the only pair with product `a₀ b₀`. Left-orderable means a linear order invariant
under left multiplication.
-/

/-- `G` is left-orderable: it admits a linear order invariant under left multiplication. -/
def IsLeftOrderable (G : Type*) [Group G] : Prop :=
  ∃ r : LinearOrder G, letI := r; ∀ a b c : G, a ≤ b → c * a ≤ c * b

/-- Kourovka 15.49 (P. Linnell): there is a unique product group that is not left-orderable.
Mathlib's `UniqueProds G` says that for all finite nonempty `X, Y ⊆ G` some product `x y` has
exactly one such representation. -/
def uniqueProductGroupNotLeftOrderable : Prop :=
  ∃ (G : Type) (_ : Group G), UniqueProds G ∧ ¬ IsLeftOrderable G

/--
Resolved true: the Kourovka Archive answers 15.49 "Yes, there does", citing Dunfield's appendix to
the paper of Kionke and Raimbault, which gives a unique product group that is not left-orderable.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.49 (P.
Linnell); resolution: N. Dunfield, Appendix B in S. Kionke and J. Raimbault, On geometric aspects of
diffuse groups, Doc. Math. 21 (2016), 873-915, arXiv:1411.6449, Section 2.2 and the appendix
(diffuse groups have unique products, by Bowditch's observation; the appendix gives a compact
hyperbolic 3-manifold group that is diffuse but not left-orderable); Kourovka Archive, Problem 15.49
(answer: Yes, there does), https://arxiv.org/abs/1411.6449.
-/
public theorem_wanted uniqueProductGroupNotLeftOrderable_holds : uniqueProductGroupNotLeftOrderable

end MathlibExt.GroupTheory.UniqueProductNotLeftOrderableKourovka15Problem49Wanted
