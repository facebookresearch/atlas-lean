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

/-- **Left-orderable groups.** A group $G$ is left-orderable if it admits a linear order $\le$ such
that $a \le b$ implies $ca \le cb$ for all $a, b, c \in G$. -/
def IsLeftOrderable (G : Type*) [Group G] : Prop :=
  ∃ r : LinearOrder G, letI := r; ∀ a b c : G, a ≤ b → c * a ≤ c * b

/-- **Kourovka Problem 15.49 (unique product groups and left orders).** The statement, asked by
P. Linnell, that there exists a group $G$ with unique products that is not left-orderable. Here $G$
has unique products if for all finite nonempty subsets $X, Y \subseteq G$ there are $x_0 \in X$ and
$y_0 \in Y$ such that $(x_0, y_0)$ is the only pair $(x, y) \in X \times Y$ with $xy = x_0 y_0$. -/
def uniqueProductGroupNotLeftOrderable : Prop :=
  ∃ (G : Type) (_ : Group G), UniqueProds G ∧ ¬ IsLeftOrderable G

/-- **A unique product group need not be left-orderable.** There exists a group $G$ that has unique
products but is not left-orderable: for all finite nonempty subsets $X, Y \subseteq G$ there are
$x_0 \in X$ and $y_0 \in Y$ such that $(x_0, y_0)$ is the only pair $(x, y) \in X \times Y$ with
$xy = x_0 y_0$, and yet $G$ admits no linear order invariant under left multiplication.

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
