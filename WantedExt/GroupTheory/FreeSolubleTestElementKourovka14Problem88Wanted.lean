/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Test elements of free soluble groups of rank 2 (Kourovka Notebook Problem 14.88)

Kourovka Notebook, Archive of Solved Problems, Problem 14.88 (B. Fine, V. Shpilrain): an element `u`
of a group `G` is a test element if every endomorphism `φ` of `G` with `φ(u) = u` is an
automorphism. Does a free soluble group of rank `2` and derived length `d > 2` have any test
elements?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.FreeSolubleTestElementKourovka14Problem88Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.88 (B. Fine,
V. Shpilrain). UnsolvedMath record UM-00701072 (`KOU-14.88`), dataset ulamai/UnsolvedMath v1.8.0.

The free soluble group of rank `2` and derived length `d` is `F₂/F₂⁽ᵈ⁾`, the quotient of the free
group on two generators by the `d`-th term of its derived series. The question is read for every `d
> 2`, the range the Archive answer "Yes, it does" refers to. An automorphism is a bijective
endomorphism.
-/

/-- The free soluble group of rank `2` and derived length `d`: the quotient `F₂ / F₂⁽ᵈ⁾` of the free
group on two generators by the `d`-th term of its derived series. -/
abbrev FreeSolubleGroupRankTwo (d : ℕ) : Type :=
  FreeGroup (Fin 2) ⧸ derivedSeries (FreeGroup (Fin 2)) d

/-- **Test element.** An element $u$ of a group $G$ is a test element of $G$ if every endomorphism
$\varphi$ of $G$ with $\varphi(u) = u$ is bijective, that is, an automorphism of $G$. -/
def IsTestElement {G : Type*} [Group G] (u : G) : Prop :=
  ∀ φ : G →* G, φ u = u → Function.Bijective φ

/-- **Kourovka Problem 14.88 (test elements of free soluble groups of rank 2).** The statement that
for every integer $d > 2$ the free soluble group $F_2 / F_2^{(d)}$ of rank $2$ and derived length
$d$ has a test element, where $F_2$ is the free group on two generators and $F_2^{(d)}$ is the
$d$-th term of its derived series.

Kourovka Notebook Problem 14.88 is due to B. Fine and V. Shpilrain. -/
def freeSolubleRankTwoHasTestElement : Prop :=
  ∀ d : ℕ, 2 < d → ∃ u : FreeSolubleGroupRankTwo d, IsTestElement u

/--
Resolved true: the Kourovka Archive answers 14.88 "Yes, it does" (Timoshenko): for every `d > 2` the
free soluble group `F₂/F₂⁽ᵈ⁾` of rank `2` and derived length `d` has a test element. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.88 (B. Fine, V. Shpilrain);
resolution: E. I. Timoshenko, Computing test rank for a free solvable group, Algebra and Logic 45
(2006), no. 4, 254-260, main result (the test rank of a non-abelian free solvable group of finite
rank is one less than its rank, so F₂/F₂⁽ᵈ⁾ has test elements for every d > 2), as recorded in V.
Shpilrain's list of open problems in combinatorial group theory, problem (S9); Kourovka Archive,
Problem 14.88 (answer: Yes, it does), https://shpilrain.ccny.cuny.edu/gworld/problems/Back2.html.
-/
public theorem_wanted freeSolubleRankTwoHasTestElement_holds : freeSolubleRankTwoHasTestElement

end MathlibExt.GroupTheory.FreeSolubleTestElementKourovka14Problem88Wanted
