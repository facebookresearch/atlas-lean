/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets of element orders realized by finitely many groups (Kourovka Notebook Problem 12.84)

Kourovka Notebook, Archive of Solved Problems, Problem 12.84 (well-known problem; S. A. Syskin): is
it true that if there exist two non-isomorphic groups with a given set of orders of elements, then
there are infinitely many groups with this set of orders of elements?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.ElementOrderSetRealizationsKourovka12Problem84Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.84
(well-known problem; S. A. Syskin). UnsolvedMath record UM-00700901 (`KOU-12.84`), dataset
ulamai/UnsolvedMath v1.8.0.

Groups are finite, as in the recognition-by-spectrum problems this question belongs to; "infinitely
many" is "for every `k`, at least `k` pairwise non-isomorphic".
-/

/-- **The spectrum of a group (Kourovka 12.84).** The spectrum of a group $G$ is the set
$\{\operatorname{ord}(g) : g \in G\}$ of the orders of its elements, where an element of infinite
order is counted as having order $0$. -/
def elementOrders (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- **Syskin's question on groups with a given spectrum (Kourovka 12.84).** The proposition that
for every set $\Omega$ of natural numbers, if two non-isomorphic finite groups both have set of
element orders $\Omega$, then for every natural number $k$ there are $k$ pairwise non-isomorphic
finite groups whose set of element orders is $\Omega$; that is, infinitely many. -/
def twoRealizationsImplyInfinitelyMany : Prop :=
  ∀ Ω : Set ℕ,
    (∃ (G H : Type) (_ : Group G) (_ : Finite G) (_ : Group H) (_ : Finite H),
      elementOrders G = Ω ∧ elementOrders H = Ω ∧ IsEmpty (G ≃* H)) →
    ∀ k : ℕ, ∃ (G : Fin k → Type) (_ : ∀ i, Group (G i)) (_ : ∀ i, Finite (G i)),
      (∀ i, elementOrders (G i) = Ω) ∧ ∀ i j, i ≠ j → IsEmpty (G i ≃* G j)

/--
**Two isospectral finite groups do not force infinitely many.** There are a set $\Omega$ of
natural numbers and a natural number $k$ such that two non-isomorphic finite groups have set of
element orders $\Omega$, but there are no $k$ pairwise non-isomorphic finite groups whose set of
element orders is $\Omega$.

For example, by Theorem 2.1(iii) of the survey of Grechkoseeva, Mazurov, Shi, Vasil'ev and Yang,
the finite groups with the set of element orders of $S_6(2)$ are exactly $S_6(2)$ and
$O_8^+(2)$, which have different orders. The Kourovka Archive answers 12.84 "No, it is not"
(V. D. Mazurov, 1994).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 12.84 (well-known problem; S. A. Syskin); resolution: V. D. Mazurov,
Algebra and Logic 33 (1994), no. 1, 49-55; M. A. Grechkoseeva, V. D. Mazurov, W. Shi, A. V. Vasil'ev
and N. Yang, Finite groups isospectral to simple groups, arXiv:2111.15198, Kourovka Archive, Problem
12.84: No, it is not; Grechkoseeva et al., Theorem 2.1(iii): a finite group has the spectrum of
S_6(2) if and only if it is S_6(2) or O_8^+(2), https://arxiv.org/abs/2111.15198.
-/
public theorem_wanted twoRealizationsImplyInfinitelyMany_refuted :
    ¬ twoRealizationsImplyInfinitelyMany

end MathlibExt.GroupTheory.ElementOrderSetRealizationsKourovka12Problem84Wanted
