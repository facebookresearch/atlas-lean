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

/-- The set of orders of elements of `G`. -/
def elementOrders (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- Kourovka 12.84 (S. A. Syskin; well-known problem): if two non-isomorphic finite groups have
the same set `Ω` of element orders, then there are infinitely many pairwise non-isomorphic finite
groups with set of element orders `Ω` (for every `k`, at least `k` of them). -/
def twoRealizationsImplyInfinitelyMany : Prop :=
  ∀ Ω : Set ℕ,
    (∃ (G H : Type) (_ : Group G) (_ : Finite G) (_ : Group H) (_ : Finite H),
      elementOrders G = Ω ∧ elementOrders H = Ω ∧ IsEmpty (G ≃* H)) →
    ∀ k : ℕ, ∃ (G : Fin k → Type) (_ : ∀ i, Group (G i)) (_ : ∀ i, Finite (G i)),
      (∀ i, elementOrders (G i) = Ω) ∧ ∀ i j, i ≠ j → IsEmpty (G i ≃* G j)

/--
Resolved false: the Kourovka Archive answers 12.84 "No, it is not" (V. D. Mazurov, 1994): some set
of element orders is realized by at least two, but only finitely many, pairwise non-isomorphic
finite groups. For example, by Theorem 2.1(iii) of the survey of Grechkoseeva, Mazurov, Shi,
Vasil'ev and Yang, the finite groups with the set of element orders of `S₆(2)` are exactly `S₆(2)`
and `O₈⁺(2)`, which have different orders. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
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
