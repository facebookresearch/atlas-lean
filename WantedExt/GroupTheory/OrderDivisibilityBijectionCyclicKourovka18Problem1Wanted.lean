/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Order-divisibility bijections onto cyclic groups (Kourovka Notebook Problem 18.1)

Kourovka Notebook, Problem 18.1 (I. M. Isaacs): given a group `G` of finite order `n`, does there
necessarily exist a bijection `f` from `G` onto a cyclic group of order `n` such that for each
element `x ∈ G`, the order of `x` divides the order of `f(x)`? (An affirmative answer for soluble
`G` was given by F. Ladisch.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.OrderDivisibilityBijectionCyclicKourovka18Problem1Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.1 (I. M. Isaacs). UnsolvedMath record
UM-00701430 (`KOU-18.1`), dataset ulamai/UnsolvedMath v1.8.0.

The cyclic group of order `n = |G|` is `ZMod n` with additive orders `addOrderOf`.
-/

/-- **Kourovka Problem 18.1 (statement).** The statement that for every finite group $G$, of order
$n$ say, there is a bijection $f$ from $G$ onto the cyclic group $\mathbb{Z}/n\mathbb{Z}$ such that
for every $x \in G$ the order of $x$ divides the additive order of $f(x)$. -/
def orderDivisibilityBijectionToCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ∃ f : G ≃ ZMod (Nat.card G),
    ∀ x : G, orderOf x ∣ addOrderOf (f x)

/--
**Amiri's theorem (Kourovka Problem 18.1).** For every finite group $G$, of order $n$ say, there is
a bijection $f$ from $G$ onto the cyclic group $\mathbb{Z}/n\mathbb{Z}$ such that for every
$x \in G$ the order of $x$ divides the additive order of $f(x)$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.1 (I. M. Isaacs); resolution: M. Amiri,
J. Pure Appl. Algebra 228 (2024), no. 7, 107632 (preprint arXiv:2002.11455), abstract (for any
finite group G of order n there is a bijection f from G onto C_n with o(x) | o(f(x)) for all x); the
Kourovka Notebook (21st issue) marks 18.1 solved (Yes, it does), https://arxiv.org/abs/2002.11455.
-/
public theorem_wanted orderDivisibilityBijectionToCyclic_holds : orderDivisibilityBijectionToCyclic

end MathlibExt.GroupTheory.OrderDivisibilityBijectionCyclicKourovka18Problem1Wanted
