/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mutually non-embedded groups with equal spectra (Kourovka Notebook Problem 16.106)

Kourovka Notebook, Archive of Solved Problems, Problem 16.106 (W. J. Shi): let `π_e(G)` denote the
set of orders of elements of `G` and `h(Γ)` the number of non-isomorphic finite groups `G` with
`π_e(G) = Γ`. Do there exist finite groups `G₁`, `G₂` such that `π_e(G₁) = π_e(G₂)`, `h(π_e(G₁)) <
∞`, and neither of them is isomorphic to a subgroup or a quotient of a normal subgroup of the other?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.SameSpectrumIncomparableGroupsKourovka16Problem106Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.106 (W. J.
Shi). UnsolvedMath record UM-00701297 (`KOU-16.106`), dataset ulamai/UnsolvedMath v1.8.0.

`h(Γ) < ∞` is stated as a bound on the orders of the finite groups with spectrum `Γ`, which is
equivalent since there are finitely many groups of each order. A quotient of a normal subgroup of
`B` is the image of some `N ⊴ B` under a surjective homomorphism.
-/

/-- **Element-order spectrum of a group.** The spectrum $\pi_e(G)$ of a group $G$ is the set of
orders of the elements of $G$, where an element of infinite order counts as having order $0$. -/
def elementOrders (G : Type*) [Group G] : Set ℕ :=
  Set.range (orderOf : G → ℕ)

/-- **Subgroup or quotient of a normal subgroup.** For groups $A$ and $B$, the statement that $A$
is isomorphic to a subgroup of $B$ or to a quotient of a normal subgroup of $B$: there is an
injective homomorphism $A \to B$, or there are a normal subgroup $N$ of $B$ and a surjective
homomorphism $N \to A$. -/
def IsSubgroupOrNormalSectionOf (A B : Type*) [Group A] [Group B] : Prop :=
  (∃ f : A →* B, Function.Injective f) ∨
    ∃ N : Subgroup B, N.Normal ∧ ∃ f : N →* A, Function.Surjective f

/-- **Finite groups with equal spectra, neither a subgroup or normal-subgroup quotient of the
other (problem).** The statement that there exist finite groups $G_1$ and $G_2$ with the same
spectrum $\pi_e(G_1) = \pi_e(G_2)$ (the set of orders of elements), such that every finite group
with spectrum $\pi_e(G_1)$ has order at most some fixed bound $B$, and such that neither of $G_1$,
$G_2$ is isomorphic to a subgroup or to a quotient of a normal subgroup of the other.

This is Kourovka Notebook Problem 16.106 (W. J. Shi), which asks for $h(\pi_e(G_1)) < \infty$,
where $h(\Gamma)$ is the number of finite groups with spectrum $\Gamma$ up to isomorphism; the
bound on orders is equivalent, since there are finitely many groups of each order. -/
def sameSpectrumIncomparableGroups : Prop :=
  ∃ (G₁ G₂ : Type) (_ : Group G₁) (_ : Group G₂) (_ : Finite G₁) (_ : Finite G₂),
    elementOrders G₁ = elementOrders G₂ ∧
    (∃ B : ℕ, ∀ (G : Type) [Group G] [Finite G], elementOrders G = elementOrders G₁ →
      Nat.card G ≤ B) ∧
    ¬ IsSubgroupOrNormalSectionOf G₁ G₂ ∧ ¬ IsSubgroupOrNormalSectionOf G₂ G₁

/--
**Finite groups with equal spectra, neither a subgroup or normal-subgroup quotient of the other
(Kourovka 16.106).** There exist finite groups $G_1$ and $G_2$ such that:

- $G_1$ and $G_2$ have the same spectrum, where the spectrum $\pi_e(G)$ of a group $G$ is the set
  of orders of its elements;
- there is a bound $B$ such that every finite group $G$ with $\pi_e(G) = \pi_e(G_1)$ has order at
  most $B$;
- $G_1$ is not isomorphic to a subgroup of $G_2$ or to a quotient of a normal subgroup of $G_2$,
  and $G_2$ is not isomorphic to a subgroup of $G_1$ or to a quotient of a normal subgroup of $G_1$.

The bound on orders says that only finitely many finite groups have spectrum $\pi_e(G_1)$, up to
isomorphism. The Kourovka Archive gives the example $G_1 = L_{15}(2^{60}).3$ and
$G_2 = L_{15}(2^{60}).5$ (Grechkoseeva).

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 16.106 (W. J. Shi); resolution: M. A. Grechkoseeva, Algebra and
Logic 47 (2008), no. 4, 229-241, Kourovka Archive, Problem 16.106 (answer: Yes, there do, for
example G₁ = L₁₅(2⁶⁰).3 and G₂ = L₁₅(2⁶⁰).5).
-/
public theorem_wanted sameSpectrumIncomparableGroups_holds : sameSpectrumIncomparableGroups

end MathlibExt.GroupTheory.SameSpectrumIncomparableGroupsKourovka16Problem106Wanted
