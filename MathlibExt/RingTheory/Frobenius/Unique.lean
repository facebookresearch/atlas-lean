/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Frobenius

@[expose] public section

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  {Q : Ideal S} {σ σ' : G}

namespace IsArithFrobAt

/-- **Frobenius elements coincide when inertia is trivial.** Let $R$ and $S$ be commutative rings
with $S$ an $R$-algebra, let a group $G$ act on $S$ by $R$-algebra automorphisms, and let $Q$ be
an ideal of $S$. Write $P$ for the preimage of $Q$ in $R$ and $q$ for the number of elements of
$R/P$ (with $q = 0$ when $R/P$ is infinite). Call $\sigma \in G$ an arithmetic Frobenius element at
$Q$ if $\sigma x - x^q \in Q$ for all $x \in S$, and call the inertia subgroup of $Q$ the set of
$\tau \in G$ with $\tau x - x \in Q$ for all $x \in S$. If $\sigma, \sigma' \in G$ are arithmetic
Frobenius elements at $Q$ and the inertia subgroup of $Q$ is trivial, then $\sigma = \sigma'$. -/
theorem eq_of_inertia_eq_bot (hσ : IsArithFrobAt R σ Q)
    (hσ' : IsArithFrobAt R σ' Q) (hbot : Q.inertia G = ⊥) : σ = σ' := by
  have hmem : σ * σ'⁻¹ ∈ Q.inertia G := hσ.mul_inv_mem_inertia hσ'
  rw [hbot] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

/-- **Existence and uniqueness of the Frobenius element under trivial inertia.** Let $R$ and $S$
be commutative rings with $S$ an $R$-algebra, and let a finite group $G$ act on $S$ by
$R$-algebra automorphisms such that every element of $S$ fixed by $G$ is the image of an element
of $R$. Let $Q$ be a prime ideal of $S$ with $S/Q$ finite, write $P$ for the preimage of $Q$ in
$R$ and $q$ for the number of elements of $R/P$. Call $\sigma \in G$ an arithmetic Frobenius
element at $Q$ if $\sigma x - x^q \in Q$ for all $x \in S$. If the inertia subgroup of $Q$, the set
of $\tau \in G$ with $\tau x - x \in Q$ for all $x \in S$, is trivial, then there is exactly one
arithmetic Frobenius element at $Q$ in $G$. -/
theorem existsUnique_of_inertia_eq_bot [Finite G] [Algebra.IsInvariant R S G]
    [Q.IsPrime] [Finite (S ⧸ Q)] (hbot : Q.inertia G = ⊥) :
    ∃! σ : G, IsArithFrobAt R σ Q := by
  obtain ⟨σ₀, h₀⟩ := exists_of_isInvariant R G Q
  exact ⟨σ₀, h₀, fun σ' h' => eq_of_inertia_eq_bot h' h₀ hbot⟩

end IsArithFrobAt
