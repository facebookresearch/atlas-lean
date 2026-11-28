/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Frobenius

/-!
# Arithmetic Frobenius is independent of the prime above in abelian extensions

ATLAS source: [`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, lines 714--729](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L714-L729)
(`arithFrobAt_eq_of_under_eq`), frozen at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`.

Source-to-API mapping: frozen ATLAS `RayClassFields.lean` lines 714--729, source
declaration `arithFrobAt_eq_of_under_eq`, maps to this module's root declaration
`arithFrobAt_eq_of_under_eq`.

This module is N402 C2a only: the arithmetic Frobenius elements at two primes
lying over the same base prime are equal when the acting group is commutative.
The source proves this by obtaining Mathlib's conjugacy theorem
(`isConj_arithFrobAt`) and collapsing the conjugacy by commutativity
(membership in the center). Chosen-prime constructions, restriction-equality
results, Artin maps, and the final compatibility stages are excluded.

Generalized from the source's number-field Galois group
(`L ≃ₐ[K] L` with `KroneckerWeber.IsAbelianExtension K L`) to Mathlib's natural
Frobenius setting (`Group G` with `IsMulCommutative G`). No unramifiedness
hypothesis is required.

This declaration lives in the root namespace, matching `arithFrobAt` and
`isConj_arithFrobAt`.
-/

@[expose] public section

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Finite G] [Algebra.IsInvariant R S G]

/-- **In an abelian group the Frobenius element depends only on the prime below.** Let $S$ be
a commutative algebra over a commutative ring $R$, and let a finite commutative group $G$ act on
$S$ by $R$-algebra automorphisms such that every element of $S$ fixed by $G$ is the image of an
element of $R$. For a prime $Q$ of $S$ with $S/Q$ finite, let $\mathrm{Frob}_Q \in G$ be the
chosen arithmetic Frobenius element at $Q$: an element $\sigma \in G$ with
$\sigma(x) \equiv x^q \pmod Q$ for all $x \in S$, where $q$ is the number of elements of $R$
modulo the preimage of $Q$ in $R$, chosen so that the elements chosen at primes with the same
preimage in $R$ are conjugate. If $Q$ and $Q'$ are primes of $S$ with $S/Q$ and $S/Q'$ finite
that have the same preimage in $R$, then $\mathrm{Frob}_Q = \mathrm{Frob}_{Q'}$. -/
theorem arithFrobAt_eq_of_under_eq [IsMulCommutative G]
    (Q Q' : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Q'.IsPrime] [Finite (S ⧸ Q')]
    (h : Q.under R = Q'.under R) :
    arithFrobAt R G Q = arithFrobAt R G Q' := by
  have hconj := isConj_arithFrobAt R G Q Q' h
  rw [isConj_iff] at hconj
  obtain ⟨c, hc⟩ := hconj
  have htriv : c * arithFrobAt R G Q * c⁻¹ = arithFrobAt R G Q := by
    rw [mul_comm' c (arithFrobAt R G Q), mul_assoc, mul_inv_cancel, mul_one]
  exact htriv.symm.trans hc
