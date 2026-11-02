/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.RingTheory.Frobenius

/-!
# Conjugacy class of the arithmetic Frobenius at an unramified prime

Let `S` be a commutative `R`-algebra with a semilinear action of a finite group `G`
fixing `R` pointwise (`Algebra.IsInvariant R S G`), and let `Q` be a prime of `S`
with finite residue field at which `S` is unramified over `R`. Mathlib provides an
arbitrary choice of Frobenius element `arithFrobAt R G Q : G` at `Q`, well defined
up to conjugacy over each prime of `R` (`isConj_arithFrobAt`).

This module packages that choice as a conjugacy class:

* `arithFrobConjClass`: the conjugacy class of `arithFrobAt R G Q`.
* `arithFrobConjClass_mem_carrier`: the chosen Frobenius lies in the class.
* `arithFrobConjClass_eq_of_under_eq`: primes lying over the same prime of `R`
  give the same class.

These declarations live in the root namespace, matching `arithFrobAt` and
`isConj_arithFrobAt`.
-/

@[expose] public section

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
  [Finite G] [Algebra.IsInvariant R S G]

/-- **Frobenius conjugacy class.** Let $S$ be a commutative algebra over a commutative ring $R$,
and let a finite group $G$ act on $S$ by $R$-algebra automorphisms such that every element of
$S$ fixed by $G$ is the image of an element of $R$. Let $Q$ be a prime of $S$ with $S/Q$ finite
at which $S$ is unramified over $R$ (the localization $S_Q$ is formally unramified over $R$).
The Frobenius conjugacy class at $Q$ is the conjugacy class in $G$ of the chosen arithmetic
Frobenius element $\mathrm{Frob}_Q$ at $Q$: an element $\sigma \in G$ with
$\sigma(x) \equiv x^q \pmod Q$ for all $x \in S$, where $q$ is the number of elements of $R$
modulo the preimage of $Q$ in $R$, chosen so that the elements chosen at primes with the same
preimage in $R$ are conjugate. -/
noncomputable def arithFrobConjClass (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Algebra.IsUnramifiedAt R Q] : ConjClasses G :=
  ConjClasses.mk (arithFrobAt R G Q)

/-- **The Frobenius element lies in the Frobenius conjugacy class.** Let a finite group $G$ act
on a commutative algebra $S$ over a commutative ring $R$ by $R$-algebra automorphisms such that
every element of $S$ fixed by $G$ is the image of an element of $R$. For every prime $Q$ of $S$
with $S/Q$ finite at which $S$ is unramified over $R$, the chosen arithmetic Frobenius element
$\mathrm{Frob}_Q$ at $Q$ belongs to the Frobenius conjugacy class at $Q$. -/
theorem arithFrobConjClass_mem_carrier (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    [Algebra.IsUnramifiedAt R Q] :
    arithFrobAt R G Q ∈ (arithFrobConjClass (R := R) (G := G) Q).carrier :=
  ConjClasses.mem_carrier_mk

/-- **The Frobenius conjugacy class depends only on the prime below.** Let a finite group $G$
act on a commutative algebra $S$ over a commutative ring $R$ by $R$-algebra automorphisms such
that every element of $S$ fixed by $G$ is the image of an element of $R$. Let $Q$ and $Q'$ be
primes of $S$ with $S/Q$ and $S/Q'$ finite at which $S$ is unramified over $R$. If $Q$ and $Q'$
have the same preimage in $R$, then the Frobenius conjugacy classes at $Q$ and $Q'$ are
equal. -/
theorem arithFrobConjClass_eq_of_under_eq (Q Q' : Ideal S) [Q.IsPrime]
    [Finite (S ⧸ Q)] [Algebra.IsUnramifiedAt R Q] [Q'.IsPrime]
    [Finite (S ⧸ Q')] [Algebra.IsUnramifiedAt R Q']
    (h : Q.under R = Q'.under R) :
    arithFrobConjClass (R := R) (G := G) Q =
      arithFrobConjClass (R := R) (G := G) Q' := by
  unfold arithFrobConjClass
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_arithFrobAt R G Q Q' h
