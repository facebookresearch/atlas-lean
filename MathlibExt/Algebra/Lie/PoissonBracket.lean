/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Poisson-bracket interface over commutative `ℂ`-algebras: brackets,
Poisson ideals and primes, Poisson cores with their universal
property, and basic closure lemmas.
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Bounds.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.Ideal.Prime

@[expose] public section

namespace MathlibExt.Algebra.Lie.PoissonBracket

/-- **Poisson bracket.** Let $A$ be a commutative $\mathbb{C}$-algebra. A Poisson bracket on $A$
is a map assigning to $x, y \in A$ an element $\lbrace x, y \rbrace \in A$ such that for all
$x, y, z \in A$ and $c \in \mathbb{C}$: $\lbrace x + y, z \rbrace = \lbrace x, z \rbrace +
\lbrace y, z \rbrace$ and $\lbrace x, y + z \rbrace = \lbrace x, y \rbrace + \lbrace x, z \rbrace$;
$\lbrace x, y \rbrace = -\lbrace y, x \rbrace$; the Leibniz rule
$\lbrace x, yz \rbrace = y \lbrace x, z \rbrace + \lbrace x, y \rbrace z$ holds; the Jacobi
identity $\lbrace x, \lbrace y, z \rbrace \rbrace + \lbrace y, \lbrace z, x \rbrace \rbrace +
\lbrace z, \lbrace x, y \rbrace \rbrace = 0$ holds; and $\lbrace c x, y \rbrace =
c \lbrace x, y \rbrace$ and $\lbrace x, c y \rbrace = c \lbrace x, y \rbrace$. -/
structure PoissonBracket (A : Type) [CommRing A] [Algebra ℂ A] where
  bracket : A → A → A
  add_left : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  add_right : ∀ x y z, bracket x (y + z) = bracket x y + bracket x z
  skew : ∀ x y, bracket x y = -bracket y x
  leibniz : ∀ x y z, bracket x (y * z) = y * bracket x z + bracket x y * z
  jacobi : ∀ x y z,
    bracket x (bracket y z) + bracket y (bracket z x) +
      bracket z (bracket x y) = 0
  smul_left : ∀ (c : ℂ) (x y : A),
    bracket (c • x) y = c • bracket x y
  smul_right : ∀ (c : ℂ) (x y : A),
    bracket x (c • y) = c • bracket x y

/-- **Poisson ideal.** Let $A$ be a commutative $\mathbb{C}$-algebra with a Poisson bracket
$\lbrace \cdot, \cdot \rbrace$. An ideal $P$ of $A$ is a Poisson ideal when
$\lbrace a, p \rbrace \in P$ for all $a \in A$ and all $p \in P$. -/
def IsPoissonIdeal (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (P : Ideal A) : Prop :=
  ∀ (a p : A), p ∈ P → br.bracket a p ∈ P

/-- **Poisson prime ideal.** Let $A$ be a commutative $\mathbb{C}$-algebra with a Poisson bracket.
An ideal $P$ of $A$ is a Poisson prime when it is both a prime ideal and a Poisson ideal. -/
def IsPoissonPrime (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (P : Ideal A) : Prop :=
  P.IsPrime ∧ IsPoissonIdeal A br P

/-- **Poisson core.** Let $A$ be a commutative $\mathbb{C}$-algebra with a Poisson bracket. For an
ideal $J$ of $A$, the Poisson core of $J$ is the supremum, in the lattice of ideals of $A$, of the
set of all Poisson ideals of $A$ contained in $J$.

It is the largest Poisson ideal contained in $J$ (universal property of the Poisson core). -/
def poissonCore (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) : Ideal A :=
  sSup {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}

/-- **Bracket with zero.** Let $A$ be a commutative $\mathbb{C}$-algebra with a Poisson bracket
$\lbrace \cdot, \cdot \rbrace$. For every $a \in A$, $\lbrace a, 0 \rbrace = 0$. -/
theorem bracket_zero (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (a : A) : br.bracket a 0 = 0 := by
  have h := br.add_right a 0 0
  rw [add_zero] at h
  have h2 : br.bracket a 0 + 0 = br.bracket a 0 + br.bracket a 0 := by
    rw [add_zero]
    exact h
  have := add_left_cancel h2
  simpa using this.symm

/-- **The zero ideal is a Poisson ideal.** Let $A$ be a commutative $\mathbb{C}$-algebra with a
Poisson bracket. The zero ideal of $A$ is a Poisson ideal. -/
theorem bot_poisson (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) : IsPoissonIdeal A br ⊥ := by
  intro a p hp
  rw [Submodule.mem_bot] at hp
  rw [hp, bracket_zero]
  exact Submodule.zero_mem _

/-- **The sum of two Poisson ideals inside an ideal.** Let $A$ be a commutative
$\mathbb{C}$-algebra with a Poisson bracket, and let $I$, $K$ and $J$ be ideals of $A$. If $I$
and $K$ are Poisson ideals contained in $J$, then their sum $I + K$ is a Poisson ideal contained
in $J$. -/
theorem sup_poisson {A : Type} [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A)
    {J I K : Ideal A} (hI : I ≤ J ∧ IsPoissonIdeal A br I)
    (hK : K ≤ J ∧ IsPoissonIdeal A br K) :
    I ⊔ K ≤ J ∧ IsPoissonIdeal A br (I ⊔ K) := by
  refine ⟨sup_le hI.1 hK.1, fun a x hx => ?_⟩
  obtain ⟨i, hi, k, hk, rfl⟩ := Submodule.mem_sup.mp hx
  rw [br.add_right]
  exact add_mem (Ideal.mem_sup_left (hI.2 a i hi))
    (Ideal.mem_sup_right (hK.2 a k hk))

/-- **The Poisson core is a Poisson ideal.** Let $A$ be a commutative $\mathbb{C}$-algebra with a
Poisson bracket. For every ideal $J$ of $A$, the Poisson core of $J$ is a Poisson ideal.

The family of Poisson ideals contained in $J$ is nonempty and directed (the sum of two members
is again a member), so every element of the core lies in some member of the family. -/
theorem poissonCore_poisson (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) :
    IsPoissonIdeal A br (poissonCore A br J) := by
  have hne : {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}.Nonempty :=
    ⟨⊥, bot_le, bot_poisson A br⟩
  have hdir : DirectedOn (· ≤ ·)
      {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P} := by
    intro I hI K hK
    exact ⟨I ⊔ K, sup_poisson br hI hK, le_sup_left, le_sup_right⟩
  have hmem {z : A} : z ∈ sSup {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P} ↔
      ∃ y ∈ {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}, z ∈ y :=
    Submodule.mem_sSup_of_directed hne hdir
  intro a p hp
  rw [poissonCore] at hp ⊢
  obtain ⟨I, hI, hpI⟩ := hmem.mp hp
  exact hmem.mpr ⟨I, hI, hI.2 a p hpI⟩

/-- **The Poisson core is contained in the ideal.** Let $A$ be a commutative $\mathbb{C}$-algebra
with a Poisson bracket. For every ideal $J$ of $A$, the Poisson core of $J$ is contained in $J$. -/
theorem poissonCore_le (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) :
    poissonCore A br J ≤ J :=
  sSup_le (fun P hP => hP.1)

/-- **Poisson ideals inside an ideal lie in its Poisson core.** Let $A$ be a commutative
$\mathbb{C}$-algebra with a Poisson bracket, and let $J$ and $P$ be ideals of $A$. If
$P \subseteq J$ and $P$ is a Poisson ideal, then $P$ is contained in the Poisson core of $J$. -/
theorem le_poissonCore (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) {J P : Ideal A}
    (hP : P ≤ J ∧ IsPoissonIdeal A br P) :
    P ≤ poissonCore A br J :=
  le_sSup hP

/-- **Universal property of the Poisson core.** Let $A$ be a commutative $\mathbb{C}$-algebra
with a Poisson bracket. For every ideal $J$ of $A$, the Poisson core of $J$ is the greatest
element of the set of Poisson ideals of $A$ contained in $J$: it is a Poisson ideal contained in
$J$, and it contains every Poisson ideal of $A$ contained in $J$. -/
theorem poissonCore_isGreatest (A : Type) [CommRing A] [Algebra ℂ A]
    (br : PoissonBracket A) (J : Ideal A) :
    IsGreatest {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}
      (poissonCore A br J) :=
  ⟨⟨poissonCore_le A br J, poissonCore_poisson A br J⟩,
    fun P hP => le_poissonCore A br hP⟩

end MathlibExt.Algebra.Lie.PoissonBracket
