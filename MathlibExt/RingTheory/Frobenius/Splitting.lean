/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Frobenius

@[expose] public section

open scoped Pointwise

namespace Ideal

section SplitsCompletely

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {p : Ideal A} {P : Ideal B} [P.IsPrime] [P.LiesOver p]

/-- **Trivial decomposition group and the number of primes above.** Let $B$ be a commutative
algebra over a commutative ring $A$, and let a finite group $G$ act on $B$ by $A$-algebra
automorphisms such that every element of $B$ fixed by $G$ is the image of an element of $A$. Let
$p$ be an ideal of $A$ and $P$ a prime of $B$ lying over $p$. Then the stabilizer of $P$ in $G$
(the decomposition group of $P$) is trivial if and only if the number of primes of $B$ lying
over $p$ equals the order of $G$. -/
theorem stabilizer_eq_bot_iff_ncard_primesOver_eq_card :
    MulAction.stabilizer G P = ⊥ ↔ (primesOver p B).ncard = Nat.card G := by
  have hfund : (primesOver p B).ncard * Nat.card (MulAction.stabilizer G P)
      = Nat.card G := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver A B G p P]
    simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hNpos : (primesOver p B).ncard ≠ 0 := by
    grind [Nat.card_pos]
  rw [← Subgroup.card_eq_one]
  constructor
  · intro hE1
    rw [hE1, mul_one] at hfund
    exact hfund
  · intro hNC
    have h1 : (primesOver p B).ncard * Nat.card (MulAction.stabilizer G P)
        = (primesOver p B).ncard * 1 := by
      rw [hfund, hNC, mul_one]
    exact mul_left_cancel₀ hNpos h1

end SplitsCompletely

end Ideal

section Conditional

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  {p : Ideal A} {P : Ideal B} [P.IsPrime] [P.LiesOver p]

/-- **Trivial Frobenius and the number of primes above, assuming the Frobenius generates.**
Let $B$ be a commutative algebra over a commutative ring $A$, and let a finite group $G$ act on
$B$ by $A$-algebra automorphisms such that every element of $B$ fixed by $G$ is the image of an
element of $A$. Let $p$ be an ideal of $A$ and $P$ a prime of $B$ lying over $p$ with $B/P$
finite, and let $\mathrm{Frob}_P \in G$ be the chosen arithmetic Frobenius element at $P$, an
element $\sigma \in G$ with $\sigma(x) \equiv x^q \pmod P$ for all $x \in B$, where $q$ is the
number of elements of $A/p$. Suppose every element of the stabilizer of $P$ in $G$ equals
$\mathrm{Frob}_P^n$ for some natural number $n$. Then $\mathrm{Frob}_P = 1$ if and only if the
number of primes of $B$ lying over $p$ equals the order of $G$. -/
theorem arithFrobAt_eq_one_iff_ncard_primesOver_eq_card_of_generates
    [Finite (B ⧸ P)]
    (hgen : ∀ g ∈ MulAction.stabilizer G P,
      ∃ n : ℕ, g = arithFrobAt A G P ^ n) :
    arithFrobAt A G P = 1 ↔ (Ideal.primesOver p B).ncard = Nat.card G := by
  have hmem : arithFrobAt A G P ∈ MulAction.stabilizer G P :=
    IsArithFrobAt.arithFrobAt_mem_stabilizer A G P
  have hstab : MulAction.stabilizer G P = ⊥ ↔ arithFrobAt A G P = 1 := by
    constructor
    · intro h
      rw [h] at hmem
      exact Subgroup.mem_bot.mp hmem
    · intro h
      rw [eq_bot_iff]
      intro g hg
      obtain ⟨n, hn⟩ := hgen g hg
      rw [h, one_pow] at hn
      exact Subgroup.mem_bot.mpr hn
  rw [← hstab]
  exact Ideal.stabilizer_eq_bot_iff_ncard_primesOver_eq_card

end Conditional

section Unramified

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [Algebra A B] [Module.Finite A B] [Module.Flat A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B]
  {p : Ideal A} [p.IsPrime] {P : Ideal B} [P.IsPrime] [P.LiesOver p]
  [PerfectField p.ResidueField]

/-- **The Frobenius element generates the decomposition group at an unramified prime.** Let $A$
and $B$ be integral domains with $B$ a finite flat $A$-algebra, and let $G$ be a finite group
acting faithfully on $B$ by $A$-algebra automorphisms such that every element of $B$ fixed by
$G$ is the image of an element of $A$. Let $p$ be a prime of $A$ and $P$ a prime of $B$ lying
over $p$, with $B/P$ finite and $B$ unramified over $A$ at $P$ (the localization $B_P$ is
formally unramified over $A$). Let $\mathrm{Frob}_P \in G$ be the chosen arithmetic Frobenius
element at $P$, an element $\sigma \in G$ with $\sigma(x) \equiv x^q \pmod P$ for all
$x \in B$, where $q$ is the number of elements of $A/p$. Then every element of the stabilizer of
$P$ in $G$ (the decomposition group of $P$) equals $\mathrm{Frob}_P^n$ for some natural
number $n$. -/
theorem arithFrobAt_generates_stabilizer_of_isUnramifiedAt
    (p : Ideal A) [p.IsPrime] [P.LiesOver p]
    [Finite (B ⧸ P)] [Algebra.IsUnramifiedAt A P] :
    ∀ g ∈ MulAction.stabilizer G P,
      ∃ n : ℕ, g = arithFrobAt A G P ^ n := by
  let _ : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  let _ : P.IsMaximal :=
    Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain (B ⧸ P))
  let _ : p.IsMaximal := Ideal.IsMaximal.of_isMaximal_liesOver P p
  let _ : Finite (A ⧸ p) :=
    Finite.of_injective (algebraMap (A ⧸ p) (B ⧸ P))
      (FaithfulSMul.algebraMap_injective (A ⧸ p) (B ⧸ P))
  let _ : Fintype (A ⧸ p) := Fintype.ofFinite (A ⧸ p)
  let _ : Fintype (B ⧸ P) := Fintype.ofFinite (B ⧸ P)
  let _ : Field (A ⧸ p) := Ideal.Quotient.field p
  let _ : Field (B ⧸ P) := Ideal.Quotient.field P
  have hram : P.ramificationIdx A = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hcard : Nat.card (P.inertia G) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn p P,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P G, hram]
  have hbot : P.inertia G = ⊥ := Subgroup.card_eq_one.mp hcard
  have hrho : Function.Injective (Ideal.Quotient.stabilizerHom P p G) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hmap : (Ideal.Quotient.stabilizerHom P p G).ker.map
        (Subgroup.subtype _) = ⊥ := by
      rw [Ideal.Quotient.map_ker_stabilizer_subtype, hbot]
    exact
      (Subgroup.map_eq_bot_iff_of_injective
        (Ideal.Quotient.stabilizerHom P p G).ker
        (Subgroup.subtype_injective (MulAction.stabilizer G P))).mp hmap
  have hmem : arithFrobAt A G P ∈ MulAction.stabilizer G P :=
    IsArithFrobAt.arithFrobAt_mem_stabilizer A G P
  have hF : Ideal.Quotient.stabilizerHom P p G ⟨arithFrobAt A G P, hmem⟩
      = FiniteField.frobeniusAlgEquivOfAlgebraic (A ⧸ p) (B ⧸ P) := by
    ext x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hFrob := (IsArithFrobAt.arithFrobAt A G P).mk_apply b
    simpa [Ideal.Quotient.stabilizerHom_apply,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← P.over_def p,
      Nat.card_eq_fintype_card] using hFrob
  intro g hg
  obtain ⟨⟨n, _⟩, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (A ⧸ p)
      (B ⧸ P)).2 (Ideal.Quotient.stabilizerHom P p G ⟨g, hg⟩)
  have hcon : (⟨g, hg⟩ : MulAction.stabilizer G P)
      = ⟨arithFrobAt A G P, hmem⟩ ^ n := by
    apply hrho
    rw [map_pow, hF]
    exact hn.symm
  have hpow : ((⟨arithFrobAt A G P, hmem⟩ ^ n :
      MulAction.stabilizer G P) : G) = arithFrobAt A G P ^ n :=
    Subgroup.coe_pow _ _ n
  have hval := congrArg (Subtype.val : MulAction.stabilizer G P → G) hcon
  rw [hpow] at hval
  exact ⟨n, hval⟩

omit [PerfectField p.ResidueField] in
/-- **The Frobenius element is trivial iff the prime splits completely.** Let $A$ and $B$ be
integral domains with $B$ a finite flat $A$-algebra, and let $G$ be a finite group acting
faithfully on $B$ by $A$-algebra automorphisms such that every element of $B$ fixed by $G$ is
the image of an element of $A$. Let $p$ be a prime of $A$ and $P$ a prime of $B$ lying over $p$,
with $B/P$ finite and $B$ unramified over $A$ at $P$ (the localization $B_P$ is formally
unramified over $A$). Let $\mathrm{Frob}_P \in G$ be the chosen arithmetic Frobenius element at
$P$, an element $\sigma \in G$ with $\sigma(x) \equiv x^q \pmod P$ for all $x \in B$, where $q$
is the number of elements of $A/p$. Then $\mathrm{Frob}_P = 1$ if and only if the number of
primes of $B$ lying over $p$ equals the order of $G$. -/
theorem arithFrobAt_eq_one_iff_ncard_primesOver_eq_card
    [Finite (B ⧸ P)] [Algebra.IsUnramifiedAt A P] :
    arithFrobAt A G P = 1 ↔ (Ideal.primesOver p B).ncard = Nat.card G :=
  arithFrobAt_eq_one_iff_ncard_primesOver_eq_card_of_generates
    (arithFrobAt_generates_stabilizer_of_isUnramifiedAt (p := p))

end Unramified
