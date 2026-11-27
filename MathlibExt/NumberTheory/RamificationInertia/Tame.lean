/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.QuasiFinite.Basic

public import Mathlib.RingTheory.RamificationInertia.Ramification

@[expose] public section

/-!
# Tame and wild ramification at a prime

Let `S` be an `R`-algebra and `q` a prime ideal of `S`. We say `q` is
*tamely ramified* over `R` if the residue-field extension
`(q.under R).ResidueField → q.ResidueField` is separable and the residue
characteristic does not divide the ramification index `q.ramificationIdx R`.
*Wild ramification* is the logical complement of tame ramification.

The residue-field algebra is the canonical one coming from
`Localization.AtPrime.algebraOfLiesOver (q.under R) q`, installed locally
inside `Algebra.IsResidueSeparableAt`, so the tame/wild predicates require no
localization-algebra hypotheses from callers.

## Main definitions

* `Algebra.IsResidueSeparableAt R q`: residue separability at `q`.
* `Algebra.IsTamelyRamifiedAt R q`: tame ramification at `q`.
* `Algebra.IsWildlyRamifiedAt R q`: wild ramification at `q`, defined as
  `¬ Algebra.IsTamelyRamifiedAt R q`.

## Main results

* `Algebra.isTamelyRamifiedAt_iff`: unfolding of tame ramification.
* `Algebra.isWildlyRamifiedAt_iff_char_dvd`: under residue separability,
  wild ramification holds iff the residue characteristic divides the
  ramification index.
* `Algebra.isWildlyRamifiedAt_of_char_dvd`: wild ramification follows from the
  residue characteristic dividing the ramification index, with no separability
  hypothesis.
* `Algebra.isWildlyRamifiedAt_of_not_isResidueSeparableAt`: wild ramification
  follows from residue inseparability.
* `Algebra.isTamelyRamifiedAt_of_isUnramifiedAt`: unramified primes are tame.
* `Algebra.isTamelyRamifiedAt_iff_isSeparable_of_charZero`: in residue
  characteristic zero, tame ramification is equivalent to residue separability.
-/

namespace Algebra

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (q : Ideal S) [q.IsPrime]

/-- **Residue separability at a prime.** Let $R$ and $S$ be commutative rings with $S$ an
$R$-algebra, let $q$ be a prime ideal of $S$, and let $p$ be its preimage in $R$. Then $q$ is
residue separable over $R$ when the residue field $\kappa(q)$ is separable over the residue field
$\kappa(p)$, for the algebra structure induced by the canonical local homomorphism $R_p \to S_q$
of localizations. -/
def IsResidueSeparableAt : Prop :=
  letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q;
    Algebra.IsSeparable (q.under R).ResidueField q.ResidueField

/-- **Tamely ramified prime.** Let $R$ and $S$ be commutative rings with $S$ an $R$-algebra, and
let $q$ be a prime ideal of $S$. Then $q$ is *tamely ramified* over $R$ when $q$ is residue
separable over $R$ and the characteristic of the residue field $\kappa(q)$ does not divide the
ramification index of $q$ over $R$. -/
def IsTamelyRamifiedAt : Prop :=
  IsResidueSeparableAt R q ∧ ¬ ringChar q.ResidueField ∣ q.ramificationIdx R

/-- **Wildly ramified prime.** Let $R$ be a commutative ring, $S$ a commutative $R$-algebra and
$q$ a prime ideal of $S$. Then $q$ is *wildly ramified* over $R$ if it is not tamely ramified
over $R$. -/
def IsWildlyRamifiedAt : Prop :=
  ¬ IsTamelyRamifiedAt R q

/-- **Residue separability, unfolded.** Let $R$ and $S$ be commutative rings with $S$ an
$R$-algebra, let $q$ be a prime ideal of $S$, and let $p$ be its preimage in $R$. Then $q$ is
residue separable over $R$ if and only if the residue field $\kappa(q)$ is separable over the
residue field $\kappa(p)$, for the algebra structure induced by the canonical local homomorphism
$R_p \to S_q$ of localizations. -/
theorem isResidueSeparableAt_iff :
    IsResidueSeparableAt R q ↔
      letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q;
      Algebra.IsSeparable (q.under R).ResidueField q.ResidueField :=
  Iff.rfl

/-- **Characterization of tame ramification.** Let $R$ and $S$ be commutative rings with $S$ an
$R$-algebra, and let $q$ be a prime ideal of $S$. Then $q$ is tamely ramified over $R$ if and only
if $q$ is residue separable over $R$ and the characteristic of the residue field $\kappa(q)$ does
not divide the ramification index of $q$ over $R$. -/
theorem isTamelyRamifiedAt_iff :
    IsTamelyRamifiedAt R q ↔
      IsResidueSeparableAt R q ∧
        ¬ ringChar q.ResidueField ∣ q.ramificationIdx R :=
  Iff.rfl

/-- **Wild ramification is the failure of tame ramification.** Let $R$ be a commutative ring,
$S$ a commutative $R$-algebra and $q$ a prime ideal of $S$. Then $q$ is wildly ramified over $R$
if and only if $q$ is not tamely ramified over $R$. -/
theorem isWildlyRamifiedAt_iff :
    IsWildlyRamifiedAt R q ↔ ¬ IsTamelyRamifiedAt R q :=
  Iff.rfl

/-- **Criterion for tame ramification.** Let $R$ and $S$ be commutative rings with $S$ an
$R$-algebra, and let $q$ be a prime ideal of $S$. If $q$ is residue separable over $R$ and the
characteristic of the residue field $\kappa(q)$ does not divide the ramification index of $q$ over
$R$, then $q$ is tamely ramified over $R$. -/
theorem isTamelyRamifiedAt_mk (hsep : IsResidueSeparableAt R q)
    (hchar : ¬ ringChar q.ResidueField ∣ q.ramificationIdx R) :
    IsTamelyRamifiedAt R q :=
  ⟨hsep, hchar⟩

/-- **Tame primes are residue separable.** Let $R$ and $S$ be commutative rings with $S$ an
$R$-algebra, and let $q$ be a prime ideal of $S$. If $q$ is tamely ramified over $R$, then $q$ is
residue separable over $R$. -/
theorem IsTamelyRamifiedAt.isSeparable (h : IsTamelyRamifiedAt R q) :
    IsResidueSeparableAt R q :=
  h.1

/-- **The residue characteristic of a tame prime does not divide its ramification index.** Let
$R$ be a commutative ring, $S$ a commutative $R$-algebra and $q$ a prime ideal of $S$ with residue
field $\kappa(q)$. If $q$ is tamely ramified over $R$, then the characteristic of $\kappa(q)$ does
not divide the ramification index of $q$ over $R$. -/
theorem IsTamelyRamifiedAt.not_dvd (h : IsTamelyRamifiedAt R q) :
    ¬ ringChar q.ResidueField ∣ q.ramificationIdx R :=
  h.2

/-- **Wild ramification under residue separability.** Let $R$ and $S$ be commutative rings with $S$
an $R$-algebra, and let $q$ be a prime ideal of $S$ that is residue separable over $R$. Then $q$ is
wildly ramified over $R$ if and only if the characteristic of the residue field $\kappa(q)$ divides
the ramification index of $q$ over $R$. -/
theorem isWildlyRamifiedAt_iff_char_dvd (hsep : IsResidueSeparableAt R q) :
    IsWildlyRamifiedAt R q ↔ ringChar q.ResidueField ∣ q.ramificationIdx R := by
  constructor
  · intro hwild
    by_contra hdvd
    exact hwild ⟨hsep, hdvd⟩
  · intro hdvd htame
    exact htame.2 hdvd

/-- **Divisibility of the ramification index forces wild ramification.** Let $R$ be a
commutative ring, $S$ a commutative $R$-algebra and $q$ a prime ideal of $S$ with residue field
$\kappa(q)$. If the characteristic of $\kappa(q)$ divides the ramification index of $q$ over $R$,
then $q$ is wildly ramified over $R$.

No separability hypothesis on the residue field extension is needed. -/
theorem isWildlyRamifiedAt_of_char_dvd
    (hdvd : ringChar q.ResidueField ∣ q.ramificationIdx R) :
    IsWildlyRamifiedAt R q :=
  fun htame => htame.2 hdvd

/-- **An inseparable residue field extension forces wild ramification.** Let $R$ be a
commutative ring, $S$ a commutative $R$-algebra, $q$ a prime ideal of $S$ and $p$ the preimage
of $q$ in $R$. If the residue field extension $\kappa(p) \to \kappa(q)$ is not separable, then
$q$ is wildly ramified over $R$. -/
theorem isWildlyRamifiedAt_of_not_isResidueSeparableAt
    (h : ¬ IsResidueSeparableAt R q) : IsWildlyRamifiedAt R q :=
  fun htame => h htame.1

/-- **Unramified primes are residue separable.** Let $R$ and $S$ be commutative rings with $S$ an
$R$-algebra that is essentially of finite type, and let $q$ be a prime ideal of $S$ at which $S$ is
unramified over $R$, that is, the localization $S_q$ is formally unramified over $R$. Then $q$ is
residue separable over $R$. -/
theorem isResidueSeparableAt_of_isUnramifiedAt [Algebra.EssFiniteType R S]
    [Algebra.IsUnramifiedAt R q] : IsResidueSeparableAt R q := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have h : Algebra.IsSeparable (q.under R).ResidueField q.ResidueField :=
    inferInstance
  exact h

/-- **Unramified primes are tamely ramified.** Let $R$ and $S$ be commutative rings with $S$ an
$R$-algebra that is essentially of finite type, and let $q$ be a prime ideal of $S$ at which $S$ is
unramified over $R$, that is, the localization $S_q$ is formally unramified over $R$. Then $q$ is
tamely ramified over $R$. -/
theorem isTamelyRamifiedAt_of_isUnramifiedAt [Algebra.EssFiniteType R S]
    [Algebra.IsUnramifiedAt R q] : IsTamelyRamifiedAt R q := by
  refine ⟨isResidueSeparableAt_of_isUnramifiedAt R q, ?_⟩
  rw [Ideal.ramificationIdx_eq_one q R]
  exact fun h => CharP.ringChar_ne_one (Nat.eq_one_of_dvd_one h)

/-- **Tameness in residue characteristic zero.** Let $R$ and $S$ be commutative rings with $S$ an
$R$-algebra that is finite as an $R$-module, and let $q$ be a prime ideal of $S$ whose residue
field $\kappa(q)$ has characteristic $0$. Then $q$ is tamely ramified over $R$ if and only if $q$
is residue separable over $R$. -/
theorem isTamelyRamifiedAt_iff_isSeparable_of_charZero [Module.Finite R S]
    (hchar : ringChar q.ResidueField = 0) :
    IsTamelyRamifiedAt R q ↔ IsResidueSeparableAt R q := by
  rw [isTamelyRamifiedAt_iff R q, hchar]
  refine and_iff_left (fun hdvd => ?_)
  exact (Ideal.ramificationIdx_pos R q).ne' (Nat.zero_dvd.mp hdvd)

end Algebra
