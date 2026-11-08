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

/-- Residue separability at `q`: the residue-field extension
`(q.under R).ResidueField → q.ResidueField` is separable, using the canonical
localization algebra `Localization.AtPrime.algebraOfLiesOver (q.under R) q`
installed locally, so callers supply no localization-algebra instances. -/
def IsResidueSeparableAt : Prop :=
  letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q;
    Algebra.IsSeparable (q.under R).ResidueField q.ResidueField

/-- A prime `q` of `S` is *tamely ramified* over `R` if the residue-field
extension is separable and the residue characteristic does not divide the
ramification index. -/
def IsTamelyRamifiedAt : Prop :=
  IsResidueSeparableAt R q ∧ ¬ ringChar q.ResidueField ∣ q.ramificationIdx R

/-- A prime `q` of `S` is *wildly ramified* over `R` if it is not tamely
ramified over `R`. -/
def IsWildlyRamifiedAt : Prop :=
  ¬ IsTamelyRamifiedAt R q

/-- The helper unfolds to separability under the canonical algebra. -/
theorem isResidueSeparableAt_iff :
    IsResidueSeparableAt R q ↔
      letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q;
      Algebra.IsSeparable (q.under R).ResidueField q.ResidueField :=
  Iff.rfl

/-- Unfolding of tame ramification into its two defining parts. -/
theorem isTamelyRamifiedAt_iff :
    IsTamelyRamifiedAt R q ↔
      IsResidueSeparableAt R q ∧
        ¬ ringChar q.ResidueField ∣ q.ramificationIdx R :=
  Iff.rfl

/-- Unfolding of wild ramification as the negation of tame ramification. -/
theorem isWildlyRamifiedAt_iff :
    IsWildlyRamifiedAt R q ↔ ¬ IsTamelyRamifiedAt R q :=
  Iff.rfl

/-- Constructor for tame ramification from its two defining parts. -/
theorem isTamelyRamifiedAt_mk (hsep : IsResidueSeparableAt R q)
    (hchar : ¬ ringChar q.ResidueField ∣ q.ramificationIdx R) :
    IsTamelyRamifiedAt R q :=
  ⟨hsep, hchar⟩

/-- The residue-separability part of tame ramification. -/
theorem IsTamelyRamifiedAt.isSeparable (h : IsTamelyRamifiedAt R q) :
    IsResidueSeparableAt R q :=
  h.1

/-- The characteristic/index part of tame ramification. -/
theorem IsTamelyRamifiedAt.not_dvd (h : IsTamelyRamifiedAt R q) :
    ¬ ringChar q.ResidueField ∣ q.ramificationIdx R :=
  h.2

/-- Under residue separability, wild ramification holds iff the residue
characteristic divides the ramification index. -/
theorem isWildlyRamifiedAt_iff_char_dvd (hsep : IsResidueSeparableAt R q) :
    IsWildlyRamifiedAt R q ↔ ringChar q.ResidueField ∣ q.ramificationIdx R := by
  constructor
  · intro hwild
    by_contra hdvd
    exact hwild ⟨hsep, hdvd⟩
  · intro hdvd htame
    exact htame.2 hdvd

/-- Wild ramification follows from the residue characteristic dividing the
ramification index, with no separability hypothesis: divisibility alone
contradicts the `.not_dvd` projection of any putative tame proof. -/
theorem isWildlyRamifiedAt_of_char_dvd
    (hdvd : ringChar q.ResidueField ∣ q.ramificationIdx R) :
    IsWildlyRamifiedAt R q :=
  fun htame => htame.2 hdvd

/-- Wild ramification follows from residue inseparability: inseparability alone
contradicts the `.isSeparable` projection of any putative tame proof. -/
theorem isWildlyRamifiedAt_of_not_isResidueSeparableAt
    (h : ¬ IsResidueSeparableAt R q) : IsWildlyRamifiedAt R q :=
  fun htame => h htame.1

/-- Residue separability at an unramified prime. -/
theorem isResidueSeparableAt_of_isUnramifiedAt [Algebra.EssFiniteType R S]
    [Algebra.IsUnramifiedAt R q] : IsResidueSeparableAt R q := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have h : Algebra.IsSeparable (q.under R).ResidueField q.ResidueField :=
    inferInstance
  exact h

/-- An unramified prime is tamely ramified. -/
theorem isTamelyRamifiedAt_of_isUnramifiedAt [Algebra.EssFiniteType R S]
    [Algebra.IsUnramifiedAt R q] : IsTamelyRamifiedAt R q := by
  refine ⟨isResidueSeparableAt_of_isUnramifiedAt R q, ?_⟩
  rw [Ideal.ramificationIdx_eq_one q R]
  exact fun h => CharP.ringChar_ne_one (Nat.eq_one_of_dvd_one h)

/-- In residue characteristic zero, tame ramification is equivalent to
residue separability. -/
theorem isTamelyRamifiedAt_iff_isSeparable_of_charZero [Module.Finite R S]
    (hchar : ringChar q.ResidueField = 0) :
    IsTamelyRamifiedAt R q ↔ IsResidueSeparableAt R q := by
  rw [isTamelyRamifiedAt_iff R q, hchar]
  refine and_iff_left (fun hdvd => ?_)
  exact (Ideal.ramificationIdx_pos R q).ne' (Nat.zero_dvd.mp hdvd)

end Algebra
