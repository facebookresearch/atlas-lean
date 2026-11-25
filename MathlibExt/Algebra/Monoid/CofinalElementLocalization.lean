/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Localization.Saturation

/-!
# Localization at a cofinal element

An element `e` of a commutative additive monoid is cofinal when every
element divides an additive multiple of `e`.  Under a multiplicative map
from the tagged monoid `Multiplicative P`, the saturation of the full image
then agrees with the saturation of the powers of the image of `e`.

The final section specializes this denominator comparison to additive
monoid algebras and transfers `IsLocalization` instances across it.
-/

@[expose] public section

noncomputable section

universe u v w

namespace AddMonoid

/-- An element is cofinal when every monoid element has an additive
complement to a natural multiple of it. -/
def IsCofinalElement {P : Type u} [AddCommMonoid P] (e : P) : Prop :=
  ∀ p : P, ∃ (n : ℕ) (q : P), p + q = n • e

namespace IsCofinalElement

variable {P : Type u} [AddCommMonoid P]
  {M : Type v} [CommMonoid M]

/-- A cofinal element generates, after saturation, the full image of any
multiplicative monoid map. -/
theorem saturation_range_eq_powers
    (phi : Multiplicative P →* M) {e : P}
    (he : IsCofinalElement e) :
    (MonoidHom.mrange phi).saturation =
      (Submonoid.powers (phi (Multiplicative.ofAdd e))).saturation := by
  apply le_antisymm
  · apply Submonoid.saturation_le_of_le
    intro x hx
    obtain ⟨p, rfl⟩ := MonoidHom.mem_mrange.mp hx
    obtain ⟨n, q, hpq⟩ := he p.toAdd
    change phi p ∈
      (Submonoid.powers (phi (Multiplicative.ofAdd e))).saturation
    rw [Submonoid.mem_saturation_iff]
    refine ⟨phi (Multiplicative.ofAdd q), ?_⟩
    apply (Submonoid.mem_powers_iff _ _).2
    refine ⟨n, ?_⟩
    rw [← phi.map_pow, ← ofAdd_nsmul,
      ← hpq, ofAdd_add, phi.map_mul, ofAdd_toAdd]
  · apply Submonoid.saturation_le_of_le
    intro x hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hx
    exact Submonoid.le_toSubmonoid_saturation
      (MonoidHom.mem_mrange.mpr
        ⟨(Multiplicative.ofAdd e) ^ n, phi.map_pow _ n⟩)

end IsCofinalElement
end AddMonoid

namespace AddMonoidAlgebra

section Semiring

variable (k : Type u) (P : Type v) [CommSemiring k] [AddCommMonoid P]

/-- The submonoid of all monomials with coefficient one. -/
abbrev monomialSubmonoid : Submonoid (AddMonoidAlgebra k P) :=
  MonoidHom.mrange (AddMonoidAlgebra.of k P)

/-- Cofinality identifies all monomial denominators with powers of the
cofinal monomial after saturation. -/
theorem monomialSubmonoid_saturation_eq_powers
    {e : P} (he : AddMonoid.IsCofinalElement e) :
    (monomialSubmonoid k P).saturation =
      (Submonoid.powers (AddMonoidAlgebra.of' k P e)).saturation := by
  simpa [AddMonoidAlgebra.of'_eq_of] using
    AddMonoid.IsCofinalElement.saturation_range_eq_powers
      (AddMonoidAlgebra.of k P) he

end Semiring

section Localization

variable (k : Type u) (P : Type v) [CommRing k] [AddCommMonoid P]
  {A : Type w} [CommRing A]
  [Algebra (AddMonoidAlgebra k P) A]

/-- Localizing an additive monoid algebra at all monomials is equivalent to
localizing at powers of one cofinal monomial. -/
theorem isLocalization_monomialSubmonoid_iff_powers
    {e : P} (he : AddMonoid.IsCofinalElement e) :
    IsLocalization (monomialSubmonoid k P) A ↔
      IsLocalization (Submonoid.powers
        (AddMonoidAlgebra.of' k P e)) A :=
  IsLocalization.isLocalization_iff_of_saturation_eq
    (monomialSubmonoid k P)
    (Submonoid.powers (AddMonoidAlgebra.of' k P e))
    (monomialSubmonoid_saturation_eq_powers k P he)

end Localization

end AddMonoidAlgebra

end
