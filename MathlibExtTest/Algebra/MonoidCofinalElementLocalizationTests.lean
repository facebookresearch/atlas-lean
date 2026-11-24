/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Monoid.CofinalElementLocalization

/-! # Tests for localization at a cofinal monoid element -/

@[expose] public section

noncomputable section

universe u v w

namespace AddMonoid.CofinalElementLocalizationTests

variable {P : Type u} [AddCommMonoid P]
  {M : Type v} [CommMonoid M]
  (phi : Multiplicative P →* M) (e : P)
  (he : AddMonoid.IsCofinalElement e)

example : (MonoidHom.mrange phi).saturation =
    (Submonoid.powers (phi (Multiplicative.ofAdd e))).saturation :=
  AddMonoid.IsCofinalElement.saturation_range_eq_powers phi he

end AddMonoid.CofinalElementLocalizationTests

namespace AddMonoidAlgebra.CofinalElementLocalizationTests

variable (k : Type u) (P : Type v) [CommRing k] [AddCommMonoid P]
  (e : P) (he : AddMonoid.IsCofinalElement e)
  {A : Type w} [CommRing A]
  [Algebra (AddMonoidAlgebra k P) A]

example :
    IsLocalization (AddMonoidAlgebra.monomialSubmonoid k P) A ↔
      IsLocalization
        (Submonoid.powers (AddMonoidAlgebra.of' k P e)) A :=
  AddMonoidAlgebra.isLocalization_monomialSubmonoid_iff_powers
    k P he

end AddMonoidAlgebra.CofinalElementLocalizationTests

end
