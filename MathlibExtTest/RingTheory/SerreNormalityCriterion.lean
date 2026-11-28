/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.SerreNormalityCriterion
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Tests for Serre's criterion for normality
-/

@[expose] public section

#check @IsLocalRing.one_le_depth_of_isDomain
#check @IsLocalRing.two_le_depth_of_isIntegrallyClosed
#check @IsLocalRing.min_two_le_depth_of_isIntegrallyClosed
#check @IsLocalRing.isRegularLocalRing_of_isIntegrallyClosed
#check @isIntegrallyClosed_of_forall_isRegularLocalRing_and_min_two_le_depth
#check @forall_isRegularLocalRing_and_min_two_le_depth_of_isIntegrallyClosed_localization
#check @isIntegrallyClosed_iff_forall_isRegularLocalRing_and_min_two_le_depth
#check @IsLocalRing.isDomain_of_isReduced_of_isIntegrallyClosed
#check @IsLocalRing.depth_self_eq_of_ringEquiv
#check @forall_isIntegrallyClosed_localization_iff

/-- `ℤ` satisfies `(R₁)` and `(S₂)`. -/
example :
    (∀ (p : Ideal ℤ) [p.IsPrime], p.height ≤ 1 →
      IsRegularLocalRing (Localization.AtPrime p)) ∧
    (∀ (p : Ideal ℤ) [p.IsPrime], min 2 (ringKrullDim (Localization.AtPrime p)) ≤
      ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
        ℕ∞) : WithBot ℕ∞)) :=
  isIntegrallyClosed_iff_forall_isRegularLocalRing_and_min_two_le_depth.mp inferInstance

/-- The polynomial ring `ℚ[X, Y]` satisfies `(S₂)`; in particular its localization at the
maximal ideal `(X, Y)` (of dimension `2`) has depth at least `2`. -/
example (p : Ideal (MvPolynomial (Fin 2) ℚ)) [p.IsPrime] :
    min 2 (ringKrullDim (Localization.AtPrime p)) ≤
      ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
        ℕ∞) : WithBot ℕ∞) :=
  (isIntegrallyClosed_iff_forall_isRegularLocalRing_and_min_two_le_depth.mp inferInstance).2 p

/-- The depth bound, instantiated on an arbitrary normal Noetherian local domain. -/
example {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] (h : 2 ≤ ringKrullDim A) :
    2 ≤ IsLocalRing.depth (ModuleCat.of A A) :=
  IsLocalRing.two_le_depth_of_isIntegrallyClosed h

/-- Serre's criterion, specialised to `ℤ`: `ℤ` is normal. -/
example (p : Ideal ℤ) [p.IsPrime] : IsDomain (Localization.AtPrime p) ∧
    IsIntegrallyClosed (Localization.AtPrime p) :=
  forall_isIntegrallyClosed_localization_iff.mpr
    (isIntegrallyClosed_iff_forall_isRegularLocalRing_and_min_two_le_depth.mp inferInstance) p
