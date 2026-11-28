/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.SerreCriterionReduced
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Tests for `MathlibExt.RingTheory.SerreCriterionReduced`
-/

@[expose] public section

#check @isReduced_iff_forall_isRegularLocalRing_and_min_one_le_depth

/-- Concrete instance: `ℤ` satisfies `(R₀)`. -/
example (p : Ideal ℤ) [p.IsPrime] (hp : p.height = 0) :
    IsRegularLocalRing (Localization.AtPrime p) :=
  (isReduced_iff_forall_isRegularLocalRing_and_min_one_le_depth.mp inferInstance).1 p hp

/-- Concrete instance: `ℤ` satisfies `(S₁)`. -/
example (p : Ideal ℤ) [p.IsPrime] :
    min 1 (ringKrullDim (Localization.AtPrime p)) ≤
      ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
        ℕ∞) : WithBot ℕ∞) :=
  (isReduced_iff_forall_isRegularLocalRing_and_min_one_le_depth.mp inferInstance).2 p

/-- The converse direction, used as a reducedness test. -/
example {R : Type} [CommRing R] [IsNoetherianRing R]
    (h0 : ∀ (p : Ideal R) [p.IsPrime], p.height = 0 →
      IsRegularLocalRing (Localization.AtPrime p))
    (h1 : ∀ (p : Ideal R) [p.IsPrime], min 1 (ringKrullDim (Localization.AtPrime p)) ≤
      ((IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :
        ℕ∞) : WithBot ℕ∞)) :
    IsReduced R :=
  isReduced_iff_forall_isRegularLocalRing_and_min_one_le_depth.mpr ⟨h0, h1⟩
