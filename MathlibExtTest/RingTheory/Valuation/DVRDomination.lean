/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.Valuation.DVRDomination
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Tests for discrete valuation rings dominating a one-dimensional local domain

The case `L = K` of `IsLocalRing.exists_isDiscreteValuationRing_dominating`, for the fraction
field `FractionRing R`.
-/

@[expose] public section

namespace MathlibExtTest.RingTheory.Valuation.DVRDomination

open IsLocalRing

/-- The case `L = K`: a discrete valuation ring in the fraction field dominates `R`. -/
example {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [Ring.KrullDimLE 1 R] (hR : ¬ IsField R) :
    ∃ V : ValuationSubring (FractionRing R), IsDiscreteValuationRing V ∧
      (∀ r : R, algebraMap R (FractionRing R) r ∈ V) ∧
      ∀ r ∈ maximalIdeal R, algebraMap R (FractionRing R) r ∈ V.nonunits :=
  exists_isDiscreteValuationRing_dominating (K := FractionRing R) hR

end MathlibExtTest.RingTheory.Valuation.DVRDomination
