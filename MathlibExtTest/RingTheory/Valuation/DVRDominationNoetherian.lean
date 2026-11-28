/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.Valuation.DVRDominationNoetherian

/-!
# Tests for discrete valuation rings dominating a Noetherian local domain

The three results of `MathlibExt.RingTheory.Valuation.DVRDominationNoetherian`, the case `L = K`
used for local rings of schemes (any dimension), and the finitely generated case from the
hypothesis that `L` is essentially of finite type over `K`.
-/

@[expose] public section

namespace MathlibExtTest.RingTheory.Valuation.DVRDominationNoetherian

open IsLocalRing

#check @exists_subalgebra_dominating_krullDimLE_one
#check @exists_isDiscreteValuationRing_dominating_of_finite
#check @exists_isDiscreteValuationRing_dominating_of_fg

/-- The case `L = K`, for a Noetherian local domain of any dimension: a discrete valuation ring
in the fraction field dominates `R`. -/
example {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : ¬ IsField R) :
    ∃ V : ValuationSubring (FractionRing R), IsDiscreteValuationRing V ∧
      (∀ r : R, algebraMap R (FractionRing R) r ∈ V) ∧
      ∀ r ∈ maximalIdeal R, algebraMap R (FractionRing R) r ∈ V.nonunits :=
  exists_isDiscreteValuationRing_dominating_of_finite (K := FractionRing R) hR

/-- A field extension essentially of finite type is finitely generated, so the general case
applies to it. -/
example {R K L : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] [Algebra.EssFiniteType K L] (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ (∀ r : R, algebraMap R L r ∈ V) ∧
      ∀ r ∈ maximalIdeal R, algebraMap R L r ∈ V.nonunits :=
  exists_isDiscreteValuationRing_dominating_of_fg (K := K) hR (IntermediateField.fg_top K L)

/-- The one-dimensional dominating ring is local, Noetherian, and not a field. -/
example {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] (hR : ¬ IsField R) :
    ∃ S : Subalgebra R K, IsNoetherianRing S ∧ Ring.KrullDimLE 1 S ∧ ¬ IsField S := by
  obtain ⟨S, -, hS, hd, hf, -⟩ := exists_subalgebra_dominating_krullDimLE_one (K := K) hR
  exact ⟨S, hS, hd, hf⟩

end MathlibExtTest.RingTheory.Valuation.DVRDominationNoetherian
