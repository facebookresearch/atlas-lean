/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInfty
public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces
import Mathlib.NumberTheory.RatFunc.Ostrowski

/-!
# Places of a rational function field

This file classifies the places of `RatFunc K`: each place comes from a prime of `K[X]` or is the
place at infinity.
-/

@[expose] public section

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve

namespace RationalFunctionField

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

instance instNontrivialValueGroupInftyValuation :
    Nontrivial (MonoidWithZeroHom.valueGroup
      (MonoidWithZeroHom.ofClass (RatFunc.inftyValuation K))) :=
  nontrivial_valueGroup_inftyValuation K

theorem placeInfty_ne_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    placeInfty K ≠ Place.ofHeightOneSpectrum w := by
  intro h
  refine RatFunc.adicValuation_not_isEquiv_infty_valuation w
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr ?_)
  have h2 := congrArg Place.toValuationSubring h
  rw [placeInfty_toValuationSubring, Place.ofHeightOneSpectrum_toValuationSubring] at h2
  exact h2.symm

end PlaceInfty

variable {K}

theorem eq_ofHeightOneSpectrum_or_eq_placeInfty [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) :
    (∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact Or.inr (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)))
  · obtain ⟨w, hw, -⟩ := h
    exact Or.inl ⟨w, Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))⟩

variable (K)

theorem placeOfPoint_ne_placeInfty [DecidableEq (RatFunc K)] (a : K) :
    placeOfPoint K a ≠ placeInfty K := by
  rw [placeOfPoint_eq_ofHeightOneSpectrum]
  exact fun h => placeInfty_ne_ofHeightOneSpectrum K _ h.symm

theorem exists_eq_placeOfPoint [IsAlgClosed K] (w : HeightOneSpectrum K[X]) :
    ∃ a : K, Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = placeOfPoint K a := by
  obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w
  have hdeg : p.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K hp]; exact one_ne_zero
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
  refine ⟨a, ?_⟩
  have hassoc : Associated ((X : K[X]) - C a) p :=
    (irreducible_X_sub_C a).associated_of_dvd hp (dvd_iff_isRoot.mpr ha)
  have hideal : w = heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a) :=
    HeightOneSpectrum.ext (by
      rw [hwp, heightOneSpectrumOfIrreducible_asIdeal]
      exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm)
  rw [hideal, placeOfPoint_eq_ofHeightOneSpectrum]

theorem eq_placeOfPoint_or_eq_placeInfty [IsAlgClosed K] [DecidableEq (RatFunc K)]
    (v : Place K (RatFunc K)) :
    (∃ a : K, v = placeOfPoint K a) ∨ v = placeInfty K := by
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, hw⟩ | hw
  · obtain ⟨a, ha⟩ := exists_eq_placeOfPoint K w
    exact Or.inl ⟨a, hw.trans ha⟩
  · exact Or.inr hw

def ofOption [DecidableEq (RatFunc K)] : Option K → Place K (RatFunc K) :=
  fun o => o.elim (placeInfty K) (placeOfPoint K)

theorem ofOption_bijective [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    Function.Bijective (ofOption K) := by
  constructor
  · rintro (_ | a) (_ | b) h
    · rfl
    · exact absurd h.symm (placeOfPoint_ne_placeInfty K b)
    · exact absurd h (placeOfPoint_ne_placeInfty K a)
    · exact congrArg some (placeOfPoint_injective K h)
  · intro v
    rcases eq_placeOfPoint_or_eq_placeInfty K v with ⟨a, ha⟩ | ha
    · exact ⟨some a, ha.symm⟩
    · exact ⟨none, ha.symm⟩

def placeEquivOption [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    Place K (RatFunc K) ≃ Option K :=
  (Equiv.ofBijective (ofOption K) (ofOption_bijective K)).symm

@[simp]
theorem placeEquivOption_symm_some [IsAlgClosed K] [DecidableEq (RatFunc K)] (a : K) :
    (placeEquivOption K).symm (some a) = placeOfPoint K a := rfl

@[simp]
theorem placeEquivOption_symm_none [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    (placeEquivOption K).symm none = placeInfty K := rfl

@[simp]
theorem placeEquivOption_placeOfPoint [IsAlgClosed K] [DecidableEq (RatFunc K)] (a : K) :
    placeEquivOption K (placeOfPoint K a) = some a :=
  (Equiv.ofBijective (ofOption K) (ofOption_bijective K)).symm_apply_apply (some a)

@[simp]
theorem placeEquivOption_placeInfty [IsAlgClosed K] [DecidableEq (RatFunc K)] :
    placeEquivOption K (placeInfty K) = none :=
  (Equiv.ofBijective (ofOption K) (ofOption_bijective K)).symm_apply_apply none

end RationalFunctionField

end AlgebraicCurve
