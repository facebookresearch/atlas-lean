/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean`
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

public import Mathlib.FieldTheory.RatFunc.Basic
public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup

/-!
# Finite places of a rational function field

This file studies the places of the rational function field `RatFunc K` attached to the primes of
`K[X]`. The transport of places along field isomorphisms is in
`MathlibExt.AlgebraicGeometry.Curve.PlaceCongr`.
-/

@[expose] public section

noncomputable section

open Polynomial IsDedekindDomain WithZero IsLocalRing

open scoped Polynomial

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem adicValuation_valuationSubring :
    v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (⟨x, hx⟩ : v.toValuationSubring)

theorem mem_iff_adicValuation_le_one {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  rw [← v.adicValuation_valuationSubring]
  exact Valuation.mem_valuationSubring_iff _ _

instance : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

instance : v.adicValuation.IsTrivialOn K :=
  Valuation.IsTrivialOn.of_le_one v.adicValuation fun a =>
    v.mem_iff_adicValuation_le_one.mp (v.algebraMap_mem' a)

theorem isEquiv_adicValuation_of_valuationSubring_eq {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) : w.IsEquiv v.adicValuation :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr
    (h.trans v.adicValuation_valuationSubring.symm)

theorem mem_maximalIdeal_iff_adicValuation_lt_one (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← v.adicValuation_coe_eq_one_iff,
    lt_iff_le_and_ne]
  have hle : v.adicValuation (a : F) ≤ 1 := v.mem_iff_adicValuation_le_one.mp a.2
  tauto

section OfHeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]

theorem isEquiv_adicValuation_ofHeightOneSpectrum (w : HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (ofHeightOneSpectrum (K := K) w).adicValuation :=
  (ofHeightOneSpectrum (K := K) w).isEquiv_adicValuation_of_valuationSubring_eq rfl

theorem ofHeightOneSpectrum_injective :
    Function.Injective (ofHeightOneSpectrum (K := K) (F := F) (R := R)) := by
  intro w w' h
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) ?_
  refine (isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := F) w).trans ?_
  rw [h]
  exact (isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := F) w').symm

theorem ord_ofHeightOneSpectrum_ne_zero_iff (w : HeightOneSpectrum R) {q : R} (hq : q ≠ 0) :
    (ofHeightOneSpectrum (K := K) (F := F) w).ord (algebraMap R F q) ≠ 0 ↔ q ∈ w.asIdeal := by
  have hq' : algebraMap R F q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hq
  rw [ne_eq, (ofHeightOneSpectrum (K := K) w).ord_eq_zero_iff_adicValuation_eq_one hq',
    ← (isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := F) w).eq_one_iff_eq_one,
    HeightOneSpectrum.valuation_eq_one_iff_notMem, not_not]

end OfHeightOneSpectrum

end Place

namespace RationalFunctionField

variable (K : Type*) [Field K]

def heightOneSpectrumOfIrreducible {p : K[X]} (hp : Irreducible p) :
    HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {p}
  isPrime := (PrincipalIdealRing.isMaximal_of_irreducible hp).isPrime
  ne_bot := by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero

@[simp]
theorem heightOneSpectrumOfIrreducible_asIdeal {p : K[X]} (hp : Irreducible p) :
    (heightOneSpectrumOfIrreducible K hp).asIdeal = Ideal.span {p} := rfl

theorem exists_irreducible_span (w : HeightOneSpectrum K[X]) :
    ∃ p : K[X], Irreducible p ∧ w.asIdeal = Ideal.span {p} := by
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal w.asIdeal).principal
  rw [Ideal.submodule_span_eq] at hp
  refine ⟨p, ?_, hp⟩
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact w.ne_bot (hp.trans (by simp))
  have hpr := w.isPrime
  rw [hp] at hpr
  exact ((Ideal.span_singleton_prime hp0).mp hpr).irreducible

def finitePlace {p : K[X]} (hp : Irreducible p) : Place K (RatFunc K) :=
  Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K hp)

theorem finitePlace_def {p : K[X]} (hp : Irreducible p) :
    finitePlace K hp = Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K hp) := rfl

section ResidueDegree

theorem algebraMap_mem_ofHeightOneSpectrum (w : HeightOneSpectrum K[X]) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring :=
  (Place.mem_iff_adicValuation_le_one _).mpr
    ((Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mp (w.valuation_le_one q))

def residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    K[X] →+* (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField :=
  (IsLocalRing.residue _).comp
    ((algebraMap K[X] (RatFunc K)).codRestrict
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring.toSubring
      (algebraMap_mem_ofHeightOneSpectrum K w))

theorem residueOfHeightOneSpectrum_apply (w : HeightOneSpectrum K[X]) (q : K[X]) :
    residueOfHeightOneSpectrum K w q = IsLocalRing.residue _
      ⟨algebraMap K[X] (RatFunc K) q, algebraMap_mem_ofHeightOneSpectrum K w q⟩ := rfl

theorem ker_residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    RingHom.ker (residueOfHeightOneSpectrum K w) = w.asIdeal := by
  ext q
  rw [RingHom.mem_ker, residueOfHeightOneSpectrum_apply, IsLocalRing.residue_eq_zero_iff,
    Place.mem_maximalIdeal_iff_adicValuation_lt_one,
    ← (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).lt_one_iff_lt_one]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem w q

theorem surjective_residueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    Function.Surjective (residueOfHeightOneSpectrum K w) := by
  intro y
  obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
  have hxval : w.valuation (RatFunc K) x ≤ 1 :=
    (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).le_one_iff_le_one.mpr ((Place.mem_iff_adicValuation_le_one _).mp hx)
  have hden_ne : algebraMap K[X] (RatFunc K) x.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr x.denom_ne_zero
  have hmul : x * algebraMap K[X] (RatFunc K) x.denom = algebraMap K[X] (RatFunc K) x.num :=
    ((div_eq_iff hden_ne).mp x.num_div_denom).symm
  have hden : x.denom ∉ w.asIdeal := by
    intro hd
    have hnum : x.num ∉ w.asIdeal := by
      intro hn
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
      obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom x
      exact hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hd)
    have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.num) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hnum
    refine absurd h1 (ne_of_lt ?_)
    calc w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.num)
        = w.valuation (RatFunc K) x
            * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.denom) := by
          rw [← map_mul, hmul]
      _ ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) x.denom) :=
          mul_le_of_le_one_left' hxval
      _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w x.denom).mpr hd
  have hmax : w.asIdeal.IsMaximal := IsPrime.to_maximal_ideal w.ne_bot
  obtain ⟨t, ht⟩ : ∃ t : K[X], x.denom * t - 1 ∈ w.asIdeal := by
    obtain ⟨b, c, hc, hbc⟩ := hmax.exists_inv hden
    refine ⟨b, ?_⟩
    rw [show x.denom * b - 1 = -c by linear_combination hbc]
    exact neg_mem hc
  refine ⟨x.num * t, ?_⟩
  rw [residueOfHeightOneSpectrum_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, Place.mem_maximalIdeal_iff_adicValuation_lt_one]
  change (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).adicValuation
    (algebraMap K[X] (RatFunc K) (x.num * t) - x) < 1
  rw [← (Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).lt_one_iff_lt_one]
  have key : algebraMap K[X] (RatFunc K) (x.num * t) - x
      = x * algebraMap K[X] (RatFunc K) (x.denom * t - 1) := by
    rw [map_sub, map_mul, map_mul, map_one, mul_sub, mul_one, ← mul_assoc, hmul]
  rw [key, map_mul]
  calc w.valuation (RatFunc K) x
        * w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) (x.denom * t - 1))
      ≤ w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) (x.denom * t - 1)) :=
        mul_le_of_le_one_left' hxval
    _ < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr ht

def residueFieldEquivOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (K[X] ⧸ w.asIdeal) ≃ₐ[K]
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ResidueField := by
  refine AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq
    (ker_residueOfHeightOneSpectrum K w).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_residueOfHeightOneSpectrum K w))) ?_
  intro a
  rw [show (algebraMap K (K[X] ⧸ w.asIdeal)) a
      = Ideal.Quotient.mk w.asIdeal (algebraMap K K[X] a) from rfl]
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, residueOfHeightOneSpectrum_apply]
  exact congrArg (IsLocalRing.residue _)
    (Subtype.ext (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a).symm)

theorem deg_ofHeightOneSpectrum {w : HeightOneSpectrum K[X]} {p : K[X]}
    (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).deg = p.natDegree := by
  rw [Place.deg, ← (residueFieldEquivOfHeightOneSpectrum K w).toLinearEquiv.finrank_eq, hw]
  exact finrank_quotient_span_eq_natDegree

theorem deg_finitePlace {p : K[X]} (hp : Irreducible p) :
    (finitePlace K hp).deg = p.natDegree :=
  deg_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible_asIdeal K hp)

end ResidueDegree

def placeOfPoint (a : K) : Place K (RatFunc K) :=
  finitePlace K (irreducible_X_sub_C a)

theorem placeOfPoint_def (a : K) :
    placeOfPoint K a = finitePlace K (irreducible_X_sub_C a) := rfl

theorem placeOfPoint_eq_ofHeightOneSpectrum (a : K) :
    placeOfPoint K a
      = Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)) :=
  rfl

theorem placeOfPoint_injective : Function.Injective (placeOfPoint K) := by
  intro a b h
  have h2 : heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)
      = heightOneSpectrumOfIrreducible K (irreducible_X_sub_C b) :=
    Place.ofHeightOneSpectrum_injective (K := K) (F := RatFunc K) h
  have h3 : Ideal.span {(X : K[X]) - C a} = Ideal.span {(X : K[X]) - C b} := by
    have := congrArg HeightOneSpectrum.asIdeal h2
    simpa using this
  have h4 : ((X : K[X]) - C a) ∣ (X - C b) :=
    (Ideal.span_singleton_eq_span_singleton.mp h3).dvd
  have h5 : (X - C b).IsRoot a := dvd_iff_isRoot.mp h4
  have h6 : a - b = 0 := by simpa [IsRoot] using h5
  exact sub_eq_zero.mp h6

@[simp]
theorem deg_placeOfPoint (a : K) : (placeOfPoint K a).deg = 1 := by
  rw [placeOfPoint, deg_finitePlace, natDegree_X_sub_C]

end RationalFunctionField

end AlgebraicCurve

end
