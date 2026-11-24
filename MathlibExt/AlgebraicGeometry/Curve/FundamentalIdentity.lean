/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg.lean`
and
`P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.DivisorPushPull
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import MathlibExt.AlgebraicGeometry.Curve.ExistsOrdPos
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces

/-!
# The fundamental identity for places of function fields

This file proves the fundamental identity `∑ e(w | v) f(w | v) = [F' : F]`, where `w` runs over the
places of a finite separable extension `F'` restricting to a place `v` of `F`.

## Main statement

* `AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg`
-/

namespace CurveGenus.FundamentalIdentity

open _root_.AlgebraicCurve

noncomputable section

noncomputable section

open IsDedekindDomain Polynomial

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place

section IntegrallyClosed

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_neg (f : F) : w.ord (-f) = w.ord f := by
  simp only [ord, Valuation.map_neg]

private theorem _root_.AlgebraicCurve.Place.mem_of_eval_monic_eq_zero {P : Polynomial F} (hP :
    P.Monic)
    (hcoeff : ∀ i, P.coeff i ∈ w.toValuationSubring) {x : F} (hx : P.eval x = 0) :
    x ∈ w.toValuationSubring := by
  have hlift : P ∈ lifts (algebraMap w.toValuationSubring F) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨P.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨Q, hQmap, -, hQmonic⟩ := lifts_and_degree_eq_and_monic hlift hP
  have hint : IsIntegral w.toValuationSubring x := by
    refine ⟨Q, hQmonic, ?_⟩
    rw [show eval₂ (algebraMap w.toValuationSubring F) x Q = (Q.map _).eval x from
      (eval_map _ x).symm, hQmap, hx]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hy ▸ y.2

private theorem _root_.AlgebraicCurve.Place.mem_maximalIdeal_iff_ord_pos {x : F} (hx : x ≠ 0)
    (hmem : x ∈ w.toValuationSubring) :
    (⟨x, hmem⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring ↔
      0 < w.ord x := by
  have hnonneg : 0 ≤ w.ord x := w.ord_nonneg_of_mem hmem
  have hcoe : ((⟨x, hmem⟩ : w.toValuationSubring) : F) = x := rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← w.adicValuation_coe_eq_one_iff,
    hcoe, ← w.ord_eq_zero_iff_adicValuation_eq_one hx]
  omega

end IntegrallyClosed

section SupportTransfer

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']

variable (w : Place K F')

omit [FiniteDimensional F F'] in
private theorem _root_.AlgebraicCurve.Place.aeval_mem {Q : Polynomial F} {x : F'}
    (hcoeff : ∀ i, algebraMap F F' (Q.coeff i) ∈ w.toValuationSubring)
    (hx : x ∈ w.toValuationSubring) :
    Polynomial.aeval x Q ∈ w.toValuationSubring := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hcoeff i) (pow_mem hx i)

private theorem exists_coeff_ord_ne_zero {f : F'} (hf : f ≠ 0) (hford : w.ord f ≠ 0) :
    ∃ i < (minpoly F f).natDegree, (minpoly F f).coeff i ≠ 0 ∧
      w.ord (algebraMap F F' ((minpoly F f).coeff i)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set P := minpoly F f with hPdef
  have hint : IsIntegral F f := Algebra.IsIntegral.isIntegral f
  have hmonic : P.Monic := minpoly.monic hint
  have hdeg : 0 < P.natDegree := minpoly.natDegree_pos hint
  have hc0 : P.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hf
  have hcoeff : ∀ i, algebraMap F F' (P.coeff i) ∈ w.toValuationSubring := by
    intro i
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · rcases eq_or_ne (P.coeff i) 0 with h0 | h0
      · simp [h0]
      · exact w.mem_of_ord_nonneg (by simpa using h0) (by have := hcon i hi h0; omega)
    · subst hi
      simp [hmonic.coeff_natDegree]
    · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]
  have hfmem : f ∈ w.toValuationSubring := by
    refine w.mem_of_eval_monic_eq_zero (P := P.map (algebraMap F F')) (hmonic.map _)
      (fun i => by simpa using hcoeff i) ?_
    rw [Polynomial.eval_map, ← Polynomial.aeval_def, hPdef, minpoly.aeval]
  have hfpos : 0 < w.ord f := lt_of_le_of_ne (w.ord_nonneg_of_mem hfmem) (Ne.symm hford)
  have hkey : algebraMap F F' (P.coeff 0) = -(f * Polynomial.aeval f P.divX) := by
    have hsplit : Polynomial.aeval f (Polynomial.X * P.divX + Polynomial.C (P.coeff 0))
        = (0 : F') := by rw [P.X_mul_divX_add]; exact minpoly.aeval F f
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hsplit
    linear_combination hsplit
  have hcof_mem : Polynomial.aeval f P.divX ∈ w.toValuationSubring :=
    w.aeval_mem (fun i => by rw [Polynomial.coeff_divX]; exact hcoeff (i + 1)) hfmem
  have hcof_ne : Polynomial.aeval f P.divX ≠ 0 := by
    intro h
    rw [h, mul_zero, neg_zero] at hkey
    exact hc0 (by simpa using hkey)
  have hpos0 : 0 < w.ord (algebraMap F F' (P.coeff 0)) := by
    rw [hkey, w.ord_neg, w.ord_mul hf hcof_ne]
    have := w.ord_nonneg_of_mem hcof_mem
    omega
  have := hcon 0 hdeg hc0
  omega

end SupportTransfer

section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

private def chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    R →+* w.toValuationSubring :=
  (algebraMap R F).codRestrict w.toValuationSubring.toSubring hw

omit [IsDedekindDomain R] [IsFractionRing R F] in
@[scoped simp]
private theorem coe_chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) (r : R) :
    (chartHom w hw r : F) = algebraMap R F r := rfl

variable (R) in
private def center (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) : Ideal R :=
  (IsLocalRing.maximalIdeal w.toValuationSubring).comap (chartHom w hw)

private scoped instance (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    (center R w hw).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsDedekindDomain R] [IsFractionRing R F] in
private theorem mem_center_iff (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) {r : R} :
    r ∈ center R w hw ↔
      (⟨algebraMap R F r, hw r⟩ : w.toValuationSubring) ∈
        IsLocalRing.maximalIdeal w.toValuationSubring :=
  Iff.rfl

private theorem mem_center_iff_ord_pos (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {r : R} (hr : r ≠ 0) :
    r ∈ center R w hw ↔ 0 < w.ord (algebraMap R F r) := by
  have hr' : algebraMap R F r ≠ 0 := by
    simpa using (IsFractionRing.injective R F).ne_iff.mpr hr
  rw [mem_center_iff, w.mem_maximalIdeal_iff_ord_pos hr']

omit [IsDedekindDomain R] [IsFractionRing R F] in
private theorem inv_algebraMap_mem (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {s : R} (hs : IsUnit (chartHom w hw s)) :
    (algebraMap R F s)⁻¹ ∈ w.toValuationSubring := by
  obtain ⟨u, hu⟩ := hs
  have hcoe : ((u : w.toValuationSubring) : F) = algebraMap R F s := by rw [hu]; rfl
  have h1 : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
      * algebraMap R F s = 1 := by
    have hmul := congrArg (fun a : w.toValuationSubring => (a : F)) u.inv_mul
    push_cast at hmul
    rwa [hcoe] at hmul
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact SetLike.coe_mem _

private theorem center_ne_bot (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    center R w hw ≠ ⊥ := by
  intro hbot
  apply w.ne_top'
  have hunit : ∀ r : R, r ≠ 0 → IsUnit (chartHom w hw r) := by
    intro r hr
    by_contra hu
    have : r ∈ center R w hw :=
      (mem_center_iff w hw).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu)
    rw [hbot] at this
    exact hr (by simpa using this)
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := R) x
  rw [← hx, div_eq_mul_inv]
  exact mul_mem (hw a) (inv_algebraMap_mem w hw (hunit b (nonZeroDivisors.ne_zero hb)))

variable (R) in
private def centerHeightOneSpectrum (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum R :=
  ⟨center R w hw, inferInstance, center_ne_bot w hw⟩

@[scoped simp]
private theorem centerHeightOneSpectrum_asIdeal
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    (centerHeightOneSpectrum R w hw).asIdeal = center R w hw := rfl

private theorem valuationSubringAtPrime_centerHeightOneSpectrum_le
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum.valuationSubringAtPrime F (centerHeightOneSpectrum R w hw) ≤
      w.toValuationSubring := by
  rintro x ⟨a, s, hs, rfl⟩
  refine mul_mem (hw a) (inv_algebraMap_mem w hw ?_)
  rw [← IsLocalRing.notMem_maximalIdeal]
  exact fun hmem => hs ((mem_center_iff w hw).mpr hmem)

private theorem toValuationSubring_eq_of_forall_mem
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    w.toValuationSubring =
      HeightOneSpectrum.valuationSubringAtPrime F (centerHeightOneSpectrum R w hw) :=
  (ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAtPrime_centerHeightOneSpectrum_le w hw) w.ne_top').symm

private theorem finite_setOf_forall_mem_and_ord_pos {r₀ : R} (hr₀ : r₀ ≠ 0) :
    {w : Place K F | (∀ r : R, algebraMap R F r ∈ w.toValuationSubring) ∧
      0 < w.ord (algebraMap R F r₀)}.Finite := by
  have hfin : {p : HeightOneSpectrum R | p.asIdeal ∣ Ideal.span {r₀}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hr₀)
  rw [← Set.finite_coe_iff]
  have := hfin.to_subtype
  refine Finite.of_injective
    (fun w => (⟨centerHeightOneSpectrum R w.1 w.2.1, ?_⟩ :
      {p : HeightOneSpectrum R | p.asIdeal ∣ Ideal.span {r₀}})) ?_
  · rw [Set.mem_ofPred_eq, centerHeightOneSpectrum_asIdeal, Ideal.dvd_span_singleton]
    exact (mem_center_iff_ord_pos w.1 w.2.1 hr₀).mpr w.2.2
  · intro w w' h
    have hcenter : centerHeightOneSpectrum R w.1 w.2.1
        = centerHeightOneSpectrum R w'.1 w'.2.1 := congrArg Subtype.val h
    refine Subtype.ext (Place.ext ?_)
    rw [toValuationSubring_eq_of_forall_mem w.1 w.2.1,
      toValuationSubring_eq_of_forall_mem w'.1 w'.2.1, hcenter]

end Chart

section FiberFiniteness

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

private theorem finite_setOf_restrict_eq (v : Place K F) :
    {w : Place K F' | w.restrict F = v}.Finite := by
  classical
  let : Algebra v.toValuationSubring F' :=
    ((algebraMap F F').comp (algebraMap v.toValuationSubring F)).toAlgebra
  have : IsScalarTower v.toValuationSubring F F' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsDedekindDomain (integralClosure v.toValuationSubring F') :=
    integralClosure.isDedekindDomain v.toValuationSubring F F'
  have : IsFractionRing (integralClosure v.toValuationSubring F') F' :=
    integralClosure.isFractionRing_of_finite_extension (A := v.toValuationSubring) F F'
  obtain ⟨π, hπ0, hπpos⟩ := v.exists_ord_pos
  have hπmem : π ∈ v.toValuationSubring := v.mem_of_ord_nonneg hπ0 hπpos.le
  set C := integralClosure v.toValuationSubring F' with hC
  set π' : C := algebraMap v.toValuationSubring C ⟨π, hπmem⟩ with hπ'
  have hπ'F : algebraMap C F' π' = algebraMap F F' π := by
    rw [hπ', ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply
      v.toValuationSubring F F']
    rfl
  have hπ'0 : π' ≠ 0 := by
    intro h
    apply hπ0
    have : algebraMap C F' π' = 0 := by rw [h, map_zero]
    rw [hπ'F] at this
    simpa using this
  refine Set.Finite.subset (finite_setOf_forall_mem_and_ord_pos (R := C) hπ'0) ?_
  rintro w (hw : w.restrict F = v)
  have hOv : ∀ g : F, g ∈ v.toValuationSubring → algebraMap F F' g ∈ w.toValuationSubring := by
    intro g hg
    rw [← hw] at hg
    exact hg
  refine ⟨?_, ?_⟩
  · intro c
    obtain ⟨Q, hQmonic, hQeval⟩ := c.2
    have : algebraMap C F' c = (c : F') := rfl
    rw [this]
    refine w.mem_of_eval_monic_eq_zero (P := Q.map (algebraMap v.toValuationSubring F'))
      (hQmonic.map _) (fun i => ?_) (by rw [Polynomial.eval_map]; exact hQeval)
    rw [Polynomial.coeff_map, IsScalarTower.algebraMap_apply v.toValuationSubring F F']
    exact hOv _ (Q.coeff i).2
  · rw [hπ'F, w.ord_restrict π, hw]
    have hepos : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    positivity

end FiberFiniteness

end Place
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place

end AlgebraicCurve
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place

section Uniqueness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring))
    {x : F} (hx : x ≠ 0) : φ x = w.ord x := by
  obtain ⟨t, ht0, ht1⟩ := hone
  have hφ1 : φ 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega
  have hinv : ∀ y, y ≠ 0 → φ y⁻¹ = -φ y := by
    intro y hy
    have h1 : φ (y * y⁻¹) = φ y + φ y⁻¹ := hmul y y⁻¹ hy (inv_ne_zero hy)
    rw [mul_inv_cancel₀ hy, hφ1] at h1
    omega
  have hpow : ∀ (y : F), y ≠ 0 → ∀ m : ℕ, φ (y ^ m) = m * φ y := by
    intro y hy m
    induction m with
    | zero => simpa using hφ1
    | succ m ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero _ hy) hy, ih]
      push_cast
      ring
  have hzpow : ∀ (y : F) (n : ℤ), y ≠ 0 → φ (y ^ n) = n * φ y := by
    intro y n hy
    rcases n with m | m
    · simpa using hpow y hy m
    · rw [zpow_negSucc, hinv _ (pow_ne_zero _ hy), hpow y hy, Int.negSucc_eq]
      push_cast
      ring
  have hsign : ∀ y, y ≠ 0 → (0 ≤ φ y ↔ 0 ≤ w.ord y) := by
    intro y hy
    rw [hiff y hy, w.mem_iff_ord_nonneg hy]
  have hzero : ∀ y, y ≠ 0 → (φ y = 0 ↔ w.ord y = 0) := by
    intro y hy
    have h1 := hsign y hy
    have h2 := hsign y⁻¹ (inv_ne_zero hy)
    rw [hinv y hy, w.ord_inv] at h2
    omega
  have htord : 0 < w.ord t := by
    have h1 := (hsign t ht0).mp (by omega)
    have h2 := (hzero t ht0).not.mp (by omega)
    omega
  have hcancel : ∀ y, y ≠ 0 → w.ord y = φ y * w.ord t := by
    intro y hy
    have hyt : y * t ^ (-(φ y)) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
    have h1 : φ (y * t ^ (-(φ y))) = 0 := by
      rw [hmul _ _ hy (zpow_ne_zero _ ht0), hzpow t _ ht0, ht1]
      ring
    have h2 : w.ord (y * t ^ (-(φ y))) = 0 := (hzero _ hyt).mp h1
    rw [w.ord_mul hy (zpow_ne_zero _ ht0), w.ord_zpow] at h2
    linarith
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hπcancel := hcancel (π : F) hπ0
  rw [w.ord_coe_irreducible hπ] at hπcancel
  have htord1 : w.ord t = 1 := by
    have hdvd : w.ord t ∣ 1 := ⟨φ (π : F), by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    omega
  have := hcancel x hx
  rw [htord1, mul_one] at this
  exact this.symm

end Uniqueness
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

variable (F') in
@[reducible] private def valuationSubringAlgebra (v : Place K F) : Algebra v.toValuationSubring
    F' :=
  ((algebraMap F F').comp (algebraMap v.toValuationSubring F)).toAlgebra

attribute [local instance 0] valuationSubringAlgebra

section Setup

variable (v : Place K F)

private scoped instance (priority := 100) : IsScalarTower v.toValuationSubring F F' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable (F') in
private abbrev integralClosureAt : Type _ := integralClosure v.toValuationSubring F'

private scoped instance : IsDedekindDomain (integralClosureAt F' v) :=
  integralClosure.isDedekindDomain v.toValuationSubring F F'

private scoped instance : IsFractionRing (integralClosureAt F' v) F' :=
  integralClosure.isFractionRing_of_finite_extension (A := v.toValuationSubring) F F'

private scoped instance : Module.Finite v.toValuationSubring (integralClosureAt F' v) :=
  IsIntegralClosure.finite v.toValuationSubring F F' _

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] in
private theorem algebraMap_integralClosureAt_injective :
    Function.Injective
      (algebraMap v.toValuationSubring (integralClosureAt F' v)) := by
  intro a b hab
  have h1 : algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) a)
        = algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) b) := by rw [hab]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
  exact ((algebraMap F F').injective.comp
    (IsFractionRing.injective v.toValuationSubring F)) h1

private scoped instance : Module.IsTorsionFree v.toValuationSubring (integralClosureAt F' v) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosureAt_injective v (by rw [h, map_zero]))
  · exact Or.inr h

private theorem maximalIdeal_ne_bot :
    IsLocalRing.maximalIdeal v.toValuationSubring ≠ ⊥ := by
  intro h
  exact ValuationSubring.not_isField_of_ne_top F v.ne_top'
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)

end Setup
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

section Center

variable {v : Place K F} {w : Place K F'}

omit [FiniteDimensional F F'] in
private theorem forall_mem_of_restrict_eq (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    algebraMap (integralClosureAt F' v) F' c ∈ w.toValuationSubring := by
  obtain ⟨Q, hQmonic, hQeval⟩ := c.2
  have hOv : ∀ g : F, g ∈ v.toValuationSubring →
      algebraMap F F' g ∈ w.toValuationSubring := by
    intro g hg
    rw [← hw] at hg
    exact hg
  refine w.mem_of_eval_monic_eq_zero (P := Q.map (algebraMap v.toValuationSubring F'))
    (hQmonic.map _) (fun i => ?_) (by rw [Polynomial.eval_map]; exact hQeval)
  rw [Polynomial.coeff_map,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F']
  exact hOv _ (Q.coeff i).2

variable (F' v) in
private def fiberCenter (hw : w.restrict F = v) : HeightOneSpectrum (integralClosureAt F' v) :=
  centerHeightOneSpectrum (integralClosureAt F' v) w (forall_mem_of_restrict_eq hw)

private theorem mem_fiberCenter_iff_ord_pos (hw : w.restrict F = v) {c : integralClosureAt F' v}
    (hc : c ≠ 0) :
    c ∈ (fiberCenter F' v hw).asIdeal ↔
      0 < w.ord (algebraMap (integralClosureAt F' v) F' c) :=
  mem_center_iff_ord_pos w (forall_mem_of_restrict_eq hw) hc

private theorem toValuationSubring_eq_of_restrict_eq (hw : w.restrict F = v) :
    w.toValuationSubring =
      HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) :=
  toValuationSubring_eq_of_forall_mem w (forall_mem_of_restrict_eq hw)

private theorem mem_maximalIdeal_iff_ord_pos' {r : v.toValuationSubring} (hr : r ≠ 0) :
    r ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔
      0 < v.ord (algebraMap v.toValuationSubring F r) := by
  have hrF : (algebraMap v.toValuationSubring F r : F) ≠ 0 := by
    simpa using (IsFractionRing.injective v.toValuationSubring F).ne_iff.mpr hr
  have := v.mem_maximalIdeal_iff_ord_pos hrF (Subtype.coe_prop r)
  simpa using this

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] in
private theorem algebraMap_integralClosureAt_ne_zero {r : v.toValuationSubring} (hr : r ≠ 0) :
    algebraMap v.toValuationSubring (integralClosureAt F' v) r ≠ 0 := fun h =>
  hr (algebraMap_integralClosureAt_injective v (by rw [h, map_zero]))

omit [FiniteDimensional F F'] in
private theorem ord_algebraMap_integralClosureAt (hw : w.restrict F
    = v) (r : v.toValuationSubring) :
    w.ord (algebraMap (integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (integralClosureAt F' v) r))
      = w.ramificationIndex F * v.ord (algebraMap v.toValuationSubring F r) := by
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F', w.ord_restrict, hw]

private theorem fiberCenter_liesOver (hw : w.restrict F = v) :
    (fiberCenter F' v hw).asIdeal.LiesOver
      (IsLocalRing.maximalIdeal v.toValuationSubring) := by
  refine ⟨?_⟩
  rw [Ideal.under_def]
  ext r
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  rw [Ideal.mem_comap,
    mem_fiberCenter_iff_ord_pos hw (algebraMap_integralClosureAt_ne_zero hr),
    ord_algebraMap_integralClosureAt hw, mem_maximalIdeal_iff_ord_pos' hr]
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos
  constructor
  · intro h
    positivity
  · intro h
    rcases mul_pos_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact h2
    · omega

end Center
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

section ValuationDictionary

variable {v : Place K F} {w : Place K F'}

private theorem neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x := by
  refine eq_ord_of_addHom_of_nonneg_iff w
    (fun y => -log ((fiberCenter F' v hw).valuation F' y)) ?_ ?_ ?_ hx
  · intro a b ha hb
    show -log ((fiberCenter F' v hw).valuation F' (a * b)) =
      -log ((fiberCenter F' v hw).valuation F' a) +
        -log ((fiberCenter F' v hw).valuation F' b)
    rw [map_mul, log_mul ((Valuation.ne_zero_iff _).mpr ha) ((Valuation.ne_zero_iff _).mpr hb)]
    ring
  · obtain ⟨t, ht⟩ := (fiberCenter F' v hw).valuation_exists_uniformizer F'
    refine ⟨t, ?_, ?_⟩
    · intro h
      rw [h, map_zero] at ht
      exact exp_ne_zero ht.symm
    · show -log ((fiberCenter F' v hw).valuation F' t) = 1
      rw [ht, log_exp]
      ring
  · intro y hy
    have hy0 : (fiberCenter F' v hw).valuation F' y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
    change 0 ≤ -log ((fiberCenter F' v hw).valuation F' y) ↔ y ∈ w.toValuationSubring
    have hmem : y ∈ w.toValuationSubring ↔ (fiberCenter F' v hw).valuation F' y ≤ 1 := by
      rw [toValuationSubring_eq_of_restrict_eq hw,
        HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact Iff.rfl
    rw [hmem]
    constructor
    · intro h
      calc (fiberCenter F' v hw).valuation F' y
          = exp (log ((fiberCenter F' v hw).valuation F' y)) := (exp_log hy0).symm
        _ ≤ exp 0 := by rw [exp_le_exp]; omega
        _ = 1 := exp_zero
    · intro h
      have h1 : exp (log ((fiberCenter F' v hw).valuation F' y)) ≤ exp 0 := by
        rw [exp_log hy0, exp_zero]
        exact h
      rw [exp_le_exp] at h1
      omega

private theorem le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n := by
  have hcF : algebraMap (integralClosureAt F' v) F' c ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hc
  rw [← neg_log_valuation_fiberCenter_eq_ord hw hcF,
    HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_le_pow_iff_mem]
  have h0 : (fiberCenter F' v hw).intValuation c ≠ 0 :=
    HeightOneSpectrum.intValuation_ne_zero _ c hc
  constructor
  · intro h
    calc (fiberCenter F' v hw).intValuation c
        = exp (log ((fiberCenter F' v hw).intValuation c)) := (exp_log h0).symm
      _ ≤ exp (-(n : ℤ)) := by rw [exp_le_exp]; omega
  · intro h
    have h1 : exp (log ((fiberCenter F' v hw).intValuation c)) ≤ exp (-(n : ℤ)) := by
      rw [exp_log h0]
      exact h
    rw [exp_le_exp] at h1
    omega

private theorem ramificationIndex_eq_ramificationIdx_fiberCenter (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπC : algebraMap v.toValuationSubring (integralClosureAt F' v) π ≠ 0 :=
    algebraMap_integralClosureAt_ne_zero hπ0
  have hmap : (IsLocalRing.maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (integralClosureAt F' v))
        = Ideal.span {algebraMap v.toValuationSubring (integralClosureAt F' v) π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hord : w.ord (algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) π))
        = w.ramificationIndex F := by
    rw [ord_algebraMap_integralClosureAt hw, ValuationSubring.algebraMap_apply,
      v.ord_coe_irreducible hπ, mul_one]
  refine (Ideal.ramificationIdx'_spec ?_ ?_).symm
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      ← le_ord_iff_mem_pow_fiberCenter hw hπC, hord]
    have : 0 < w.ramificationIndex F := w.ramificationIndex_pos
    push_cast
    omega

end ValuationDictionary
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

section ResidueDictionary

variable {v : Place K F} {w : Place K F'}

private def toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring :=
  (algebraMap (integralClosureAt F' v) F').codRestrict
    w.toValuationSubring.toSubring (forall_mem_of_restrict_eq hw)

omit [FiniteDimensional F F'] in
@[scoped simp]
private theorem coe_toValuationSubringOfRestrictEq (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    (toValuationSubringOfRestrictEq hw c : F')
      = algebraMap (integralClosureAt F' v) F' c := rfl

private def residueOfCenter (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.ResidueField :=
  (IsLocalRing.residue w.toValuationSubring).comp (toValuationSubringOfRestrictEq hw)

omit [FiniteDimensional F F'] in
private theorem residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c = IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw c) := rfl

private theorem ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal := by
  ext c
  rw [RingHom.mem_ker, residueOfCenter_apply, IsLocalRing.residue_eq_zero_iff]
  exact Iff.rfl

private theorem surjective_residueOfCenter (hw : w.restrict F = v) :
    Function.Surjective (residueOfCenter hw) := by
  classical
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : (x : F') ∈ HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) := by
    rw [← toValuationSubring_eq_of_restrict_eq hw]
    exact x.2
  obtain ⟨a, s, hs, hxas⟩ := hx
  have hsP : s ∉ (fiberCenter F' v hw).asIdeal := hs
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ (fiberCenter F' v hw).asIdeal.zero_mem)
  have hsF : algebraMap (integralClosureAt F' v) F' s ≠ 0 := by
    simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hs0
  have hsord : w.ord (algebraMap (integralClosureAt F' v) F' s) = 0 := by
    have h1 : ¬ 0 < w.ord (algebraMap (integralClosureAt F' v) F' s) := by
      rw [← mem_fiberCenter_iff_ord_pos hw hs0]
      exact hsP
    have h2 : 0 ≤ w.ord (algebraMap (integralClosureAt F' v) F' s) :=
      w.ord_nonneg_of_mem (forall_mem_of_restrict_eq hw s)
    omega
  have hmax : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  obtain ⟨t, i, hi, hti⟩ := hmax.exists_inv hsP
  have hst : s * t - 1 ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : s * t - 1 = -i := by linear_combination hti
    rw [h1]
    exact neg_mem hi
  refine ⟨a * t, ?_⟩
  rw [residueOfCenter_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hcoe : ((toValuationSubringOfRestrictEq hw (a * t) - x : w.toValuationSubring) : F')
      = algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') := rfl
  rcases eq_or_ne (toValuationSubringOfRestrictEq hw (a * t) - x) 0 with hzero | hne
  · rw [hzero]
    exact (IsLocalRing.maximalIdeal w.toValuationSubring).zero_mem
  have hcoene : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F') ≠ 0 := by
    intro h
    exact hne (by rwa [← hcoe, ZeroMemClass.coe_eq_zero] at h)
  have hfactor : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      = algebraMap (integralClosureAt F' v) F' (a * t * s - a)
          * (algebraMap (integralClosureAt F' v) F' s)⁻¹ := by
    rw [hxas, map_sub, map_mul (algebraMap (integralClosureAt F' v) F') (a * t) s,
      sub_mul, mul_assoc, mul_inv_cancel₀ hsF, mul_one]
  have hdiffC : a * t * s - a ≠ 0 := by
    intro h
    apply hcoene
    rw [hfactor, h, map_zero, zero_mul]
  have hdiffP : a * t * s - a ∈ (fiberCenter F' v hw).asIdeal := by
    have h1 : a * t * s - a = a * (s * t - 1) := by ring
    rw [h1]
    exact Ideal.mul_mem_left _ _ hst
  have hmem' : algebraMap (integralClosureAt F' v) F' (a * t) - (x : F')
      ∈ w.toValuationSubring := by
    rw [← hcoe]
    exact Subtype.coe_prop _
  rw [show (toValuationSubringOfRestrictEq hw (a * t) - x)
      = (⟨_, hmem'⟩ : w.toValuationSubring) from Subtype.ext hcoe,
    w.mem_maximalIdeal_iff_ord_pos hcoene hmem']
  rw [hfactor, w.ord_mul (by
      simpa using (IsFractionRing.injective (integralClosureAt F' v) F').ne_iff.mpr hdiffC)
    (inv_ne_zero hsF), w.ord_inv, hsord, neg_zero, add_zero]
  exact (mem_fiberCenter_iff_ord_pos hw hdiffC).mp hdiffP

private def residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField :=
  (Ideal.quotEquivOfEq (ker_residueOfCenter hw).symm).trans
    ((residueOfCenter hw).quotientKerEquivOfSurjective (surjective_residueOfCenter hw))

private theorem residueFieldEquivQuotientCenter_mk (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    residueFieldEquivQuotientCenter hw (Ideal.Quotient.mk _ c) = residueOfCenter hw c := by
  change ((residueOfCenter hw).quotientKerEquivOfSurjective (surjective_residueOfCenter hw))
    ((Ideal.quotEquivOfEq (ker_residueOfCenter hw).symm) (Ideal.Quotient.mk _ c))
      = residueOfCenter hw c
  rw [Ideal.quotEquivOfEq_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ c

private def placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun x := ⟨x.1, h.symm ▸ x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[scoped simp]
private theorem coe_placeCongrEquiv {u u' : Place K F} (h : u = u') (x : u.toValuationSubring) :
    (placeCongrEquiv h x : F) = (x : F) := rfl

private def restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring :=
  IsLocalRing.ResidueField.mapEquiv (placeCongrEquiv hw)

omit [FiniteDimensional F F'] in
private theorem restrictResidueFieldEquiv_residue (hw : w.restrict F = v)
    (a : (w.restrict F).toValuationSubring) :
    restrictResidueFieldEquiv hw (IsLocalRing.residue _ a)
      = IsLocalRing.residue _ (placeCongrEquiv hw a) := by
  simp only [restrictResidueFieldEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue, RingEquiv.coe_toRingHom]

private theorem inertiaDeg_eq_inertiaDeg_fiberCenter (hw : w.restrict F = v) :
    w.inertiaDeg F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg'
        (fiberCenter F' v hw).asIdeal := by
  have := fiberCenter_liesOver hw
  rw [Ideal.inertiaDeg_algebraMap]
  change Module.finrank (w.restrict F).ResidueField w.ResidueField = _
  refine Algebra.finrank_eq_of_equiv_equiv (restrictResidueFieldEquiv hw)
    (residueFieldEquivQuotientCenter hw).symm ?_
  ext a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  apply (residueFieldEquivQuotientCenter hw).injective
  rw [RingEquiv.apply_symm_apply]
  change IsLocalRing.residue w.toValuationSubring
      (toValuationSubringOfRestrictEq hw
        (algebraMap v.toValuationSubring (integralClosureAt F' v) (placeCongrEquiv hw a)))
    = IsLocalRing.residue w.toValuationSubring (restrictInclusion F w a)
  refine congrArg _ (Subtype.ext ?_)
  change algebraMap (integralClosureAt F' v) F'
      (algebraMap v.toValuationSubring (integralClosureAt F' v) (placeCongrEquiv hw a))
    = algebraMap F F' (a : F)
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F']
  rfl

end ResidueDictionary
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

section Bijection

variable {v : Place K F}

private def placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) : Place K F' where
  toValuationSubring := HeightOneSpectrum.valuationSubringAtPrime F' P
  algebraMap_mem' := fun a => by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
    have h1 : algebraMap K F' a = algebraMap (integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (integralClosureAt F' v)
          (algebraMap K v.toValuationSubring a)) := by
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply v.toValuationSubring F F',
        ← IsScalarTower.algebraMap_apply K v.toValuationSubring F,
        ← IsScalarTower.algebraMap_apply K F F']
    rw [h1]
    exact P.valuation_le_one _
  ne_top' := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  isPrincipalIdealRing' := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact isPrincipalIdealRing_valuationSubring P

@[scoped simp]
private theorem placeOfPrime_toValuationSubring (P : HeightOneSpectrum (integralClosureAt F' v)) :
    (placeOfPrime P).toValuationSubring = HeightOneSpectrum.valuationSubringAtPrime F' P :=
  rfl

private theorem restrict_placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) :
    (placeOfPrime P).restrict F = v := by
  have hle : v.toValuationSubring ≤ ((placeOfPrime P).restrict F).toValuationSubring := by
    intro g hg
    rw [restrict_toValuationSubring, ValuationSubring.mem_comap,
      placeOfPrime_toValuationSubring,
      HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
    have h1 : algebraMap F F' g = algebraMap (integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (integralClosureAt F' v) ⟨g, hg⟩) := by
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply v.toValuationSubring F F']
      rfl
    rw [h1]
    exact P.valuation_le_one _
  exact (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle
    ((placeOfPrime P).restrict F).ne_top')).symm

private theorem fiberCenter_placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) :
    fiberCenter F' v (restrict_placeOfPrime P) = P := by
  have h1 : HeightOneSpectrum.valuationSubringAtPrime F'
      (fiberCenter F' v (restrict_placeOfPrime P))
        = HeightOneSpectrum.valuationSubringAtPrime F' P := by
    rw [← toValuationSubring_eq_of_restrict_eq (restrict_placeOfPrime P),
      placeOfPrime_toValuationSubring]
  refine HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F') ?_
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, h1]

private theorem eq_of_fiberCenter_eq {w w' : Place K F'} (hw : w.restrict F = v)
    (hw' : w'.restrict F = v)
    (h : fiberCenter F' v hw = fiberCenter F' v hw') : w = w' := by
  refine Place.ext ?_
  rw [toValuationSubring_eq_of_restrict_eq hw, toValuationSubring_eq_of_restrict_eq hw', h]

end Bijection
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

section Assembly

variable (v : Place K F)

private theorem sum_ramificationIndex_mul_inertiaDeg_infra [HasPrincipalDivisors K F'] :
    ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)
      = (Module.finrank F F' : ℤ) := by
  classical
  have hkey := Ideal.sum_ramification_inertia (integralClosureAt F' v) F F'
    (p := IsLocalRing.maximalIdeal v.toValuationSubring) (maximalIdeal_ne_bot v)
  rw [← hkey]
  push_cast
  refine Finset.sum_bij
    (fun w hw => (fiberCenter F' v (Place.mem_fiber.mp hw)).asIdeal) ?_ ?_ ?_ ?_
  · intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v (Place.mem_fiber.mp hw)).isPrime,
      fiberCenter_liesOver (Place.mem_fiber.mp hw)⟩
  · intro w hw w' hw' h
    exact eq_of_fiberCenter_eq (Place.mem_fiber.mp hw) (Place.mem_fiber.mp hw')
      (HeightOneSpectrum.ext h)
  · intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)] at hP
    obtain ⟨hP1, hP2⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro h
      apply maximalIdeal_ne_bot v
      have h2 := hP2.over
      rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _
        (algebraMap_integralClosureAt_injective v)] at h2
      exact h2
    refine ⟨placeOfPrime ⟨P, hP1, hPne⟩,
      Place.mem_fiber.mpr (restrict_placeOfPrime ⟨P, hP1, hPne⟩), ?_⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))
  · intro w hw
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter (Place.mem_fiber.mp hw),
      inertiaDeg_eq_inertiaDeg_fiberCenter (Place.mem_fiber.mp hw)]

end Assembly
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

end Place
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

private scoped instance instSumRamificationInertia {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] :
    SumRamificationInertia K F F' :=
  ⟨fun v => Place.sum_ramificationIndex_mul_inertiaDeg_infra v⟩

end AlgebraicCurve
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

/-- The fundamental identity: for a finite separable extension `F'` of `F` and a place `v` of `F`,
the sum of `e(w | v) f(w | v)` over the places `w` above `v` is `[F' : F]`. -/
public theorem _root_.AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    [HasPrincipalDivisors K F'] (v : Place K F) :
    ∑ w ∈ v.fiber F',
        (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) = (Module.finrank F F' : ℤ) :=
  AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_infra v

end
open scoped _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve.Place
    _root_.CurveGenus.FundamentalIdentity.AlgebraicCurve

end

end

end FundamentalIdentity

end CurveGenus
