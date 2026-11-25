/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`
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
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Places lying over a place of a subfield

This file describes the places of a finite separable extension lying over a place through the
integral closure of its valuation ring, and defines the fiber of places over a place.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

section IntegrallyClosed

open Polynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem ord_neg (f : F) : w.ord (-f) = w.ord f := by
  simp only [ord, Valuation.map_neg]

theorem mem_of_eval_monic_eq_zero {P : Polynomial F} (hP : P.Monic)
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

theorem mem_maximalIdeal_iff_ord_pos {x : F} (hx : x ≠ 0)
    (hmem : x ∈ w.toValuationSubring) :
    (⟨x, hmem⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring ↔
      0 < w.ord x := by
  have hnonneg : 0 ≤ w.ord x := w.ord_nonneg_of_mem hmem
  have hcoe : ((⟨x, hmem⟩ : w.toValuationSubring) : F) = x := rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← w.adicValuation_coe_eq_one_iff,
    hcoe, ← w.ord_eq_zero_iff_adicValuation_eq_one hx]
  omega

end IntegrallyClosed

section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

def chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    R →+* w.toValuationSubring :=
  (algebraMap R F).codRestrict w.toValuationSubring.toSubring hw

omit [IsDedekindDomain R] [IsFractionRing R F] in
@[simp]
theorem coe_chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) (r : R) :
    (chartHom w hw r : F) = algebraMap R F r := rfl

variable (R) in
def center (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) : Ideal R :=
  (IsLocalRing.maximalIdeal w.toValuationSubring).comap (chartHom w hw)

instance (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    (center R w hw).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsDedekindDomain R] [IsFractionRing R F] in
theorem mem_center_iff (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) {r : R} :
    r ∈ center R w hw ↔
      (⟨algebraMap R F r, hw r⟩ : w.toValuationSubring) ∈
        IsLocalRing.maximalIdeal w.toValuationSubring :=
  Iff.rfl

theorem mem_center_iff_ord_pos (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
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

theorem center_ne_bot (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
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
def centerHeightOneSpectrum (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum R :=
  ⟨center R w hw, inferInstance, center_ne_bot w hw⟩

@[simp]
theorem centerHeightOneSpectrum_asIdeal
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    (centerHeightOneSpectrum R w hw).asIdeal = center R w hw := rfl

theorem valuationSubringAtPrime_centerHeightOneSpectrum_le
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum.valuationSubringAtPrime F (centerHeightOneSpectrum R w hw) ≤
      w.toValuationSubring := by
  rintro x ⟨a, s, hs, rfl⟩
  refine mul_mem (hw a) (inv_algebraMap_mem w hw ?_)
  rw [← IsLocalRing.notMem_maximalIdeal]
  exact fun hmem => hs ((mem_center_iff w hw).mpr hmem)

theorem toValuationSubring_eq_of_forall_mem
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    w.toValuationSubring =
      HeightOneSpectrum.valuationSubringAtPrime F (centerHeightOneSpectrum R w hw) :=
  (ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAtPrime_centerHeightOneSpectrum_le w hw) w.ne_top').symm

theorem finite_setOf_forall_mem_and_ord_pos {r₀ : R} (hr₀ : r₀ ≠ 0) :
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

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

variable (F') in
@[reducible] def valuationSubringAlgebra (v : Place K F) : Algebra v.toValuationSubring F' :=
  ((algebraMap F F').comp (algebraMap v.toValuationSubring F)).toAlgebra

section Setup

variable (v : Place K F)

variable (F') in
abbrev integralClosureAt : Type _ := integralClosure v.toValuationSubring F'

instance : IsDedekindDomain (integralClosureAt F' v) :=
  integralClosure.isDedekindDomain v.toValuationSubring F F'

instance : IsFractionRing (integralClosureAt F' v) F' :=
  integralClosure.isFractionRing_of_finite_extension (A := v.toValuationSubring) F F'

instance : Module.Finite v.toValuationSubring (integralClosureAt F' v) :=
  IsIntegralClosure.finite v.toValuationSubring F F' _

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] in
theorem algebraMap_integralClosureAt_injective :
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

instance : Module.IsTorsionFree v.toValuationSubring (integralClosureAt F' v) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (algebraMap_integralClosureAt_injective v (by rw [h, map_zero]))
  · exact Or.inr h

theorem maximalIdeal_ne_bot :
    IsLocalRing.maximalIdeal v.toValuationSubring ≠ ⊥ := by
  intro h
  exact ValuationSubring.not_isField_of_ne_top F v.ne_top'
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)

end Setup

section Center

variable {v : Place K F} {w : Place K F'}

omit [FiniteDimensional F F'] in
theorem forall_mem_of_restrict_eq (hw : w.restrict F = v) (c : integralClosureAt F' v) :
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
def fiberCenter (hw : w.restrict F = v) : HeightOneSpectrum (integralClosureAt F' v) :=
  centerHeightOneSpectrum (integralClosureAt F' v) w (forall_mem_of_restrict_eq hw)

theorem mem_fiberCenter_iff_ord_pos (hw : w.restrict F = v) {c : integralClosureAt F' v}
    (hc : c ≠ 0) :
    c ∈ (fiberCenter F' v hw).asIdeal ↔
      0 < w.ord (algebraMap (integralClosureAt F' v) F' c) :=
  mem_center_iff_ord_pos w (forall_mem_of_restrict_eq hw) hc

theorem toValuationSubring_eq_of_restrict_eq (hw : w.restrict F = v) :
    w.toValuationSubring =
      HeightOneSpectrum.valuationSubringAtPrime F' (fiberCenter F' v hw) :=
  toValuationSubring_eq_of_forall_mem w (forall_mem_of_restrict_eq hw)

theorem mem_maximalIdeal_iff_ord_pos' {r : v.toValuationSubring} (hr : r ≠ 0) :
    r ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔
      0 < v.ord (algebraMap v.toValuationSubring F r) := by
  have hrF : (algebraMap v.toValuationSubring F r : F) ≠ 0 := by
    simpa using (IsFractionRing.injective v.toValuationSubring F).ne_iff.mpr hr
  have := v.mem_maximalIdeal_iff_ord_pos hrF (Subtype.coe_prop r)
  simpa using this

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F'] in
theorem algebraMap_integralClosureAt_ne_zero {r : v.toValuationSubring} (hr : r ≠ 0) :
    algebraMap v.toValuationSubring (integralClosureAt F' v) r ≠ 0 := fun h =>
  hr (algebraMap_integralClosureAt_injective v (by rw [h, map_zero]))

omit [FiniteDimensional F F'] in
theorem ord_algebraMap_integralClosureAt (hw : w.restrict F = v) (r : v.toValuationSubring) :
    w.ord (algebraMap (integralClosureAt F' v) F'
        (algebraMap v.toValuationSubring (integralClosureAt F' v) r))
      = w.ramificationIndex F * v.ord (algebraMap v.toValuationSubring F r) := by
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply v.toValuationSubring F F', w.ord_restrict, hw]

theorem fiberCenter_liesOver (hw : w.restrict F = v) :
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

section Bijection

variable {v : Place K F}

def placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) : Place K F' where
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

@[simp]
theorem placeOfPrime_toValuationSubring (P : HeightOneSpectrum (integralClosureAt F' v)) :
    (placeOfPrime P).toValuationSubring = HeightOneSpectrum.valuationSubringAtPrime F' P :=
  rfl

theorem restrict_placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) :
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

theorem fiberCenter_placeOfPrime (P : HeightOneSpectrum (integralClosureAt F' v)) :
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

theorem eq_of_fiberCenter_eq {w w' : Place K F'} (hw : w.restrict F = v)
    (hw' : w'.restrict F = v)
    (h : fiberCenter F' v hw = fiberCenter F' v hw') : w = w' := by
  refine Place.ext ?_
  rw [toValuationSubring_eq_of_restrict_eq hw, toValuationSubring_eq_of_restrict_eq hw', h]

end Bijection

section Fiber

variable (v : Place K F)

variable (F') in
def fiberEquiv :
    {w : Place K F' // w.restrict F = v} ≃ HeightOneSpectrum (integralClosureAt F' v) where
  toFun w := fiberCenter F' v w.2
  invFun P := ⟨placeOfPrime P, restrict_placeOfPrime P⟩
  left_inv w := Subtype.ext (eq_of_fiberCenter_eq (restrict_placeOfPrime _) w.2
    (fiberCenter_placeOfPrime (fiberCenter F' v w.2)))
  right_inv P := fiberCenter_placeOfPrime P

@[simp]
theorem fiberEquiv_apply (w : {w : Place K F' // w.restrict F = v}) :
    fiberEquiv F' v w = fiberCenter F' v w.2 := rfl

@[simp]
theorem fiberEquiv_symm_apply (P : HeightOneSpectrum (integralClosureAt F' v)) :
    ((fiberEquiv F' v).symm P : Place K F') = placeOfPrime P := rfl

theorem finite_setOf_restrict_eq : {w : Place K F' | w.restrict F = v}.Finite := by
  classical
  let c : {w : Place K F' | w.restrict F = v} →
      (IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
        (integralClosureAt F' v) : Set (Ideal (integralClosureAt F' v))) :=
    fun w => ⟨(fiberCenter F' v w.2).asIdeal, by
      rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
      exact ⟨(fiberCenter F' v w.2).isPrime, fiberCenter_liesOver w.2⟩⟩
  have hc : Function.Injective c := fun w w' h =>
    Subtype.ext (eq_of_fiberCenter_eq w.2 w'.2 (HeightOneSpectrum.ext (congrArg Subtype.val h)))
  have : Finite {w : Place K F' | w.restrict F = v} := Finite.of_injective c hc
  exact Set.toFinite _

variable (F') in
def fiberOver : Finset (Place K F') :=
  (finite_setOf_restrict_eq (F' := F') v).toFinset

@[simp]
theorem mem_fiberOver {w : Place K F'} : w ∈ v.fiberOver F' ↔ w.restrict F = v := by
  rw [fiberOver, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

theorem restrict_mem_fiberOver (w : Place K F') : w ∈ (w.restrict F).fiberOver F' :=
  (mem_fiberOver _).mpr rfl

theorem restrict_eq_of_mem_fiberOver {w : Place K F'} (hw : w ∈ v.fiberOver F') :
    w.restrict F = v :=
  (mem_fiberOver v).mp hw

theorem subset_fiberOver_of_forall_restrict_eq {S : Finset (Place K F')}
    (hS : ∀ w ∈ S, w.restrict F = v) : S ⊆ v.fiberOver F' :=
  fun w hw => (mem_fiberOver v).mpr (hS w hw)

theorem card_fiberOver_eq :
    (v.fiberOver F').card =
      (IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
        (integralClosureAt F' v)).card := by
  classical
  refine Finset.card_bij (fun w hw => (fiberCenter F' v ((mem_fiberOver v).mp hw)).asIdeal) ?_ ?_ ?_
  · intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v _).isPrime, fiberCenter_liesOver _⟩
  · intro w hw w' hw' h
    exact eq_of_fiberCenter_eq ((mem_fiberOver v).mp hw) ((mem_fiberOver v).mp hw')
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
    exact ⟨placeOfPrime ⟨P, hP1, hPne⟩, (mem_fiberOver v).mpr (restrict_placeOfPrime _),
      congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))⟩

theorem fiber_eq_fiberOver [HasPrincipalDivisors K F'] : v.fiber F' = v.fiberOver F' :=
  Finset.ext fun w => by rw [mem_fiber, mem_fiberOver]

end Fiber

end Place

end AlgebraicCurve

end
