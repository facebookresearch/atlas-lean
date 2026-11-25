/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files of the FLT project
(https://github.com/anthropics/fermats-last-theorem):
`Theorems/Thm_AlgebraicCurve_N.lean` and `P2M/Sol/S_AlgebraicCurve_N.lean`
for each `N` in:
`FunctionField_exists_ratFuncAlgHom_apply_X_eq`;
`FunctionField_finite_of_ratFuncAlgHom`;
`RationalFunctionField_finite_setOf_ord_ne_zero`;
`RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum`;
`RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum`;
`RationalFunctionField_ord_ofHeightOneSpectrum_eq_neg_log`;
`RationalFunctionField_ord_ofHeightOneSpectrum_of_span`;
`RationalFunctionField_toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum`;
`RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum`;
`RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum`;
`RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap`;
`RationalFunctionField_degree_eq_zero_of_forall_eq_ord`;
`RationalFunctionField_hasPrincipalDivisors`;
`RationalFunctionField_deg_eq_one_of_isAlgClosed`.
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

public import MathlibExt.AlgebraicGeometry.Curve.PlaceDivisor
import Mathlib.NumberTheory.RatFunc.Ostrowski
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Places and principal divisors of the rational function field

The places of `RatFunc K` over `K` are the finite places attached to monic irreducible
polynomials together with the place at infinity. We show that a nonzero rational function
has finitely many zeros and poles, that its principal divisor has degree zero
(`AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors`), and that every place has degree
one when `K` is algebraically closed. We also show that a finite extension of `RatFunc K`
generated over `K` by a nonconstant element `g` is finite over the subfield `K(g)`.
-/

@[expose] public section

noncomputable section

section

open Polynomial

theorem AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq {K F : Type*} [Field K]
    [IsAlgClosed K] [Field F] [Algebra K F] {g : F} (hg : g ∉ Set.range (algebraMap K F)) : ∃ φ :
    RatFunc K →ₐ[K] F, φ RatFunc.X = g := by

  have htr : Transcendental K g := by
    intro halg
    apply hg
    have hint : IsIntegral K g := halg.isIntegral
    have hdeg : (minpoly K g).degree = 1 :=
      IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
    obtain ⟨a, ha⟩ := minpoly.degree_eq_one_iff.mp hdeg
    exact ⟨a, ha⟩
  have hinj : Function.Injective (Polynomial.aeval (R := K) g) :=
    transcendental_iff_injective.mp htr
  refine ⟨RatFunc.liftAlgHom (Polynomial.aeval g) ?_, ?_⟩
  · intro p hp
    simp only [Submonoid.mem_comap]
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))
  · rw [RatFunc.liftAlgHom_apply]
    simp

end

section

open Polynomial

set_option synthInstance.maxHeartbeats 800000

namespace G1

private theorem isTranscendenceBasis_polynomial_X (K : Type*) [Field K] :
    IsTranscendenceBasis K ![(X : K[X])] := by
  rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
  refine ⟨algebraicIndependent_iff_transcendental.mpr (transcendental_X K), ?_⟩
  have h : Algebra.adjoin K (Set.range ![(X : K[X])]) = ⊤ := by
    simp [Polynomial.adjoin_X]
  rw [h]
  exact ⟨fun x => isAlgebraic_algebraMap (⟨x, Algebra.mem_top⟩ : (⊤ : Subalgebra K K[X]))⟩

private theorem isTranscendenceBasis_ratFunc_X (K : Type*) [Field K] :
    IsTranscendenceBasis K ![(RatFunc.X : RatFunc K)] := by
  haveI : Algebra.IsAlgebraic K[X] (RatFunc K) :=
    IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors K[X])
  haveI : FaithfulSMul K[X] (RatFunc K) :=
    (faithfulSMul_iff_algebraMap_injective K[X] (RatFunc K)).mpr
      (IsFractionRing.injective K[X] (RatFunc K))
  have h := (isTranscendenceBasis_polynomial_X K).algebraMap_comp (A := RatFunc K)
  convert h using 1
  ext i
  fin_cases i
  simp [RatFunc.algebraMap_X]

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]

private theorem isTranscendenceBasis_t0 :
    IsTranscendenceBasis K ![algebraMap (RatFunc K) F RatFunc.X] := by
  haveI : Algebra.IsAlgebraic (RatFunc K) F := Algebra.IsAlgebraic.of_finite _ _
  have h := (isTranscendenceBasis_ratFunc_X K).algebraMap_comp (A := F)
  convert h using 1
  ext i
  fin_cases i
  simp

private theorem transcendental_apply_X (φ : RatFunc K →ₐ[K] F) :
    Transcendental K (φ RatFunc.X) := by
  rw [transcendental_iff_injective]
  have hX : Function.Injective (aeval (R := K) (RatFunc.X : RatFunc K)) :=
    transcendental_iff_injective.mp RatFunc.transcendental_X
  intro p q hpq
  apply hX
  apply φ.toRingHom.injective
  simpa [aeval_algHom_apply] using hpq

private theorem isTranscendenceBasis_apply_X (φ : RatFunc K →ₐ[K] F) :
    IsTranscendenceBasis K (Subtype.val : ({φ RatFunc.X} : Set F) → F) := by
  classical
  set g := φ RatFunc.X with hg
  set t₀ := algebraMap (RatFunc K) F RatFunc.X with ht₀

  have hbase_t : (AlgebraicIndependent.matroid K F).IsBase ({t₀} : Set F) := by
    rw [AlgebraicIndependent.matroid_isBase_iff]
    have h := (isTranscendenceBasis_t0 (K := K) (F := F)).to_subtype_range
    convert h using 2 <;> simp [ht₀]

  have hind_g : (AlgebraicIndependent.matroid K F).Indep ({g} : Set F) := by
    rw [AlgebraicIndependent.matroid_indep_iff]
    have h := (algebraicIndependent_iff_transcendental.mpr (transcendental_apply_X
      φ)).to_subtype_range
    have hr : Set.range ![g] = {g} := by simp
    rw [hr] at h
    exact h
  obtain ⟨B, hB, hgB⟩ := hind_g.exists_isBase_superset
  have hcard : B.ncard = 1 := by
    rw [hB.ncard_eq_ncard_of_isBase hbase_t, Set.ncard_singleton]
  obtain ⟨b, rfl⟩ := Set.ncard_eq_one.mp hcard
  have hgb : g = b := by simpa using hgB
  rw [← AlgebraicIndependent.matroid_isBase_iff, hgb]
  exact hB

private theorem algebraMap_polynomial_mem {E : Type*} [Field E] [Algebra K E] [Algebra E F]
    [IsScalarTower K E F]
    (T : IntermediateField E F) (ht : algebraMap (RatFunc K) F RatFunc.X ∈ T) (p : K[X]) :
    algebraMap (RatFunc K) F (algebraMap K[X] (RatFunc K) p) ∈ T := by
  have h1 : algebraMap K[X] (RatFunc K) p = aeval (RatFunc.X : RatFunc K) p := by
    rw [← RatFunc.algebraMap_X, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [h1, ← aeval_algebraMap_apply]
  have h2 : Algebra.adjoin K {algebraMap (RatFunc K) F RatFunc.X}
      ≤ (T.restrictScalars K).toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ht)
  exact h2 (aeval_mem_adjoin_singleton K _)

private theorem finite_over_adjoin (φ : RatFunc K →ₐ[K] F) :
    FiniteDimensional (IntermediateField.adjoin K ({φ RatFunc.X} : Set F)) F := by
  classical
  set g := φ RatFunc.X with hg
  set Kg := IntermediateField.adjoin K ({g} : Set F) with hKg
  have halg : Algebra.IsAlgebraic Kg F := by
    have h := (isTranscendenceBasis_apply_X φ).isAlgebraic_field
    have hr : Set.range (Subtype.val : ({g} : Set F) → F) = {g} := Subtype.range_coe
    rw [hr] at h
    exact h
  set t₀ := algebraMap (RatFunc K) F RatFunc.X with ht₀
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := RatFunc K) (M := F)
  let S : Set F := insert t₀ (s : Set F)
  haveI : Finite S := Set.finite_coe_iff.mpr ((s.finite_toSet).insert t₀)
  have hint : ∀ x ∈ S, IsIntegral Kg x := fun x _ => (halg.isAlgebraic x).isIntegral
  have hfin : FiniteDimensional Kg (IntermediateField.adjoin Kg S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have ht₀S : t₀ ∈ IntermediateField.adjoin Kg S :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have htop : IntermediateField.adjoin Kg S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ Submodule.span (RatFunc K) (s : Set F) := by rw [hs]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · intro x hx
      exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hx)
    · exact zero_mem _
    · intro x y _ _ hx hy
      exact add_mem hx hy
    · intro c x _ hx
      rw [Algebra.smul_def]
      refine mul_mem ?_ hx
      rw [← RatFunc.num_div_denom c, map_div₀]
      exact div_mem (algebraMap_polynomial_mem _ ht₀S _) (algebraMap_polynomial_mem _ ht₀S _)
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := Kg) (E := F)).toLinearEquiv

end G1

open G1 in
theorem AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] (φ : RatFunc K →ₐ[K] F) : @Module.Finite (RatFunc K) F _ _
    (φ.toRingHom.toAlgebra).toModule := by
  classical
  set g := φ RatFunc.X with hg
  set Kg := IntermediateField.adjoin K ({g} : Set F) with hKg
  haveI hKF : FiniteDimensional Kg F := finite_over_adjoin φ

  have hrange : ∀ c : RatFunc K, φ c ∈ Kg := by
    intro c
    have hpoly : ∀ p : K[X], φ (algebraMap K[X] (RatFunc K) p) ∈ Kg := by
      intro p
      have h1 : algebraMap K[X] (RatFunc K) p = aeval (RatFunc.X : RatFunc K) p := by
        rw [← RatFunc.algebraMap_X, aeval_algebraMap_apply, aeval_X_left_apply]
      rw [h1, ← aeval_algHom_apply]
      exact IntermediateField.algebra_adjoin_le_adjoin K _ (aeval_mem_adjoin_singleton K _)
    rw [← RatFunc.num_div_denom c, map_div₀]
    exact div_mem (hpoly _) (hpoly _)

  let φ' : RatFunc K →+* Kg := φ.toRingHom.codRestrict Kg.toSubalgebra.toSubring hrange
  have hsurj : Function.Surjective φ' := by
    have hle : Kg ≤ φ.fieldRange := by
      rw [hKg, IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact ⟨RatFunc.X, rfl⟩
    intro y
    obtain ⟨c, hc⟩ := hle y.2
    exact ⟨c, Subtype.ext hc⟩
  letI : Algebra (RatFunc K) Kg := φ'.toAlgebra
  letI algφ : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc K) Kg F := IsScalarTower.of_algebraMap_eq fun c => rfl
  haveI : Module.Finite (RatFunc K) Kg :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) Kg) hsurj
  exact Module.Finite.trans Kg F

end

section

section

open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve

namespace RationalFunctionField

variable (K : Type*) [Field K]

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

private theorem finite_setOf_valuation_ne_one' {f : RatFunc K} (hf : f ≠ 0) :
    {w : HeightOneSpectrum K[X] | w.valuation (RatFunc K) f ≠ 1}.Finite := by
  have hnum : (Ideal.span {f.num} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using RatFunc.num_ne_zero hf
  have hden : (Ideal.span {f.denom} : Ideal K[X]) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using f.denom_ne_zero
  refine Set.Finite.subset ((Ideal.finite_factors hnum).union (Ideal.finite_factors hden))
    fun w hw => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, Ideal.dvd_span_singleton] at hcon
  refine hw ?_
  have h1 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.num) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.1
  have h2 : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) f.denom) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem w).mpr hcon.2
  rw [show f = algebraMap K[X] (RatFunc K) f.num / algebraMap K[X] (RatFunc K) f.denom from
    f.num_div_denom.symm, map_div₀, h1, h2]
  exact div_one 1

theorem subsingleton_setOf_forall_ne_ofHeightOneSpectrum :
    {v : Place K (RatFunc K) |
      ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w}.Subsingleton := by
  classical
  intro v hv v' hv'
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, h⟩ | h
  · exact absurd h (hv w)
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v' with ⟨w, h'⟩ | h'
  · exact absurd h' (hv' w)
  rw [h, h']

theorem finite_setOf_ord_ne_zero {f : RatFunc K} (hf : f ≠ 0) :
    {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.union
      (Set.Finite.image (Place.ofHeightOneSpectrum (K := K))
        (finite_setOf_valuation_ne_one' hf))
      (Set.Subsingleton.finite subsingleton_setOf_forall_ne_ofHeightOneSpectrum))
    fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv
  simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
  by_cases hcase : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w
  · obtain ⟨w, rfl⟩ := hcase
    refine Or.inl ⟨w, fun hone => hv ?_, rfl⟩
    exact ((Place.ofHeightOneSpectrum (K := K) w).ord_eq_zero_iff_adicValuation_eq_one hf).mpr
      ((Place.isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := RatFunc K)
        w).eq_one_iff_eq_one.mp hone)
  · exact Or.inr fun w h => hcase ⟨w, h⟩

end RationalFunctionField

end AlgebraicCurve

end

end

section

open AlgebraicCurve in
theorem AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum {K : Type*}
    [Field K] : ∃ v : Place K (RatFunc K), ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
    v ≠ Place.ofHeightOneSpectrum w := by
  classical
  refine ⟨RationalFunctionField.placeInfty K, fun w h => ?_⟩
  refine RatFunc.adicValuation_not_isEquiv_infty_valuation w
    ((Valuation.isEquiv_iff_valuationSubring _ _).mpr ?_)
  have h2 := congrArg Place.toValuationSubring h
  rw [RationalFunctionField.placeInfty_toValuationSubring,
    Place.ofHeightOneSpectrum_toValuationSubring] at h2
  exact h2.symm

end

section

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log {K : Type*} [Field
  K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0) (hw :
    w.asIdeal = Ideal.span {p}) {f : RatFunc K} (hf : f ≠ 0) : (Place.ofHeightOneSpectrum (K := K)
      (F := RatFunc K) w).ord f = -WithZero.log (w.valuation (RatFunc K) f) := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  exact (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K)
    w).ord_eq_neg_log_of_valuationSubring_eq (w.valuation (RatFunc K)) rfl hval hf

end

section

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_of_span {K : Type*} [Field K]
  (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) {p : Polynomial K} (hp : p ≠ 0) (hw :
    w.asIdeal = Ideal.span {p}) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap (Polynomial K) (RatFunc K) p) = 1 := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  rw [AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log w hp hw
    (RatFunc.algebraMap_ne_zero hp), hval]
  simp [log_exp]

end

section

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
    {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w)
    : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring := by
  haveI := v.adicValuation_isRankOneDiscrete
  haveI := v.adicValuation_isTrivialOn
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)
  · obtain ⟨w, hw, -⟩ := h
    exact absurd (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))) (hv w)

end

section

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
    {K : Type*} [Field K] (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w)
    {f : RatFunc K} (hf : f ≠ 0) : v.ord f = -f.intDegree := by
  classical
  have hπ : RatFunc.inftyValuation K (RatFunc.X)⁻¹ = exp (-1 : ℤ) := by
    rw [map_inv₀, RatFunc.inftyValuation.X]
    exact (exp_neg (1 : ℤ)).symm
  rw [v.ord_eq_neg_log_of_valuationSubring_eq (RatFunc.inftyValuation K)
      (AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
        v hv).symm hπ hf,
    RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hf, log_exp]

end

section

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

section

namespace AlgebraicCurve
namespace RationalFunctionField
open AlgebraicCurve

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

private theorem exists_sub_algebraMap_intDegree_neg {x : RatFunc K}
    (hx : RatFunc.inftyValuation K x ≤ 1) :
    ∃ c : K, x - algebraMap K (RatFunc K) c = 0 ∨
      (x - algebraMap K (RatFunc K) c).intDegree < 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, Or.inl (by simp)⟩
  have hdeg : x.intDegree ≤ 0 := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero K hx0,
      show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_le_exp] at hx
    exact hx
  have hnum0 : x.num ≠ 0 := RatFunc.num_ne_zero hx0
  have hden0 : x.denom ≠ 0 := x.denom_ne_zero
  rcases lt_or_eq_of_le hdeg with hlt | heq
  · exact ⟨0, Or.inr (by simpa using hlt)⟩
  have hndeg : x.num.natDegree = x.denom.natDegree := by
    have h2 := heq
    rw [RatFunc.intDegree, sub_eq_zero] at h2
    exact_mod_cast h2
  set c : K := x.num.leadingCoeff / x.denom.leadingCoeff with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnum0)
      (Polynomial.leadingCoeff_ne_zero.mpr hden0)
  refine ⟨c, ?_⟩
  have hsub : x - algebraMap K (RatFunc K) c
      = algebraMap K[X] (RatFunc K) (x.num - Polynomial.C c * x.denom)
        / algebraMap K[X] (RatFunc K) x.denom := by
    rw [map_sub, map_mul, sub_div, x.num_div_denom, mul_div_assoc,
      div_self ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
      mul_one, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  rcases eq_or_ne (x.num - Polynomial.C c * x.denom) 0 with hzero | hnz
  · exact Or.inl (by rw [hsub, hzero, map_zero, zero_div])
  refine Or.inr ?_
  rw [hsub, RatFunc.intDegree_div ((map_ne_zero_iff _
      (IsFractionRing.injective K[X] (RatFunc K))).mpr hnz)
    ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hden0),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, sub_neg]
  have hCdeg : (Polynomial.C c * x.denom).degree = x.denom.degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_C hc0, zero_add]
  have hdegeq : x.num.degree = (Polynomial.C c * x.denom).degree := by
    rw [hCdeg, Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_eq_natDegree hden0,
      hndeg]
  have hlc : x.num.leadingCoeff = (Polynomial.C c * x.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
      div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hden0)]
  have hlt := Polynomial.degree_sub_lt hdegeq hnum0 hlc
  rw [hdegeq, hCdeg] at hlt
  exact_mod_cast Polynomial.natDegree_lt_natDegree hnz hlt


end AlgebraicCurve.RationalFunctionField

end

theorem AlgebraicCurve.RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum {K : Type*}
    [Field K] (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w)
    : v.deg = 1 := by
  classical
  have hvS : v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring :=
    AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum v hv
  have hequiv : (RatFunc.inftyValuation K).IsEquiv v.adicValuation :=
    v.isEquiv_adicValuation_of_valuationSubring_eq hvS.symm
  have hbij : Function.Bijective (Algebra.ofId K v.ResidueField) := by
    constructor
    · exact fun a b h => (algebraMap K v.ResidueField).injective h
    · intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
      have hx' : RatFunc.inftyValuation K x ≤ 1 := by
        rw [hvS] at hx
        exact (Valuation.mem_valuationSubring_iff _ _).mp hx
      obtain ⟨c, hc⟩ :=
        AlgebraicCurve.RationalFunctionField.exists_sub_algebraMap_intDegree_neg K hx'
      refine ⟨c, ?_⟩
      show IsLocalRing.residue _ (algebraMap K v.toValuationSubring c) = _
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
        Place.mem_maximalIdeal_iff_adicValuation_lt_one]
      show v.adicValuation (algebraMap K (RatFunc K) c - x) < 1
      rw [← hequiv.lt_one_iff_lt_one,
        show algebraMap K (RatFunc K) c - x = -(x - algebraMap K (RatFunc K) c) from
          (neg_sub _ _).symm, Valuation.map_neg]
      rcases hc with hc | hc
      · rw [hc, map_zero]
        exact zero_lt_one
      · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuationDef]
        split
        · exact zero_lt_one
        · rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
          exact hc
  rw [Place.deg, ← (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

end

section

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

section

namespace AlgebraicCurve
namespace RationalFunctionField
open AlgebraicCurve

variable (K : Type*) [Field K]

variable {K}

private theorem single_add_single_apply_eq_ord {vinf : Place K (RatFunc K)}
    (hvinf : ∀ w : HeightOneSpectrum K[X], vinf ≠ Place.ofHeightOneSpectrum w)
    {p : K[X]} (hp : Irreducible p) (v : Place K (RatFunc K)) :
    (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ))) v
      = v.ord (algebraMap K[X] (RatFunc K) p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [Finsupp.add_apply]
  by_cases hfin : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w
  · obtain ⟨w, rfl⟩ := hfin

    rw [Finsupp.single_eq_of_ne (hvinf w).symm, add_zero]
    by_cases hcase :
        Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = finitePlace K hp
    · rw [hcase, Finsupp.single_eq_same]
      exact (ord_ofHeightOneSpectrum_of_span (heightOneSpectrumOfIrreducible K hp) hp0
        (heightOneSpectrumOfIrreducible_asIdeal K hp)).symm
    · rw [Finsupp.single_eq_of_ne hcase]
      symm
      by_contra hne
      refine hcase ?_
      have hmem : p ∈ w.asIdeal :=
        (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hp0).mp hne
      have hspan : Ideal.span {p} = w.asIdeal :=
        (PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le w.isPrime.ne_top
          ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      have hwp : w = heightOneSpectrumOfIrreducible K hp :=
        HeightOneSpectrum.ext
          (hspan.symm.trans (heightOneSpectrumOfIrreducible_asIdeal K hp).symm)
      rw [hwp]
      rfl
  ·
    have hv : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w :=
      fun w h => hfin ⟨w, h⟩
    have hveq : v = vinf := subsingleton_setOf_forall_ne_ofHeightOneSpectrum hv hvinf
    rw [Finsupp.single_eq_of_ne (show v ≠ finitePlace K hp from hv _), zero_add, hveq,
      Finsupp.single_eq_same,
      ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum vinf hvinf (RatFunc.algebraMap_ne_zero
        hp0),
      RatFunc.intDegree_polynomial]

private theorem degree_single_add_single {vinf : Place K (RatFunc K)}
    (hvinf : ∀ w : HeightOneSpectrum K[X], vinf ≠ Place.ofHeightOneSpectrum w)
    {p : K[X]} (hp : Irreducible p) :
    Divisor.degree (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ))) = 0 := by
  rw [map_add, Divisor.degree_single, Divisor.degree_single,
    show (finitePlace K hp).deg = p.natDegree from
      deg_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible_asIdeal K hp),
    deg_eq_one_of_forall_ne_ofHeightOneSpectrum vinf hvinf]
  push_cast
  ring


end AlgebraicCurve.RationalFunctionField

end

theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap {K : Type*}
    [Field K] (q : Polynomial K) : ∀ D : Divisor K (RatFunc K),
    (∀ v : Place K (RatFunc K), D v = v.ord (algebraMap (Polynomial K) (RatFunc K) q)) →
    Divisor.degree D = 0 := by
  classical
  obtain ⟨vinf, hvinf⟩ := AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum
    (K := K)
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro D hD
    have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  · intro x hx D hD
    obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hx
    have hC : (algebraMap K[X] (RatFunc K)) (Polynomial.C r) = algebraMap K (RatFunc K) r := by
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    have hzero : D = 0 := by
      ext v
      rw [hD v, hC, v.ord_algebraMap]
      simp
    rw [hzero, map_zero]
  · intro a p ha hp ih D hD
    have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
    have ha' : algebraMap K[X] (RatFunc K) a ≠ 0 := RatFunc.algebraMap_ne_zero ha
    set Dp : Divisor K (RatFunc K) :=
      Finsupp.single (AlgebraicCurve.RationalFunctionField.finitePlace K hp.irreducible) (1
        : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ)) with hDp_def
    have hDp : ∀ v : Place K (RatFunc K), Dp v = v.ord (algebraMap K[X] (RatFunc K) p) :=
      fun v => AlgebraicCurve.RationalFunctionField.single_add_single_apply_eq_ord hvinf
        hp.irreducible v
    have hDa : ∀ v : Place K (RatFunc K),
        (D - Dp) v = v.ord (algebraMap K[X] (RatFunc K) a) := by
      intro v
      rw [Finsupp.sub_apply, hD v, hDp v, map_mul, v.ord_mul hp' ha']
      ring
    have hdeg_p : Divisor.degree Dp = 0 :=
      AlgebraicCurve.RationalFunctionField.degree_single_add_single hvinf hp.irreducible
    have hdeg_a : Divisor.degree (D - Dp) = 0 := ih (D - Dp) hDa
    have hsplit : D = Dp + (D - Dp) := by abel
    rw [hsplit, map_add, hdeg_p, zero_add]
    exact hdeg_a

end

section

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord {K : Type*} [Field K]
    {f : RatFunc K} (D : Divisor K (RatFunc K)) (hD : ∀ v : Place K (RatFunc K), D v = v.ord f) :
    Divisor.degree D = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  · have hden : f.denom ≠ 0 := f.denom_ne_zero
    have hdenF : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := RatFunc.algebraMap_ne_zero hden

    set Dden : Divisor K (RatFunc K) :=
      Finsupp.ofSupportFinite
        (fun v : Place K (RatFunc K) => v.ord (algebraMap K[X] (RatFunc K) f.denom))
        (AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero hdenF) with hDden_def
    have hDden : ∀ v : Place K (RatFunc K),
        Dden v = v.ord (algebraMap K[X] (RatFunc K) f.denom) := fun v => rfl
    have hsplit : ∀ v : Place K (RatFunc K),
        (D + Dden) v = v.ord (algebraMap K[X] (RatFunc K) f.num) := by
      intro v
      rw [Finsupp.add_apply, hD v, hDden v]
      have hmul : f * algebraMap K[X] (RatFunc K) f.denom
          = algebraMap K[X] (RatFunc K) f.num :=
        ((div_eq_iff hdenF).mp f.num_div_denom).symm
      have h2 := v.ord_mul hf hdenF
      rw [hmul] at h2
      exact h2.symm
    have h1 := AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap
      f.num (D + Dden) hsplit
    have h2 := AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap
      f.denom Dden hDden
    rw [map_add, h2, add_zero] at h1
    exact h1

end

section

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnAdicValuation
attribute [-simp] AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
open AlgebraicCurve
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

theorem AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors (K : Type*) [Field K] :
    HasPrincipalDivisors K (RatFunc K) :=
  ⟨fun f hf =>
    ⟨Finsupp.ofSupportFinite (fun v : Place K (RatFunc K) => v.ord f)
        (AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero hf),
      fun _ => rfl,
      AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord _ fun _ => rfl⟩⟩

end

section

section

open Polynomial IsDedekindDomain WithZero IsLocalRing

open scoped Polynomial

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end Place

namespace RationalFunctionField

variable (K : Type*) [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

theorem inftyValuation_isEquiv_adicValuation :
    (RatFunc.inftyValuation K).IsEquiv (placeInfty K).adicValuation :=
  (placeInfty K).isEquiv_adicValuation_of_valuationSubring_eq rfl

end PlaceInfty

variable {K}

section DegInfty

variable (K) [DecidableEq (RatFunc K)]

theorem deg_placeInfty : (placeInfty K).deg = 1 := by
  have hbij : Function.Bijective (Algebra.ofId K (placeInfty K).ResidueField) := by
    constructor
    · exact fun a b h => (algebraMap K ((placeInfty K).ResidueField)).injective h
    · intro y
      obtain ⟨⟨x, hx⟩, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨c, hc⟩ := exists_sub_algebraMap_intDegree_neg K
        ((Valuation.mem_valuationSubring_iff _ _).mp hx)
      refine ⟨c, ?_⟩
      show IsLocalRing.residue _ (algebraMap K (placeInfty K).toValuationSubring c) = _
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
        Place.mem_maximalIdeal_iff_adicValuation_lt_one]
      show (placeInfty K).adicValuation (algebraMap K (RatFunc K) c - x) < 1
      rw [← (inftyValuation_isEquiv_adicValuation K).lt_one_iff_lt_one,
        show algebraMap K (RatFunc K) c - x = -(x - algebraMap K (RatFunc K) c) from
          (neg_sub _ _).symm, Valuation.map_neg]
      rcases hc with hc | hc
      · rw [hc, map_zero]
        exact zero_lt_one
      · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuationDef]
        split
        · exact zero_lt_one
        · rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp]
          exact hc
  rw [Place.deg, ← (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

end DegInfty

end RationalFunctionField

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

end Place

namespace RationalFunctionField

variable {K : Type*} [Field K]

section PlaceInftyOrd

variable [DecidableEq (RatFunc K)]

end PlaceInftyOrd

section IrreducibleDivisor

variable [DecidableEq (RatFunc K)]

end IrreducibleDivisor

end RationalFunctionField

namespace RationalFunctionField
open AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

variable {K}

variable (K)

theorem exists_eq_placeOfPoint [IsAlgClosed K] (w : HeightOneSpectrum K[X]) :
    ∃ a : K, Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = placeOfPoint K a := by
  obtain ⟨p, hp, hwp⟩ := exists_irreducible_span K w

  have hdeg : p.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K hp]
    exact one_ne_zero
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

theorem deg_eq_one_of_isAlgClosed [IsAlgClosed K] (v : Place K (RatFunc K)) : v.deg = 1 := by
  classical
  rcases eq_placeOfPoint_or_eq_placeInfty K v with ⟨a, rfl⟩ | rfl
  · exact deg_placeOfPoint K a
  · exact deg_placeInfty K

end RationalFunctionField

namespace RationalFunctionField
open AlgebraicCurve.RationalFunctionField

variable {K : Type*} [Field K]

section PlaceInfty

variable [DecidableEq (RatFunc K)]

end PlaceInfty

section CrossRatio

variable [DecidableEq (RatFunc K)]

end CrossRatio

section Reciprocity

variable [IsAlgClosed K] [DecidableEq (RatFunc K)]

end Reciprocity

end RationalFunctionField

end AlgebraicCurve

end

end

end
