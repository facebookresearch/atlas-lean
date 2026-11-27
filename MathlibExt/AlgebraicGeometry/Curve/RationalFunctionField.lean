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

public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceClassification
import MathlibExt.AlgebraicGeometry.Curve.OrdEqNegLog
import MathlibExt.AlgebraicGeometry.Curve.RatFuncNonFinitePlaceOrd
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyDeg
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPrincipalDivisors

/-!
# Principal divisors of the rational function field

The places of `RatFunc K` over `K` are the finite places attached to irreducible polynomials
(`Curve/RatFuncPlaces`) and the place at infinity (`Curve/RatFuncPlaceInfty`). We show that the
divisor of a nonzero rational function has degree zero
(`AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord`;
`Curve/RatFuncPrincipalDivisors` states this as `HasPrincipalDivisors K (RatFunc K)`), and that
every place has degree one when `K` is algebraically closed. We also show that a field `F` finite
over `RatFunc K` is finite over the image of any `K`-algebra map `RatFunc K → F`, and that over
an algebraically closed `K` every nonconstant element of `F` is the image of `X` under such a map.
-/

@[expose] public section

noncomputable section

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

section FiniteOverImage

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
  have : Algebra.IsAlgebraic K[X] (RatFunc K) :=
    IsLocalization.isAlgebraic (RatFunc K) (nonZeroDivisors K[X])
  have : FaithfulSMul K[X] (RatFunc K) :=
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
  have : Algebra.IsAlgebraic (RatFunc K) F := Algebra.IsAlgebraic.of_finite _ _
  have h := (isTranscendenceBasis_ratFunc_X K).algebraMap_comp (A := F)
  convert h using 1
  ext i
  fin_cases i
  simp

omit [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] in
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

omit [FiniteDimensional (RatFunc K) F] in
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
  have : Finite S := Set.finite_coe_iff.mpr ((s.finite_toSet).insert t₀)
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

end FiniteOverImage

theorem AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom {K F : Type*} [Field K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] (φ : RatFunc K →ₐ[K] F) : @Module.Finite (RatFunc K) F _ _
    (φ.toRingHom.toAlgebra).toModule := by
  classical
  set g := φ RatFunc.X with hg
  set Kg := IntermediateField.adjoin K ({g} : Set F) with hKg
  have hKF : FiniteDimensional Kg F := finite_over_adjoin φ
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
  let : Algebra (RatFunc K) Kg := φ'.toAlgebra
  let algφ : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  have : IsScalarTower (RatFunc K) Kg F := IsScalarTower.of_algebraMap_eq fun c => rfl
  have : Module.Finite (RatFunc K) Kg :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) Kg) hsurj
  exact Module.Finite.trans Kg F

namespace AlgebraicCurve

namespace RationalFunctionField

open IsDedekindDomain WithZero IsLocalRing

variable {K : Type*} [Field K]

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

end RationalFunctionField

end AlgebraicCurve

open AlgebraicCurve IsDedekindDomain WithZero IsLocalRing

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

theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord {K : Type*} [Field K]
    {f : RatFunc K} (D : Divisor K (RatFunc K)) (hD : ∀ v : Place K (RatFunc K), D v = v.ord f) :
    Divisor.degree D = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  · obtain ⟨E, hE, hdeg⟩ :=
      (AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors K).exists_divisor f hf
    rw [show D = E from Finsupp.ext fun v => (hD v).trans (hE v).symm, hdeg]

theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap {K : Type*}
    [Field K] (q : Polynomial K) : ∀ D : Divisor K (RatFunc K),
    (∀ v : Place K (RatFunc K), D v = v.ord (algebraMap (Polynomial K) (RatFunc K) q)) →
    Divisor.degree D = 0 :=
  fun D hD => AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord D hD

namespace AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

theorem deg_eq_one_of_isAlgClosed [IsAlgClosed K] (v : Place K (RatFunc K)) : v.deg = 1 := by
  classical
  rcases eq_placeOfPoint_or_eq_placeInfty K v with ⟨a, rfl⟩ | rfl
  · exact deg_placeOfPoint K a
  · exact deg_placeInfty K

end AlgebraicCurve.RationalFunctionField
