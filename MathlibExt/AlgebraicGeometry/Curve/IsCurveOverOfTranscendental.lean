/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicCurve_Divisor_degree_eq_sum.lean`,
`P2M/Sol/S_AlgebraicCurve_Divisor_degree_eq_sum.lean`,
`Theorems/Thm_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional.lean`,
`P2M/Sol/S_AlgebraicCurve_Place_finite_residueField_of_finiteDimensional.lean`,
`Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.lean`,
`P2M/Sol/S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.lean`,
`Theorems/Thm_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional.lean`,
`P2M/Sol/S_AlgebraicCurve_finite_setOf_ord_ne_zero_of_finiteDimensional.lean`,
`P2M/Sol/S_AlgebraicCurve_kaehlerRankOne_of_transcendental.lean`,
`Theorems/Thm_AlgebraicCurve_instIsCurveOverRatFunc.lean`,
`Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental.lean`,
`P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental.lean`,
`Theorems/Thm_AlgebraicCurve_exists_separating_transcendental_of_perfectField.lean`,
`P2M/Sol/S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean`,
`Theorems/Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean`
and
`P2M/Sol/S_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField.lean`
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

public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.RatFunc.Basic
public import MathlibExt.AlgebraicGeometry.Curve.DivisorPushPull
public import MathlibExt.AlgebraicGeometry.Curve.IsCurveOver
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Norm.Transitivity
import MathlibExt.AlgebraicGeometry.Curve.FundamentalIdentityFiber
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaces
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPrincipalDivisors

/-!
# Curve function fields from a transcendental element

Let `F / K` be a field extension and `x : F` transcendental over `K` with `F` finite over `K(x)`.
If `F / K(x)` is separable, or if `K` is perfect, then `F` is the function field of a curve over
`K` in the sense of `AlgebraicCurve.IsCurveOver`: every nonzero function has a principal divisor
of degree zero, every residue field has finite degree over `K`, and the Kähler differentials of
`F / K` are free of rank one.

## Main statements

* `AlgebraicCurve.Place.finite_residueField_restrict`
* `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`
* `AlgebraicCurve.instIsCurveOverRatFunc`
* `AlgebraicCurve.exists_ratFunc_algebra_of_transcendental`
* `AlgebraicCurve.isCurveOver_of_transcendental`
* `AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField`
-/

@[expose] public section

noncomputable section

open IntermediateField Polynomial Module IsLocalRing

namespace AlgebraicCurve

private theorem degree_eq_sum {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor K F) : Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
  Finsupp.liftAddHom_apply (fun v : Place K F => AddMonoidHom.mulRight (v.deg : ℤ)) D

private theorem Place.ord_finsetProd {K F : Type*} [Field K] [Field F] [Algebra K F]
    {ι : Type*} (v : Place K F) (s : Finset ι) (g : ι → F) (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      v.ord_mul (hg i (Finset.mem_cons_self i s))
        (Finset.prod_ne_zero_iff.mpr fun j hj => hg j (Finset.mem_cons_of_mem hj)),
      ih fun j hj => hg j (Finset.mem_cons_of_mem hj)]

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']

private theorem linearIndependent_lift (w : Place K F') {ι : Type*} [Finite ι]
    (x : ι → w.toValuationSubring)
    (hx : LinearIndependent (w.restrict F).ResidueField
      fun i => (residue w.toValuationSubring (x i) : w.ResidueField)) :
    LinearIndependent F fun i => ((x i : w.toValuationSubring) : F') := by
  classical
  cases nonempty_fintype ι
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  obtain ⟨i₀, hi₀⟩ : ∃ i, g i ≠ 0 := not_forall.mp hne
  set O : ValuationSubring F := (w.restrict F).toValuationSubring
  have hne' : (Finset.univ.filter fun i => g i ≠ 0).Nonempty := ⟨i₀, by simpa using hi₀⟩
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image _ (fun i => O.valuation (g i)) hne'
  have hgk : g k ≠ 0 := by simpa using hk
  have hb : ∀ i, g i / g k ∈ O := by
    intro i
    by_cases hi : g i = 0
    · simp [hi]
    · apply O.mem_of_valuation_le_one
      rw [map_div₀]
      have hk0 : (0 : O.ValueGroup) < O.valuation (g k) := by
        rw [zero_lt_iff]
        exact (_root_.map_ne_zero _).mpr hgk
      exact (div_le_one₀ hk0).mpr (hkmax i (by simpa using hi))
  let b : ι → O := fun i => ⟨g i / g k, hb i⟩
  have hrel : ∑ i, Place.restrictInclusion F w (b i) * x i = 0 := by
    apply Subtype.ext
    have hcoe : ((∑ i, Place.restrictInclusion F w (b i) * x i : w.toValuationSubring) : F') =
        ∑ i, algebraMap F F' (g i / g k) * (x i : F') := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MulMemClass.coe_mul, Place.coe_restrictInclusion]
    rw [hcoe]
    have : ∑ i, algebraMap F F' (g i / g k) * (x i : F') =
        algebraMap F F' (g k)⁻¹ * ∑ i, g i • ((x i : w.toValuationSubring) : F') := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, div_eq_inv_mul, map_mul, mul_assoc]
    rw [this, hg, mul_zero]
    rfl
  have hres : ∑ i, (residue O (b i) : (w.restrict F).ResidueField) •
      (residue w.toValuationSubring (x i) : w.ResidueField) = 0 := by
    have h := congrArg (residue w.toValuationSubring) hrel
    rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Place.algebraMap_residueField_eq, Place.restrictResidueMap_residue,
      map_mul]
  have hk1 := (Fintype.linearIndependent_iff.mp hx) _ hres k
  have hbk : b k = 1 := Subtype.ext (div_self hgk)
  rw [hbk, map_one] at hk1
  exact one_ne_zero hk1

/-- **Residue fields in a finite extension.** In a finite extension `F' / F`, the residue field of
a place of `F'` has finite degree over the residue field of its restriction to `F`. -/
theorem Place.finite_residueField_restrict (w : Place K F') :
    Module.Finite (w.restrict F).ResidueField w.ResidueField := by
  classical
  rw [← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt (rank_le (n := Module.finrank F F') fun s hs => ?_)
    Cardinal.natCast_lt_aleph0
  choose x hx using fun y : s => residue_surjective (R := w.toValuationSubring) (y : w.ResidueField)
  have hs' : LinearIndependent (w.restrict F).ResidueField
      fun i : s => (residue w.toValuationSubring (x i) : w.ResidueField) := by
    simpa only [hx] using hs
  have := linearIndependent_lift (F := F) w x hs'
  simpa [Fintype.card_coe] using this.fintype_card_le_finrank

end Restrict

section Separable

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

private theorem degree_eq_finrank_mul {g : F}
    {D' : Divisor K F'} (hD' : ∀ w : Place K F', D' w = w.ord (algebraMap F F' g))
    {D : Divisor K F} (hD : ∀ v : Place K F, D v = v.ord g) :
    Divisor.degree D' = (Module.finrank F F' : ℤ) * Divisor.degree D := by
  classical
  have hmaps : ∀ w ∈ D'.support, w.restrict F ∈ D.support := by
    intro w hw
    rw [Finsupp.mem_support_iff] at hw ⊢
    intro h0
    apply hw
    rw [hD' w, w.ord_restrict g, ← hD (w.restrict F), h0, mul_zero]
  have happ : ∀ w : Place K F', D' w = (w.ramificationIndex F : ℤ) * D (w.restrict F) := by
    intro w
    rw [hD' w, w.ord_restrict g, hD]
  rw [degree_eq_sum, degree_eq_sum,
    ← Finset.sum_fiberwise_of_maps_to hmaps fun w => D' w * (w.deg : ℤ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hfiber : D'.support.filter (fun w => w.restrict F = v) = v.fiberOver F' := by
    ext w
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, Place.mem_fiberOver,
      and_iff_right_iff_imp]
    intro hw
    rw [happ w, hw]
    have he : 0 < w.ramificationIndex F := w.ramificationIndex_pos (F := F)
    have hv0 : D v ≠ 0 := Finsupp.mem_support_iff.mp hv
    exact mul_ne_zero (by exact_mod_cast he.ne') hv0
  calc
    ∑ w ∈ D'.support with w.restrict F = v, D' w * (w.deg : ℤ)
        = D v * ∑ w ∈ v.fiberOver F',
            (w.ramificationIndex F : ℤ) * (w.deg : ℤ) := by
          rw [hfiber, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [happ w, (Place.mem_fiberOver v).mp hw]
          ring
    _ = D v * ((Module.finrank F F' : ℤ) * (v.deg : ℤ)) := by
          congr 1
          rw [← Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver (K := K) (F' := F') v,
            Finset.sum_mul]
          refine Finset.sum_congr rfl fun w hw => ?_
          have hdeg := w.deg_restrict_mul_inertiaDeg (F := F)
          rw [(Place.mem_fiberOver v).mp hw] at hdeg
          have hdegZ : (w.deg : ℤ) = (v.deg : ℤ) * (w.inertiaDeg F : ℤ) := by
            exact_mod_cast hdeg.symm
          rw [hdegZ]
          ring
    _ = (Module.finrank F F' : ℤ) * (D v * (v.deg : ℤ)) := by ring

omit [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
private theorem mapDomain_congrEquiv_apply (σ : F' ≃ₐ[K] F') {f : F'} {D : Divisor K F'}
    (hD : ∀ w : Place K F', D w = w.ord f) (w : Place K F') :
    Finsupp.mapDomain (Place.congrEquiv σ.toRingEquiv fun a => σ.commutes a) D w
      = w.ord (σ f) := by
  rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply, hD]
  obtain ⟨u, rfl⟩ := (Place.congrEquiv σ.toRingEquiv fun a => σ.commutes a).surjective w
  rw [Equiv.symm_apply_apply]
  exact (Place.ord_congrRingEquiv σ.toRingEquiv (fun a => σ.commutes a) u f).symm

omit [FiniteDimensional F F'] [Algebra.IsSeparable F F'] in
private theorem degree_mapDomain_congrEquiv (σ : F' ≃ₐ[K] F') (D : Divisor K F') :
    Divisor.degree (Finsupp.mapDomain (Place.congrEquiv σ.toRingEquiv fun a => σ.commutes a) D)
      = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_add, map_add, ih,
      Divisor.degree_single, Divisor.degree_single, Place.congrEquiv_apply,
      Place.deg_congrRingEquiv]

private theorem degree_eq_zero_of_isGalois [IsGalois F F'] [HasPrincipalDivisors K F]
    {f : F'} {D : Divisor K F'} (hD : ∀ w : Place K F', D w = w.ord f) :
    Divisor.degree D = 0 := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · have : D = 0 := Finsupp.ext fun w => by simpa using hD w
    rw [this, map_zero]
  set E : Divisor K F' := ∑ σ : F' ≃ₐ[F] F', Finsupp.mapDomain
    (Place.congrEquiv (σ.restrictScalars K).toRingEquiv fun a => (σ.restrictScalars K).commutes a)
    D with hE
  have hEord : ∀ w : Place K F', E w = w.ord (algebraMap F F' (Algebra.norm F f)) := by
    intro w
    rw [Algebra.norm_eq_prod_automorphisms F f,
      Place.ord_finsetProd w _ _ (fun σ _ => by simpa using hf), hE, Finset.sum_apply']
    exact Finset.sum_congr rfl fun σ _ => mapDomain_congrEquiv_apply (σ.restrictScalars K) hD w
  have hnorm : Algebra.norm F f ≠ 0 := (Algebra.norm_ne_zero_iff (R := F)).mpr hf
  obtain ⟨D₀, hD₀, hD₀deg⟩ := HasPrincipalDivisors.exists_divisor (K := K)
    (Algebra.norm F f) hnorm
  have hEdeg : Divisor.degree E = 0 := by
    rw [degree_eq_finrank_mul hEord hD₀, hD₀deg, mul_zero]
  have hEdeg' : Divisor.degree E = (Module.finrank F F' : ℤ) * Divisor.degree D := by
    rw [hE, map_sum]
    simp only [degree_mapDomain_congrEquiv]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    exact_mod_cast (Nat.card_eq_fintype_card (α := F' ≃ₐ[F] F')).symm.trans
      (IsGalois.card_aut_eq_finrank F F')
  have hpos : (0 : ℤ) < (Module.finrank F F' : ℤ) := by
    exact_mod_cast Module.finrank_pos (R := F) (M := F')
  rw [hEdeg] at hEdeg'
  exact (mul_eq_zero.mp hEdeg'.symm).resolve_left hpos.ne'

private theorem degree_eq_zero_of_tower
    (htop : ∀ (h : F') (E : Divisor K F'), (∀ w : Place K F', E w = w.ord h) →
      Divisor.degree E = 0)
    (hex : ∀ h : F', h ≠ 0 → ∃ E : Divisor K F', ∀ w : Place K F', E w = w.ord h)
    {f : F} {D : Divisor K F} (hD : ∀ v : Place K F, D v = v.ord f) :
    Divisor.degree D = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · have : D = 0 := Finsupp.ext fun w => by simpa using hD w
    rw [this, map_zero]
  obtain ⟨E, hE⟩ := hex (algebraMap F F' f) (by simpa using hf)
  have hcomp : Divisor.degree E = (Module.finrank F F' : ℤ) * Divisor.degree D :=
    degree_eq_finrank_mul hE hD
  rw [htop _ E hE] at hcomp
  have hpos : (0 : ℤ) < (Module.finrank F F' : ℤ) := by
    exact_mod_cast Module.finrank_pos (R := F) (M := F')
  exact (mul_eq_zero.mp hcomp.symm).resolve_left hpos.ne'

end Separable

section Support

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F'] [Algebra F F']
  [FiniteDimensional F F']

omit [FiniteDimensional F F'] in
private theorem Place.aeval_mem (w : Place K F') {Q : Polynomial F} {x : F'}
    (hcoeff : ∀ i, algebraMap F F' (Q.coeff i) ∈ w.toValuationSubring)
    (hx : x ∈ w.toValuationSubring) :
    Polynomial.aeval x Q ∈ w.toValuationSubring := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hcoeff i) (pow_mem hx i)

/-- If `f` has nonzero order at `w`, then so does some lower coefficient of its minimal
polynomial. -/
private theorem Place.exists_coeff_ord_ne_zero (w : Place K F') {f : F'} (hf : f ≠ 0)
    (hford : w.ord f ≠ 0) :
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
        = (0 : F') := by
      rw [P.X_mul_divX_add]
      exact minpoly.aeval F f
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

end Support

section RatFuncTower

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra (RatFunc K) E]
  [IsScalarTower K (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
  [Algebra.IsSeparable (RatFunc K) E]

private theorem finite_setOf_ord_ne_zero_of_finiteDimensional {f : E} (hf : f ≠ 0) :
    {w : Place K E | w.ord f ≠ 0}.Finite := by
  classical
  set P := minpoly (RatFunc K) f with hPdef
  refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio P.natDegree) (fun i _ =>
    Set.Finite.biUnion (s := {v : Place K (RatFunc K) | v.ord (P.coeff i) ≠ 0})
      ?_ (fun v _ => Place.finite_setOf_restrict_eq v))) ?_
  · rcases eq_or_ne (P.coeff i) 0 with h0 | h0
    · simp [h0]
    · exact RationalFunctionField.finite_setOf_ord_ne_zero h0
  · intro w hw
    obtain ⟨i, hi, hci, hord⟩ := w.exists_coeff_ord_ne_zero (F := RatFunc K) hf hw
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨i, hi, w.restrict (RatFunc K), ?_, rfl⟩
    intro h0
    apply hord
    rw [w.ord_restrict, h0, mul_zero]

private def principalDivisorOf {f : E} (hf : f ≠ 0) : Divisor K E :=
  Finsupp.ofSupportFinite (fun w : Place K E => w.ord f)
    (finite_setOf_ord_ne_zero_of_finiteDimensional hf)

variable (K E) in
/-- **Principal divisors in finite separable extensions of the rational function field.** A
finite separable extension of `RatFunc K` has principal divisors of degree zero. -/
theorem hasPrincipalDivisors_of_finiteDimensional_of_isSeparable :
    HasPrincipalDivisors K E := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (RatFunc K) E
  have hint : IsIntegral (RatFunc K) α := Algebra.IsIntegral.isIntegral α
  have hsep : (minpoly (RatFunc K) α).Separable := Algebra.IsSeparable.isSeparable _ α
  set L := (minpoly (RatFunc K) α).SplittingField
  obtain ⟨g⟩ : Nonempty (E →ₐ[RatFunc K] L) := by
    refine IntermediateField.nonempty_algHom_of_adjoin_splits (fun s hs => ?_) hα
    obtain rfl : s = α := by simpa using hs
    exact ⟨hint, Polynomial.SplittingField.splits _⟩
  let : Algebra E L := g.toRingHom.toAlgebra
  have : IsScalarTower (RatFunc K) E L :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : IsScalarTower K E L :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap K L x = g (algebraMap K E x)
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) E x, g.commutes,
        ← IsScalarTower.algebraMap_apply K (RatFunc K) L x]
  have : IsGalois (RatFunc K) L := IsGalois.of_separable_splitting_field hsep
  have : FiniteDimensional E L := FiniteDimensional.right (RatFunc K) E L
  have : Algebra.IsSeparable E L := Algebra.isSeparable_tower_top_of_isSeparable (RatFunc K) E L
  have : HasPrincipalDivisors K (RatFunc K) := RationalFunctionField.hasPrincipalDivisors K
  refine ⟨fun f hf => ⟨principalDivisorOf hf, fun _ => rfl, ?_⟩⟩
  exact degree_eq_zero_of_tower (K := K) (F := E) (F' := L)
    (fun _ _ hE' => degree_eq_zero_of_isGalois (K := K) (F := RatFunc K) (F' := L) hE')
    (fun _ hh => ⟨principalDivisorOf hh, fun _ => rfl⟩) (fun _ => rfl)

variable (K) in
private def kaehlerRatFuncBasis : Basis Unit (RatFunc K) Ω[RatFunc K⁄K] :=
  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])
  ((((Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm).baseChange
    (RatFunc K))).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

omit [FiniteDimensional (RatFunc K) E] in
private theorem kaehler_free_finrank_eq_one :
    Module.Free E Ω[E⁄K] ∧ Module.finrank E Ω[E⁄K] = 1 := by
  have : Algebra.FormallyEtale (RatFunc K) E := Algebra.FormallyEtale.of_isSeparable _ _
  let b : Basis Unit E Ω[E⁄K] := ((kaehlerRatFuncBasis K).baseChange E).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (RatFunc K) E)
  exact ⟨Module.Free.of_basis b, (Module.finrank_eq_card_basis b).trans (by simp)⟩

private theorem isCurveOver_of_ratFunc : IsCurveOver K E where
  finiteResidue v := by
    have := RationalFunctionField.finite_residueField (v.restrict (RatFunc K))
    have := Place.finite_residueField_restrict (F := RatFunc K) v
    exact Module.Finite.trans (v.restrict (RatFunc K)).ResidueField v.ResidueField
  exists_divisor := (hasPrincipalDivisors_of_finiteDimensional_of_isSeparable K E).exists_divisor
  kaehler_free_rank_one := kaehler_free_finrank_eq_one

end RatFuncTower

/-- **The rational function field is the function field of a curve.** For every field `K`,
`RatFunc K` is the function field of a curve over `K`. -/
instance instIsCurveOverRatFunc {K : Type*} [Field K] : IsCurveOver K (RatFunc K) := by
  exact isCurveOver_of_ratFunc

/-- **Function fields as finite separable extensions of the rational function field.** If
`x : F` is transcendental over `K` and `F` is finite and separable over `K(x)`, then `F` has a
`RatFunc K`-algebra structure, compatible with `K`, that sends `X` to `x`, over which `F` is
finite and separable, of the same degree as over `K(x)`. -/
theorem exists_ratFunc_algebra_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x) (hfd : FiniteDimensional K⟮x⟯ F)
    (hsep : Algebra.IsSeparable K⟮x⟯ F) :
    ∃ _ : Algebra (RatFunc K) F, IsScalarTower K (RatFunc K) F ∧
      FiniteDimensional (RatFunc K) F ∧ Algebra.IsSeparable (RatFunc K) F ∧
      algebraMap (RatFunc K) F RatFunc.X = x ∧
      Module.finrank K⟮x⟯ F = Module.finrank (RatFunc K) F := by
  let e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr
  let : Algebra (RatFunc K) F := ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
    refine RingHom.ext fun a => ?_
    change algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
    rw [e.apply_symm_apply]
  refine ⟨this, ?_, Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq,
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq,
    RatFunc.algEquivOfTranscendental_X x htr,
    Algebra.finrank_eq_of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq⟩
  exact IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]

/-- **Curve function fields from a separating transcendental element.** If `x : F` is
transcendental over `K` and `F` is a finite separable extension of `K(x)`, then `F` is the
function field of a curve over `K`. -/
theorem isCurveOver_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x) (hfd : FiniteDimensional K⟮x⟯ F)
    (hsep : Algebra.IsSeparable K⟮x⟯ F) : IsCurveOver K F := by
  obtain ⟨_, _, _, _, -, -⟩ := exists_ratFunc_algebra_of_transcendental htr hfd hsep
  exact isCurveOver_of_ratFunc

open scoped IntermediateField.algebraAdjoinAdjoin in
private theorem exists_separating_transcendental_of_perfectField {K F : Type*} [Field K]
    [Field F] [Algebra K F] [PerfectField K] {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) :
    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by
  have := hfd
  have : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K K⟮x⟯ F
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have hx : IsTranscendenceBasis K (fun _ : Unit => x) := by
    refine isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr ⟨?_, ?_⟩
    · exact (algebraicIndependent_unique_type_iff (ι := Unit)).mpr htr
    · rw [Set.range_const, ← IntermediateField.isAlgebraic_adjoin_iff_top]
      infer_instance
  have hcard : s.card = 1 := by simpa using hs.lift_cardinalMk_eq hx
  obtain ⟨t, rfl⟩ := Finset.card_eq_one.mp hcard
  have htr' : Transcendental K t := by
    have h1 := hs.1
    rw [show ((↑) : (↑({t} : Finset F)) → F) = fun _ => t from
      funext fun y => (Finset.mem_singleton.mp y.2).symm ▸ rfl] at h1
    exact (algebraicIndependent_unique_type_iff (ι := (↑({t} : Finset F)))).mp h1
  have heq : IntermediateField.adjoin K (↑({t} : Finset F) : Set F) = K⟮t⟯ := by
    rw [Finset.coe_singleton]
  have hsep' : Algebra.IsSeparable K⟮t⟯ F :=
    Algebra.IsSeparable.of_equiv_equiv
      (IntermediateField.equivOfEq heq).toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun _ => rfl)
  have : Algebra.EssFiniteType K⟮t⟯ F := Algebra.EssFiniteType.of_comp K K⟮t⟯ F
  exact ⟨t, htr', Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep'⟩

/-- **Curve function fields over a perfect field.** If `K` is perfect, `x : F` is transcendental
over `K` and `F` is finite over `K(x)`, then `F` is the function field of a curve over `K`. -/
theorem isCurveOver_of_transcendental_of_perfectField {K F : Type*} [Field K] [Field F]
    [Algebra K F] [PerfectField K] {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional K⟮x⟯ F) : IsCurveOver K F := by
  obtain ⟨t, ht, htfd, htsep⟩ := exists_separating_transcendental_of_perfectField htr hfd
  exact isCurveOver_of_transcendental ht htfd htsep

end AlgebraicCurve
