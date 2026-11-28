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
`Place_isRational_of_isAlgClosed`;
`weilReciprocity_algebraMap`;
`weilReciprocity`.
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
public import MathlibExt.AlgebraicGeometry.Curve.PlaceExtension
import Mathlib.Algebra.BigOperators.Field
import MathlibExt.AlgebraicGeometry.Curve.NormFormula
import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluationLemmas
import MathlibExt.AlgebraicGeometry.Curve.RationalWeilReciprocity

/-!
# Weil reciprocity for function fields

Let `K` be algebraically closed of characteristic zero and let `F` be a finite extension of
`RatFunc K`. For nonzero `f, g ∈ F` with disjoint divisors, `f(div g) = g(div f)`. The proof
reduces to the rational function field: for nonconstant `g`, `F` is a finite separable
extension of `K(g)`, and Weil reciprocity descends along it through norms and the pushforward
of divisors. For constant `g`, the statement says that the divisor of `f` has degree zero, which
the same descent proves: the pushforward of the divisor of `f` to `RatFunc K` is the divisor of
its norm and has the same degree.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve Polynomial

/-- Over an algebraically closed field every place of a finite extension of `RatFunc K` is
rational. -/
theorem AlgebraicCurve.Place.isRational_of_isAlgClosed_of_finiteDimensional {K F : Type*}
    [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [Algebra (RatFunc K) F]
    [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] (v : Place K F) :
    v.IsRational := by
  classical
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  let u : Place K (RatFunc K) := v.restrict (RatFunc K)
  have hu : u.IsRational :=
    (AlgebraicCurve.Place.isRational_iff_deg_eq_one u).2
      (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed u)
  have hconst : ∀ {b : RatFunc K} (hb : algebraMap (RatFunc K) F b ∈ v.toValuationSubring),
      ∃ c : K, algebraMap K v.ResidueField c
        = IsLocalRing.residue _ (⟨algebraMap (RatFunc K) F b, hb⟩ : v.toValuationSubring) := by
    intro b hb
    have hb' : b ∈ u.toValuationSubring := ValuationSubring.mem_comap.mpr hb
    refine ⟨u.evalAt hu b, ?_⟩
    have h1 : algebraMap K u.ResidueField (u.evalAt hu b) = IsLocalRing.residue _ ⟨b, hb'⟩ :=
      u.algebraMap_evalAt hu hb'
    have h2 : (⟨algebraMap (RatFunc K) F b, hb⟩ : v.toValuationSubring)
        = Place.restrictInclusion (RatFunc K) v ⟨b, hb'⟩ := rfl
    rw [h2, ← Place.restrictResidueMap_residue, ← h1, ← Place.algebraMap_residueField_eq,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨p, hp0, hpx⟩ : IsAlgebraic (RatFunc K) (x : F) := Algebra.IsAlgebraic.isAlgebraic _
  have hsupp : p.support.Nonempty := Polynomial.support_nonempty.mpr hp0
  obtain ⟨j, hj, hjmin⟩ := p.support.exists_min_image
    (fun i => v.ord (algebraMap (RatFunc K) F (p.coeff i))) hsupp
  have haj0 : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hajF : algebraMap (RatFunc K) F (p.coeff j) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc K) F).injective).mpr haj0
  have hbmem : ∀ i, algebraMap (RatFunc K) F (p.coeff i / p.coeff j) ∈ v.toValuationSubring := by
    intro i
    by_cases hi : i ∈ p.support
    · have hai0 : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
      have haiF : algebraMap (RatFunc K) F (p.coeff i) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap (RatFunc K) F).injective).mpr hai0
      rw [map_div₀]
      refine v.mem_of_ord_nonneg (div_ne_zero haiF hajF) ?_
      rw [div_eq_mul_inv, v.ord_mul haiF (inv_ne_zero hajF), v.ord_inv]
      have := hjmin i hi
      omega
    · rw [Polynomial.notMem_support_iff.mp hi, zero_div, map_zero]
      exact zero_mem _
  have haeval : ∀ (q : (RatFunc K)[X]) (z : F),
      aeval z q = ∑ i ∈ q.support, algebraMap (RatFunc K) F (q.coeff i) * z ^ i := by
    intro q z
    conv_lhs => rw [q.as_sum_support]
    simp [map_sum, ← C_mul_X_pow_eq_monomial]
  have hrel : ∑ i ∈ p.support,
      algebraMap (RatFunc K) F (p.coeff i / p.coeff j) * (x : F) ^ i = 0 := by
    have hsum : ∑ i ∈ p.support, algebraMap (RatFunc K) F (p.coeff i) * (x : F) ^ i = 0 := by
      rw [← haeval, hpx]
    have hfac : ∑ i ∈ p.support, algebraMap (RatFunc K) F (p.coeff i / p.coeff j) * (x : F) ^ i
        = (∑ i ∈ p.support, algebraMap (RatFunc K) F (p.coeff i) * (x : F) ^ i)
            / algebraMap (RatFunc K) F (p.coeff j) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_div₀]
      ring
    rw [hfac, hsum, zero_div]
  set B : ℕ → v.toValuationSubring := fun i => ⟨_, hbmem i⟩ with hB
  have hrelO : ∑ i ∈ p.support, B i * x ^ i = 0 := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
      ZeroMemClass.coe_zero, hB]
    exact hrel
  choose c hc using fun i => hconst (hbmem i)
  have hcj : c j = 1 := by
    have h1 : (B j) = 1 := Subtype.ext (by simp [hB, haj0])
    have := hc j
    rw [show (⟨_, hbmem j⟩ : v.toValuationSubring) = B j from rfl, h1, map_one] at this
    exact (algebraMap K v.ResidueField).injective (by rw [this, map_one])
  set R : K[X] := ∑ i ∈ p.support, C (c i) * X ^ i with hR
  have hRy : aeval (IsLocalRing.residue v.toValuationSubring x) R = 0 := by
    have h := congrArg (IsLocalRing.residue v.toValuationSubring) hrelO
    rw [map_sum, map_zero] at h
    simp only [map_mul, map_pow] at h
    rw [hR, map_sum]
    simp only [map_mul, map_pow, aeval_C, aeval_X]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i]
  have hRj : R.coeff j = 1 := by
    rw [hR, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq p.support j, ite_eq_left hj, hcj]
  have hR0 : R ≠ 0 := fun h => by
    have := hRj
    rw [h, coeff_zero] at this
    exact zero_ne_one this
  have halgy : IsAlgebraic K (IsLocalRing.residue v.toValuationSubring x) := ⟨R, hR0, hRy⟩
  have hdeg : (minpoly K (IsLocalRing.residue v.toValuationSubring x)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halgy.isIntegral)
  obtain ⟨a, ha⟩ := minpoly.degree_eq_one_iff.mp hdeg
  exact ⟨a, ha⟩

/-- In a finite extension `F` of `RatFunc K`, with `K` of characteristic zero, the divisor of a
function has degree zero. -/
theorem AlgebraicCurve.Divisor.degree_eq_zero_of_forall_eq_ord {K F : Type*} [Field K]
    [CharZero K] [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] {f : F} (D : Divisor K F)
    (hD : ∀ v : Place K F, D v = v.ord f) : Divisor.degree D = 0 := by
  rcases eq_or_ne f 0 with rfl | hf
  · have hzero : D = 0 := Finsupp.ext fun v => by rw [hD v, Place.ord_zero, Finsupp.coe_zero,
      Pi.zero_apply]
    rw [hzero, map_zero]
  have : CharZero (RatFunc K) :=
    charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  have : Algebra.IsAlgebraic (RatFunc K) F := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsSeparable (RatFunc K) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨E, hE, -⟩ := (RationalFunctionField.hasPrincipalDivisors K).exists_divisor
    (Algebra.norm (RatFunc K) f) (Algebra.norm_ne_zero_iff.mpr hf)
  rw [← Divisor.degree_pushforward (F := RatFunc K) D, Divisor.pushforward_div hf hD hE]
  exact RationalFunctionField.degree_eq_zero_of_forall_eq_ord E hE

/-- Weil reciprocity descends along a finite separable extension `F' / F`. Let `f ∈ F'` and
`g ∈ F` be nonzero, with the divisors of `f` and `algebraMap F F' g` disjoint. If Weil
reciprocity holds for `F`, then it holds for the pair `f`, `algebraMap F F' g`, provided `F` has
characteristic zero and principal divisors (`HasPrincipalDivisors K F`), every place of `F` is
rational, and so are the places in the supports of the divisors of `f` and `algebraMap F F' g`.
-/
theorem AlgebraicCurve.weilReciprocity_algebraMap {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] [CharZero F] [HasPrincipalDivisors K F]
    (hbase : WeilReciprocity K F) {f : F'} {g : F} (hf : f ≠ 0) (hg : g ≠ 0) (Df Dg : Divisor K F')
    (hDf : ∀ w : Place K F', Df w = w.ord f)
    (hDg : ∀ w : Place K F', Dg w = w.ord (algebraMap F F' g))
    (hdisj : ∀ w : Place K F', w.ord f = 0 ∨ w.ord (algebraMap F F' g) = 0)
    (hratF : ∀ v : Place K F, v.IsRational) (hratf : ∀ w ∈ Df.support, Place.IsRational w)
    (hratg : ∀ w ∈ Dg.support, Place.IsRational w) :
    CurveDivisor.evalFun f Dg hratg = CurveDivisor.evalFun (algebraMap F F' g) Df hratf := by
  classical
  have hNf : Algebra.norm F f ≠ 0 := Algebra.norm_ne_zero_iff.mpr hf
  obtain ⟨Eg, hEg, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  obtain ⟨EN, hEN, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (Algebra.norm F f) hNf
  have hord : ∀ v : Place K F, v.ord g ≠ 0 →
      ∀ w ∈ v.fiberOver F', w.ord (algebraMap F F' g) ≠ 0 := by
    intro v hv w hw
    rw [w.ord_restrict (F := F) g, (Place.mem_fiberOver v).mp hw]
    exact mul_ne_zero (by exact_mod_cast (w.ramificationIndex_pos (F := F)).ne') hv
  have hfib : ∀ v : Place K F, v.ord g ≠ 0 → ∀ w ∈ v.fiberOver F', w.ord f = 0 :=
    fun v hv w hw => (hdisj w).resolve_right (hord v hv w hw)
  have hratfib : ∀ v : Place K F, v.ord g ≠ 0 → ∀ w ∈ v.fiberOver F', w.IsRational :=
    fun v hv w hw => hratg w (by rw [Finsupp.mem_support_iff, hDg w]; exact hord v hv w hw)
  have hres : ∀ w : Place K F', w.ord f ≠ 0 → (w.restrict F).ord g = 0 := by
    intro w hw
    have hzero := (hdisj w).resolve_left hw
    rw [w.ord_restrict (F := F) g] at hzero
    have hepos := w.ramificationIndex_pos (F := F)
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h (by exact_mod_cast hepos.ne')
    · exact h
  have hdisjF : ∀ v : Place K F, v.ord (Algebra.norm F f) = 0 ∨ v.ord g = 0 := by
    intro v
    rcases eq_or_ne (v.ord g) 0 with h | h
    · exact Or.inr h
    · exact Or.inl (Place.ord_norm_eq_zero_of_forall_fiber hf v (hfib v h))
  have hsupp : ∀ v ∈ Eg.support, v.ord g ≠ 0 := fun v hv => by
    rw [← hEg v]
    exact Finsupp.mem_support_iff.mp hv
  obtain rfl : Dg = Divisor.pullbackOver F' Eg := by
    ext w
    rw [hDg w, Divisor.pullbackOver_apply_eq_ord (fun u => hEg u)]
  obtain rfl : Divisor.pushforward F Df = EN := Divisor.pushforward_div hf hDf hEN
  exact (CurveDivisor.evalFun_pullbackOver hf Eg (fun v _ => hratF v)
      (fun v hv => hratfib v (hsupp v hv)) (fun v hv => hfib v (hsupp v hv))).trans
    ((hbase (Algebra.norm F f) g _ Eg hNf hg hEN hEg hdisjF (fun v _ => hratF v)
      (fun v _ => hratF v)).trans
    (CurveDivisor.evalFun_algebraMap_pushforward hg Df hratf (fun w _ => hratF _)
      fun w hw => hres w (by rw [← hDf w]; exact Finsupp.mem_support_iff.mp hw)).symm)

private theorem degree_eq_sum_of_rational {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor K F) (hrat : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v hv => ?_
  rw [AddMonoidHom.mulRight_apply, (Place.isRational_iff_deg_eq_one v).1 (hrat v hv),
    Nat.cast_one, mul_one]

/-- **Weil reciprocity.** For `K` algebraically closed of characteristic zero and `F` a finite
extension of `RatFunc K`, nonzero `f, g ∈ F` with disjoint divisors satisfy
`f(div g) = g(div f)`. -/
theorem AlgebraicCurve.weilReciprocity (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] : WeilReciprocity K F := by
  classical
  intro f g Df Dg hf hg hDf hDg hdisj hratf hratg
  by_cases hconst : g ∈ Set.range (algebraMap K F)
  · obtain ⟨c, rfl⟩ := hconst
    have hc : c ≠ 0 := fun h => hg (by rw [h, map_zero])
    obtain rfl : Dg = 0 := by
      ext v
      rw [hDg v, Place.ord_algebraMap, Finsupp.coe_zero, Pi.zero_apply]
    have hsum : (Df.sum fun _ n => n) = 0 := by
      rw [← degree_eq_sum_of_rational Df hratf, Divisor.degree_eq_zero_of_forall_eq_ord Df hDf]
    rw [CurveDivisor.evalFun_zero, CurveDivisor.evalFun_def,
      Finset.prod_congr rfl fun v _ => by rw [Place.evalAt_algebraMap],
      Finset.prod_attach Df.support fun v => c ^ Df v,
      RationalFunctionField.zpow_sum_eq_prod hc]
    exact ((congrArg (c ^ ·) hsum).trans (zpow_zero c)).symm
  · obtain ⟨φ, hφ⟩ := AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq hconst
    have finφ : @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule :=
      AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom φ
    let algφ : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
    have stφ : @IsScalarTower K (RatFunc K) F _ algφ.toSMul _ :=
      @IsScalarTower.of_algebraMap_eq K (RatFunc K) F _ _ _ _ algφ _ fun x => (φ.commutes x).symm
    have : CharZero (RatFunc K) :=
      charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
    have algc : @Algebra.IsAlgebraic (RatFunc K) F _ _ algφ :=
      @Algebra.IsAlgebraic.of_finite (RatFunc K) F _ _ _ algφ finφ
    have sepφ : @Algebra.IsSeparable (RatFunc K) F _ _ algφ :=
      @Algebra.IsAlgebraic.isSeparable_of_perfectField (RatFunc K) F _ _ algφ algc _
    have : HasPrincipalDivisors K (RatFunc K) :=
      AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors K
    have hXg : @algebraMap (RatFunc K) F _ _ algφ RatFunc.X = g := hφ
    have hratF : ∀ v : Place K (RatFunc K), v.IsRational := fun v =>
      (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).2
        (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed v)
    have key := @AlgebraicCurve.weilReciprocity_algebraMap K (RatFunc K) F _ _ _ _ _ algφ stφ finφ
      sepφ _ _ (AlgebraicCurve.RationalFunctionField.weilReciprocity K) f RatFunc.X hf
      RatFunc.X_ne_zero Df Dg hDf (fun w => by rw [hDg w, ← hXg])
      (fun w => by rw [← hXg] at hdisj; exact hdisj w) hratF hratf hratg
    rw [hXg] at key
    exact key
