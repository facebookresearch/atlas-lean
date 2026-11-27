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
`RationalFunctionField_weilReciprocity`.
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

public import MathlibExt.AlgebraicGeometry.Curve.IsCurveOverOfTranscendental
public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluation
public import MathlibExt.AlgebraicGeometry.Curve.RatFuncPrincipalDivisors
public import MathlibExt.AlgebraicGeometry.Curve.RationalFunctionField
import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluationLemmas
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyDeg
import MathlibExt.AlgebraicGeometry.Curve.RatFuncPlaceInftyOrd

/-!
# Weil reciprocity for the rational function field

For `K` algebraically closed, two nonzero rational functions `f, g` in `RatFunc K` with disjoint
divisors satisfy `f(div g) = g(div f)`.
-/

@[expose] public section

noncomputable section

section

section

open Polynomial IsDedekindDomain WithZero IsLocalRing

open scoped Polynomial

namespace AlgebraicCurve

namespace RationalFunctionField

variable (K : Type*) [Field K]

theorem ord_finitePlace_ne_zero_iff {p : K[X]} (hp : Irreducible p) {q : K[X]} (hq : q ≠ 0) :
    (finitePlace K hp).ord (algebraMap K[X] (RatFunc K) q) ≠ 0 ↔ p ∣ q := by
  rw [finitePlace, Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) _ hq,
    heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton]

variable {K}

end RationalFunctionField

namespace RationalFunctionField
open AlgebraicCurve.RationalFunctionField

variable {K : Type*} [Field K]

theorem ord_ofHeightOneSpectrum_eq_zero_of_notMem (w : HeightOneSpectrum K[X]) {q : K[X]}
    (hq : q ≠ 0) (hmem : q ∉ w.asIdeal) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 0 := by
  by_contra h
  exact hmem
    ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hq).mp h)

section PlaceInftyOrd

variable [DecidableEq (RatFunc K)]

theorem ord_placeInfty_algebraMap {q : K[X]} (hq : q ≠ 0) :
    (placeInfty K).ord (algebraMap K[X] (RatFunc K) q) = -(q.natDegree : ℤ) := by
  rw [ord_placeInfty (RatFunc.algebraMap_ne_zero hq), RatFunc.intDegree_polynomial]

end PlaceInftyOrd

section IrreducibleDivisor

variable [DecidableEq (RatFunc K)]

private theorem single_add_single_apply_eq_ord_loc {p : K[X]} (hp : Irreducible p)
    (v : Place K (RatFunc K)) :
    (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single (placeInfty K) (-(p.natDegree : ℤ))) v
      = v.ord (algebraMap K[X] (RatFunc K) p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [Finsupp.add_apply]
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · rw [Finsupp.single_eq_of_ne (Ne.symm (placeInfty_ne_ofHeightOneSpectrum K w)), add_zero]
    by_cases hcase :
        Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = finitePlace K hp
    · rw [hcase, Finsupp.single_eq_same]
      exact (ord_ofHeightOneSpectrum_of_span (heightOneSpectrumOfIrreducible K hp) hp0
        (heightOneSpectrumOfIrreducible_asIdeal K hp)).symm
    · rw [Finsupp.single_eq_of_ne hcase]
      refine (ord_ofHeightOneSpectrum_eq_zero_of_notMem w hp0 fun hmem => hcase ?_).symm
      have hspan : Ideal.span {p} = w.asIdeal :=
        (PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le w.isPrime.ne_top
          ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      have hwp : w = heightOneSpectrumOfIrreducible K hp :=
        HeightOneSpectrum.ext
          (hspan.symm.trans (heightOneSpectrumOfIrreducible_asIdeal K hp).symm)
      rw [hwp, finitePlace_def]
  · rw [Finsupp.single_eq_of_ne
        (show placeInfty K ≠ finitePlace K hp from
          placeInfty_ne_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible K hp)),
      Finsupp.single_eq_same, zero_add]
    exact (ord_placeInfty_algebraMap hp0).symm

end IrreducibleDivisor

def principalDivisor {f : RatFunc K} (hf : f ≠ 0) : Divisor K (RatFunc K) :=
  ⟨(finite_setOf_ord_ne_zero hf).toFinset, fun v => v.ord f, fun v => by
    simp [Set.Finite.mem_toFinset]⟩

@[scoped simp]
theorem principalDivisor_apply {f : RatFunc K} (hf : f ≠ 0) (v : Place K (RatFunc K)) :
    principalDivisor hf v = v.ord f := rfl

theorem degree_principalDivisor {f : RatFunc K} (hf : f ≠ 0) :
    Divisor.degree (principalDivisor hf) = 0 :=
  degree_eq_zero_of_forall_eq_ord (principalDivisor hf) fun _ => rfl

end RationalFunctionField

namespace RationalFunctionField
open AlgebraicCurve.RationalFunctionField

variable (K : Type*) [Field K]

variable {K}

theorem ord_placeOfPoint_algebraMap_eq_mul (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (rootMultiplicity a q : ℤ)
          * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) := by
  obtain ⟨r, hr⟩ := pow_rootMultiplicity_dvd q a
  set m : ℕ := rootMultiplicity a q with hm
  have hXa : (X : K[X]) - C a ≠ 0 := X_sub_C_ne_zero a
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hq (by simpa using hr)
  have hndvd : ¬((X : K[X]) - C a) ∣ r := by
    intro ⟨s, hs⟩
    have : (X - C a) ^ (m + 1) ∣ q := ⟨s, by rw [hr, hs]; ring⟩
    have := (le_rootMultiplicity_iff hq).mpr this
    omega
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hXa' : algebraMap K[X] (RatFunc K) (X - C a) ≠ 0 := (map_ne_zero_iff _ hinj).mpr hXa
  have hr0' : algebraMap K[X] (RatFunc K) r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr0
  have hpow' : algebraMap K[X] (RatFunc K) ((X - C a) ^ m) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero m hXa)
  have hordr : (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) = 0 := by
    by_contra hcon
    exact hndvd (((ord_finitePlace_ne_zero_iff K (irreducible_X_sub_C a) hr0).mp) hcon)
  calc (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m)
          * algebraMap K[X] (RatFunc K) r) := by rw [← map_mul, ← hr]
    _ = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m))
          + (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) :=
        (placeOfPoint K a).ord_mul hpow' hr0'
    _ = (placeOfPoint K a).ord ((algebraMap K[X] (RatFunc K) (X - C a)) ^ (m : ℤ)) := by
        rw [hordr, add_zero, map_pow, ← zpow_natCast]
    _ = (m : ℤ) * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) :=
        (placeOfPoint K a).ord_zpow _ _

theorem dvd_ord_placeOfPoint (a : K) {f : RatFunc K} (hf : f ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) ∣ (placeOfPoint K a).ord f := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := f.denom_ne_zero
  have hnum' : algebraMap K[X] (RatFunc K) f.num ≠ 0 := (map_ne_zero_iff _ hinj).mpr hnum
  have hden' : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := (map_ne_zero_iff _ hinj).mpr hden
  have hsplit : f = algebraMap K[X] (RatFunc K) f.num
      * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ := by
    rw [← div_eq_mul_inv, f.num_div_denom]
  rw [hsplit, (placeOfPoint K a).ord_mul hnum' (inv_ne_zero hden'), Place.ord_inv,
    ord_placeOfPoint_algebraMap_eq_mul a hnum, ord_placeOfPoint_algebraMap_eq_mul a hden]
  exact dvd_add (Dvd.intro_left _ rfl) ((Dvd.intro_left _ rfl).neg_right)

theorem ord_placeOfPoint_X_sub_C (a : K) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) = 1 := by
  set v := placeOfPoint K a with hv
  set n : ℤ := v.ord (algebraMap K[X] (RatFunc K) (X - C a)) with hn
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : (π : RatFunc K) ≠ 0 := by
    simpa using hπ.ne_zero
  have h1 : v.ord (π : RatFunc K) = 1 := v.ord_coe_irreducible hπ
  have hdvd : n ∣ 1 := h1 ▸ dvd_ord_placeOfPoint a hπ0
  have hmem : algebraMap K[X] (RatFunc K) (X - C a) ∈ v.toValuationSubring := by
    rw [hv, placeOfPoint_eq_ofHeightOneSpectrum]
    exact algebraMap_mem_ofHeightOneSpectrum K _ _
  have hnonneg : 0 ≤ n := v.ord_nonneg_of_mem hmem
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · exact h
  · omega

theorem ord_placeOfPoint_algebraMap (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q) = rootMultiplicity a q := by
  rw [ord_placeOfPoint_algebraMap_eq_mul a hq, ord_placeOfPoint_X_sub_C a, mul_one]

variable (K)

end RationalFunctionField

namespace RationalFunctionField
open AlgebraicCurve.RationalFunctionField

variable {K : Type*} [Field K]

theorem isRational_placeOfPoint (a : K) : (placeOfPoint K a).IsRational :=
  (Place.isRational_iff_deg_eq_one _).2 (deg_placeOfPoint K a)

theorem evalAt_placeOfPoint_algebraMap (a : K) (q : K[X]) :
    (placeOfPoint K a).evalAt (isRational_placeOfPoint a) (algebraMap K[X] (RatFunc K) q)
      = q.eval a := by
  have hmem : algebraMap K[X] (RatFunc K) q ∈ (placeOfPoint K a).toValuationSubring :=
    algebraMap_mem_ofHeightOneSpectrum K _ q
  have hmem' : algebraMap K (RatFunc K) (q.eval a) ∈ (placeOfPoint K a).toValuationSubring :=
    (placeOfPoint K a).algebraMap_mem' _
  have hsub : algebraMap K[X] (RatFunc K) q - algebraMap K (RatFunc K) (q.eval a)
      = algebraMap K[X] (RatFunc K) (q - C (q.eval a)) := by
    rw [map_sub, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C]
  have hcongr :
      (placeOfPoint K a).evalAt (isRational_placeOfPoint a) (algebraMap K[X] (RatFunc K) q)
        = (placeOfPoint K a).evalAt (isRational_placeOfPoint a)
            (algebraMap K (RatFunc K) (q.eval a)) := by
    refine Place.evalAt_congr _ _ hmem hmem' ?_
    rw [hsub]
    rcases eq_or_ne (q - C (q.eval a)) 0 with h0 | h0
    · exact Or.inl (by rw [h0, map_zero])
    · refine Or.inr ?_
      rw [ord_placeOfPoint_algebraMap a h0]
      have hroot : (q - C (q.eval a)).IsRoot a := by
        simp [IsRoot.def]
      exact_mod_cast (rootMultiplicity_pos h0).mpr hroot
  rw [hcongr, Place.evalAt_algebraMap]

theorem evalAt_placeOfPoint_X_sub_C (a b : K) :
    (placeOfPoint K a).evalAt (isRational_placeOfPoint a) (algebraMap K[X] (RatFunc K) (X - C b))
      = a - b := by
  rw [evalAt_placeOfPoint_algebraMap]
  simp

section PlaceInfty

variable [DecidableEq (RatFunc K)]

theorem mem_placeInfty_of_intDegree_nonpos {f : RatFunc K} (hf : f ≠ 0)
    (h : f.intDegree ≤ 0) : f ∈ (placeInfty K).toValuationSubring :=
  (placeInfty K).mem_of_ord_nonneg hf (by rw [ord_placeInfty hf]; omega)

variable (K) in
theorem isRational_placeInfty : (placeInfty K).IsRational :=
  (Place.isRational_iff_deg_eq_one _).2 (deg_placeInfty K)

theorem evalAt_placeInfty_eq {f : RatFunc K} {c : K}
    (h : f - algebraMap K (RatFunc K) c = 0
      ∨ (f - algebraMap K (RatFunc K) c).intDegree < 0) :
    (placeInfty K).evalAt (isRational_placeInfty K) f = c := by
  have hsubmem : f - algebraMap K (RatFunc K) c ∈ (placeInfty K).toValuationSubring := by
    rcases h with h | h
    · rw [h]; exact zero_mem _
    · refine mem_placeInfty_of_intDegree_nonpos ?_ h.le
      intro h0
      rw [h0] at h
      simp [RatFunc.intDegree_zero] at h
  have hmem : f ∈ (placeInfty K).toValuationSubring := by
    have : f = (f - algebraMap K (RatFunc K) c) + algebraMap K (RatFunc K) c := by ring
    rw [this]
    exact add_mem hsubmem ((placeInfty K).algebraMap_mem' c)
  have hcongr : (placeInfty K).evalAt (isRational_placeInfty K) f
      = (placeInfty K).evalAt (isRational_placeInfty K) (algebraMap K (RatFunc K) c) := by
    refine Place.evalAt_congr _ _ hmem ((placeInfty K).algebraMap_mem' c) ?_
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      have hne : f - algebraMap K (RatFunc K) c ≠ 0 := by
        intro h0
        rw [h0] at h
        simp [RatFunc.intDegree_zero] at h
      rw [ord_placeInfty hne]
      omega
  rw [hcongr, Place.evalAt_algebraMap]

theorem evalAt_placeInfty_X_sub_C_div (a a₀ : K) :
    (placeInfty K).evalAt (isRational_placeInfty K)
        (algebraMap K[X] (RatFunc K) (X - C a) / algebraMap K[X] (RatFunc K) (X - C a₀))
      = 1 := by
  have ha₀ : algebraMap K[X] (RatFunc K) (X - C a₀) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a₀)
  refine evalAt_placeInfty_eq ?_
  have hkey : algebraMap K[X] (RatFunc K) (X - C a) / algebraMap K[X] (RatFunc K) (X - C a₀)
        - algebraMap K (RatFunc K) 1
      = algebraMap K[X] (RatFunc K) (C (a₀ - a)) / algebraMap K[X] (RatFunc K) (X - C a₀) := by
    rw [map_one, div_sub_one ha₀, ← map_sub]
    congr 2
    rw [map_sub]
    ring
  rw [hkey]
  rcases eq_or_ne a₀ a with rfl | hne
  · exact Or.inl (by simp)
  · refine Or.inr ?_
    have hC : (C (a₀ - a) : K[X]) ≠ 0 := by
      simpa [sub_eq_zero] using hne
    rw [RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hC) ha₀,
      RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, natDegree_C,
      natDegree_X_sub_C]
    norm_num

end PlaceInfty

section CrossRatio

variable [DecidableEq (RatFunc K)]

theorem principalDivisor_X_sub_C (b : K) :
    principalDivisor (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero b))
      = Finsupp.single (placeOfPoint K b) 1 + Finsupp.single (placeInfty K) (-1) := by
  ext v
  have h := single_add_single_apply_eq_ord_loc (irreducible_X_sub_C b) v
  rw [natDegree_X_sub_C, Nat.cast_one] at h
  rw [principalDivisor_apply, ← h]
  rfl

theorem ord_X_sub_C (b : K) (v : Place K (RatFunc K)) :
    v.ord (algebraMap K[X] (RatFunc K) (X - C b))
      = (Finsupp.single (placeOfPoint K b) (1 : ℤ)
          + Finsupp.single (placeInfty K) (-1 : ℤ)) v := by
  rw [← principalDivisor_X_sub_C b, principalDivisor_apply]

omit [DecidableEq (RatFunc K)] in
theorem ord_X_sub_C_placeOfPoint_of_ne {a b : K} (hab : a ≠ b) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C b)) = 0 := by
  classical
  rw [ord_X_sub_C, Finsupp.add_apply,
    Finsupp.single_eq_of_ne
      (show placeOfPoint K a ≠ placeOfPoint K b from
        fun h => hab (placeOfPoint_injective K h)),
    Finsupp.single_eq_of_ne (placeOfPoint_ne_placeInfty K a), add_zero]

omit [DecidableEq (RatFunc K)] in
theorem principalDivisor_X_sub_C_div (a a₀ : K) :
    principalDivisor (div_ne_zero (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a))
        (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a₀)))
      = Finsupp.single (placeOfPoint K a) 1 + Finsupp.single (placeOfPoint K a₀) (-1) := by
  classical
  have hLa : algebraMap K[X] (RatFunc K) (X - C a) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)
  have hLa₀ : algebraMap K[X] (RatFunc K) (X - C a₀) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a₀)
  ext v
  have hneg : (Finsupp.single (placeOfPoint K a₀) (-1 : ℤ)) v
      = -((Finsupp.single (placeOfPoint K a₀) (1 : ℤ)) v) := by
    rcases eq_or_ne v (placeOfPoint K a₀) with rfl | h
    · rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h, neg_zero]
  rw [principalDivisor_apply, div_eq_mul_inv, v.ord_mul hLa (inv_ne_zero hLa₀), v.ord_inv,
    ord_X_sub_C a v, ord_X_sub_C a₀ v]
  simp only [Finsupp.add_apply]
  rw [hneg]
  ring

omit [DecidableEq (RatFunc K)] in
theorem evalAt_placeOfPoint_X_sub_C_div (a a₀ : K) {b : K} (hba₀ : b ≠ a₀) :
    (placeOfPoint K b).evalAt (isRational_placeOfPoint b)
        (algebraMap K[X] (RatFunc K) (X - C a) / algebraMap K[X] (RatFunc K) (X - C a₀))
      = (b - a) / (b - a₀) := by
  classical
  have hLa₀ : algebraMap K[X] (RatFunc K) (X - C a₀) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a₀)
  have hord : (placeOfPoint K b).ord (algebraMap K[X] (RatFunc K) (X - C a₀)) = 0 :=
    ord_X_sub_C_placeOfPoint_of_ne hba₀
  rw [div_eq_mul_inv, (placeOfPoint K b).evalAt_mul (isRational_placeOfPoint b)
      (algebraMap_mem_ofHeightOneSpectrum K _ _)
      ((placeOfPoint K b).mem_of_ord_nonneg (inv_ne_zero hLa₀)
        (by rw [Place.ord_inv, hord, neg_zero])),
    (placeOfPoint K b).evalAt_inv (isRational_placeOfPoint b) hLa₀ hord,
    evalAt_placeOfPoint_X_sub_C, evalAt_placeOfPoint_X_sub_C, div_eq_mul_inv]

end CrossRatio

section Reciprocity

variable [IsAlgClosed K] [DecidableEq (RatFunc K)]

-- Every place of `RatFunc K` is rational over an algebraically closed `K`: it has degree one.
local notation "isRatR " v:max =>
  Iff.mpr (Place.isRational_iff_deg_eq_one v) (IsCurveOver.deg_eq_one_of_isAlgClosed v)

/-- Evaluation on a divisor of `RatFunc K`, every place being rational over an algebraically
closed `K`. -/
local notation "evalFunR " f:max D:max =>
  CurveDivisor.evalFun f D (fun v _ =>
    Iff.mpr (Place.isRational_iff_deg_eq_one v) (IsCurveOver.deg_eq_one_of_isAlgClosed v))

omit [IsAlgClosed K] [DecidableEq (RatFunc K)] in
theorem algebraMap_const_ne_zero {c : K} (hc : c ≠ 0) : algebraMap K (RatFunc K) c ≠ 0 := by
  simpa using hc

local instance : DecidableEq (Place K (RatFunc K)) := Classical.decEq _

omit [IsAlgClosed K] [DecidableEq (RatFunc K)] in
theorem ord_ne_zero_of_mem_support {g : RatFunc K} (hg : g ≠ 0) {v : Place K (RatFunc K)}
    (hv : v ∈ (principalDivisor hg).support) : v.ord g ≠ 0 := by
  rwa [Finsupp.mem_support_iff, principalDivisor_apply] at hv

omit [DecidableEq (RatFunc K)] in
theorem sum_ord_eq_zero {f : RatFunc K} (hf : f ≠ 0) :
    ∑ v ∈ (principalDivisor hf).support, v.ord f = 0 := by
  have h := degree_principalDivisor hf
  rw [← Finsupp.sum_single (principalDivisor hf), Finsupp.sum, map_sum] at h
  rw [← h]
  exact Finset.sum_congr rfl fun v _ => by
    rw [Divisor.degree_single, principalDivisor_apply, IsCurveOver.deg_eq_one_of_isAlgClosed v,
      Nat.cast_one, mul_one]

omit [IsAlgClosed K] [DecidableEq (RatFunc K)] in
theorem zpow_sum_eq_prod {c : K} (hc : c ≠ 0) {ι : Type*} (s : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ s, c ^ n i = c ^ (∑ i ∈ s, n i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

omit [IsAlgClosed K] [DecidableEq (RatFunc K)] in
theorem principalDivisor_congr {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0) (h : f = g) :
    principalDivisor hf = principalDivisor hg := by
  subst h
  rfl

omit [DecidableEq (RatFunc K)] in
theorem reciprocity_algebraMap_right {f : RatFunc K} (hf : f ≠ 0) {c : K} (hc : c ≠ 0) :
    evalFunR f (principalDivisor (algebraMap_const_ne_zero hc))
      = evalFunR (algebraMap K (RatFunc K) c) (principalDivisor hf) := by
  have hzero : principalDivisor (algebraMap_const_ne_zero hc) = 0 := by
    ext v
    rw [principalDivisor_apply, v.ord_algebraMap, Finsupp.coe_zero, Pi.zero_apply]
  rw [hzero, CurveDivisor.evalFun_zero, CurveDivisor.evalFun_def,
    Finset.prod_attach (principalDivisor hf).support fun v =>
      v.evalAt (isRatR v) (algebraMap K (RatFunc K) c) ^ principalDivisor hf v,
    Finset.prod_congr rfl fun v _ => by rw [Place.evalAt_algebraMap], zpow_sum_eq_prod hc]
  rw [show ∑ v ∈ (principalDivisor hf).support, principalDivisor hf v
      = ∑ v ∈ (principalDivisor hf).support, v.ord f from
    Finset.sum_congr rfl fun v _ => principalDivisor_apply hf v, sum_ord_eq_zero hf,
    zpow_zero]

omit [DecidableEq (RatFunc K)] in
theorem reciprocity_mul_right {f g₁ g₂ : RatFunc K} (hf : f ≠ 0) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    (hd₁ : ∀ v : Place K (RatFunc K), v.ord f = 0 ∨ v.ord g₁ = 0)
    (hd₂ : ∀ v : Place K (RatFunc K), v.ord f = 0 ∨ v.ord g₂ = 0)
    (h₁ : evalFunR f (principalDivisor hg₁) = evalFunR g₁ (principalDivisor hf))
    (h₂ : evalFunR f (principalDivisor hg₂)
      = evalFunR g₂ (principalDivisor hf)) :
    evalFunR f (principalDivisor (mul_ne_zero hg₁ hg₂))
      = evalFunR (g₁ * g₂) (principalDivisor hf) := by
  have hsplit : principalDivisor (mul_ne_zero hg₁ hg₂)
      = principalDivisor hg₁ + principalDivisor hg₂ := by
    ext v
    rw [principalDivisor_apply, Finsupp.add_apply, principalDivisor_apply,
      principalDivisor_apply, v.ord_mul hg₁ hg₂]
  rw [hsplit,
    CurveDivisor.evalFun_add f (fun v _ => isRatR v)
      (fun v _ => isRatR v) (fun v _ => isRatR v)
      (fun v hv hvD => v.evalAt_ne_zero hv hf
        ((hd₁ v).resolve_right (ord_ne_zero_of_mem_support hg₁ hvD)))
      (fun v hv hvD => v.evalAt_ne_zero hv hf
        ((hd₂ v).resolve_right (ord_ne_zero_of_mem_support hg₂ hvD))),
    h₁, h₂,
    ← CurveDivisor.evalFun_mul (fun v _ => isRatR v)
      (fun v hv => v.mem_of_ord_nonneg hg₁
        ((hd₁ v).resolve_left (ord_ne_zero_of_mem_support hf hv)).ge)
      (fun v hv => v.mem_of_ord_nonneg hg₂
        ((hd₂ v).resolve_left (ord_ne_zero_of_mem_support hf hv)).ge)]

omit [DecidableEq (RatFunc K)] in
theorem reciprocity_mul_left {f₁ f₂ g : RatFunc K} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hg : g ≠ 0)
    (hd₁ : ∀ v : Place K (RatFunc K), v.ord f₁ = 0 ∨ v.ord g = 0)
    (hd₂ : ∀ v : Place K (RatFunc K), v.ord f₂ = 0 ∨ v.ord g = 0)
    (h₁ : evalFunR f₁ (principalDivisor hg) = evalFunR g (principalDivisor hf₁))
    (h₂ : evalFunR f₂ (principalDivisor hg)
      = evalFunR g (principalDivisor hf₂)) :
    evalFunR (f₁ * f₂) (principalDivisor hg)
      = evalFunR g (principalDivisor (mul_ne_zero hf₁ hf₂)) :=
  (reciprocity_mul_right hg hf₁ hf₂ (fun v => (hd₁ v).symm) (fun v => (hd₂ v).symm)
    h₁.symm h₂.symm).symm

omit [DecidableEq (RatFunc K)] in
theorem reciprocity_zpow_right {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0) (n : ℤ)
    (hd : ∀ v : Place K (RatFunc K), v.ord f = 0 ∨ v.ord g = 0)
    (h : evalFunR f (principalDivisor hg)
      = evalFunR g (principalDivisor hf)) :
    evalFunR f (principalDivisor (zpow_ne_zero n hg))
      = evalFunR (g ^ n) (principalDivisor hf) := by
  have hsplit : principalDivisor (zpow_ne_zero n hg) = n • principalDivisor hg := by
    ext v
    rw [principalDivisor_apply, Finsupp.smul_apply, principalDivisor_apply, v.ord_zpow,
      smul_eq_mul]
  rw [hsplit, CurveDivisor.evalFun_zsmul f _ n fun v _ => isRatR v, h,
    ← CurveDivisor.evalFun_zpow_left hg n (fun v _ => isRatR v)
      (fun v hv => (hd v).resolve_left (ord_ne_zero_of_mem_support hf hv))]

omit [DecidableEq (RatFunc K)] in
theorem reciprocity_zpow_left {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0) (n : ℤ)
    (hd : ∀ v : Place K (RatFunc K), v.ord f = 0 ∨ v.ord g = 0)
    (h : evalFunR f (principalDivisor hg)
      = evalFunR g (principalDivisor hf)) :
    evalFunR (f ^ n) (principalDivisor hg)
      = evalFunR g (principalDivisor (zpow_ne_zero n hf)) :=
  (reciprocity_zpow_right hg hf n (fun v => (hd v).symm) h.symm).symm

omit [IsAlgClosed K] [DecidableEq (RatFunc K)] in
theorem exists_algebraMap_of_forall_ord_eq_zero {g : RatFunc K} (hg : g ≠ 0)
    (h : ∀ v : Place K (RatFunc K), v.ord g = 0) :
    ∃ c : K, c ≠ 0 ∧ g = algebraMap K (RatFunc K) c := by
  have hnum0 : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden0 : g.denom ≠ 0 := g.denom_ne_zero
  have hnum0' : algebraMap K[X] (RatFunc K) g.num ≠ 0 := RatFunc.algebraMap_ne_zero hnum0
  have hden0' : algebraMap K[X] (RatFunc K) g.denom ≠ 0 := RatFunc.algebraMap_ne_zero hden0
  have hsplit : g = algebraMap K[X] (RatFunc K) g.num
      * (algebraMap K[X] (RatFunc K) g.denom)⁻¹ := by
    rw [← div_eq_mul_inv, g.num_div_denom]
  have hkey : ∀ p : K[X], Irreducible p → ¬p ∣ g.num ∧ ¬p ∣ g.denom := by
    intro p hpirr
    have hord : (finitePlace K hpirr).ord (algebraMap K[X] (RatFunc K) g.num)
        = (finitePlace K hpirr).ord (algebraMap K[X] (RatFunc K) g.denom) := by
      have h0 := h (finitePlace K hpirr)
      rw [hsplit, (finitePlace K hpirr).ord_mul hnum0' (inv_ne_zero hden0'),
        Place.ord_inv] at h0
      omega
    constructor
    · intro hdvd
      refine hpirr.not_isUnit (g.isCoprime_num_denom.isUnit_of_dvd' hdvd ?_)
      refine (ord_finitePlace_ne_zero_iff K hpirr hden0).mp ?_
      rw [← hord]
      exact (ord_finitePlace_ne_zero_iff K hpirr hnum0).mpr hdvd
    · intro hdvd
      refine hpirr.not_isUnit (g.isCoprime_num_denom.isUnit_of_dvd' ?_ hdvd)
      refine (ord_finitePlace_ne_zero_iff K hpirr hnum0).mp ?_
      rw [hord]
      exact (ord_finitePlace_ne_zero_iff K hpirr hden0).mpr hdvd
  have hunit : ∀ q : K[X], q ≠ 0 → (∀ p : K[X], Irreducible p → ¬p ∣ q) → IsUnit q := by
    intro q hq hp
    by_contra hu
    obtain ⟨p, hpirr, hpdvd⟩ := WfDvdMonoid.exists_irreducible_factor hu hq
    exact hp p hpirr hpdvd
  obtain ⟨c₁, hc₁u, hc₁⟩ :=
    Polynomial.isUnit_iff.mp (hunit g.num hnum0 fun p hp => (hkey p hp).1)
  obtain ⟨c₂, hc₂u, hc₂⟩ :=
    Polynomial.isUnit_iff.mp (hunit g.denom hden0 fun p hp => (hkey p hp).2)
  have hc₁0 : c₁ ≠ 0 := fun h0 => hnum0 (by rw [← hc₁, h0, map_zero])
  have hc₂0 : c₂ ≠ 0 := fun h0 => hden0 (by rw [← hc₂, h0, map_zero])
  refine ⟨c₁ / c₂, div_ne_zero hc₁0 hc₂0, ?_⟩
  rw [← g.num_div_denom, ← hc₁, ← hc₂, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
    ← RatFunc.algebraMap_eq_C, map_div₀]

omit [IsAlgClosed K] [DecidableEq (RatFunc K)] in
theorem crossRatio_reciprocity {a a₀ b : K} (hba : b ≠ a) (hba₀ : b ≠ a₀)
    (hD₁ : ∀ v ∈ (principalDivisor (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero b))).support,
      v.IsRational)
    (hD₂ : ∀ v ∈ (principalDivisor (div_ne_zero (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a))
      (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a₀)))).support, v.IsRational) :
    CurveDivisor.evalFun
        (algebraMap K[X] (RatFunc K) (X - C a) / algebraMap K[X] (RatFunc K) (X - C a₀))
        (principalDivisor (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero b))) hD₁
      = CurveDivisor.evalFun (algebraMap K[X] (RatFunc K) (X - C b))
        (principalDivisor (div_ne_zero (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a))
          (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a₀)))) hD₂ := by
  classical
  have key : ∀ (D₁ D₂ : Divisor K (RatFunc K)) (h₁ : ∀ v ∈ D₁.support, v.IsRational)
      (h₂ : ∀ v ∈ D₂.support, v.IsRational),
      D₁ = Finsupp.single (placeOfPoint K b) 1 + Finsupp.single (placeInfty K) (-1) →
      D₂ = Finsupp.single (placeOfPoint K a) 1 + Finsupp.single (placeOfPoint K a₀) (-1) →
      CurveDivisor.evalFun
          (algebraMap K[X] (RatFunc K) (X - C a) / algebraMap K[X] (RatFunc K) (X - C a₀)) D₁ h₁
        = CurveDivisor.evalFun (algebraMap K[X] (RatFunc K) (X - C b)) D₂ h₂ := by
    rintro D₁ D₂ h₁ h₂ rfl rfl
    rw [CurveDivisor.evalFun_single_sub_single _ (isRational_placeOfPoint b)
        (isRational_placeInfty K)
        (by rw [evalAt_placeOfPoint_X_sub_C_div a a₀ hba₀]
            exact div_ne_zero (sub_ne_zero.mpr hba) (sub_ne_zero.mpr hba₀))
        (by rw [evalAt_placeInfty_X_sub_C_div a a₀]; exact one_ne_zero),
      CurveDivisor.evalFun_single_sub_single _ (isRational_placeOfPoint a)
        (isRational_placeOfPoint a₀)
        (by rw [evalAt_placeOfPoint_X_sub_C]
            exact sub_ne_zero.mpr fun h => hba h.symm)
        (by rw [evalAt_placeOfPoint_X_sub_C]
            exact sub_ne_zero.mpr fun h => hba₀ h.symm),
      evalAt_placeOfPoint_X_sub_C_div a a₀ hba₀, evalAt_placeInfty_X_sub_C_div a a₀,
      evalAt_placeOfPoint_X_sub_C, evalAt_placeOfPoint_X_sub_C, div_one]
    rw [div_eq_div_iff (sub_ne_zero.mpr hba₀) (sub_ne_zero.mpr fun h => hba₀ h.symm)]
    ring
  exact key _ _ hD₁ hD₂ (principalDivisor_X_sub_C b) (principalDivisor_X_sub_C_div a a₀)

omit [DecidableEq (RatFunc K)] in
theorem reciprocity_of_forall_ord_eq_zero {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0)
    (hzero : ∀ v : Place K (RatFunc K), v.ord g = 0) :
    evalFunR f (principalDivisor hg) = evalFunR g (principalDivisor hf) := by
  obtain ⟨c, hc, rfl⟩ := exists_algebraMap_of_forall_ord_eq_zero hg hzero
  exact reciprocity_algebraMap_right hf hc

omit [IsAlgClosed K] [DecidableEq (RatFunc K)] in
theorem ord_div_zpow (v : Place K (RatFunc K)) {g h : RatFunc K} (hg : g ≠ 0) (hh : h ≠ 0)
    (m : ℤ) : v.ord (g / h ^ m) = v.ord g - m * v.ord h := by
  rw [div_eq_mul_inv, v.ord_mul hg (inv_ne_zero (zpow_ne_zero m hh)), v.ord_inv, v.ord_zpow,
    sub_eq_add_neg]

omit [IsAlgClosed K] in
theorem ord_X_sub_C_eq_zero_of_ne (b : K) {v : Place K (RatFunc K)}
    (hvb : v ≠ placeOfPoint K b) (hvinf : v ≠ placeInfty K) :
    v.ord (algebraMap K[X] (RatFunc K) (X - C b)) = 0 := by
  rw [ord_X_sub_C b v, Finsupp.add_apply, Finsupp.single_eq_of_ne hvb,
    Finsupp.single_eq_of_ne hvinf, add_zero]

theorem reciprocity_linear (b : K) :
    ∀ (n : ℕ) (f : RatFunc K) (hf : f ≠ 0),
      (placeInfty K).ord f = 0 → (placeOfPoint K b).ord f = 0 →
      (principalDivisor hf).support.card ≤ n →
      evalFunR f
          (principalDivisor (RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero b)))
        = evalFunR (algebraMap K[X] (RatFunc K) (X - C b)) (principalDivisor hf) := by
  have hLb : algebraMap K[X] (RatFunc K) (X - C b) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero b)
  intro n
  induction n with
  | zero =>
    intro f hf hinf hb hcard
    refine (reciprocity_of_forall_ord_eq_zero hLb hf fun v => ?_).symm
    rw [← principalDivisor_apply hf v,
      Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))]
    rfl
  | succ n ih =>
    intro f hf hinf hb hcard
    rcases Finset.eq_empty_or_nonempty (principalDivisor hf).support with hempty | hne
    · refine (reciprocity_of_forall_ord_eq_zero hLb hf fun v => ?_).symm
      rw [← principalDivisor_apply hf v, Finsupp.support_eq_empty.mp hempty]
      rfl
    have hsum := sum_ord_eq_zero hf
    have hexpos : ∃ v ∈ (principalDivisor hf).support, 0 < v.ord f := by
      by_contra hcon
      have hcon' : ∀ v ∈ (principalDivisor hf).support, v.ord f ≤ 0 := fun v hv => by
        by_contra hgt
        exact hcon ⟨v, hv, not_le.mp hgt⟩
      have hlt : ∑ v ∈ (principalDivisor hf).support, v.ord f
          < ∑ v ∈ (principalDivisor hf).support, (0 : ℤ) :=
        Finset.sum_lt_sum_of_nonempty hne fun v hv =>
          lt_of_le_of_ne (hcon' v hv) (ord_ne_zero_of_mem_support hf hv)
      rw [Finset.sum_const_zero, hsum] at hlt
      exact lt_irrefl 0 hlt
    have hexneg : ∃ v ∈ (principalDivisor hf).support, v.ord f < 0 := by
      by_contra hcon
      have hcon' : ∀ v ∈ (principalDivisor hf).support, 0 ≤ v.ord f := fun v hv => by
        by_contra hgt
        exact hcon ⟨v, hv, not_le.mp hgt⟩
      have hlt : ∑ v ∈ (principalDivisor hf).support, (0 : ℤ)
          < ∑ v ∈ (principalDivisor hf).support, v.ord f :=
        Finset.sum_lt_sum_of_nonempty hne fun v hv =>
          lt_of_le_of_ne (hcon' v hv) (Ne.symm (ord_ne_zero_of_mem_support hf hv))
      rw [Finset.sum_const_zero, hsum] at hlt
      exact lt_irrefl 0 hlt
    obtain ⟨vp, hvp_mem, hvp⟩ := hexpos
    obtain ⟨vn, hvn_mem, hvn⟩ := hexneg
    obtain ⟨a, rfl⟩ : ∃ x : K, vp = placeOfPoint K x := by
      rcases eq_placeOfPoint_or_eq_placeInfty K vp with h | h
      · exact h
      · rw [h, hinf] at hvp
        exact absurd hvp (lt_irrefl 0)
    obtain ⟨a₀, rfl⟩ : ∃ x : K, vn = placeOfPoint K x := by
      rcases eq_placeOfPoint_or_eq_placeInfty K vn with h | h
      · exact h
      · rw [h, hinf] at hvn
        exact absurd hvn (lt_irrefl 0)
    have hab : a ≠ b := by
      rintro rfl
      rw [hb] at hvp
      exact lt_irrefl 0 hvp
    have ha₀b : a₀ ≠ b := by
      rintro rfl
      rw [hb] at hvn
      exact lt_irrefl 0 hvn
    have haa₀ : placeOfPoint K a ≠ placeOfPoint K a₀ := by
      intro h
      rw [h] at hvp
      omega
    have hLa : algebraMap K[X] (RatFunc K) (X - C a) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)
    have hLa₀ : algebraMap K[X] (RatFunc K) (X - C a₀) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a₀)
    have hrne : algebraMap K[X] (RatFunc K) (X - C a) / algebraMap K[X] (RatFunc K) (X - C a₀)
        ≠ 0 := div_ne_zero hLa hLa₀
    have hord_r : ∀ v : Place K (RatFunc K),
        v.ord (algebraMap K[X] (RatFunc K) (X - C a) / algebraMap K[X] (RatFunc K) (X - C a₀))
          = (Finsupp.single (placeOfPoint K a) (1 : ℤ)
              + Finsupp.single (placeOfPoint K a₀) (-1 : ℤ)) v := fun v => by
      rw [← principalDivisor_apply hrne v, principalDivisor_X_sub_C_div a a₀]
    set m : ℤ := (placeOfPoint K a).ord f with hm
    have hrm_ne : (algebraMap K[X] (RatFunc K) (X - C a)
        / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m ≠ 0 := zpow_ne_zero m hrne
    have hf' : f / (algebraMap K[X] (RatFunc K) (X - C a)
        / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m ≠ 0 := div_ne_zero hf hrm_ne
    have hord_f' : ∀ v : Place K (RatFunc K),
        v.ord (f / (algebraMap K[X] (RatFunc K) (X - C a)
            / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m)
          = v.ord f - m * (Finsupp.single (placeOfPoint K a) (1 : ℤ)
              + Finsupp.single (placeOfPoint K a₀) (-1 : ℤ)) v := fun v => by
      rw [ord_div_zpow v hf hrne m, hord_r v]
    have hf'_inf : (placeInfty K).ord (f / (algebraMap K[X] (RatFunc K) (X - C a)
        / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m) = 0 := by
      rw [hord_f', hinf, Finsupp.add_apply,
        Finsupp.single_eq_of_ne (Ne.symm (placeOfPoint_ne_placeInfty K a)),
        Finsupp.single_eq_of_ne (Ne.symm (placeOfPoint_ne_placeInfty K a₀))]
      ring
    have hf'_b : (placeOfPoint K b).ord (f / (algebraMap K[X] (RatFunc K) (X - C a)
        / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m) = 0 := by
      rw [hord_f', hb, Finsupp.add_apply,
        Finsupp.single_eq_of_ne
          (show placeOfPoint K b ≠ placeOfPoint K a from
            fun h => hab (placeOfPoint_injective K h).symm),
        Finsupp.single_eq_of_ne
          (show placeOfPoint K b ≠ placeOfPoint K a₀ from
            fun h => ha₀b (placeOfPoint_injective K h).symm)]
      ring
    have hf'_a : (placeOfPoint K a).ord (f / (algebraMap K[X] (RatFunc K) (X - C a)
        / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m) = 0 := by
      rw [hord_f', Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne haa₀, ← hm]
      ring
    have hsupp' : (principalDivisor hf').support
        ⊆ (principalDivisor hf).support.erase (placeOfPoint K a) := by
      intro v hv
      have hvord := ord_ne_zero_of_mem_support hf' hv
      rw [Finset.mem_erase]
      constructor
      · rintro rfl
        exact hvord hf'_a
      · rw [Finsupp.mem_support_iff, principalDivisor_apply]
        intro hvf
        apply hvord
        rw [hord_f' v, hvf, Finsupp.add_apply]
        rcases eq_or_ne v (placeOfPoint K a) with rfl | hva
        · rw [hf'_a] at hvord
          exact absurd rfl hvord
        rcases eq_or_ne v (placeOfPoint K a₀) with rfl | hva₀
        · rw [hvf] at hvn
          exact absurd hvn (lt_irrefl 0)
        · rw [Finsupp.single_eq_of_ne hva, Finsupp.single_eq_of_ne hva₀]
          ring
    have hcard' : (principalDivisor hf').support.card ≤ n := by
      have h1 := Finset.card_le_card hsupp'
      rw [Finset.card_erase_of_mem hvp_mem] at h1
      omega
    have hd_r_Lb : ∀ v : Place K (RatFunc K),
        v.ord (algebraMap K[X] (RatFunc K) (X - C a)
            / algebraMap K[X] (RatFunc K) (X - C a₀)) = 0
          ∨ v.ord (algebraMap K[X] (RatFunc K) (X - C b)) = 0 := by
      intro v
      rcases eq_or_ne v (placeOfPoint K a) with rfl | hva
      · exact Or.inr (ord_X_sub_C_placeOfPoint_of_ne hab)
      rcases eq_or_ne v (placeOfPoint K a₀) with rfl | hva₀
      · exact Or.inr (ord_X_sub_C_placeOfPoint_of_ne ha₀b)
      · refine Or.inl ?_
        rw [hord_r v, Finsupp.add_apply, Finsupp.single_eq_of_ne hva,
          Finsupp.single_eq_of_ne hva₀]
        ring
    have hd_rm_Lb : ∀ v : Place K (RatFunc K),
        v.ord ((algebraMap K[X] (RatFunc K) (X - C a)
            / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m) = 0
          ∨ v.ord (algebraMap K[X] (RatFunc K) (X - C b)) = 0 := fun v =>
      (hd_r_Lb v).imp_left fun h => by rw [v.ord_zpow, h, mul_zero]
    have hd_f'_Lb : ∀ v : Place K (RatFunc K),
        v.ord (f / (algebraMap K[X] (RatFunc K) (X - C a)
            / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m) = 0
          ∨ v.ord (algebraMap K[X] (RatFunc K) (X - C b)) = 0 := by
      intro v
      rcases eq_or_ne v (placeOfPoint K b) with rfl | hvb
      · exact Or.inl hf'_b
      rcases eq_or_ne v (placeInfty K) with rfl | hvinf
      · exact Or.inl hf'_inf
      · exact Or.inr (ord_X_sub_C_eq_zero_of_ne b hvb hvinf)
    have hcross_pow :
        evalFunR ((algebraMap K[X] (RatFunc K) (X - C a)
            / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m)
          (principalDivisor hLb)
        = evalFunR (algebraMap K[X] (RatFunc K) (X - C b))
            (principalDivisor (zpow_ne_zero m hrne)) :=
      reciprocity_zpow_left hrne hLb m hd_r_Lb
        (crossRatio_reciprocity (fun h => hab h.symm) (fun h => ha₀b h.symm)
          (fun v _ => isRatR v) (fun v _ => isRatR v))
    have hih :
        evalFunR (f / (algebraMap K[X] (RatFunc K) (X - C a)
            / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m)
          (principalDivisor hLb)
        = evalFunR (algebraMap K[X] (RatFunc K) (X - C b)) (principalDivisor hf') :=
      ih _ hf' hf'_inf hf'_b hcard'
    have hmul :
        evalFunR ((algebraMap K[X] (RatFunc K) (X - C a)
              / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m
            * (f / (algebraMap K[X] (RatFunc K) (X - C a)
              / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m))
          (principalDivisor hLb)
        = evalFunR (algebraMap K[X] (RatFunc K) (X - C b))
            (principalDivisor (mul_ne_zero (zpow_ne_zero m hrne) hf')) :=
      reciprocity_mul_left (zpow_ne_zero m hrne) hf' hLb hd_rm_Lb hd_f'_Lb hcross_pow hih
    have hfeq : f = (algebraMap K[X] (RatFunc K) (X - C a)
        / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m
        * (f / (algebraMap K[X] (RatFunc K) (X - C a)
          / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m) := by
      rw [mul_comm, div_mul_cancel₀ _ hrm_ne]
    calc evalFunR f (principalDivisor hLb)
        = evalFunR ((algebraMap K[X] (RatFunc K) (X - C a)
              / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m
            * (f / (algebraMap K[X] (RatFunc K) (X - C a)
              / algebraMap K[X] (RatFunc K) (X - C a₀)) ^ m))
          (principalDivisor hLb) := by rw [← hfeq]
      _ = evalFunR (algebraMap K[X] (RatFunc K) (X - C b))
            (principalDivisor (mul_ne_zero (zpow_ne_zero m hrne) hf')) := hmul
      _ = evalFunR (algebraMap K[X] (RatFunc K) (X - C b)) (principalDivisor hf) := by
          rw [principalDivisor_congr (mul_ne_zero (zpow_ne_zero m hrne) hf') hf hfeq.symm]

theorem reciprocity_of_ord_placeInfty_eq_zero :
    ∀ (n : ℕ) (f g : RatFunc K) (hf : f ≠ 0) (hg : g ≠ 0),
      (placeInfty K).ord f = 0 →
      (∀ v : Place K (RatFunc K), v.ord f = 0 ∨ v.ord g = 0) →
      ((principalDivisor hg).support.erase (placeInfty K)).card ≤ n →
      evalFunR f (principalDivisor hg) = evalFunR g (principalDivisor hf) := by
  have hbase : ∀ (f g : RatFunc K) (hf : f ≠ 0) (hg : g ≠ 0),
      (principalDivisor hg).support.erase (placeInfty K) = ∅ →
      evalFunR f (principalDivisor hg) = evalFunR g (principalDivisor hf) := by
    intro f g hf hg hempty
    refine reciprocity_of_forall_ord_eq_zero hf hg fun v => ?_
    by_contra hv
    have hvmem : v ∈ (principalDivisor hg).support := by
      rw [Finsupp.mem_support_iff, principalDivisor_apply]
      exact hv
    have hsubset : (principalDivisor hg).support ⊆ {placeInfty K} := by
      intro w hw
      rw [Finset.mem_singleton]
      by_contra hwne
      exact absurd (hempty ▸ Finset.mem_erase.mpr ⟨hwne, hw⟩) (Finset.notMem_empty w)
    have hsupp_eq : (principalDivisor hg).support = {placeInfty K} :=
      Finset.Subset.antisymm hsubset
        (Finset.singleton_subset_iff.mpr (Finset.mem_singleton.mp (hsubset hvmem) ▸ hvmem))
    have hsum := sum_ord_eq_zero hg
    rw [hsupp_eq, Finset.sum_singleton] at hsum
    rw [Finset.mem_singleton.mp (hsubset hvmem)] at hv
    exact hv hsum
  intro n
  induction n with
  | zero =>
    intro f g hf hg hinf hd hcard
    exact hbase f g hf hg (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ n ih =>
    intro f g hf hg hinf hd hcard
    rcases Finset.eq_empty_or_nonempty
      ((principalDivisor hg).support.erase (placeInfty K)) with hempty | hne
    · exact hbase f g hf hg hempty
    obtain ⟨vb, hvb⟩ := hne
    rw [Finset.mem_erase] at hvb
    obtain ⟨b, rfl⟩ : ∃ x : K, vb = placeOfPoint K x := by
      rcases eq_placeOfPoint_or_eq_placeInfty K vb with h | h
      · exact h
      · exact absurd h hvb.1
    have hordb : (placeOfPoint K b).ord g ≠ 0 := ord_ne_zero_of_mem_support hg hvb.2
    have hfb : (placeOfPoint K b).ord f = 0 := (hd _).resolve_right hordb
    have hLb : algebraMap K[X] (RatFunc K) (X - C b) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero b)
    set m : ℤ := (placeOfPoint K b).ord g with hm
    have hLbm : (algebraMap K[X] (RatFunc K) (X - C b)) ^ m ≠ 0 := zpow_ne_zero m hLb
    have hg' : g / (algebraMap K[X] (RatFunc K) (X - C b)) ^ m ≠ 0 := div_ne_zero hg hLbm
    have hord_g' : ∀ v : Place K (RatFunc K),
        v.ord (g / (algebraMap K[X] (RatFunc K) (X - C b)) ^ m)
          = v.ord g - m * v.ord (algebraMap K[X] (RatFunc K) (X - C b)) := fun v =>
      ord_div_zpow v hg hLb m
    have hg'_b : (placeOfPoint K b).ord
        (g / (algebraMap K[X] (RatFunc K) (X - C b)) ^ m) = 0 := by
      rw [hord_g', ord_placeOfPoint_X_sub_C, ← hm]
      ring
    have hsupp' : (principalDivisor hg').support.erase (placeInfty K)
        ⊆ ((principalDivisor hg).support.erase (placeInfty K)).erase (placeOfPoint K b) := by
      intro v hv
      rw [Finset.mem_erase] at hv
      have hvord := ord_ne_zero_of_mem_support hg' hv.2
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨?_, hv.1, ?_⟩
      · rintro rfl
        exact hvord hg'_b
      · rw [Finsupp.mem_support_iff, principalDivisor_apply]
        intro hvg
        apply hvord
        rw [hord_g' v, hvg,
          ord_X_sub_C_eq_zero_of_ne b (fun h => hvord (by rw [h]; exact hg'_b)) hv.1]
        ring
    have hcard' : ((principalDivisor hg').support.erase (placeInfty K)).card ≤ n := by
      have h1 := Finset.card_le_card hsupp'
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr hvb)] at h1
      omega
    have hd_f_Lb : ∀ v : Place K (RatFunc K),
        v.ord f = 0 ∨ v.ord (algebraMap K[X] (RatFunc K) (X - C b)) = 0 := by
      intro v
      rcases eq_or_ne v (placeOfPoint K b) with rfl | hvb'
      · exact Or.inl hfb
      rcases eq_or_ne v (placeInfty K) with rfl | hvinf
      · exact Or.inl hinf
      · exact Or.inr (ord_X_sub_C_eq_zero_of_ne b hvb' hvinf)
    have hd_f_Lbm : ∀ v : Place K (RatFunc K),
        v.ord f = 0 ∨ v.ord ((algebraMap K[X] (RatFunc K) (X - C b)) ^ m) = 0 := fun v =>
      (hd_f_Lb v).imp_right fun h => by rw [v.ord_zpow, h, mul_zero]
    have hd_f_g' : ∀ v : Place K (RatFunc K),
        v.ord f = 0 ∨ v.ord (g / (algebraMap K[X] (RatFunc K) (X - C b)) ^ m) = 0 := by
      intro v
      by_cases hv : v.ord f = 0
      · exact Or.inl hv
      · refine Or.inr ?_
        rw [hord_g' v, (hd v).resolve_left hv, (hd_f_Lb v).resolve_left hv, mul_zero,
          sub_zero]
    have hlin :
        evalFunR f (principalDivisor hLb)
          = evalFunR (algebraMap K[X] (RatFunc K) (X - C b)) (principalDivisor hf) :=
      reciprocity_linear b (principalDivisor hf).support.card f hf hinf hfb le_rfl
    have hlin_pow :
        evalFunR f (principalDivisor hLbm)
          = evalFunR ((algebraMap K[X] (RatFunc K) (X - C b)) ^ m)
              (principalDivisor hf) :=
      reciprocity_zpow_right hf hLb m hd_f_Lb hlin
    have hih :
        evalFunR f (principalDivisor hg')
          = evalFunR (g / (algebraMap K[X] (RatFunc K) (X - C b)) ^ m)
              (principalDivisor hf) :=
      ih f _ hf hg' hinf hd_f_g' hcard'
    have hmul :
        evalFunR f (principalDivisor (mul_ne_zero hLbm hg'))
          = evalFunR ((algebraMap K[X] (RatFunc K) (X - C b)) ^ m
              * (g / (algebraMap K[X] (RatFunc K) (X - C b)) ^ m)) (principalDivisor hf) :=
      reciprocity_mul_right hf hLbm hg' hd_f_Lbm hd_f_g' hlin_pow hih
    have hgeq : g = (algebraMap K[X] (RatFunc K) (X - C b)) ^ m
        * (g / (algebraMap K[X] (RatFunc K) (X - C b)) ^ m) := by
      rw [mul_comm, div_mul_cancel₀ _ hLbm]
    calc evalFunR f (principalDivisor hg)
        = evalFunR f (principalDivisor (mul_ne_zero hLbm hg')) := by
          rw [principalDivisor_congr hg (mul_ne_zero hLbm hg') hgeq]
      _ = evalFunR ((algebraMap K[X] (RatFunc K) (X - C b)) ^ m
            * (g / (algebraMap K[X] (RatFunc K) (X - C b)) ^ m)) (principalDivisor hf) := hmul
      _ = evalFunR g (principalDivisor hf) := by rw [← hgeq]

end Reciprocity

end RationalFunctionField

end AlgebraicCurve

end

open Polynomial IsDedekindDomain WithZero IsLocalRing _root_.AlgebraicCurve AlgebraicCurve
  _root_.AlgebraicCurve.RationalFunctionField AlgebraicCurve.RationalFunctionField in
/-- Weil reciprocity for the rational function field: for `K` algebraically closed, nonzero
`f, g ∈ RatFunc K` with disjoint divisors satisfy `f(div g) = g(div f)`. -/
theorem AlgebraicCurve.RationalFunctionField.weilReciprocity (K : Type*) [Field K] [IsAlgClosed K] :
    WeilReciprocity K (RatFunc K) := by
  classical
  intro f g Df Dg hf hg hDf hDg hdisj _ _
  obtain rfl : Df = principalDivisor hf := Finsupp.ext fun v => hDf v
  obtain rfl : Dg = principalDivisor hg := Finsupp.ext fun v => hDg v
  rcases hdisj (placeInfty K) with h | h
  · exact reciprocity_of_ord_placeInfty_eq_zero
      (principalDivisor hg).support.card f g hf hg h hdisj Finset.card_erase_le
  · exact (reciprocity_of_ord_placeInfty_eq_zero
      (principalDivisor hf).support.card g f hg hf h
      (fun v => (hdisj v).symm) Finset.card_erase_le).symm

end

end
