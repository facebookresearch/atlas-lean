/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units.lean`
and
`P2M/Sol/S_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.RingTheory.ClassGroup

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

open IsDedekindDomain

universe u v

open IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors

variable {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K]

private theorem eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, count K v I = count K v J) : I = J := by
  rw [← finprod_heightOneSpectrum_factorization' K hI,
    ← finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

private theorem pow_injective {n : ℕ} (hn : n ≠ 0) {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : I ^ n = J ^ n) : I = J := by
  refine Units.ext (eq_of_count_eq I.ne_zero J.ne_zero fun v => ?_)
  have hc := congrArg (fun U : (FractionalIdeal R⁰ K)ˣ => count K v ↑U) h
  simp only [Units.val_pow_eq_pow_val, count_pow] at hc
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) hc

private theorem exists_pow_eq {n : ℕ} {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ count K v I) :
    ∃ J : FractionalIdeal R⁰ K, J ≠ 0 ∧ J ^ n = I := by
  classical
  have hfin : {v : HeightOneSpectrum R | ¬count K v I / (n : ℤ) = 0}.Finite := by
    refine Set.Finite.subset (Filter.eventually_cofinite.mp (finite_factors I)) ?_
    intro v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    exact fun h0 => hv (by rw [h0, Int.zero_ediv])
  set exps : HeightOneSpectrum R →₀ ℤ :=
    ⟨hfin.toFinset, fun v => count K v I / (n : ℤ), fun v => by
      rw [Set.Finite.mem_toFinset]; exact Iff.rfl⟩ with hexps
  have hJ0 : (exps.prod fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)
  refine ⟨_, hJ0, eq_of_count_eq (pow_ne_zero n hJ0) hI fun v => ?_⟩
  rw [count_pow, count_finsuppProd]
  show (n : ℤ) * (count K v I / (n : ℤ)) = count K v I
  exact Int.mul_ediv_cancel' (h v)

private theorem toAdd_valuationOfNeZero (v : HeightOneSpectrum R) (x : Kˣ) :
    Multiplicative.toAdd (v.valuationOfNeZero x) =
      -count K v (spanSingleton R⁰ (x : K)) := by
  classical
  have hd0 : (algebraMap R K) ((IsLocalization.sec R⁰ (x : K)).2 : R) ≠ 0 := fun h0 =>
    nonZeroDivisors.coe_ne_zero _
      ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mp h0)
  have hspan : spanSingleton R⁰ (x : K) =
      spanSingleton R⁰ ((algebraMap R K) ((IsLocalization.sec R⁰ (x : K)).2 : R))⁻¹ *
        ↑(Ideal.span {(IsLocalization.sec R⁰ (x : K)).1} : Ideal R) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton]
    have hx : ((algebraMap R K) ((IsLocalization.sec R⁰ (x : K)).2 : R))⁻¹ *
        (algebraMap R K) (IsLocalization.sec R⁰ (x : K)).1 = (x : K) := by
      rw [← IsLocalization.sec_spec R⁰ (x : K), mul_comm (x : K), ← mul_assoc,
        inv_mul_cancel₀ hd0, one_mul]
    rw [hx]
  rw [count_well_defined K v (spanSingleton_ne_zero_iff.mpr x.ne_zero) hspan]
  have hval : v.valuationOfNeZero x = v.valuationOfNeZeroToFun x := rfl
  rw [hval]
  unfold HeightOneSpectrum.valuationOfNeZeroToFun
  rw [toAdd_ofAdd]
  ring

private theorem valuationOfNeZeroMod_eq_one_iff {n : ℕ} (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 ↔
      (n : ℤ) ∣ count K v (spanSingleton R⁰ (x : K)) := by
  rw [← dvd_neg, ← toAdd_valuationOfNeZero v x, ← Int.mem_zmultiples_iff,
    ← Multiplicative.mem_toSubgroup, ← QuotientGroup.eq_one_iff]
  unfold HeightOneSpectrum.valuationOfNeZeroMod
  erw [MonoidHom.comp_apply, QuotientGroup.map_mk]
  exact map_eq_one_iff _ (MulEquiv.injective _)

private def Dvble (n : ℕ) (x : Kˣ) : Prop :=
  ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ count K v (spanSingleton R⁰ (x : K))

private theorem Dvble.mul {n : ℕ} {x y : Kˣ} (hx : Dvble (R := R) n x) (hy : Dvble (R := R) n y) :
    Dvble (R := R) n (x * y) := fun v => by
  have hs : spanSingleton R⁰ ((x * y : Kˣ) : K) =
      spanSingleton R⁰ (x : K) * spanSingleton R⁰ (y : K) := by
    rw [Units.val_mul, spanSingleton_mul_spanSingleton]
  rw [hs, count_mul K v (spanSingleton_ne_zero_iff.mpr x.ne_zero)
    (spanSingleton_ne_zero_iff.mpr y.ne_zero)]
  exact dvd_add (hx v) (hy v)

private theorem Dvble.pow {n : ℕ} (y : Kˣ) : Dvble (R := R) n (y ^ n) := fun v => by
  have hs : spanSingleton R⁰ ((y ^ n : Kˣ) : K) = spanSingleton R⁰ (y : K) ^ n := by
    rw [Units.val_pow_eq_pow_val, spanSingleton_pow]
  rw [hs, count_pow]
  exact dvd_mul_right _ _

private theorem Dvble.of_mul_pow {n : ℕ} {x y : Kˣ} (h : Dvble (R := R) n (x * y ^ n)) :
    Dvble (R := R) n x := by
  have h2 := h.mul (Dvble.pow (R := R) (n := n) y⁻¹)
  have hxy : x * y ^ n * y⁻¹ ^ n = x := by
    rw [mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]
  rwa [hxy] at h2

private noncomputable def rootUnit {n : ℕ} (x : Kˣ) (h : Dvble (R := R) n x) :
    (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (exists_pow_eq (spanSingleton_ne_zero_iff.mpr x.ne_zero) h).choose
    (exists_pow_eq (spanSingleton_ne_zero_iff.mpr x.ne_zero) h).choose_spec.1

private theorem rootUnit_pow {n : ℕ} (x : Kˣ) (h : Dvble (R := R) n x) :
    rootUnit x h ^ n = toPrincipalIdeal R K x := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_toPrincipalIdeal]
  show (exists_pow_eq (spanSingleton_ne_zero_iff.mpr x.ne_zero) h).choose ^ n = _
  exact (exists_pow_eq (spanSingleton_ne_zero_iff.mpr x.ne_zero) h).choose_spec.2

private theorem rootUnit_mul {n : ℕ} (hn : n ≠ 0) (x y : Kˣ) (hx : Dvble (R := R) n x)
    (hy : Dvble (R := R) n y) (hxy : Dvble (R := R) n (x * y)) :
    rootUnit (x * y) hxy = rootUnit x hx * rootUnit y hy := by
  refine pow_injective hn ?_
  rw [mul_pow, rootUnit_pow, rootUnit_pow, rootUnit_pow, ← map_mul]

open Classical in

private noncomputable def classOf (n : ℕ) (x : Kˣ) : ClassGroup R :=
  if h : Dvble (R := R) n x then ClassGroup.mk K (rootUnit x h) else 1

private theorem classOf_of_dvble {n : ℕ} (x : Kˣ) (h : Dvble (R := R) n x) :
    classOf (R := R) (K := K) n x = ClassGroup.mk K (rootUnit x h) :=
  dite_eq_left h

private theorem classOf_mul {n : ℕ} (hn : n ≠ 0) {x y : Kˣ} (hx : Dvble (R := R) n x)
    (hy : Dvble (R := R) n y) :
    classOf (R := R) (K := K) n (x * y) = classOf n x * classOf n y := by
  rw [classOf_of_dvble x hx, classOf_of_dvble y hy,
    classOf_of_dvble (x * y) (hx.mul hy), rootUnit_mul hn x y hx hy (hx.mul hy), map_mul]

private theorem classOf_pow_eq_one {n : ℕ} (hn : n ≠ 0) (y : Kˣ) :
    classOf (R := R) (K := K) n (y ^ n) = 1 := by
  rw [classOf_of_dvble _ (Dvble.pow y)]
  have hroot : rootUnit (y ^ n) (Dvble.pow y) = toPrincipalIdeal R K y := by
    refine pow_injective hn ?_
    rw [rootUnit_pow, ← map_pow]
  rw [hroot, ClassGroup.mk_eq_one_iff]
  exact ⟨⟨(y : K), by rw [coe_toPrincipalIdeal, coe_spanSingleton]⟩⟩

private theorem classOf_mul_pow {n : ℕ} (hn : n ≠ 0) (x y : Kˣ) :
    classOf (R := R) (K := K) n (x * y ^ n) = classOf n x := by
  by_cases hx : Dvble (R := R) n x
  · rw [classOf_mul hn hx (Dvble.pow y), classOf_pow_eq_one hn y, mul_one]
  · unfold classOf
    rw [dite_eq_right (fun h => hx h.of_mul_pow), dite_eq_right hx]

private noncomputable def classOfMod {n : ℕ} (hn : n ≠ 0) :
    (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) → ClassGroup R := fun q =>
  Quotient.liftOn' q (classOf n) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab
    obtain ⟨c, hc⟩ := hab
    have hc' : c ^ n = a⁻¹ * b := hc
    have hb : b = a * c ^ n := by rw [hc', mul_inv_cancel_left]
    rw [hb]
    exact (classOf_mul_pow hn a c).symm

private theorem classOfMod_mk {n : ℕ} (hn : n ≠ 0) (x : Kˣ) :
    classOfMod (R := R) (K := K) hn (QuotientGroup.mk x) = classOf n x :=
  rfl

private theorem dvble_of_mem {n : ℕ} {x : Kˣ}
    (hx : (QuotientGroup.mk x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
      selmerGroup (R := R) (K := K) (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) :
    Dvble (R := R) n x :=
  fun v => (valuationOfNeZeroMod_eq_one_iff v x).mp (hx v (Set.notMem_empty v))

private noncomputable def selmerToClass {n : ℕ} (hn : n ≠ 0) :
    selmerGroup (R := R) (K := K) (S := (∅ : Set (HeightOneSpectrum R))) (n := n) →*
      ClassGroup R :=
  MonoidHom.mk' (fun x => classOfMod hn (x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range))
    (by
      rintro ⟨q, hq⟩ ⟨r, hr⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
      show classOf (R := R) (K := K) n (x * y) = classOf n x * classOf n y
      exact classOf_mul hn (dvble_of_mem hq) (dvble_of_mem hr))

omit [IsDedekindDomain R] in

private theorem exists_unit_of_spanSingleton_eq {a b : K}
    (h : spanSingleton R⁰ a = spanSingleton R⁰ b) :
    ∃ u : Rˣ, b = algebraMap R K ((u : Rˣ) : R) * a := by
  have hb : b ∈ spanSingleton R⁰ a := by rw [h]; exact mem_spanSingleton_self R⁰ b
  have ha : a ∈ spanSingleton R⁰ b := by rw [← h]; exact mem_spanSingleton_self R⁰ a
  obtain ⟨r, hr⟩ := (mem_spanSingleton R⁰).mp hb
  obtain ⟨s, hs⟩ := (mem_spanSingleton R⁰).mp ha
  by_cases hb0 : b = 0
  · refine ⟨1, ?_⟩
    rw [hb0] at hs ⊢
    rw [smul_zero] at hs
    rw [← hs, mul_zero]
  · have hrsb : algebraMap R K (r * s) * b = b := by
      rw [← Algebra.smul_def, mul_smul, hs, hr]
    have hrs1 : r * s = 1 := by
      refine FaithfulSMul.algebraMap_injective R K ?_
      rw [map_one]
      exact mul_right_cancel₀ hb0 (by rw [hrsb, one_mul])
    refine ⟨⟨r, s, hrs1, by rwa [mul_comm] at hrs1⟩, ?_⟩
    rw [← Algebra.smul_def]
    exact hr.symm

private theorem selmerToClass_ker_le {n : ℕ} (hn : n ≠ 0) :
    (selmerToClass (R := R) (K := K) hn).ker ≤
      (selmerGroup.fromUnit (R := R) (K := K) (n := n)).range := by
  rintro ⟨q, hq⟩ hker
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MonoidHom.mem_ker] at hker
  have hdv : Dvble (R := R) n x := dvble_of_mem hq
  have h1 : classOf (R := R) (K := K) n x = 1 := by
    have happ : selmerToClass (R := R) (K := K) hn ⟨QuotientGroup.mk x, hq⟩ =
        classOf n x := classOfMod_mk hn x
    rw [← happ]
    exact hker
  rw [classOf_of_dvble x hdv, ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨c, hc⟩ := h1.principal
  have hcoe : (rootUnit x hdv : FractionalIdeal R⁰ K) = spanSingleton R⁰ c := by
    apply coeToSubmodule_injective
    show ((rootUnit x hdv : FractionalIdeal R⁰ K) : Submodule R K) =
      ((spanSingleton R⁰ c : FractionalIdeal R⁰ K) : Submodule R K)
    rw [coe_spanSingleton]
    exact hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply Units.ne_zero (rootUnit x hdv)
    rw [hcoe]
    exact spanSingleton_eq_zero_iff.mpr h0
  have hcuP : toPrincipalIdeal R K (Units.mk0 c hc0) = rootUnit x hdv :=
    toPrincipalIdeal_eq_iff.mpr (by rw [hcoe, Units.val_mk0])
  have hxc : spanSingleton R⁰ ((Units.mk0 c hc0 ^ n : Kˣ) : K) = spanSingleton R⁰ (x : K) := by
    have hpow := rootUnit_pow x hdv
    rw [← hcuP, ← map_pow] at hpow
    have hiff := toPrincipalIdeal_eq_iff.mp hpow
    rwa [coe_toPrincipalIdeal] at hiff
  obtain ⟨u, hu⟩ := exists_unit_of_spanSingleton_eq hxc
  rw [MonoidHom.mem_range]
  refine ⟨u, Subtype.ext ?_⟩
  show QuotientGroup.mk (Units.map (algebraMap R K).toMonoidHom u) = QuotientGroup.mk x
  have hxu : x = Units.map (algebraMap R K).toMonoidHom u * Units.mk0 c hc0 ^ n := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.coe_map]
    exact hu
  have hmk1 : (QuotientGroup.mk (Units.mk0 c hc0 ^ n) :
      Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨Units.mk0 c hc0, rfl⟩)
  rw [hxu, QuotientGroup.mk_mul, hmk1]
  exact (mul_one (QuotientGroup.mk (Units.map (algebraMap R K).toMonoidHom u) :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)).symm

private theorem finite_of_finite_ker_codom {G H : Type*} [Group G] [Group H] (f : G →* H)
    [Finite H] (hker : Finite f.ker) : Finite G := by
  haveI := hker
  haveI : Finite (G ⧸ f.ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange f).symm.toEquiv
  exact Finite.of_subgroup_quotient f.ker

omit [IsDedekindDomain R] in

private theorem finite_unitsModPow (n : ℕ) (hn : n ≠ 0) [Monoid.FG Rˣ] :
    Finite (Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range) := by
  haveI : Group.FG Rˣ := Group.fg_iff_monoid_fg.mpr ‹_›
  haveI : Group.FG (Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  exact CommGroup.finite_of_fg_isMulTorsion _
    (CommGroup.isMulTorsion_quotient_range_powMonoidHom Rˣ hn)

private theorem finite_selmerEmpty (n : ℕ) (hn : n ≠ 0) [Finite (ClassGroup R)] [Monoid.FG Rˣ] :
    Finite (selmerGroup (R := R) (K := K) (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) := by
  refine finite_of_finite_ker_codom (selmerToClass (R := R) (K := K) hn) ?_
  haveI : Fact (0 < n) := ⟨Nat.pos_of_ne_zero hn⟩
  haveI h1 : Finite (Rˣ ⧸ (selmerGroup.fromUnit (R := R) (K := K) (n := n)).ker) := by
    rw [selmerGroup.fromUnit_ker]
    exact finite_unitsModPow n hn
  haveI hfr : Finite (selmerGroup.fromUnit (R := R) (K := K) (n := n)).range :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange _).toEquiv
  exact Finite.of_injective _ (Subgroup.inclusion_injective (selmerToClass_ker_le hn))

/-- The Selmer group of a Dedekind domain is finite when the class group is
finite, the unit group is finitely generated, the set of places is finite, and
the exponent is positive. -/
public theorem IsDedekindDomain.selmerGroup.finite_of_finite_classGroup_of_fg_units
    {S : Set (HeightOneSpectrum R)} {n : ℕ} [hn : Fact (0 < n)]
    [Finite (ClassGroup R)] [Monoid.FG Rˣ] [Finite S] :
    Finite (selmerGroup (R := R) (K := K) (S := S) (n := n)) := by
  haveI : NeZero n := ⟨hn.out.ne'⟩
  haveI h0 := finite_selmerEmpty (R := R) (K := K) n hn.out.ne'
  refine finite_of_finite_ker_codom
    (selmerGroup.valuation (R := R) (K := K) (S := S) (n := n)) ?_
  rw [selmerGroup.valuation_ker_eq]
  exact Finite.of_equiv _
    (Subgroup.subgroupOfEquivOfLe (selmerGroup.monotone (Set.empty_subset S))).symm.toEquiv
