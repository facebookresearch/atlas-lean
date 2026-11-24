/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_IsDedekindDomain_FiniteUnitIdeles.lean`,
`Theorems/Thm_IsDedekindDomain_FiniteAdeleRing_exists_monoidHom_
units_classGroup_surjective_ker_eq.lean`
and
`P2M/Sol/S_IsDedekindDomain_FiniteAdeleRing_exists_monoidHom_
units_classGroup_surjective_ker_eq.lean`
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

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

import Mathlib.RingTheory.DedekindDomain.SelmerGroup

@[expose] public section

open scoped nonZeroDivisors WithZero

open IsDedekindDomain.HeightOneSpectrum WithZero

namespace IsDedekindDomain
namespace FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The subgroup of finite ideles that are integral units at every finite
place: both the idele and its inverse are integral everywhere. -/
public def unitIdeles : Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {δ | (∀ v : HeightOneSpectrum R,
      (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K) ∧
    ∀ v : HeightOneSpectrum R,
      ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈
        v.adicCompletionIntegers K}
  one_mem' := ⟨fun v => by rw [Units.val_one]; exact one_mem _,
              fun v => by rw [inv_one, Units.val_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨fun v => by rw [Units.val_mul]; exact mul_mem (hx1 v) (hy1 v),
           fun v => by rw [mul_inv, Units.val_mul]; exact mul_mem (hx2 v) (hy2 v)⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, fun v => by rw [inv_inv]; exact hx1 v⟩

/-- Membership in `unitIdeles` is integrality of the idele and its inverse
at every finite place. -/
public theorem mem_unitIdeles_iff (δ : (FiniteAdeleRing R K)ˣ) :
    δ ∈ unitIdeles R K ↔
      (∀ v : HeightOneSpectrum R,
        (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v : HeightOneSpectrum R,
          ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈
            v.adicCompletionIntegers K :=
  Iff.rfl

noncomputable section

private lemma far_mul_apply (x y : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (x * y) v = x v * y v := rfl

private lemma far_one_apply (v : HeightOneSpectrum R) : (1 : FiniteAdeleRing R K) v = 1 := rfl

private def evalAt (v : HeightOneSpectrum R) : (FiniteAdeleRing R K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (RestrictedProduct.evalRingHom _ v).toMonoidHom

@[scoped simp] private lemma evalAt_val (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    (evalAt R K v x : v.adicCompletion K) = (x : FiniteAdeleRing R K) v := rfl

private lemma valued_ne_zero (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    Valued.v ((x : FiniteAdeleRing R K) v) ≠ 0 := by
  rw [← evalAt_val]
  simp only [ne_eq, map_eq_zero]
  exact (evalAt R K v x).ne_zero

public def expAt (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) : ℤ :=
  -log (Valued.v ((x : FiniteAdeleRing R K) v))

private lemma expAt_one (v : HeightOneSpectrum R) : expAt R K v 1 = 0 := by
  rw [expAt, Units.val_one, far_one_apply, map_one, log_one, neg_zero]

private lemma expAt_mul (v : HeightOneSpectrum R) (x y : (FiniteAdeleRing R K)ˣ) :
    expAt R K v (x * y) = expAt R K v x + expAt R K v y := by
  simp only [expAt]
  rw [Units.val_mul, far_mul_apply, map_mul,
    log_mul (valued_ne_zero R K v x) (valued_ne_zero R K v y)]
  ring

private lemma expAt_inv (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    expAt R K v x⁻¹ = -expAt R K v x := by
  have h := expAt_mul R K v x x⁻¹
  rw [mul_inv_cancel, expAt_one] at h
  omega

private lemma expAt_eq_zero_iff (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    expAt R K v x = 0 ↔ Valued.v ((x : FiniteAdeleRing R K) v) = 1 := by
  rw [expAt, neg_eq_zero]
  constructor
  · intro h
    rw [← exp_log (valued_ne_zero R K v x), h, exp_zero]
  · intro h
    rw [h, log_one]

private lemma eq_one_of_mul_eq_one_of_le_one {a b : ℤᵐ⁰} (hab : a * b = 1)
    (ha : a ≤ 1) (hb : b ≤ 1) : a = 1 := by
  have hb1 : b = 1 := le_antisymm hb (by
    calc (1 : ℤᵐ⁰) = a * b := hab.symm
    _ ≤ 1 * b := by gcongr
    _ = b := one_mul b)
  rw [hb1, mul_one] at hab
  exact hab

private theorem expAt_eq_zero_of_integral {v : HeightOneSpectrum R} {x : (FiniteAdeleRing R K)ˣ}
    (hx : Valued.v ((x : FiniteAdeleRing R K) v) ≤ 1)
    (hxi : Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) ≤ 1) :
    expAt R K v x = 0 := by
  rw [expAt_eq_zero_iff]
  have hmul : Valued.v ((x : FiniteAdeleRing R K) v) *
      Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) = 1 := by
    rw [← map_mul, ← far_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      far_one_apply, map_one]
  exact eq_one_of_mul_eq_one_of_le_one hmul hx hxi

private theorem finite_support_expAt (x : (FiniteAdeleRing R K)ˣ) :
    {v : HeightOneSpectrum R | expAt R K v x ≠ 0}.Finite := by
  have hx : ∀ᶠ v in Filter.cofinite,
      (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K := (x : FiniteAdeleRing R K).2
  have hxi : ∀ᶠ v in Filter.cofinite,
      ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
    ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K).2
  have hboth := hx.and hxi
  rw [Filter.eventually_cofinite] at hboth
  refine hboth.subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  intro hcon
  exact hv (expAt_eq_zero_of_integral R K
    ((mem_adicCompletionIntegers R K v).mp hcon.1)
    ((mem_adicCompletionIntegers R K v).mp hcon.2))

omit [IsDedekindDomain R] in
private lemma coeIdeal_asIdeal_ne_zero (v : HeightOneSpectrum R) :
    (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot

private lemma zpow_asIdeal_ne_zero (v : HeightOneSpectrum R) (n : ℤ) :
    (v.asIdeal : FractionalIdeal R⁰ K) ^ n ≠ 0 :=
  zpow_ne_zero n (coeIdeal_asIdeal_ne_zero R K v)

private lemma mulSupport_zpow_subset (e : HeightOneSpectrum R → ℤ) :
    (Function.mulSupport fun v => (v.asIdeal : FractionalIdeal R⁰ K) ^ (e v)) ⊆
      {v | e v ≠ 0} := by
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  simp only [Set.mem_setOf_eq]
  intro h0
  exact hv (by rw [h0, zpow_zero])

public def assocIdeal (x : (FiniteAdeleRing R K)ˣ) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (expAt R K v x)

public lemma assocIdeal_ne_zero (x : (FiniteAdeleRing R K)ˣ) : assocIdeal R K x ≠ 0 := by
  rw [assocIdeal, finprod_eq_prod_of_mulSupport_subset _
    (s := (finite_support_expAt R K x).toFinset)
    (by simpa using mulSupport_zpow_subset R K _)]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_asIdeal_ne_zero R K v _

public theorem count_assocIdeal (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    FractionalIdeal.count K v (assocIdeal R K x) = expAt R K v x :=
  FractionalIdeal.count_finprod K v _ (Filter.eventually_cofinite.mpr
    (by simpa using finite_support_expAt R K x))

private theorem assocIdeal_mul (x y : (FiniteAdeleRing R K)ˣ) :
    assocIdeal R K (x * y) = assocIdeal R K x * assocIdeal R K y := by
  unfold assocIdeal
  rw [← finprod_mul_distrib
    ((finite_support_expAt R K x).subset (mulSupport_zpow_subset R K _))
    ((finite_support_expAt R K y).subset (mulSupport_zpow_subset R K _))]
  apply finprod_congr
  intro v
  rw [expAt_mul, zpow_add₀ (coeIdeal_asIdeal_ne_zero R K v)]

private theorem fractionalIdeal_eq_of_count_eq {I J : FractionalIdeal R⁰ K}
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J :=
  calc I = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
        (FractionalIdeal.count K v I) :=
      (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI).symm
  _ = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
        (FractionalIdeal.count K v J) := finprod_congr fun v => by rw [h v]
  _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ

public def contentHom : (FiniteAdeleRing R K)ˣ →* ClassGroup R where
  toFun x := ClassGroup.mk (K := K) (Units.mk0 (assocIdeal R K x) (assocIdeal_ne_zero R K x))
  map_one' := by
    have h1 : assocIdeal R K (1 : (FiniteAdeleRing R K)ˣ) = 1 := by
      unfold assocIdeal
      rw [finprod_eq_one_of_forall_eq_one]
      intro v
      rw [expAt_one, zpow_zero]
    rw [← map_one (ClassGroup.mk (R := R) (K := K))]
    congr 1
    exact Units.ext (by simpa using h1)
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    exact Units.ext (by simpa using assocIdeal_mul R K x y)

@[scoped simp] public lemma contentHom_apply (x : (FiniteAdeleRing R K)ˣ) :
    contentHom R K x =
      ClassGroup.mk (K := K)
        (Units.mk0 (assocIdeal R K x) (assocIdeal_ne_zero R K x)) :=
  rfl

private theorem count_spanSingleton_eq_neg_log_valuation (v : HeightOneSpectrum R) (u : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (u : K)) =
      -log (v.valuation K (u : K)) := by
  classical
  rw [← valuationOfNeZeroToFun_eq v u]
  set n : R := (IsLocalization.sec R⁰ (u : K)).1 with hn
  set d : ↥R⁰ := (IsLocalization.sec R⁰ (u : K)).2 with hd
  have hsec : (u : K) * algebraMap R K (d : R) = algebraMap R K n :=
    IsLocalization.sec_spec R⁰ (u : K)
  have hd0 : algebraMap R K (d : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have h_aJ : FractionalIdeal.spanSingleton R⁰ (u : K) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K (d : R)))⁻¹ * ↑(Ideal.span {n}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    field_simp
    linear_combination hsec
  rw [FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr u.ne_zero) h_aJ]
  show _ = -log ((valuationOfNeZeroToFun v u : Multiplicative ℤ) : ℤᵐ⁰)
  rw [valuationOfNeZeroToFun]
  simp only [← hn, ← hd]
  rw [show ((Multiplicative.ofAdd _ : Multiplicative ℤ) : ℤᵐ⁰) = exp _ from rfl, log_exp]
  ring

private lemma valued_coe_eq_valuation (v : HeightOneSpectrum R) (k : K) :
    Valued.v ((algebraMap K (FiniteAdeleRing R K) k) v) = v.valuation K k := by
  show Valued.v ((k : v.adicCompletion K)) = _
  exact valuedAdicCompletion_eq_valuation' v k

private theorem expAt_principal (v : HeightOneSpectrum R) (u : Kˣ) :
    expAt R K v (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u) =
      -log (v.valuation K (u : K)) := by
  unfold expAt
  rw [Units.coe_map, MonoidHom.coe_coe, valued_coe_eq_valuation]

private theorem contentHom_principal (u : Kˣ) :
    contentHom R K (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u)
      = 1 := by
  rw [contentHom_apply, ClassGroup.mk_eq_one_iff]
  have key : assocIdeal R K
      (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u) =
      FractionalIdeal.spanSingleton R⁰ (u : K) := by
    apply fractionalIdeal_eq_of_count_eq R K (assocIdeal_ne_zero R K _)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr u.ne_zero)
    intro v
    rw [count_assocIdeal, count_spanSingleton_eq_neg_log_valuation, expAt_principal]
  simp only [Units.val_mk0, key]
  rw [FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(u : K), rfl⟩⟩

private lemma expAt_eq_zero_of_mem_unitIdeles {x : (FiniteAdeleRing R K)ˣ} (h : x ∈ unitIdeles R K)
    (v : HeightOneSpectrum R) : expAt R K v x = 0 :=
  expAt_eq_zero_of_integral R K ((mem_adicCompletionIntegers R K v).mp (h.1 v))
    ((mem_adicCompletionIntegers R K v).mp (h.2 v))

private lemma mem_unitIdeles_of_expAt_eq_zero {x : (FiniteAdeleRing R K)ˣ}
    (h : ∀ v : HeightOneSpectrum R, expAt R K v x = 0) : x ∈ unitIdeles R K := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · exact (mem_adicCompletionIntegers R K v).mpr ((expAt_eq_zero_iff R K v x).mp (h v)).le
  · have h' : expAt R K v x⁻¹ = 0 := by rw [expAt_inv, h v, neg_zero]
    exact (mem_adicCompletionIntegers R K v).mpr ((expAt_eq_zero_iff R K v x⁻¹).mp h').le

public theorem contentHom_eq_one_of_mem_unitIdeles
    {x : (FiniteAdeleRing R K)ˣ} (h : x ∈ unitIdeles R K) :
    contentHom R K x = 1 := by
  have h1 : assocIdeal R K x = 1 := by
    unfold assocIdeal
    rw [finprod_eq_one_of_forall_eq_one]
    intro v
    rw [expAt_eq_zero_of_mem_unitIdeles R K h v, zpow_zero]
  rw [contentHom_apply, ← map_one (ClassGroup.mk (R := R) (K := K))]
  congr 1
  exact Units.ext (by simpa using h1)

public theorem ker_contentHom_eq :
    (contentHom R K).ker = unitIdeles R K ⊔
      (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)).range := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker, contentHom_apply, ClassGroup.mk_eq_one_iff] at hx
    obtain ⟨a, ha⟩ := hx.principal
    have ha' : assocIdeal R K x = FractionalIdeal.spanSingleton R⁰ a := by
      apply FractionalIdeal.coeToSubmodule_injective
      show (assocIdeal R K x : Submodule R K) = (FractionalIdeal.spanSingleton R⁰ a : Submodule R K)
      rw [FractionalIdeal.coe_spanSingleton]
      simpa using ha
    have ha0 : a ≠ 0 := by
      intro h0
      apply assocIdeal_ne_zero R K x
      rw [ha', h0, FractionalIdeal.spanSingleton_zero]
    set u : Kˣ := Units.mk0 a ha0 with hu
    set p : (FiniteAdeleRing R K)ˣ :=
      Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u with hp
    have hquot : x * p⁻¹ ∈ unitIdeles R K := by
      apply mem_unitIdeles_of_expAt_eq_zero
      intro v
      rw [expAt_mul, expAt_inv]
      have h1 : expAt R K v x = FractionalIdeal.count K v (assocIdeal R K x) :=
        (count_assocIdeal R K v x).symm
      have h2 : expAt R K v p = FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton R⁰ (u : K)) := by
        rw [hp, expAt_principal, count_spanSingleton_eq_neg_log_valuation]
      rw [h1, h2, ha']
      simp [hu]
    have hxp : x = (x * p⁻¹) * p := by group
    rw [hxp]
    exact Subgroup.mul_mem_sup hquot ⟨u, rfl⟩
  · rw [sup_le_iff]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      exact contentHom_eq_one_of_mem_unitIdeles R K hx
    · rintro _ ⟨u, rfl⟩
      rw [MonoidHom.mem_ker]
      exact contentHom_principal R K u

private lemma log_exp_neg_one_pow (n : ℕ) : log ((exp (-1 : ℤ)) ^ n) = -(n : ℤ) := by
  induction n with
  | zero => rw [pow_zero, log_one]; simp
  | succ n ih =>
    rw [pow_succ, log_mul (pow_ne_zero _ exp_ne_zero) exp_ne_zero, ih, log_exp]
    push_cast
    ring

public theorem contentHom_surjective : Function.Surjective (contentHom R K) := by
  classical
  intro c
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
  choose π hπ using fun v : HeightOneSpectrum R => valuation_exists_uniformizer K v
  set n : HeightOneSpectrum R → ℕ :=
    fun v => (FractionalIdeal.count K v (I : FractionalIdeal R⁰ K)).toNat with hn_def
  have hn : ∀ v, (n v : ℤ) = FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := fun v =>
    Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K v _)
  have hfin : ∀ᶠ v in Filter.cofinite, n v = 0 :=
    (FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K)).mono fun v hv => by
      simp [hn_def, hv]
  have hval : ∀ v : HeightOneSpectrum R,
      Valued.v ((algebraMap K (FiniteAdeleRing R K) (π v)) v) = exp (-1 : ℤ) := fun v => by
    rw [valued_coe_eq_valuation, hπ v]

  set a : (v : HeightOneSpectrum R) → v.adicCompletion K :=
    fun v => (algebraMap K (FiniteAdeleRing R K) (π v)) v with ha_def
  have hva : ∀ v, Valued.v (a v) = exp (-1 : ℤ) := fun v => hval v
  have ha0 : ∀ v, a v ≠ 0 := fun v => by
    intro h
    have := hva v
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  have hale : ∀ v, Valued.v (a v) ≤ 1 := fun v => by
    rw [hva v, ← exp_zero, exp_le_exp]
    norm_num
  let f : FiniteAdeleRing R K :=
    ⟨fun v => a v ^ n v, Filter.Eventually.of_forall fun v =>
      (mem_adicCompletionIntegers R K v).mpr (by
        rw [map_pow]
        exact pow_le_one₀ zero_le' (hale v))⟩
  let g : FiniteAdeleRing R K :=
    ⟨fun v => (a v)⁻¹ ^ n v, hfin.mono fun v hv => by
      simp only at hv ⊢
      rw [hv, pow_zero]
      exact one_mem _⟩
  have hfg : f * g = 1 := RestrictedProduct.ext _ _ fun v => by
    show a v ^ n v * (a v)⁻¹ ^ n v = 1
    rw [← mul_pow, mul_inv_cancel₀ (ha0 v), one_pow]
  have hgf : g * f = 1 := by rw [mul_comm]; exact hfg
  set j : (FiniteAdeleRing R K)ˣ := ⟨f, g, hfg, hgf⟩ with hj
  refine ⟨j, ?_⟩
  have hexp : ∀ w : HeightOneSpectrum R, expAt R K w j =
      FractionalIdeal.count K w (I : FractionalIdeal R⁰ K) := fun w => by
    rw [← hn w, expAt]
    show -log (Valued.v (a w ^ n w)) = _
    rw [map_pow, hva w, log_exp_neg_one_pow, neg_neg]
  have hassoc : assocIdeal R K j = (I : FractionalIdeal R⁰ K) := by
    apply fractionalIdeal_eq_of_count_eq R K (assocIdeal_ne_zero R K j)
      (FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero I))
    intro v
    rw [count_assocIdeal, hexp v]
  rw [contentHom_apply, ← hI, ← ClassGroup.mk_mk0 K]
  congr 1
  exact Units.ext (by simpa using hassoc)
end

/-- There is a surjective homomorphism from the units of the finite adele
ring to the class group whose kernel is generated by the integral unit
ideles and the principal ideles. The homomorphism sends a finite idele to
the class of its associated fractional ideal. -/
public theorem exists_monoidHom_units_classGroup_surjective_ker_eq :
    ∃ φ : (FiniteAdeleRing R K)ˣ →* ClassGroup R, Function.Surjective φ ∧
      φ.ker = unitIdeles R K ⊔
        (Units.map (algebraMap K (FiniteAdeleRing R K) : K →*
          FiniteAdeleRing R K)).range :=
  ⟨contentHom R K, contentHom_surjective R K, ker_contentHom_eq R K⟩

end FiniteAdeleRing
end IsDedekindDomain
