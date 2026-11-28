/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PowerSeries_nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq.lean`
and
`P2M/Sol/S_PowerSeries_nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq.lean`
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

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Fixed subalgebras of power series rings

The fixed subalgebra of `W⟦X⟧` under a finite group of `W`-algebra
automorphisms is `W`-algebra isomorphic to `W⟦X⟧` itself, when `W` is a
complete discrete valuation ring.
-/


set_option autoImplicit false

open PowerSeries

namespace PowerSeriesFixedAux

section general

variable {W : Type*} [CommRing W]

private theorem algHom_coe_polynomial (φ : W⟦X⟧ →ₐ[W] W⟦X⟧) (p : Polynomial W) :
    φ (p : W⟦X⟧) = Polynomial.aeval (φ X) p := by
  have key : (φ : W⟦X⟧ →+* W⟦X⟧).comp (Polynomial.coeToPowerSeries.ringHom (R := W)) =
      (Polynomial.aeval (R := W) (φ X) : Polynomial W →ₐ[W] W⟦X⟧) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
        C_eq_algebraMap, RingHom.coe_coe, AlgHom.commutes, Polynomial.aeval_C]
    · simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
        RingHom.coe_coe, Polynomial.aeval_X]
  have := congrArg (fun f : Polynomial W →+* W⟦X⟧ => f p) key
  simpa only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    RingHom.coe_coe] using this

private theorem algHom_ext_of_map_X_eq [IsNoetherianRing W] [IsLocalRing W]
    (φ ψ : W⟦X⟧ →ₐ[W] W⟦X⟧) (h : φ X = ψ X)
    (hm : φ X ∈ IsLocalRing.maximalIdeal W⟦X⟧) : φ = ψ := by
  apply AlgHom.ext
  intro f

  have key : ∀ N : ℕ, φ f - ψ f ∈ IsLocalRing.maximalIdeal W⟦X⟧ ^ N := by
    intro N
    set p : Polynomial W := trunc N f with hp
    obtain ⟨g, hg⟩ : (X : W⟦X⟧) ^ N ∣ f - (p : W⟦X⟧) := by
      rw [X_pow_dvd_iff]
      intro m hm'
      rw [map_sub, hp, Polynomial.coeff_coe, coeff_trunc, ite_eq_left hm', sub_self]
    have hf : f = (p : W⟦X⟧) + X ^ N * g := by rw [← hg]; ring
    have e : φ f - ψ f = φ X ^ N * (φ g - ψ g) := by
      rw [hf, map_add, map_add, algHom_coe_polynomial, algHom_coe_polynomial, h, map_mul, map_mul,
        map_pow,
        map_pow, h]
      ring
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hm N)
  have hmem : φ f - ψ f ∈ ⨅ N : ℕ, IsLocalRing.maximalIdeal W⟦X⟧ ^ N := Ideal.mem_iInf.mpr key
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _
    (IsLocalRing.maximalIdeal.isMaximal W⟦X⟧).ne_top] at hmem
  exact sub_eq_zero.mp hmem

private theorem mem_maximalIdeal_iff [IsLocalRing W] (f : W⟦X⟧) :
    f ∈ IsLocalRing.maximalIdeal W⟦X⟧ ↔ constantCoeff f ∈ IsLocalRing.maximalIdeal W := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff,
    isUnit_iff_constantCoeff]

private theorem constantCoeff_mem_and_coeff_one_notMem [IsLocalRing W] (τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) :
    constantCoeff (τ X) ∈ IsLocalRing.maximalIdeal W ∧ coeff 1
      (τ X) ∉ IsLocalRing.maximalIdeal W := by
  have hXm : ∀ ρ : W⟦X⟧ ≃ₐ[W] W⟦X⟧, constantCoeff (ρ X) ∈ IsLocalRing.maximalIdeal W := by
    intro ρ
    rw [← mem_maximalIdeal_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have : IsUnit (X : W⟦X⟧) := by simpa using hu.map ρ.symm
    rw [isUnit_iff_constantCoeff, constantCoeff_X] at this
    exact not_isUnit_zero this
  refine ⟨hXm τ, fun ha => ?_⟩

  have hC : ∀ a : W, τ (C a) = C a := fun a => by rw [C_eq_algebraMap, AlgEquiv.commutes]
  set k := IsLocalRing.ResidueField W
  let red : W⟦X⟧ →+* k⟦X⟧ := PowerSeries.map (IsLocalRing.residue W)

  obtain ⟨t, ht⟩ : (X : k⟦X⟧) ^ 2 ∣ red (τ X) := by
    rw [X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · rw [coeff_map, coeff_zero_eq_constantCoeff_apply, (IsLocalRing.residue_eq_zero_iff _).mpr
      (hXm τ)]
    · rw [coeff_map, (IsLocalRing.residue_eq_zero_iff _).mpr ha]
  set s := τ.symm X with hs
  have hsplit : s = C (coeff 0 s) + C (coeff 1 s) * X + X ^ 2 * (mk fun p => coeff (p + 2) s) := by
    ext n
    rw [map_add, map_add, coeff_C, coeff_C_mul, coeff_X, coeff_X_pow_mul']
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hn, coeff_mk, mul_zero,
        zero_add, zero_add, Nat.sub_add_cancel hn]
  have e1 : (X : W⟦X⟧) = C (coeff 0 s) + C (coeff 1 s) * τ X + τ X ^ 2 * τ (mk fun p => coeff (p +
    2) s) := by
    conv_lhs => rw [← τ.apply_symm_apply X, ← hs, hsplit]
    rw [map_add, map_add, map_mul, map_mul, map_pow, hC, hC]
  have e2 := congrArg (fun f => coeff 1 (red f)) e1
  simp only [map_add red, map_mul red, map_pow red, ht] at e2
  rw [show red X = X from map_X _, show ∀ a : W, red (C a) = C
    (IsLocalRing.residue W a) from fun a => map_C _ a,
    show ∀ a : W, red (C a) = C (IsLocalRing.residue W a) from fun a => map_C _ a,
      coeff_one_X] at e2

  have h3 : coeff 1 (C (IsLocalRing.residue W (coeff 0 s)) + C (IsLocalRing.residue W
    (coeff 1 s)) * (X ^ 2 * t) +
      (X ^ 2 * t) ^ 2 * red (τ (mk fun p => coeff (p + 2) s))) = (0 : k) := by
    have r1 : C (IsLocalRing.residue W (coeff 1 s)) * ((X : k⟦X⟧) ^ 2 * t) = X ^ 2 * (C
      (IsLocalRing.residue W (coeff 1 s)) * t) := by ring
    have r2 : ((X : k⟦X⟧) ^ 2 * t) ^ 2 * red (τ (mk fun p => coeff (p + 2) s)) =
        X ^ 2 * (X ^ 2 * t ^ 2 * red (τ (mk fun p => coeff (p + 2) s))) := by ring
    rw [r1, r2, map_add, map_add, coeff_C, ite_eq_right one_ne_zero, coeff_X_pow_mul',
      ite_eq_right (by omega), coeff_X_pow_mul', ite_eq_right (by omega)]
    ring
  rw [h3] at e2
  exact one_ne_zero e2

end general

section dvr

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  [IsAdicComplete (IsLocalRing.maximalIdeal W) W]

omit [IsAdicComplete (IsLocalRing.maximalIdeal W) W] in

private theorem one_le_order_toNat (u : W⟦X⟧) (hu0 : constantCoeff u = 0) (hu : u.map
  (IsLocalRing.residue W) ≠ 0) :
    1 ≤ (u.map (IsLocalRing.residue W)).order.toNat := by
  have h1 : (1 : ℕ∞) ≤ (u.map (IsLocalRing.residue W)).order := by
    refine nat_le_order _ _ fun i hi => ?_
    interval_cases i
    rw [coeff_map, coeff_zero_eq_constantCoeff_apply, hu0, map_zero]
  have hfin : (u.map (IsLocalRing.residue W)).order ≠ ⊤ := by rwa [ne_eq, order_eq_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hn, ENat.toNat_coe]
  rw [← hn] at h1
  exact_mod_cast h1

omit [IsAdicComplete (IsLocalRing.maximalIdeal W) W] in
private theorem subst_injective (u : W⟦X⟧) (hu0 : constantCoeff u = 0) (hu : u.map
  (IsLocalRing.residue W) ≠ 0) :
    Function.Injective fun c : W⟦X⟧ => c.subst u := by
  classical
  have ha : HasSubst u := HasSubst.of_constantCoeff_zero' hu0
  have hm := one_le_order_toNat u hu0 hu
  suffices key : ∀ c : W⟦X⟧, c.subst u = 0 → c = 0 by
    intro c c' h
    have := key (c - c') (by rw [subst_sub ha]; exact sub_eq_zero.mpr h)
    exact sub_eq_zero.mp this
  intro c hc
  by_contra hne
  have hex : ∃ j, coeff j c ≠ 0 := by
    by_contra h0
    push Not at h0
    exact hne (PowerSeries.ext fun j => by rw [h0 j, map_zero])
  obtain ⟨j, hj, hlt⟩ : ∃ j, coeff j c ≠ 0 ∧ ∀ i < j, coeff i c = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => by
      have := Nat.find_min hex hi; push Not at this; exact this⟩
  obtain ⟨q, hq⟩ := (X_pow_dvd_iff (φ := c)).mpr hlt
  set w : W := coeff j c with hw
  have hqw : coeff 0 q = w := by
    have e := coeff_X_pow_mul q j 0
    rw [zero_add] at e
    rw [hw, hq, e]
  set q₁ : W⟦X⟧ := mk fun p => coeff (p + 1) q
  have hq' : q = X * q₁ + C w := by
    rw [← hqw, coeff_zero_eq_constantCoeff_apply]
    exact eq_X_mul_shift_add_const q
  have hu_ne : u ≠ 0 := by rintro rfl; exact hu (by simp)
  have e1 : c.subst u = u ^ j * (u * q₁.subst u + C w) := by
    rw [hq, hq', subst_mul ha, subst_pow ha, subst_X ha, subst_add ha, subst_mul ha, subst_X ha,
      subst_C]
    rfl
  rw [e1] at hc
  have e2 : u * q₁.subst u + C w = 0 := (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ hu_ne)
  have hdeg : (Polynomial.C w).degree < (u.map (IsLocalRing.residue W)).order.toNat := by
    refine (Polynomial.degree_C_le).trans_lt ?_
    exact_mod_cast hm
  have H1 : IsWeierstrassDivision (C w : W⟦X⟧) u 0 (Polynomial.C w) :=
    ⟨hdeg, by rw [mul_zero, zero_add, Polynomial.coe_C]⟩
  have H2 : IsWeierstrassDivision (C w : W⟦X⟧) u (-(q₁.subst u)) 0 := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · rw [Polynomial.coe_zero, add_zero]; linear_combination e2
  have := (H1.elim hu H2).2
  rw [Polynomial.C_eq_zero] at this
  exact hj this

private theorem exists_sum_subst_mul_X_pow (u : W⟦X⟧) (hu0 : constantCoeff u = 0) (m : ℕ)
    (hum : ∀ i < m, coeff i u ∈ IsLocalRing.maximalIdeal W)
      (hm : coeff m u ∉ IsLocalRing.maximalIdeal W)
    (f : W⟦X⟧) :
    ∃ c : Fin m → W⟦X⟧, f = ∑ i : Fin m, (c i).subst u * X ^ (i : ℕ) := by
  classical

  have hres_coeff : ∀ i, coeff i (u.map (IsLocalRing.residue W)) = IsLocalRing.residue W
    (coeff i u) := fun i =>
    coeff_map _ _ _
  have hres : u.map (IsLocalRing.residue W) ≠ 0 := by
    intro h
    apply hm
    have := congrArg (coeff m) h
    rw [hres_coeff, map_zero] at this
    exact (IsLocalRing.residue_eq_zero_iff _).1 this
  have hord : (u.map (IsLocalRing.residue W)).order = m := by
    apply order_eq_nat.2
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hres_coeff]; exact fun h => hm ((IsLocalRing.residue_eq_zero_iff _).1 h)
    · rw [hres_coeff]; exact (IsLocalRing.residue_eq_zero_iff _).2 (hum i hi)
  have hordn : (u.map (IsLocalRing.residue W)).order.toNat = m := by rw [hord]; rfl
  have hus : HasSubst u := HasSubst.of_constantCoeff_zero' hu0

  have hu_ord : 1 ≤ u.order := by
    apply nat_le_order
    intro i hi
    interval_cases i
    simpa using hu0
  have hpow : ∀ (d n : ℕ), n < d → coeff n (u ^ d) = 0 := by
    intro d n hnd
    apply coeff_of_lt_order
    calc (n : ℕ∞) < d := by exact_mod_cast hnd
      _ = d • (1 : ℕ∞) := by simp
      _ ≤ d • u.order := by exact nsmul_le_nsmul_right hu_ord d
      _ ≤ (u ^ d).order := le_order_pow u d

  let q : ℕ → W⟦X⟧ := fun k => (fun g => g /ʷ u)^[k] f
  let r : ℕ → Polynomial W := fun k => q k %ʷ u
  have hq0 : q 0 = f := rfl
  have hstep : ∀ k, q k = u * q (k + 1) + (r k : W⟦X⟧) := fun k => by
    show q k = u * ((fun g => g /ʷ u)^[k + 1] f) + _
    rw [Function.iterate_succ_apply']
    exact eq_mul_weierstrassDiv_add_weierstrassMod (q k) hres
  have hpartial : ∀ K, f = (∑ k ∈ Finset.range K, (r k : W⟦X⟧) * u ^ k) + q K * u ^ K := by
    intro K
    induction K with
    | zero => simp [hq0]
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, hstep K]
      ring
  have hdeg : ∀ k i, m ≤ i → (r k).coeff i = 0 := by
    intro k i hi
    apply Polynomial.coeff_eq_zero_of_degree_lt
    calc (r k).degree < ((u.map (IsLocalRing.residue W)).order.toNat : WithBot ℕ) :=
        degree_weierstrassMod_lt (q k) u
      _ = m := by rw [hordn]
      _ ≤ i := by exact_mod_cast hi

  have hr_sum : ∀ k, (r k : W⟦X⟧) = ∑ i : Fin m, (r k).coeff i • X ^ (i : ℕ) := by
    intro k
    ext n
    rw [Polynomial.coeff_coe, map_sum]
    simp only [coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hn : n < m
    · rw [Finset.sum_eq_single (⟨n, hn⟩ : Fin m)]
      · simp
      · intro b _ hb
        rw [ite_eq_right]
        intro h; apply hb; exact Fin.ext h.symm
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [hdeg k n (not_lt.1 hn)]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [ite_eq_right]
      intro h; exact hn (h ▸ i.2)

  let c : Fin m → W⟦X⟧ := fun i => PowerSeries.mk fun k => (r k).coeff i
  refine ⟨c, ?_⟩

  have htrunc_subst : ∀ (K : ℕ) (i : Fin m), 0 < K →
      ((trunc K (c i) : Polynomial W) : W⟦X⟧).subst u = ∑ k ∈ Finset.range K,
        (r k).coeff i • u ^ k := by
    intro K i hK
    obtain ⟨K', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
    rw [subst_coe hus, Polynomial.aeval_eq_sum_range' (natDegree_trunc_lt (c i) K')]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [coeff_trunc, ite_eq_left (Finset.mem_range.1 hk), coeff_mk]
  have hSK : ∀ K, 0 < K → ∑ i : Fin m, ((trunc K (c i) : Polynomial W) : W⟦X⟧).subst u * X ^
    (i : ℕ) = f - q K * u ^ K := by
    intro K hK
    rw [eq_sub_iff_add_eq]
    conv_rhs => rw [hpartial K]
    rw [add_left_inj]
    rw [Finset.sum_congr rfl (fun i _ => by rw [htrunc_subst K i hK, Finset.sum_mul]),
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hr_sum k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, mul_comm]

  have hcoeff_trunc : ∀ (n j : ℕ) (i : Fin m), j ≤ n →
      coeff j ((c i).subst u) = coeff j (((trunc (n + 1)
        (c i) : Polynomial W) : W⟦X⟧).subst u) := by
    intro n j i hj
    rw [coeff_subst' hus, coeff_subst' hus]
    refine finsum_congr fun d => ?_
    by_cases hd : d < n + 1
    · rw [Polynomial.coeff_coe, coeff_trunc, ite_eq_left hd]
    · rw [hpow d j (by omega), smul_zero, smul_zero]
  ext n
  have h1 : coeff n (∑ i : Fin m, (c i).subst u * X ^ (i : ℕ)) =
      coeff n (∑ i : Fin m, ((trunc (n + 1) (c i) : Polynomial W) : W⟦X⟧).subst u * X ^
        (i : ℕ)) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_mul_X_pow', coeff_mul_X_pow']
    split_ifs with hi
    · exact hcoeff_trunc n (n - i) i (Nat.sub_le n i)
    · rfl
  rw [h1, hSK (n + 1) (Nat.succ_pos n), map_sub, coeff_mul_of_lt_order, sub_zero]
  calc (n : ℕ∞) < (n + 1 : ℕ) := by exact_mod_cast Nat.lt_succ_self n
    _ = (n + 1) • (1 : ℕ∞) := by simp
    _ ≤ (n + 1) • u.order := nsmul_le_nsmul_right hu_ord (n + 1)
    _ ≤ (u ^ (n + 1)).order := le_order_pow u (n + 1)

private theorem exists_sum_subst_mul_X_pow_range
    (u : W⟦X⟧) (hu0 : constantCoeff u = 0) (hu : u.map (IsLocalRing.residue W) ≠ 0) (f : W⟦X⟧) :
    ∃ c : ℕ → W⟦X⟧,
      f = ∑ i ∈ Finset.range (u.map (IsLocalRing.residue W)).order.toNat, (c i).subst u *
        X ^ i := by
  classical
  set m : ℕ := (u.map (IsLocalRing.residue W)).order.toNat with hm
  have hfin : (u.map (IsLocalRing.residue W)).order ≠ ⊤ := by rwa [ne_eq, order_eq_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hmn : m = n := by rw [hm, ← hn, ENat.toNat_coe]
  have hord := order_eq_nat.mp hn.symm
  have hum : ∀ i < m, coeff i u ∈ IsLocalRing.maximalIdeal W := fun i hi => by
    rw [← IsLocalRing.residue_eq_zero_iff, ← coeff_map]
    exact hord.2 i (hmn ▸ hi)
  have hmm : coeff m u ∉ IsLocalRing.maximalIdeal W := by
    rw [← IsLocalRing.residue_eq_zero_iff, ← coeff_map, hmn]
    exact hord.1
  obtain ⟨c, hc⟩ := exists_sum_subst_mul_X_pow u hu0 m hum hmm f
  refine ⟨fun i => if h : i < m then c ⟨i, h⟩ else 0, ?_⟩
  rw [hc, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp only [dite_eq_left i.2]

end dvr

end PowerSeriesFixedAux

/-- The fixed subalgebra of `W⟦X⟧` under a finite group of `W`-algebra
automorphisms is `W`-algebra isomorphic to `W⟦X⟧`, for `W` a complete
discrete valuation ring. The group action need not be faithful, and the
subalgebra is required to be exactly the fixed points. -/
theorem PowerSeries.nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq
    (W : Type*) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (G : Type*) [Group G] [Finite G]
    (σ : G →* (PowerSeries W ≃ₐ[W] PowerSeries W))
    (S : Subalgebra W (PowerSeries W)) (hS : ∀ f : PowerSeries W, f ∈ S ↔ ∀ g : G, σ g f = f) :
    Nonempty (PowerSeries W ≃ₐ[W] ↥S) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G

  set Gb : Subgroup (W⟦X⟧ ≃ₐ[W] W⟦X⟧) := σ.range with hGb
  haveI : Finite Gb := Finite.of_surjective (fun g : G => (⟨σ g, g, rfl⟩ : Gb)) (by
    rintro ⟨_, g, rfl⟩; exact ⟨g, rfl⟩)
  haveI : Fintype Gb := Fintype.ofFinite Gb
  have hmemS : ∀ f : W⟦X⟧, f ∈ S ↔ ∀ τ : Gb, (τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) f = f := by
    intro f
    rw [hS]
    constructor
    · rintro h ⟨_, g, rfl⟩; exact h g
    · intro h g; exact h ⟨σ g, g, rfl⟩
  have hLOC := fun τ : Gb => PowerSeriesFixedAux.constantCoeff_mem_and_coeff_one_notMem
    (τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧)
  have hC : ∀ (τ : Gb) (a : W), (τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) (C a) = C a := fun τ a => by
    rw [C_eq_algebraMap, AlgEquiv.commutes]

  set u₀ : W⟦X⟧ := ∏ τ : Gb, (τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) X with hu₀
  set u : W⟦X⟧ := u₀ - C (constantCoeff u₀) with hu_def
  have hu0 : constantCoeff u = 0 := by rw [hu_def, map_sub, constantCoeff_C, sub_self]
  have hτu : ∀ τ : Gb, (τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) u = u := by
    intro τ
    have e : (τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) u₀ = u₀ := by
      rw [hu₀, map_prod]
      exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun ρ => by
        rw [Equiv.coe_mulLeft, Subgroup.coe_mul, AlgEquiv.mul_apply]
    rw [hu_def, map_sub, e, hC]
  have huS : u ∈ S := (hmemS u).mpr hτu

  set k := IsLocalRing.ResidueField W with hk
  set red : W⟦X⟧ →+* k⟦X⟧ := PowerSeries.map (IsLocalRing.residue W) with hred_def
  set v : Gb → k⟦X⟧ := fun τ => mk fun p => coeff (p + 1) (red ((τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) X)) with hv
  have hredτ : ∀ τ : Gb, red ((τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) X) = X * v τ := by
    intro τ
    have h0 : constantCoeff (red ((τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) X)) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, hred_def, coeff_map,
        coeff_zero_eq_constantCoeff_apply,
        (IsLocalRing.residue_eq_zero_iff _).mpr (hLOC τ).1]
    conv_lhs => rw [eq_X_mul_shift_add_const (red ((τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) X)), h0, map_zero,
      add_zero]
  have hvτ : ∀ τ : Gb, constantCoeff (v τ) ≠ 0 := by
    intro τ
    rw [← coeff_zero_eq_constantCoeff_apply, hv, coeff_mk, zero_add, hred_def, coeff_map, ne_eq,
      IsLocalRing.residue_eq_zero_iff]
    exact (hLOC τ).2
  set V : k⟦X⟧ := ∏ τ : Gb, v τ with hV_def
  have hV : constantCoeff V ≠ 0 := by
    rw [hV_def, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => hvτ τ
  set m : ℕ := Fintype.card Gb with hm
  have hm1 : 1 ≤ m := Fintype.card_pos
  have hred0 : red u₀ = X ^ m * V := by
    rw [hu₀, map_prod]
    simp_rw [hredτ]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hred : u.map (IsLocalRing.residue W) = X ^ m * V := by
    change red u = X ^ m * V
    have hc : IsLocalRing.residue W (constantCoeff u₀) = 0 := by
      have := congrArg constantCoeff hred0
      rw [← coeff_zero_eq_constantCoeff_apply, hred_def, coeff_map,
        coeff_zero_eq_constantCoeff_apply] at this
      rw [this, ← coeff_zero_eq_constantCoeff_apply, coeff_X_pow_mul', ite_eq_right (by omega)]
    rw [hu_def, map_sub, hred0, hred_def, map_C, hc, map_zero, sub_zero]
  have hu_ne : u.map (IsLocalRing.residue W) ≠ 0 := by
    rw [hred]
    refine mul_ne_zero (pow_ne_zero _ X_ne_zero) fun h => hV ?_
    rw [h, map_zero]
  have horder : (u.map (IsLocalRing.residue W)).order.toNat = m := by
    rw [hred]
    have hord : (X ^ m * V).order = (m : ℕ∞) := by
      refine order_eq_nat.mpr ⟨?_, fun i hi => ?_⟩
      · have e := coeff_X_pow_mul V m 0
        rw [zero_add] at e
        rw [e, coeff_zero_eq_constantCoeff_apply]
        exact hV
      · rw [coeff_X_pow_mul', ite_eq_right (by omega)]
    rw [hord, ENat.toNat_coe]

  have ha : HasSubst u := HasSubst.of_constantCoeff_zero' hu0
  let Φ : W⟦X⟧ →ₐ[W] W⟦X⟧ := substAlgHom ha
  have hΦ : ∀ c : W⟦X⟧, Φ c = c.subst u := fun c => congrFun (coe_substAlgHom ha) c
  have hΦX : Φ X = u := substAlgHom_X ha
  have hum : u ∈ IsLocalRing.maximalIdeal W⟦X⟧ :=
    (PowerSeriesFixedAux.mem_maximalIdeal_iff u).mpr (by rw [hu0]; exact zero_mem _)

  have hΦS : ∀ c : W⟦X⟧, Φ c ∈ S := by
    intro c
    rw [hmemS]
    intro τ
    have e := PowerSeriesFixedAux.algHom_ext_of_map_X_eq
      (((τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) : W⟦X⟧ →ₐ[W] W⟦X⟧).comp Φ) Φ
      (by rw [AlgHom.comp_apply, hΦX, AlgEquiv.coe_algHom]; exact hτu τ)
      (by rw [AlgHom.comp_apply, hΦX, AlgEquiv.coe_algHom, hτu τ]; exact hum)
    exact AlgHom.congr_fun e c

  have hinjX : Function.Injective fun τ : Gb => (τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) X := by
    intro τ₁ τ₂ h12
    have e := PowerSeriesFixedAux.algHom_ext_of_map_X_eq ((τ₁ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) : W⟦X⟧ →ₐ[W] W⟦X⟧)
      ((τ₂ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) : W⟦X⟧ →ₐ[W] W⟦X⟧) h12
      ((PowerSeriesFixedAux.mem_maximalIdeal_iff _).mpr (hLOC τ₁).1)
    exact Subtype.ext (AlgEquiv.ext fun f => AlgHom.congr_fun e f)

  have hsurj : ∀ s ∈ S, ∃ c : W⟦X⟧, Φ c = s := by
    intro s hs
    obtain ⟨c, hc⟩ := PowerSeriesFixedAux.exists_sum_subst_mul_X_pow_range u hu0 hu_ne s
    rw [horder] at hc
    refine ⟨c 0, ?_⟩
    set P : Polynomial W⟦X⟧ :=
      ∑ i ∈ Finset.range m, Polynomial.C (Φ (c i)) * Polynomial.X ^ i - Polynomial.C s with hP
    have heval : ∀ τ : Gb, P.eval ((τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) X) = 0 := by
      intro τ
      have e1 : (τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) (∑ i ∈ Finset.range m, Φ (c i) * X ^ i) =
          ∑ i ∈ Finset.range m, Φ (c i) * (τ : W⟦X⟧ ≃ₐ[W] W⟦X⟧) X ^ i := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_pow, ((hmemS _).mp (hΦS (c i))) τ]
      have e2 : ∑ i ∈ Finset.range m, Φ (c i) * X ^ i = s := by
        rw [hc]
        exact Finset.sum_congr rfl fun i _ => by rw [hΦ]
      rw [hP, Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_C]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← e1, e2, ((hmemS s).mp hs) τ, sub_self]
    have hPdeg : P.natDegree < m := by
      rw [hP]
      refine (Polynomial.natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · refine Nat.lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _
        (n := m - 1) fun i hi => ?_) (by omega)
        exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by
          have := Finset.mem_range.mp hi; omega)
      · rw [Polynomial.natDegree_C]; exact hm1
    have hP0 : P = 0 :=
      Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinjX heval
        (lt_of_lt_of_eq hPdeg hm)
    have h0 := congrArg (fun Q : Polynomial W⟦X⟧ => Q.coeff 0) hP0
    simp only [hP, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_zero, Polynomial.coeff_zero] at h0
    rw [Finset.sum_ite_eq (Finset.range m) 0 (fun i => Φ (c i)), ite_eq_left
      (Finset.mem_range.mpr hm1)] at h0
    exact sub_eq_zero.mp h0

  have hinj : Function.Injective Φ := by
    intro a b h
    apply PowerSeriesFixedAux.subst_injective u hu0 hu_ne
    simp only [← hΦ]
    exact h
  refine ⟨AlgEquiv.ofBijective (Φ.codRestrict S hΦS) ⟨fun a b h => hinj ?_, fun s => ?_⟩⟩
  · exact congrArg Subtype.val h
  · obtain ⟨c, hc⟩ := hsurj s.1 s.2
    exact ⟨c, Subtype.ext hc⟩
