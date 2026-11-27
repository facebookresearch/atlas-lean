/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_X0.lean`,
`Theorems/Thm_ModularCurve_one_le_coeff_jq.lean`
and
`P2M/Sol/S_ModularCurve_one_le_coeff_jq.lean`
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

public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

noncomputable section

open scoped PowerSeries.WithPiTopology

open PowerSeries HahnSeries

namespace ModularCurve


public def eisenstein4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3

@[simp]
public theorem constantCoeff_eisenstein4 : PowerSeries.constantCoeff eisenstein4 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [eisenstein4]

public def etaProd : PowerSeries ℤ :=
  ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))

public theorem constantCoeff_etaProd : PowerSeries.constantCoeff etaProd = 1 := by
  rw [etaProd]
  simp [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod _
    (PowerSeries.WithPiTopology.continuous_constantCoeff ℤ)]

public def dedekindEtaUnit : PowerSeries ℤ := etaProd ^ 24

public theorem constantCoeff_dedekindEtaUnit : PowerSeries.constantCoeff dedekindEtaUnit = 1 := by
  rw [dedekindEtaUnit, map_pow, constantCoeff_etaProd, one_pow]

public def dedekindEtaUnitInv : PowerSeries ℤ := dedekindEtaUnit.invOfUnit 1

public theorem dedekindEtaUnit_mul_inv : dedekindEtaUnit * dedekindEtaUnitInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_dedekindEtaUnit]; rfl)

public theorem constantCoeff_dedekindEtaUnitInv :
    PowerSeries.constantCoeff dedekindEtaUnitInv = 1 := by
  have h := congrArg (PowerSeries.constantCoeff (R := ℤ)) dedekindEtaUnit_mul_inv
  rwa [map_mul, constantCoeff_dedekindEtaUnit, one_mul, map_one] at h

public def jNum : PowerSeries ℤ := eisenstein4 ^ 3 * dedekindEtaUnitInv

@[simp]
public theorem constantCoeff_jNum : PowerSeries.constantCoeff jNum = 1 := by
  rw [jNum, map_mul, map_pow, constantCoeff_eisenstein4, constantCoeff_dedekindEtaUnitInv,
    one_pow, one_mul]

public def jNumQ : PowerSeries ℚ := jNum.map (Int.castRingHom ℚ)

@[simp]
public theorem constantCoeff_jNumQ : PowerSeries.constantCoeff jNumQ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, jNumQ, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum]
  simp

public def jq : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ

private theorem ofPowerSeries_coeff_of_neg {R : Type*} [Semiring R] (f : PowerSeries R) {k : ℤ}
    (hk : k < 0) : (HahnSeries.ofPowerSeries ℤ R f).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact absurd hk (not_lt.mpr (Int.natCast_nonneg m))

public theorem jq_pow (n : ℕ) :
    jq ^ n = HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℚ (jNumQ ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jq, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

public theorem coeff_jq_pow_self (n : ℕ) : (jq ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNumQ, one_pow]

public theorem coeff_jq_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : (jq ^ n).coeff m = 0 := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

@[simp]
public theorem coeff_jq_neg_one : jq.coeff (-1 : ℤ) = 1 := by
  have h := coeff_jq_pow_self 1
  simpa using h

public theorem coeff_jq_of_lt {k : ℤ} (hk : k < -1) : jq.coeff k = 0 := by
  have h := coeff_jq_pow_of_lt (n := 1) (m := k) (by simpa using hk)
  simpa using h

public theorem jq_ne_zero : jq ≠ 0 := fun h => by simpa [h] using coeff_jq_neg_one


private theorem coeff_one_sub_X_pow_of_lt {R : Type*} [CommRing R] {e m : ℕ} (h : m < e) :
    PowerSeries.coeff m ((1 : PowerSeries R) - X ^ e) = if m = 0 then 1 else 0 := by
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow, if_neg (Nat.ne_of_lt h),
    sub_zero]

private theorem coeff_prod_one_sub_X_pow_eq_coeff_one {R : Type*} [CommRing R]
    {ι : Type*} [DecidableEq ι] {n : ℕ} (s : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ s, n < e i) :
    ∀ m ≤ n, PowerSeries.coeff m (∏ i ∈ s, ((1 : PowerSeries R) - X ^ e i)) =
      if m = 0 then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m _; simp [PowerSeries.coeff_one]
  | @insert a s ha ih =>
    intro m hm
    rw [Finset.prod_insert ha, PowerSeries.coeff_mul]
    have hea : n < e a := he a (Finset.mem_insert_self a s)
    have hsum :
        ∀ p ∈ Finset.HasAntidiagonal.antidiagonal m,
          PowerSeries.coeff p.1 ((1 : PowerSeries R) - X ^ e a) *
              PowerSeries.coeff p.2 (∏ i ∈ s, ((1 : PowerSeries R) - X ^ e i)) =
            if p.1 = 0 then
              PowerSeries.coeff p.2 (∏ i ∈ s, ((1 : PowerSeries R) - X ^ e i)) else 0 := by
      intro p hp
      have hp1 : p.1 ≤ m := Finset.HasAntidiagonal.antidiagonal.fst_le hp
      rw [coeff_one_sub_X_pow_of_lt (lt_of_le_of_lt (le_trans hp1 hm) hea)]
      by_cases h0 : p.1 = 0
      · rw [if_pos h0, if_pos h0, one_mul]
      · rw [if_neg h0, if_neg h0, zero_mul]
    rw [Finset.sum_congr rfl hsum]
    rw [Finset.sum_eq_single_of_mem (0, m) (by simp)]
    · rw [if_pos rfl]
      exact ih (fun i hi => he i (Finset.mem_insert_of_mem hi)) m hm
    · rintro ⟨b₁, b₂⟩ hb hne
      have hb' : b₁ + b₂ = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      have : b₁ ≠ 0 := by
        rintro rfl
        exact hne (by simp [← hb'])
      rw [if_neg this]

private theorem coeff_prod_one_sub_pow_le {R : Type*} [CommRing R] (k n : ℕ) (h : n ≤ k) :
    PowerSeries.coeff n
        (∏ i ∈ Finset.range (k + 1), ((1 : PowerSeries R) - X ^ (i + 1))) =
      PowerSeries.coeff n
        (∏ i ∈ Finset.range (n + 1), ((1 : PowerSeries R) - X ^ (i + 1))) := by
  classical
  have hsplit :
      (∏ i ∈ Finset.range (k + 1), ((1 : PowerSeries R) - X ^ (i + 1))) =
        (∏ i ∈ Finset.range (n + 1), ((1 : PowerSeries R) - X ^ (i + 1))) *
          ∏ i ∈ Finset.Ico (n + 1) (k + 1), ((1 : PowerSeries R) - X ^ (i + 1)) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.prod_Ico_consecutive _ (Nat.zero_le _) (Nat.succ_le_succ h)]
  rw [hsplit, PowerSeries.coeff_mul]
  have htail : ∀ m ≤ n,
      PowerSeries.coeff m
          (∏ i ∈ Finset.Ico (n + 1) (k + 1), ((1 : PowerSeries R) - X ^ (i + 1))) =
        if m = 0 then 1 else 0 := by
    refine coeff_prod_one_sub_X_pow_eq_coeff_one _ _ ?_
    intro i hi
    have : n + 1 ≤ i := (Finset.mem_Ico.mp hi).1
    omega
  rw [Finset.sum_eq_single_of_mem (n, 0) (by simp)]
  · rw [htail 0 (Nat.zero_le n), if_pos rfl, mul_one]
  · rintro ⟨b₁, b₂⟩ hb hne
    have hb' : b₁ + b₂ = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    have hb₂ : b₂ ≤ n := Finset.HasAntidiagonal.antidiagonal.snd_le hb
    have : b₂ ≠ 0 := by
      rintro rfl
      exact hne (by simp [← hb'])
    rw [htail b₂ hb₂, if_neg this, mul_zero]

private theorem coeff_etaProd_eq_coeff_partialProd (n : ℕ) :
    PowerSeries.coeff n etaProd =
      PowerSeries.coeff n
        (∏ i ∈ Finset.range (n + 1), (1 - X ^ (i + 1) : PowerSeries ℤ)) := by
  classical
  have hconv : Filter.Tendsto
      (fun s : Finset ℕ =>
        PowerSeries.coeff n (∏ i ∈ s, (1 - X ^ (i + 1) : PowerSeries ℤ)))
      Filter.atTop (nhds (PowerSeries.coeff n etaProd)) := by
    have h0 : Filter.Tendsto
        (fun s : Finset ℕ => ∏ i ∈ s, (1 - X ^ (i + 1) : PowerSeries ℤ))
        Filter.atTop (nhds etaProd) :=
      (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd
    exact (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mp h0 n
  rw [show nhds (PowerSeries.coeff n etaProd) = pure (PowerSeries.coeff n etaProd) from
      congrFun (nhds_discrete ℤ) _,
    Filter.tendsto_pure] at hconv
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp hconv
  rw [← ht₀ (t₀ ∪ Finset.range (n + 1)) Finset.subset_union_left]
  rw [show t₀ ∪ Finset.range (n + 1)
        = Finset.range (n + 1) ∪ (t₀ \ Finset.range (n + 1)) by
      rw [Finset.union_sdiff_self_eq_union, Finset.union_comm],
    Finset.prod_union Finset.disjoint_sdiff, PowerSeries.coeff_mul]
  have htail : ∀ m ≤ n,
      PowerSeries.coeff m
          (∏ i ∈ t₀ \ Finset.range (n + 1), (1 - X ^ (i + 1) : PowerSeries ℤ)) =
        if m = 0 then 1 else 0 := by
    refine coeff_prod_one_sub_X_pow_eq_coeff_one _ _ (fun i hi => ?_)
    have hi' : ¬ i < n + 1 := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_range.mpr h)
    omega
  rw [Finset.sum_eq_single_of_mem (n, 0) (by simp)]
  · rw [htail 0 (Nat.zero_le n), if_pos rfl, mul_one]
  · rintro ⟨b₁, b₂⟩ hb hne
    have hb' : b₁ + b₂ = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    have hb₂ : b₂ ≤ n := Finset.HasAntidiagonal.antidiagonal.snd_le hb
    have h2 : b₂ ≠ 0 := by
      rintro rfl
      exact hne (by simp [← hb'])
    rw [htail b₂ hb₂, if_neg h2, mul_zero]

private theorem coeff_jq_eq_coeff_jNum (n : ℕ) :
    jq.coeff ((n : ℤ) - 1) = ((PowerSeries.coeff n jNum : ℤ) : ℚ) := by
  rw [jq, HahnSeries.coeff_single_mul, one_mul,
    show ((n : ℤ) - 1 - (-1) : ℤ) = ((n : ℕ) : ℤ) by ring,
    HahnSeries.ofPowerSeries_apply_coeff, jNumQ, PowerSeries.coeff_map]
  simp

private def geomSeries (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => if d ∣ k then 1 else 0

@[scoped simp]
private theorem coeff_geomSeries (d k : ℕ) :
    PowerSeries.coeff k (geomSeries d) = if d ∣ k then 1 else 0 := by
  rw [geomSeries, PowerSeries.coeff_mk]

@[scoped simp]
private theorem constantCoeff_geomSeries (d : ℕ) :
    PowerSeries.constantCoeff (geomSeries d) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_geomSeries, if_pos (dvd_zero d)]

private theorem coeff_geomSeries_nonneg (d k : ℕ) :
    0 ≤ PowerSeries.coeff k (geomSeries d) := by
  rw [coeff_geomSeries]
  split <;> norm_num

private theorem coeff_geomSeries_one (k : ℕ) :
    PowerSeries.coeff k (geomSeries 1) = 1 := by
  rw [coeff_geomSeries, if_pos (one_dvd k)]

private theorem one_sub_X_pow_mul_geomSeries {d : ℕ} (hd : d ≠ 0) :
    ((1 : PowerSeries ℤ) - X ^ d) * geomSeries d = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, ← mul_comm (geomSeries d) (X ^ d),
    PowerSeries.coeff_mul_X_pow', coeff_geomSeries, PowerSeries.coeff_one]
  by_cases hdn : d ≤ n
  ·
    have hn0 : ¬ (n = 0) := by omega
    rw [if_pos hdn, coeff_geomSeries, if_neg hn0]
    have hiff : d ∣ n ↔ d ∣ n - d := by
      constructor
      · intro h; exact Nat.dvd_sub h dvd_rfl
      · intro h
        have := Nat.dvd_add h (dvd_refl d)
        rwa [Nat.sub_add_cancel hdn] at this
    by_cases h : d ∣ n
    · rw [if_pos h, if_pos (hiff.mp h), sub_self]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc)), sub_self]
  ·
    rw [if_neg hdn, sub_zero]
    by_cases hn : n = 0
    · subst hn; rw [if_pos (dvd_zero d), if_pos rfl]
    · rw [if_neg hn, if_neg (fun hc => hdn (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hc))]

private theorem coeff_mul_nonneg {f g : PowerSeries ℤ}
    (hf : ∀ k, 0 ≤ PowerSeries.coeff k f) (hg : ∀ k, 0 ≤ PowerSeries.coeff k g) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (f * g) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hf p.1) (hg p.2)

private theorem coeff_prod_nonneg {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℤ)
    (hf : ∀ i ∈ s, ∀ k, 0 ≤ PowerSeries.coeff k (f i)) :
    ∀ n, 0 ≤ PowerSeries.coeff n (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    rw [Finset.prod_empty, PowerSeries.coeff_one]
    split <;> norm_num
  | @insert a s ha ih =>
    intro n
    rw [Finset.prod_insert ha]
    exact coeff_mul_nonneg (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))) n

private theorem coeff_pow_nonneg {f : PowerSeries ℤ}
    (hf : ∀ k, 0 ≤ PowerSeries.coeff k f) (m : ℕ) :
    ∀ n, 0 ≤ PowerSeries.coeff n (f ^ m) := by
  induction m with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split <;> norm_num
  | succ m ih =>
    intro n
    rw [pow_succ]
    exact coeff_mul_nonneg ih hf n

private theorem one_le_coeff_mul_of_nonneg {f g : PowerSeries ℤ}
    (hf : ∀ k, 0 ≤ PowerSeries.coeff k f) (hf0 : PowerSeries.constantCoeff f = 1)
    (hg : ∀ k, 1 ≤ PowerSeries.coeff k g) (n : ℕ) :
    1 ≤ PowerSeries.coeff n (f * g) := by
  rw [PowerSeries.coeff_mul]
  have hmem : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
  have hterm : (1 : ℤ) ≤ PowerSeries.coeff (0 : ℕ) f * PowerSeries.coeff n g := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, hf0, one_mul]
    exact hg n
  calc (1 : ℤ) ≤ PowerSeries.coeff (0 : ℕ) f * PowerSeries.coeff n g := hterm
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g :=
        Finset.single_le_sum
          (fun p _ => mul_nonneg (hf p.1) (le_trans zero_le_one (hg p.2))) hmem

private theorem one_le_coeff_mul {f g : PowerSeries ℤ}
    (hf : ∀ k, 1 ≤ PowerSeries.coeff k f) (hg : ∀ k, 1 ≤ PowerSeries.coeff k g) (n : ℕ) :
    1 ≤ PowerSeries.coeff n (f * g) := by
  rw [PowerSeries.coeff_mul]
  have hmem : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
  calc (1 : ℤ) = 1 * 1 := (one_mul 1).symm
    _ ≤ PowerSeries.coeff (0 : ℕ) f * PowerSeries.coeff n g :=
        mul_le_mul (hf 0) (hg n) zero_le_one (le_trans zero_le_one (hf 0))
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g :=
        Finset.single_le_sum
          (fun p _ => mul_nonneg (le_trans zero_le_one (hf p.1))
            (le_trans zero_le_one (hg p.2))) hmem

private theorem one_le_coeff_pow {f : PowerSeries ℤ}
    (hf : ∀ k, 1 ≤ PowerSeries.coeff k f) (m : ℕ) :
    ∀ n, 1 ≤ PowerSeries.coeff n (f ^ (m + 1)) := by
  induction m with
  | zero => intro n; simpa using hf n
  | succ m ih => intro n; rw [pow_succ]; exact one_le_coeff_mul ih hf n

private theorem coeff_mul_congr {A C g : PowerSeries ℤ} {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff k A = PowerSeries.coeff k C) :
    ∀ k ≤ n, PowerSeries.coeff k (A * g) = PowerSeries.coeff k (C * g) := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h1 : p.1 ≤ k := Finset.HasAntidiagonal.antidiagonal.fst_le hp
  rw [h p.1 (le_trans h1 hk)]

private theorem coeff_pow_congr {A C : PowerSeries ℤ} {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff k A = PowerSeries.coeff k C) (m : ℕ) :
    ∀ k ≤ n, PowerSeries.coeff k (A ^ m) = PowerSeries.coeff k (C ^ m) := by
  induction m with
  | zero => intro k _; rfl
  | succ m ih =>
    intro k hk
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h1 : p.1 ≤ k := Finset.HasAntidiagonal.antidiagonal.fst_le hp
    have h2 : p.2 ≤ k := Finset.HasAntidiagonal.antidiagonal.snd_le hp
    rw [ih p.1 (le_trans h1 hk), h p.2 (le_trans h2 hk)]

private theorem coeff_inv_congr {A B C D : PowerSeries ℤ}
    (hAB : A * B = 1) (hCD : C * D = 1) {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff k A = PowerSeries.coeff k C) :
    ∀ k ≤ n, PowerSeries.coeff k B = PowerSeries.coeff k D := by
  intro k hk

  have hCB : ∀ m ≤ n, PowerSeries.coeff m (C * B) =
      PowerSeries.coeff m (1 : PowerSeries ℤ) := by
    intro m hm
    rw [← hAB]
    exact (coeff_mul_congr (fun k hk => (h k hk).symm) m hm)

  have key : B = D * (C * B) := by
    rw [← mul_assoc, mul_comm D C, hCD, one_mul]
  rw [key, PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single_of_mem (k, 0) (by simp)]
  · rw [hCB 0 (Nat.zero_le n), PowerSeries.coeff_one, if_pos rfl, mul_one]
  · rintro ⟨b₁, b₂⟩ hb hne
    have hb' : b₁ + b₂ = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    have hb₂ : b₂ ≤ k := Finset.HasAntidiagonal.antidiagonal.snd_le hb
    have h2 : b₂ ≠ 0 := by
      rintro rfl
      exact hne (by simp [← hb'])
    rw [hCB b₂ (le_trans hb₂ hk), PowerSeries.coeff_one, if_neg h2, mul_zero]

private abbrev partialEta (N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range N, ((1 : PowerSeries ℤ) - X ^ (i + 1))

private abbrev partialGeom (N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range N, geomSeries (i + 1)

private theorem partialEta_mul_partialGeom (N : ℕ) :
    partialEta N * partialGeom N = 1 := by
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl
    (fun i _ => one_sub_X_pow_mul_geomSeries (Nat.succ_ne_zero i))]
  exact Finset.prod_const_one

private theorem coeff_etaProd_eq_coeff_partialEta {k n : ℕ} (hk : k ≤ n) :
    PowerSeries.coeff k etaProd = PowerSeries.coeff k (partialEta (n + 1)) := by
  rw [coeff_etaProd_eq_coeff_partialProd k]
  exact (coeff_prod_one_sub_pow_le n k hk).symm

private theorem coeff_dedekindEtaUnitInv_eq_coeff_partialGeom_pow (n : ℕ) :
    ∀ k ≤ n, PowerSeries.coeff k dedekindEtaUnitInv =
      PowerSeries.coeff k (partialGeom (n + 1) ^ 24) := by

  have hunits : ∀ k ≤ n, PowerSeries.coeff k dedekindEtaUnit =
      PowerSeries.coeff k (partialEta (n + 1) ^ 24) := by
    intro k hk
    rw [dedekindEtaUnit]
    exact coeff_pow_congr (fun k hk => coeff_etaProd_eq_coeff_partialEta hk) 24 k hk

  have hinv : partialEta (n + 1) ^ 24 * partialGeom (n + 1) ^ 24 = 1 := by
    rw [← mul_pow, partialEta_mul_partialGeom, one_pow]
  exact coeff_inv_congr dedekindEtaUnit_mul_inv hinv hunits

private theorem one_le_coeff_partialGeom_pow (n k : ℕ) :
    1 ≤ PowerSeries.coeff k (partialGeom (n + 1) ^ 24) := by

  have hsplit : partialGeom (n + 1) =
      (∏ i ∈ Finset.range n, geomSeries (i + 2)) * geomSeries 1 :=
    Finset.prod_range_succ' (fun i => geomSeries (i + 1)) n
  rw [hsplit, mul_pow]

  have htail_nonneg : ∀ j, 0 ≤ PowerSeries.coeff j
      ((∏ i ∈ Finset.range n, geomSeries (i + 2)) ^ 24) :=
    coeff_pow_nonneg
      (coeff_prod_nonneg _ _ (fun i _ k => coeff_geomSeries_nonneg (i + 2) k)) 24
  have htail_cc : PowerSeries.constantCoeff
      ((∏ i ∈ Finset.range n, geomSeries (i + 2)) ^ 24) = 1 := by
    rw [map_pow, map_prod]
    simp only [constantCoeff_geomSeries, Finset.prod_const_one, one_pow]

  have hhead : ∀ j, 1 ≤ PowerSeries.coeff j (geomSeries 1 ^ 24) :=
    one_le_coeff_pow (fun j => le_of_eq (coeff_geomSeries_one j).symm) 23
  exact one_le_coeff_mul_of_nonneg htail_nonneg htail_cc hhead k

private theorem one_le_coeff_dedekindEtaUnitInv (n : ℕ) :
    1 ≤ PowerSeries.coeff n dedekindEtaUnitInv := by
  rw [coeff_dedekindEtaUnitInv_eq_coeff_partialGeom_pow n n le_rfl]
  exact one_le_coeff_partialGeom_pow n n

private theorem coeff_eisenstein4_nonneg (n : ℕ) :
    0 ≤ PowerSeries.coeff n eisenstein4 := by
  rw [eisenstein4, PowerSeries.coeff_mk]
  split
  · norm_num
  · refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => ?_)
    exact pow_nonneg (Int.natCast_nonneg d) 3

private theorem one_le_coeff_jNum (n : ℕ) : 1 ≤ PowerSeries.coeff n jNum := by
  rw [jNum]
  exact one_le_coeff_mul_of_nonneg (coeff_pow_nonneg coeff_eisenstein4_nonneg 3)
    (by rw [map_pow, constantCoeff_eisenstein4, one_pow])
    one_le_coeff_dedekindEtaUnitInv n

private theorem one_le_coeff_jq_aux (n : ℕ) : (1 : ℚ) ≤ jq.coeff (n : ℤ) := by
  have h : ((n : ℤ)) = ((n + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
  rw [h, coeff_jq_eq_coeff_jNum]
  exact_mod_cast one_le_coeff_jNum (n + 1)

public theorem coeff_jq_ne_zero (n : ℕ) : jq.coeff (n : ℤ) ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_coeff_jq_aux n))
/-- Every coefficient of the `j` Laurent series at a nonnegative index is
at least `1`. The series is `jq = X⁻¹ · jNumQ`, where the numerator has
nonnegative coefficients after expanding the Dedekind eta inverse as a
product of geometric series. -/
public theorem one_le_coeff_jq (n : ℕ) : (1 : ℚ) ≤ jq.coeff (n : ℤ) :=
  one_le_coeff_jq_aux n

end ModularCurve

end
