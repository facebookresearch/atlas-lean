/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDiscreteValuationRing_charpoly_mulLeft_single_slope_of_isAdicComplete.lean`
and
`P2M/Sol/S_IsDiscreteValuationRing_charpoly_mulLeft_single_slope_of_isAdicComplete.lean`
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

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic

import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuedField

@[expose] public section


set_option maxHeartbeats 800000
set_option autoImplicit false
universe u

open IsLocalRing Polynomial

namespace P1Arch

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

private def IsPureSlope (r : ℕ) (n : W) (d : ℕ) (f : Polynomial W) : Prop :=
  f.Monic ∧ f.natDegree = d ∧
    (∀ i : ℕ, i ≤ d → ((d - i : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W n ≤
      (r : ℕ∞) * IsDiscreteValuationRing.addVal W (f.coeff i)) ∧
    ((d : ℕ∞) * IsDiscreteValuationRing.addVal W n = (r : ℕ∞) * IsDiscreteValuationRing.addVal W
      (f.coeff 0))

namespace HCprime

section Algebra

variable {R : Type*} [CommRing R] {O : Type*} [CommRing O] [Algebra R O] [Module.Free R O]
  [Module.Finite R O]

private theorem aeval_eq_zero_of_aeval_charpoly_mulLeft (a : O) (p : R[X]) (hp : aeval a p = 0)
    (L : Type*) [Field L] [Algebra R L] (x : L) (hx : aeval x (LinearMap.mulLeft R a).charpoly = 0)
      :
    aeval x p = 0 := by
  set T : Module.End R O := LinearMap.mulLeft R a with hTdef
  have hT : aeval T p = 0 := by
    have h1 : T = Algebra.lmul R O a := LinearMap.ext fun _ => rfl
    rw [h1, aeval_algHom_apply, hp, map_zero]
  have hev : Module.End.HasEigenvalue (T.baseChange L) x := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange, IsRoot,
      eval_map,
      ← aeval_def, hx]
  obtain ⟨y, hy⟩ := hev.exists_hasEigenvector
  have h2 : aeval (T.baseChange L) (p.map (algebraMap R L)) = 0 := by
    rw [aeval_map_algebraMap]
    change aeval (Module.End.baseChangeHom R L O T) p = 0
    rw [aeval_algHom_apply, hT, map_zero]
  have h3 := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap R L)) hy
  rw [h2, LinearMap.zero_apply, eval_map, ← aeval_def, eq_comm, smul_eq_zero] at h3
  exact h3.resolve_right hy.2

end Algebra

section Normed

private theorem apply_multiset_sum_le_of_isNonarchimedean {α : Type*} [AddCommMonoid α] {g : α → ℝ}
    (hg : IsNonarchimedean g) {C : ℝ} (h0 : g 0 ≤ C) (s : Multiset α) (hs : ∀ x ∈ s, g x ≤ C) :
    g s.sum ≤ C := by
  induction s using Multiset.induction_on with
  | empty => simpa using h0
  | cons a s ih =>
    rw [Multiset.sum_cons]
    exact (hg _ _).trans (max_le (hs a (Multiset.mem_cons_self a s))
      (ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)))

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

private theorem spectralMulAlgNorm_multiset_prod_eq_pow (s : Multiset L) {ρ : ℝ}
    (hρ : ∀ α ∈ s, spectralNorm K L α = ρ) : spectralMulAlgNorm K L s.prod = ρ ^ s.card := by
  rw [map_multiset_prod, Multiset.map_congr rfl (fun a ha => (spectralMulAlgNorm_def (K := K)
    a).trans (hρ a ha)),
    Multiset.map_const', Multiset.prod_replicate]

private theorem norm_coeff_le_of_spectralNorm_roots_eq (f : K[X]) (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ α ∈ (f.map (algebraMap K L)).roots,
      spectralNorm K L α = ρ) (k : ℕ) (hk : k ≤ f.natDegree) :
    ‖f.coeff k‖ ≤ ρ ^ (f.natDegree - k) := by
  set fL := f.map (algebraMap K L) with hfLdef
  have hfL : fL.Monic := hf.map _
  have hdeg : fL.natDegree = f.natDegree := hf.natDegree_map _
  have hcard : fL.roots.card = fL.natDegree := splits_iff_card_roots.mp hs
  have hcoef := coeff_eq_esymm_roots_of_card hcard (k := k) (by omega)
  rw [hfL.leadingCoeff, one_mul] at hcoef
  have e1 : ‖f.coeff k‖ = spectralMulAlgNorm K L (fL.coeff k) := by
    rw [coeff_map, spectralMulAlgNorm_def, spectralNorm_extends]
  rw [e1, hcoef, map_mul, map_pow, map_neg_eq_map, map_one, one_pow, one_mul, hdeg, Multiset.esymm]
  refine apply_multiset_sum_le_of_isNonarchimedean (g := spectralMulAlgNorm K L)
    (fun x y => isNonarchimedean_spectralNorm x y) (by rw [map_zero]; positivity) _ ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
  rw [Multiset.mem_powersetCard] at ht
  rw [spectralMulAlgNorm_multiset_prod_eq_pow t (fun a ha => hρ a (Multiset.mem_of_le ht.1 ha)),
    ht.2]

private theorem norm_coeff_zero_eq_of_spectralNorm_roots_eq (f : K[X]) (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) {ρ : ℝ}
    (hρ : ∀ α ∈ (f.map (algebraMap K L)).roots, spectralNorm K L α = ρ) :
    ‖f.coeff 0‖ = ρ ^ f.natDegree := by
  set fL := f.map (algebraMap K L) with hfLdef
  have hfL : fL.Monic := hf.map _
  have hdeg : fL.natDegree = f.natDegree := hf.natDegree_map _
  have hcard : fL.roots.card = fL.natDegree := splits_iff_card_roots.mp hs
  have e1 : ‖f.coeff 0‖ = spectralMulAlgNorm K L (fL.coeff 0) := by
    rw [coeff_map, spectralMulAlgNorm_def, spectralNorm_extends]
  rw [e1, hs.coeff_zero_eq_prod_roots_of_monic hfL, map_mul, map_pow, map_neg_eq_map, map_one,
    one_pow,
    one_mul, spectralMulAlgNorm_multiset_prod_eq_pow _ hρ, hcard, hdeg]

private theorem norm_coeff_pow_le_of_spectralNorm_roots_eq (f : K[X]) (hf : f.Monic)
    (hs : (f.map (algebraMap K L)).Splits) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ α ∈ (f.map (algebraMap K L)).roots, spectralNorm K L α = ρ) (k : ℕ) :
    ‖f.coeff k‖ ^ f.natDegree ≤ ‖f.coeff 0‖ ^ (f.natDegree - k) := by
  by_cases hk : k ≤ f.natDegree
  · rw [norm_coeff_zero_eq_of_spectralNorm_roots_eq f hf hs hρ, ← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_coeff_le_of_spectralNorm_roots_eq f hf hs hρ0 hρ k
      hk) _
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero, Nat.sub_eq_zero_of_le (by omega),
    pow_zero]
    exact pow_le_one₀ le_rfl zero_le_one

end Normed

section Bridge

variable (W)

@[reducible] private noncomputable def adicValuedFrac : Valued (FractionRing W) (WithZero
  (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal W).adicValued

attribute [local instance] adicValuedFrac

private theorem v_apply (x : FractionRing W) :
    Valued.v x = (IsDiscreteValuationRing.maximalIdeal W).valuation (FractionRing W) x := rfl

@[reducible] private noncomputable def rankOneFrac : (Valued.v : Valuation (FractionRing W)
  (WithZero (Multiplicative ℤ))).RankOne :=
  @Valuation.IsRankOneDiscrete.rankOne _ _ _ _ Valued.v
    (IsDiscreteValuationRing.isRankOneDiscrete W (FractionRing W)) 2 one_lt_two

attribute [local instance] rankOneFrac

open scoped Valued

noncomputable example : NontriviallyNormedField (FractionRing W) := inferInstance
example : IsUltrametricDist (FractionRing W) := inferInstance

private theorem dvd_of_v_le {x y : W}
    (h : Valued.v (algebraMap W (FractionRing W) x) ≤ Valued.v (algebraMap W (FractionRing W) y)) :
      y ∣ x := by
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff,
      map_eq_zero_iff _ (IsFractionRing.injective W (FractionRing W))] at h
    rw [h]
  · have hy' : algebraMap W (FractionRing W) y ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).mpr hy
    have hle : Valued.v (algebraMap W (FractionRing W) x / algebraMap W (FractionRing W) y) ≤ 1 :=
      by
      rw [map_div₀]
      exact (div_le_one₀ ((Valuation.pos_iff _).mpr hy')).mpr h
    obtain ⟨z, hz⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hle
    refine ⟨z, IsFractionRing.injective W (FractionRing W) ?_⟩
    rw [map_mul, hz, mul_div_cancel₀ _ hy']

private theorem addVal_le_of_norm_le {x y : W}
    (h : ‖algebraMap W (FractionRing W) x‖ ≤ ‖algebraMap W (FractionRing W) y‖) :
    IsDiscreteValuationRing.addVal W y ≤ IsDiscreteValuationRing.addVal W x :=
  IsDiscreteValuationRing.addVal_le_iff_dvd.mpr (dvd_of_v_le W (Valued.toNormedField.norm_le_iff.mp
    h))

private theorem mem_pow_iff_v_le {ϖ : W} (hϖ : Irreducible ϖ) (z : W) (k : ℕ) :
    z ∈ maximalIdeal W ^ k ↔
      Valued.v (algebraMap W (FractionRing W) z) ≤ Valued.v (algebraMap W (FractionRing W) ϖ ^ k)
        := by
  rw [← map_pow, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    rw [map_mul, Valuation.map_mul]
    exact mul_le_of_le_one_right' ((IsDiscreteValuationRing.maximalIdeal W).valuation_le_one w)
  · exact dvd_of_v_le W

private theorem exists_pow_lt_withZero {q γ : WithZero (Multiplicative ℤ)} (hq0 : q ≠ 0) (hq : q <
  1) (hγ : γ ≠ 0) :
    ∃ k : ℕ, q ^ k < γ := by
  obtain ⟨a, rfl⟩ : ∃ a : ℤ, q = WithZero.exp a := ⟨q.log, (WithZero.exp_log hq0).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℤ, γ = WithZero.exp b := ⟨γ.log, (WithZero.exp_log hγ).symm⟩
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hq
  refine ⟨b.natAbs + 1, ?_⟩
  rw [← WithZero.exp_nsmul, WithZero.exp_lt_exp, nsmul_eq_mul]
  push_cast
  have ha : a ≤ -1 := by omega
  have h1 : (|b| + 1) * a ≤ (|b| + 1) * (-1) := mul_le_mul_of_nonneg_left ha (by positivity)
  linarith [neg_abs_le b]

set_option backward.isDefEq.respectTransparency false in
open Filter Topology in

private theorem completeSpace_fractionRing [IsAdicComplete (maximalIdeal W) W] : CompleteSpace
  (FractionRing W) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  set π : FractionRing W := algebraMap W (FractionRing W) ϖ with hπ
  have hπ0 : π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).mpr
    hϖ.ne_zero
  have hvπ0 : ∀ k : ℕ, Valued.v (π ^ k) ≠ 0 := fun k => by
    rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ hπ0
  have hvπ1 : Valued.v π < 1 := by
    rw [v_apply, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hϖ.not_isUnit
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  rw [(Valued.hasBasis_uniformity (FractionRing W)
    (WithZero (Multiplicative ℤ))).cauchySeq_iff] at hu
  have hu' : ∀ k : ℕ, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → Valued.v (u n - u m) < Valued.v (π ^ k) := by
    intro k
    obtain ⟨N, hN⟩ := hu (Units.mk0 (Valued.v.restrict (π ^ k))
      (mt (Valuation.restrict_eq_zero_iff _).mp (hvπ0 k))) trivial
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hN m hm n hn
    simp only [Set.mem_setOf_eq, Units.val_mk0] at h
    rwa [Valuation.restrict_lt_iff] at h
  choose N hN using hu'
  let M : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup N
  have hMN : ∀ {j k : ℕ}, j ≤ k → N j ≤ M k := fun {j k} h =>
    Finset.le_sup (f := N) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
  have hlift : ∀ k, ∃ y : W, algebraMap W (FractionRing W) y = u (M k) - u (M 0) := by
    intro k
    apply IsDiscreteValuationRing.exists_lift_of_le_one
    have := hN 0 (M 0) (hMN le_rfl) (M k) (hMN (Nat.zero_le _))
    rw [pow_zero, Valuation.map_one] at this
    exact this.le
  choose y hy using hlift
  have hprec : ∀ {m n : ℕ}, m ≤ n → y m ≡ y n [SMOD (maximalIdeal W ^ m • ⊤ : Submodule W W)] := by
    intro m n hmn
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, mem_pow_iff_v_le W hϖ, map_sub, hy, hy,
      sub_sub_sub_cancel_right]
    exact (hN m (M n) (hMN hmn) (M m) (hMN le_rfl)).le
  obtain ⟨Lim, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := maximalIdeal W) (R
    := W)) hprec
  refine ⟨u (M 0) + algebraMap W (FractionRing W) Lim, ?_⟩
  rw [tendsto_def]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := (_root_.map_ne_zero _).mpr γ.ne_zero
  obtain ⟨k, hk⟩ := exists_pow_lt_withZero ((Valuation.ne_zero_iff _).mpr hπ0) hvπ1 hγ0
  rw [mem_atTop_sets]
  refine ⟨M k, fun n hn => hγ ?_⟩
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  have e1 : u n - (u (M 0) + algebraMap W (FractionRing W) Lim) =
      (u n - u (M k)) + algebraMap W (FractionRing W) (y k - Lim) := by
    rw [map_sub, hy]; ring
  rw [e1]
  refine lt_of_le_of_lt (Valued.v.map_add _ _) (lt_of_le_of_lt (max_le (hN k (M k) (hMN le_rfl) n
    ((hMN le_rfl).trans hn)).le ?_) ?_)
  · rw [← mem_pow_iff_v_le W hϖ, ← Ideal.mul_top (maximalIdeal W ^ k), ← smul_eq_mul,
    ← SModEq.sub_mem]
    exact hL k
  · rw [Valuation.map_pow]; exact hk

end Bridge

section Main

open IsDiscreteValuationRing

attribute [local instance] adicValuedFrac rankOneFrac
open scoped Valued

set_option backward.isDefEq.respectTransparency false in

private theorem norm_charpoly_coeff_pow_le [IsAdicComplete (maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a :
      O) (i : ℕ) :
    ‖algebraMap W (FractionRing W) ((LinearMap.mulLeft W a).charpoly.coeff i)‖ ^ Module.finrank W O
      ≤
      ‖algebraMap W (FractionRing W) ((LinearMap.mulLeft W a).charpoly.coeff 0)‖ ^ (Module.finrank
        W O - i) := by
  haveI : CompleteSpace (FractionRing W) := completeSpace_fractionRing W
  set K := FractionRing W with hK
  set χ := (LinearMap.mulLeft W a).charpoly with hχ
  have hmon : χ.Monic := LinearMap.charpoly_monic _
  have hdeg : χ.natDegree = Module.finrank W O := LinearMap.charpoly_natDegree _
  set χK := χ.map (algebraMap W K) with hχK
  have hmonK : χK.Monic := hmon.map _
  have hdegK : χK.natDegree = Module.finrank W O := by rw [hmon.natDegree_map, hdeg]
  let L := AlgebraicClosure K

  have hint : IsIntegral W a := Algebra.IsIntegral.isIntegral a
  set m := minpoly W a with hm
  have hmirr : Irreducible (m.map (algebraMap W K)) :=
    ((minpoly.monic hint).irreducible_iff_irreducible_map_fraction_map).mp (minpoly.irreducible
      hint)
  have hmmon : (m.map (algebraMap W K)).Monic := (minpoly.monic hint).map _

  set ρ : ℝ := spectralValue (m.map (algebraMap W K)) with hρ
  have hroots : ∀ α ∈ (χK.map (algebraMap K L)).roots, spectralNorm K L α = ρ := by
    intro α hα
    have hχα : aeval α χ = 0 := by
      rw [mem_roots ((hmonK.map _).ne_zero), IsRoot, hχK, map_map, ← IsScalarTower.algebraMap_eq,
        eval_map,
        ← aeval_def] at hα
      exact hα
    have hmα : aeval α (m.map (algebraMap W K)) = 0 := by
      rw [aeval_map_algebraMap]
      exact aeval_eq_zero_of_aeval_charpoly_mulLeft a m (minpoly.aeval W a) L α hχα
    rw [spectralNorm, ← minpoly.eq_of_irreducible_of_monic hmirr hmα hmmon]
  have key := norm_coeff_pow_le_of_spectralNorm_roots_eq (L := L) χK hmonK (IsAlgClosed.splits _)
    (spectralValue_nonneg _) hroots i
  rwa [hdegK, hχK, coeff_map, coeff_map] at key

private theorem _root_.P1Arch.HCprime.charpoly_mulLeft_isPureSlope_of_isDomain [IsAdicComplete
  (maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a :
      O) :
    IsPureSlope (Module.finrank W O) (Algebra.norm W a) (Module.finrank W O) (LinearMap.mulLeft W
      a).charpoly := by
  set d := Module.finrank W O with hd
  set χ := (LinearMap.mulLeft W a).charpoly with hχ
  have hmon : χ.Monic := LinearMap.charpoly_monic _
  have hdeg : χ.natDegree = d := LinearMap.charpoly_natDegree _
  have hc0 : addVal W (Algebra.norm W a) = addVal W (χ.coeff 0) := by
    have h1 : Algebra.norm W a = (-1) ^ d * χ.coeff 0 := by
      rw [Algebra.norm_apply, ← LinearMap.det_eq_sign_charpoly_coeff]
      congr 1
    rw [h1, addVal_mul, addVal_pow, AddValuation.map_neg, addVal_one, nsmul_zero, zero_add]
  refine ⟨hmon, hdeg, ?_, by rw [hc0]⟩
  intro i hi
  have key := norm_charpoly_coeff_pow_le (W := W) O a i
  rw [← norm_pow, ← norm_pow, ← map_pow (algebraMap W (FractionRing W)),
    ← map_pow (algebraMap W (FractionRing W))] at key
  have h2 := addVal_le_of_norm_le W key
  rw [addVal_pow, addVal_pow, nsmul_eq_mul, nsmul_eq_mul] at h2
  rw [hc0]
  exact h2

end Main

end HCprime

private theorem _root_.P1Arch.charpoly_mulLeft_isPureSlope_of_isDomain [IsAdicComplete
  (maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a :
      O) :
    IsPureSlope (Module.finrank W O) (Algebra.norm W a) (Module.finrank W O) (LinearMap.mulLeft W
      a).charpoly :=
  HCprime.charpoly_mulLeft_isPureSlope_of_isDomain O a

end P1Arch

/-- The characteristic polynomial of multiplication by an element of a finite
free domain over an adically complete discrete valuation ring has a single
Newton slope: its coefficients satisfy the valuation bounds determined by the
norm, with equality at the constant coefficient. -/
theorem IsDiscreteValuationRing.charpoly_mulLeft_single_slope_of_isAdicComplete
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a :
      O) :
    (LinearMap.mulLeft W a).charpoly.Monic ∧
    (LinearMap.mulLeft W a).charpoly.natDegree = Module.finrank W O ∧
    (∀ i : ℕ, i ≤ Module.finrank W O →
      ((Module.finrank W O - i : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W a) ≤
        (Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W ((LinearMap.mulLeft W
          a).charpoly.coeff i)) ∧
    ((Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W a) =
      (Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W ((LinearMap.mulLeft W
        a).charpoly.coeff 0)) := by
  exact P1Arch.charpoly_mulLeft_isPureSlope_of_isDomain O a
