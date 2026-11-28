/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ValuationSubring_forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing.lean`
and
`P2M/Sol/S_ValuationSubring_forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing.lean`
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

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Valuation.LocalSubring
import MathlibExt.RingTheory.Henselian.IdempotentLifting

@[expose] public section

open Polynomial

universe u v

namespace S17Hens

private theorem isLocalRing_of_isDomain_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by
  classical
  by_contra hS

  have h1 : ∃ a : S, ¬ IsUnit a ∧ ¬ IsUnit (1 - a) := by
    by_contra h
    push Not at h
    exact hS (IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      by_cases ha : IsUnit a
      · exact Or.inl ha
      · exact Or.inr (h a ha))
  obtain ⟨a, ha, ha'⟩ := h1
  obtain ⟨m₁, hm₁, ham₁⟩ := exists_max_ideal_of_mem_nonunits ha
  obtain ⟨m₂, hm₂, ham₂⟩ := exists_max_ideal_of_mem_nonunits ha'
  have hne : m₁ ≠ m₂ := by
    intro h
    subst h
    have : (1 : S) ∈ m₁ := by
      have := m₁.add_mem ham₁ ham₂
      rwa [add_sub_cancel] at this
    exact hm₁.ne_top ((Ideal.eq_top_iff_one _).mpr this)

  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  have hJle : ∀ m : Ideal S, m.IsMaximal → J ≤ m := by
    intro m hm
    rw [hJ, Ideal.map_le_iff_le_comap]
    haveI := hm
    have hmax : (m.comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) m
    rw [IsLocalRing.eq_maximalIdeal hmax]

  have : IsArtinianRing (S ⧸ J) := by
    let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    have : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (S ⧸ J) :=
      .of_restrictScalars_finite R _ _
    exact .of_finite (R ⧸ IsLocalRing.maximalIdeal R) _
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have hmaxq : ∀ m : Ideal S, m.IsMaximal → (m.map (Ideal.Quotient.mk J)).IsMaximal := by
    intro m hm
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm with h | h
    · exfalso
      have : m = ⊤ := by
        have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h
        rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_top] at h2
        have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J := by
          rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        rw [hker, sup_eq_left.mpr (hJle m hm)] at h2
        exact h2
      exact hm.ne_top this
    · exact h
  let M₁ : MaximalSpectrum (S ⧸ J) := ⟨m₁.map (Ideal.Quotient.mk J), hmaxq m₁ hm₁⟩
  let M₂ : MaximalSpectrum (S ⧸ J) := ⟨m₂.map (Ideal.Quotient.mk J), hmaxq m₂ hm₂⟩
  have hM : M₁ ≠ M₂ := by
    intro h
    apply hne
    have h2 : m₁.map (Ideal.Quotient.mk J) = m₂.map (Ideal.Quotient.mk J) :=
      congrArg MaximalSpectrum.asIdeal h
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h2
    rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_map_of_surjective _ hsurj] at h3
    have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rwa [hker, sup_eq_left.mpr (hJle m₁ hm₁), sup_eq_left.mpr (hJle m₂ hm₂)] at h3

  let π := IsArtinianRing.quotNilradicalEquivPi (S ⧸ J)
  let f₀ : ∀ I : MaximalSpectrum (S ⧸ J), (S ⧸ J) ⧸ I.asIdeal := Pi.single M₁ 1
  have hf₀ : IsIdempotentElem f₀ := by
    show f₀ * f₀ = f₀
    ext I
    by_cases hI : I = M₁
    · subst hI; simp [f₀]
    · simp [f₀, hI]
  have hf₀0 : f₀ ≠ 0 := by
    intro h
    have := congrFun h M₁
    simp [f₀] at this
    exact M₁.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp this.symm)
  have hf₀1 : f₀ ≠ 1 := by
    intro h
    have := congrFun h M₂
    have h0 : f₀ M₂ = 0 := Pi.single_eq_of_ne hM.symm _
    rw [h0, Pi.one_apply] at this
    exact M₂.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp this)
  let ē₀ := π.symm f₀
  have hē₀ : IsIdempotentElem ē₀ := by
    show π.symm f₀ * π.symm f₀ = π.symm f₀
    rw [← map_mul, hf₀.eq]

  have hnil : ∀ y ∈ RingHom.ker (Ideal.Quotient.mk (nilradical (S ⧸ J))), IsNilpotent y := by
    intro y hy
    rw [Ideal.mk_ker] at hy
    exact hy
  obtain ⟨ē, hē, hēē₀⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (Ideal.Quotient.mk (nilradical (S ⧸ J))) hnil ē₀
    (Ideal.Quotient.mk_surjective ē₀) hē₀

  obtain ⟨e, ⟨he, hemk⟩, -⟩ :=
    HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite ē hē

  rcases IsIdempotentElem.iff_eq_zero_or_one.mp he with h0 | h1
  · apply hf₀0
    have : ē = 0 := by rw [← hemk, h0, map_zero]
    have : ē₀ = 0 := by rw [← hēē₀, this, map_zero]
    have : f₀ = π 0 := by rw [← this]; exact (π.apply_symm_apply f₀).symm
    rw [this, map_zero]
  · apply hf₀1
    have : ē = 1 := by rw [← hemk, h1, map_one]
    have : ē₀ = 1 := by rw [← hēē₀, this, map_one]
    have : f₀ = π 1 := by rw [← this]; exact (π.apply_symm_apply f₀).symm
    rw [this, map_one]

end S17Hens

namespace EsbG2bPrufer

variable {E F : Type*} [Field E] [Field F] [Algebra E F]

private theorem val_le_one_of_isIntegral (O : ValuationSubring E) (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) {b : F} (hb : IsIntegral ↥O b) :
    O'.valuation b ≤ 1 := by
  obtain ⟨p, hpm, hpe⟩ := hb
  by_contra hgt
  rw [not_le] at hgt
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hgt
    exact absurd hgt (by simp)
  have hvb0 : O'.valuation b ≠ 0 := (Valuation.ne_zero_iff _).mpr hb0
  have hn : p.natDegree ≠ 0 := by
    intro h0
    have h1 : p = 1 := hpm.natDegree_eq_zero.mp h0
    rw [h1, Polynomial.eval₂_one] at hpe
    exact one_ne_zero hpe
  have hrel : ∑ i ∈ Finset.range (p.natDegree + 1),
      algebraMap ↥O F (p.coeff i) * b ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hpe
  rw [Finset.sum_range_succ, Polynomial.Monic.coeff_natDegree hpm, map_one, one_mul] at hrel
  have hbn : b ^ p.natDegree
      = -∑ i ∈ Finset.range p.natDegree, algebraMap ↥O F (p.coeff i) * b ^ i :=
    eq_neg_of_add_eq_zero_right hrel
  have hlt : O'.valuation (∑ i ∈ Finset.range p.natDegree,
      algebraMap ↥O F (p.coeff i) * b ^ i) < O'.valuation b ^ p.natDegree := by
    refine Valuation.map_sum_lt _ (pow_ne_zero _ hvb0) fun i hi => ?_
    rw [map_mul, map_pow]
    calc O'.valuation (algebraMap ↥O F (p.coeff i)) * O'.valuation b ^ i
        ≤ 1 * O'.valuation b ^ i := by
          gcongr
          exact O'.valuation_le_one ⟨_, (hO _).mpr (p.coeff i).2⟩
      _ = O'.valuation b ^ i := one_mul _
      _ < O'.valuation b ^ p.natDegree := by
          exact pow_lt_pow_right₀ hgt (Finset.mem_range.mp hi)
  rw [← map_pow, hbn, Valuation.map_neg] at hlt
  exact lt_irrefl _ hlt

private def tail (A : ℕ → E) (x : F) (n j : ℕ) : F :=
  ∑ i ∈ Finset.Ico j (n + 1), algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ))

private theorem tail_top (A : ℕ → E) (x : F) (n : ℕ) : tail A x n (n + 1) = 0 := by
  rw [tail, Finset.Ico_self, Finset.sum_empty]

private theorem tail_pull (A : ℕ → E) {x : F} (hx0 : x ≠ 0) (n j : ℕ) :
    x ^ (j : ℤ) * tail A x n j
      = ∑ i ∈ Finset.Ico j (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) := by
  rw [tail, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc x ^ (j : ℤ) * (algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ)))
      = algebraMap E F (A i) * (x ^ (j : ℤ) * x ^ ((i : ℤ) - (j : ℤ))) := by ring
    _ = algebraMap E F (A i) * x ^ ((j : ℤ) + ((i : ℤ) - (j : ℤ))) := by
        rw [zpow_add₀ hx0]
    _ = algebraMap E F (A i) * x ^ (i : ℤ) := by
        rw [show (j : ℤ) + ((i : ℤ) - (j : ℤ)) = (i : ℤ) from by omega]

private theorem tail_eq_neg (A : ℕ → E) {x : F} (hx0 : x ≠ 0) {n : ℕ}
    (hrel : ∑ i ∈ Finset.range (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) = 0)
    {j : ℕ} (hj : j ≤ n + 1) :
    tail A x n j = -∑ i ∈ Finset.range j, algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ)) := by
  have hxj : x ^ (j : ℤ) ≠ 0 := zpow_ne_zero _ hx0
  have hsplit : ∑ i ∈ Finset.range j, algebraMap E F (A i) * x ^ (i : ℤ)
      + ∑ i ∈ Finset.Ico j (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) = 0 := by
    rw [Finset.range_eq_Ico] at hrel ⊢
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le j) hj]
    exact hrel
  have h1 : ∑ i ∈ Finset.Ico j (n + 1), algebraMap E F (A i) * x ^ (i : ℤ)
      = -∑ i ∈ Finset.range j, algebraMap E F (A i) * x ^ (i : ℤ) :=
    eq_neg_of_add_eq_zero_right hsplit
  refine mul_left_cancel₀ hxj ?_
  rw [tail_pull A hx0 n j, h1, mul_neg, neg_inj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc algebraMap E F (A i) * x ^ (i : ℤ)
      = algebraMap E F (A i) * x ^ ((j : ℤ) + ((i : ℤ) - (j : ℤ))) := by
        rw [show (j : ℤ) + ((i : ℤ) - (j : ℤ)) = (i : ℤ) from by omega]
    _ = algebraMap E F (A i) * (x ^ (j : ℤ) * x ^ ((i : ℤ) - (j : ℤ))) := by
        rw [zpow_add₀ hx0]
    _ = x ^ (j : ℤ) * (algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ))) := by ring

private theorem tail_horner (A : ℕ → E) {x : F} (hx0 : x ≠ 0) {n : ℕ}
    {j : ℕ} (hj : j ≤ n) :
    tail A x n j = algebraMap E F (A j) + x * tail A x n (j + 1) := by
  have hxj : x ^ (j : ℤ) ≠ 0 := zpow_ne_zero _ hx0
  refine mul_left_cancel₀ hxj ?_
  have hpull := tail_pull A hx0 n j
  have hpull1 := tail_pull A hx0 n (j + 1)
  have hbot : ∑ i ∈ Finset.Ico j (n + 1), algebraMap E F (A i) * x ^ (i : ℤ)
      = algebraMap E F (A j) * x ^ (j : ℤ)
        + ∑ i ∈ Finset.Ico (j + 1) (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) :=
    Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hj) _
  have hx1 : x ^ ((j : ℤ) + 1) = x ^ (j : ℤ) * x := by
    rw [zpow_add₀ hx0, zpow_one]
  calc x ^ (j : ℤ) * tail A x n j
      = algebraMap E F (A j) * x ^ (j : ℤ)
        + ∑ i ∈ Finset.Ico (j + 1) (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) := by
        rw [hpull, hbot]
    _ = algebraMap E F (A j) * x ^ (j : ℤ) + x ^ ((j + 1 : ℕ) : ℤ) * tail A x n (j + 1) := by
        rw [hpull1]
    _ = x ^ (j : ℤ) * (algebraMap E F (A j) + x * tail A x n (j + 1)) := by
        have h2 : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by omega
        rw [h2, hx1]
        ring

private theorem exists_rep [Algebra.IsAlgebraic E F] (O : ValuationSubring E)
    (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) {x : F} (hxO : x ∈ O') (hx0 : x ≠ 0) :
    ∃ b s : ↥(integralClosure ↥O F), O'.valuation (s : F) = 1 ∧ x * ↑s = ↑b := by
  classical
  obtain ⟨p, hp0, hpe⟩ := Algebra.IsAlgebraic.isAlgebraic (R := E) x
  set n := p.natDegree with hndef
  have hvx : O'.valuation x ≤ 1 := (O'.valuation_le_one_iff x).mpr hxO

  have hn0 : n ≠ 0 := by
    intro h0
    have hc : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    rw [hc, Polynomial.aeval_C] at hpe
    have : p.coeff 0 = 0 := by
      have := (map_eq_zero (algebraMap E F)).mp hpe
      exact this
    rw [this, map_zero] at hc
    exact hp0 hc

  have hrel0 : ∑ i ∈ Finset.range (n + 1), algebraMap E F (p.coeff i) * x ^ (i : ℤ) = 0 := by
    have h1 := hpe
    rw [Polynomial.aeval_eq_sum_range] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, zpow_natCast]

  obtain ⟨i₀, hi₀mem, hi₀max⟩ :=
    Finset.exists_max_image (Finset.range (n + 1))
      (fun i => O'.valuation (algebraMap E F (p.coeff i))) ⟨0, Finset.mem_range.mpr n.succ_pos⟩
  have hcn : p.coeff n ≠ 0 := by
    rw [hndef]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have hvi₀pos : 0 < O'.valuation (algebraMap E F (p.coeff i₀)) := by
    have h1 : O'.valuation (algebraMap E F (p.coeff n))
        ≤ O'.valuation (algebraMap E F (p.coeff i₀)) :=
      hi₀max n (Finset.mem_range.mpr n.lt_succ_self)
    have h2 : O'.valuation (algebraMap E F (p.coeff n)) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact fun h => hcn ((map_eq_zero (algebraMap E F)).mp h)
    exact lt_of_lt_of_le (zero_lt_iff.mpr h2) h1
  have hci₀ : p.coeff i₀ ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hvi₀pos
    exact lt_irrefl 0 hvi₀pos

  set A : ℕ → E := fun i => p.coeff i / p.coeff i₀ with hAdef
  have hAi₀ : A i₀ = 1 := div_self hci₀
  have hvA : ∀ i, O'.valuation (algebraMap E F (A i))
      = O'.valuation (algebraMap E F (p.coeff i))
        / O'.valuation (algebraMap E F (p.coeff i₀)) := by
    intro i
    rw [hAdef]
    dsimp only
    rw [map_div₀, map_div₀]
  have hAle : ∀ i ∈ Finset.range (n + 1), O'.valuation (algebraMap E F (A i)) ≤ 1 := by
    intro i hi
    rw [hvA i, div_le_one₀ hvi₀pos]
    exact hi₀max i hi
  have hAmemO : ∀ i ∈ Finset.range (n + 1), A i ∈ O := fun i hi =>
    (hO _).mp (O'.mem_of_valuation_le_one _ (hAle i hi))

  have hrelA : ∑ i ∈ Finset.range (n + 1), algebraMap E F (A i) * x ^ (i : ℤ) = 0 := by
    have h1 : ∀ i, algebraMap E F (A i) * x ^ (i : ℤ)
        = algebraMap E F (p.coeff i) * x ^ (i : ℤ) * (algebraMap E F (p.coeff i₀))⁻¹ := by
      intro i
      rw [hAdef]
      dsimp only
      rw [div_eq_mul_inv, map_mul, map_inv₀]
      ring
    calc ∑ i ∈ Finset.range (n + 1), algebraMap E F (A i) * x ^ (i : ℤ)
        = (∑ i ∈ Finset.range (n + 1), algebraMap E F (p.coeff i) * x ^ (i : ℤ))
          * (algebraMap E F (p.coeff i₀))⁻¹ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => h1 i
      _ = 0 := by rw [hrel0, zero_mul]

  have hS : (Finset.filter (fun i => O'.valuation (algebraMap E F (A i)) = 1)
      (Finset.range (n + 1))).Nonempty := by
    refine ⟨i₀, Finset.mem_filter.mpr ⟨hi₀mem, ?_⟩⟩
    rw [hAi₀, map_one, map_one]
  set k := (Finset.filter (fun i => O'.valuation (algebraMap E F (A i)) = 1)
      (Finset.range (n + 1))).max' hS with hkdef
  have hkmem := (Finset.filter (fun i => O'.valuation (algebraMap E F (A i)) = 1)
      (Finset.range (n + 1))).max'_mem hS
  rw [← hkdef] at hkmem
  have hkrange : k ∈ Finset.range (n + 1) := (Finset.mem_filter.mp hkmem).1
  have hvAk : O'.valuation (algebraMap E F (A k)) = 1 := (Finset.mem_filter.mp hkmem).2
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkrange)
  have hklt : ∀ i ∈ Finset.range (n + 1), k < i →
      O'.valuation (algebraMap E F (A i)) < 1 := by
    intro i hi hik
    refine lt_of_le_of_ne (hAle i hi) fun he => ?_
    have : i ≤ k := Finset.le_max' _ i (Finset.mem_filter.mpr ⟨hi, he⟩)
    omega

  set W : Submodule ↥O F :=
    Submodule.span ↥O (((Finset.range (2 * n + 1)).image
      fun m : ℕ => x ^ ((m : ℤ) - (n : ℤ))) : Finset F) with hWdef
  have hgen : ∀ m : ℤ, -(n : ℤ) ≤ m → m ≤ (n : ℤ) → x ^ m ∈ W := by
    intro m h1 h2
    refine Submodule.subset_span ?_
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨(m + (n : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    rw [show (((m + (n : ℤ)).toNat : ℤ) - (n : ℤ)) = m from by omega]
  have hWfg : W.FG := Submodule.fg_span (Finset.finite_toSet _)
  have hWne : W ≠ ⊥ := by
    intro hbot
    have h1 : (1 : F) ∈ W := by
      have := hgen 0 (by omega) (by omega)
      rwa [zpow_zero] at this
    rw [hbot, Submodule.mem_bot] at h1
    exact one_ne_zero h1

  have hsmul : ∀ (a : E) (ha : a ∈ O) (y : F),
      algebraMap E F a * y = (⟨a, ha⟩ : ↥O) • y := by
    intro a ha y
    rw [Algebra.smul_def]
    rfl

  have hTmemW : ∀ j ≤ n, tail A x n j ∈ W := by
    intro j hj
    rw [tail]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi' := Finset.mem_Ico.mp hi
    rw [hsmul (A i) (hAmemO i (Finset.mem_range.mpr hi'.2)) _]
    refine Submodule.smul_mem _ _ (hgen _ (by omega) (by omega))

  have hstab : ∀ j ≤ n, ∀ w ∈ W, tail A x n j * w ∈ W := by
    intro j hj w hw
    induction hw using Submodule.span_induction with
    | mem w hwmem =>
      rw [Finset.mem_coe, Finset.mem_image] at hwmem
      obtain ⟨m0, hm0r, rfl⟩ := hwmem
      have hm0' : m0 < 2 * n + 1 := Finset.mem_range.mp hm0r
      rcases le_or_gt 0 ((m0 : ℤ) - (n : ℤ)) with hmnn | hmnn
      ·
        rw [tail_eq_neg A hx0 hrelA (le_trans hj (Nat.le_succ n)), neg_mul, Finset.sum_mul]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
        have hi' := Finset.mem_range.mp hi
        have he : algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ)) * x ^ ((m0 : ℤ) - (n : ℤ))
            = algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ) + ((m0 : ℤ) - (n : ℤ))) := by
          rw [mul_assoc, ← zpow_add₀ hx0]
        rw [he, hsmul (A i) (hAmemO i (Finset.mem_range.mpr (by omega))) _]
        refine Submodule.smul_mem _ _ (hgen _ (by omega) (by omega))
      ·
        rw [tail, Finset.sum_mul]
        refine Submodule.sum_mem _ fun i hi => ?_
        have hi' := Finset.mem_Ico.mp hi
        have he : algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ)) * x ^ ((m0 : ℤ) - (n : ℤ))
            = algebraMap E F (A i) * x ^ ((i : ℤ) - (j : ℤ) + ((m0 : ℤ) - (n : ℤ))) := by
          rw [mul_assoc, ← zpow_add₀ hx0]
        rw [he, hsmul (A i) (hAmemO i (Finset.mem_range.mpr hi'.2)) _]
        refine Submodule.smul_mem _ _ (hgen _ (by omega) (by omega))
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      rw [mul_add]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ ha

  have hTint : ∀ j ≤ n, IsIntegral ↥O (tail A x n j) := by
    intro j hj
    refine isIntegral_of_smul_mem_submodule W hWne hWfg _ fun w hw => ?_
    rw [smul_eq_mul]
    exact hstab j hj w hw

  have hTk1 : O'.valuation (tail A x n (k + 1)) < 1 := by
    rcases eq_or_lt_of_le hkn with heq | hklt'
    · rw [heq, tail_top, map_zero]
      exact zero_lt_one
    · rw [tail]
      refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
      have hi' := Finset.mem_Ico.mp hi
      have hnn : (0 : ℤ) ≤ (i : ℤ) - ((k + 1 : ℕ) : ℤ) := by omega
      have hz : x ^ ((i : ℤ) - ((k + 1 : ℕ) : ℤ)) = x ^ (i - (k + 1)) := by
        rw [← zpow_natCast x (i - (k + 1))]
        congr 1
        omega
      rw [map_mul, hz, map_pow]
      calc O'.valuation (algebraMap E F (A i)) * O'.valuation x ^ (i - (k + 1))
          ≤ O'.valuation (algebraMap E F (A i)) * 1 := by
            gcongr
            exact pow_le_one₀ zero_le' hvx
        _ = O'.valuation (algebraMap E F (A i)) := mul_one _
        _ < 1 := hklt i (Finset.mem_range.mpr hi'.2) (by omega)

  have hvTk : O'.valuation (tail A x n k) = 1 := by
    have hh := tail_horner A hx0 hkn
    have hsmall : O'.valuation (x * tail A x n (k + 1)) < 1 := by
      rw [map_mul]
      calc O'.valuation x * O'.valuation (tail A x n (k + 1))
          ≤ 1 * O'.valuation (tail A x n (k + 1)) := by gcongr
        _ = O'.valuation (tail A x n (k + 1)) := one_mul _
        _ < 1 := hTk1
    have hne : O'.valuation (x * tail A x n (k + 1))
        < O'.valuation (algebraMap E F (A k)) := by
      rw [hvAk]
      exact hsmall
    rw [hh, Valuation.map_add_eq_of_lt_left _ hne]
    exact hvAk

  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk00 : k = 0 := by omega
    have hT0 : tail A x n 0 = 0 := by
      have h1 := tail_eq_neg A hx0 hrelA (Nat.zero_le (n + 1))
      rw [h1, Finset.range_zero, Finset.sum_empty, neg_zero]
    have hh := tail_horner A hx0 (Nat.zero_le n)
    rw [hT0] at hh
    have h2 : algebraMap E F (A 0) = -(x * tail A x n 1) :=
      eq_neg_of_add_eq_zero_left hh.symm
    have h3 : O'.valuation (algebraMap E F (A 0)) < 1 := by
      rw [h2, Valuation.map_neg, map_mul]
      have hk1' : O'.valuation (tail A x n 1) < 1 := by
        have := hTk1
        rwa [hk00, zero_add] at this
      calc O'.valuation x * O'.valuation (tail A x n 1)
          ≤ 1 * O'.valuation (tail A x n 1) := by gcongr
        _ = O'.valuation (tail A x n 1) := one_mul _
        _ < 1 := hk1'
    rw [hk00] at hvAk
    rw [hvAk] at h3
    exact lt_irrefl 1 h3

  have hkn1 : k - 1 ≤ n := by omega
  have hk1k : (k - 1) + 1 = k := by omega
  have hbint : IsIntegral ↥O (tail A x n (k - 1) - algebraMap E F (A (k - 1))) := by
    refine (hTint (k - 1) hkn1).sub ?_
    have hmem : A (k - 1) ∈ O := hAmemO (k - 1) (Finset.mem_range.mpr (by omega))
    exact isIntegral_algebraMap (x := (⟨A (k - 1), hmem⟩ : ↥O))
  have hmul : x * tail A x n k = tail A x n (k - 1) - algebraMap E F (A (k - 1)) := by
    have hh := tail_horner A hx0 hkn1
    rw [hk1k] at hh
    rw [hh]
    ring
  exact ⟨⟨_, hbint⟩, ⟨_, hTint k hkn⟩, hvTk, hmul⟩

private theorem mem_iff_rep [Algebra.IsAlgebraic E F] (O : ValuationSubring E)
    (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) (x : F) :
    x ∈ O' ↔ ∃ b s : ↥(integralClosure ↥O F), O'.valuation (s : F) = 1 ∧ x * ↑s = ↑b := by
  constructor
  · intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · refine ⟨0, 1, ?_, ?_⟩
      · rw [OneMemClass.coe_one, map_one]
      · rw [OneMemClass.coe_one, ZeroMemClass.coe_zero, zero_mul]
    · exact exists_rep O O' hO hx hx0
  · rintro ⟨b, s, hs1, hmul⟩
    have hble : O'.valuation (b : F) ≤ 1 := val_le_one_of_isIntegral O O' hO b.2
    have hxv : O'.valuation x * O'.valuation (s : F) = O'.valuation (b : F) := by
      rw [← map_mul, hmul]
    rw [hs1, mul_one] at hxv
    exact O'.mem_of_valuation_le_one x (le_of_eq_of_le hxv hble)

private theorem mem_of_agree [Algebra.IsAlgebraic E F] (O : ValuationSubring E)
    (W₁ W₂ : ValuationSubring F)
    (h₁ : ∀ x : E, algebraMap E F x ∈ W₁ ↔ x ∈ O)
    (h₂ : ∀ x : E, algebraMap E F x ∈ W₂ ↔ x ∈ O)
    (hag : ∀ b : ↥(integralClosure ↥O F), W₁.valuation (b : F) < 1 ↔ W₂.valuation (b : F) < 1)
    {x : F} (hx : x ∈ W₁) : x ∈ W₂ := by
  obtain ⟨b, s, hs1, hmul⟩ := (mem_iff_rep O W₁ h₁ x).mp hx
  have hsle : W₂.valuation (s : F) ≤ 1 := val_le_one_of_isIntegral O W₂ h₂ s.2
  have hs2 : W₂.valuation (s : F) = 1 := by
    rcases lt_or_eq_of_le hsle with hlt | he
    · exfalso
      have := (hag s).mpr hlt
      rw [hs1] at this
      exact lt_irrefl 1 this
    · exact he
  have hble : W₂.valuation (b : F) ≤ 1 := val_le_one_of_isIntegral O W₂ h₂ b.2
  have hxv : W₂.valuation x * W₂.valuation (s : F) = W₂.valuation (b : F) := by
    rw [← map_mul, hmul]
  rw [hs2, mul_one] at hxv
  exact W₂.mem_of_valuation_le_one x (le_of_eq_of_le hxv hble)

end EsbG2bPrufer

private theorem mem_iff_exists_integralClosure_valuation_eq_one_mul_eq
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [Algebra.IsAlgebraic E F]
    (O : ValuationSubring E)
    (O' : ValuationSubring F)
    (hO : ∀ x : E, algebraMap E F x ∈ O' ↔ x ∈ O) :
    (∀ x : F, x ∈ O' ↔ ∃ b s : integralClosure O F, O'.valuation (s : F) = 1 ∧ x * s = b) ∧
    (∀ O'' : ValuationSubring F, (∀ x : E, algebraMap E F x ∈ O'' ↔ x ∈ O) →
      (∀ b : integralClosure O F, O'.valuation (b : F) < 1 ↔
        O''.valuation (b : F) < 1) → O'' = O') := by
  constructor
  · intro x
    exact EsbG2bPrufer.mem_iff_rep O O' hO x
  · intro O'' hO'' hagree
    ext x
    constructor
    · intro hx
      exact EsbG2bPrufer.mem_of_agree O O'' O' hO'' hO (fun b => (hagree b).symm) hx
    · intro hx
      exact EsbG2bPrufer.mem_of_agree O O' O'' hO hO'' hagree hx

namespace HensUniq

open Polynomial IsLocalRing

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private noncomputable def incl (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) : O →+* V where
  toFun o := ⟨algebraMap K L o, (hV o).mpr o.2⟩
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

@[scoped simp] private lemma incl_apply (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) (o : O) :
    ((incl O V hV o : V) : L) = algebraMap K L o := rfl

private lemma algebraMap_comp_incl (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) :
    (algebraMap V L).comp (incl O V hV) = algebraMap O L := by
  ext o
  rfl

private lemma mem_of_isIntegral (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) {x : L} (hx : IsIntegral O x) : x ∈ V := by
  have hx' : IsIntegral V x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (incl O V hV), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, algebraMap_comp_incl]
    exact hpx
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).mp hx'
  rw [← hy]
  exact y.2

private lemma isUnit_incl_iff (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) (o : O) :
    IsUnit (incl O V hV o) ↔ IsUnit o := by
  constructor
  · intro hu
    by_contra hno
    have ho0 : (o : K) ≠ 0 := by
      intro h0
      have : incl O V hV o = 0 := by
        ext
        simp [h0]
      rw [this] at hu
      exact not_isUnit_zero hu

    have hinvV : (algebraMap K L (o : K))⁻¹ ∈ V := by
      obtain ⟨u, hu'⟩ := hu
      have h1 : (((u⁻¹ : Vˣ) : V) : L) * ((u : V) : L) = 1 := by
        have h := u.inv_mul
        rw [Subtype.ext_iff] at h
        exact h
      have h2 : (((u⁻¹ : Vˣ) : V) : L) = ((u : V) : L)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : ((u : V) : L) = algebraMap K L (o : K) := by
        rw [hu']
        rfl
      rw [← h3, ← h2]
      exact ((u⁻¹ : Vˣ) : V).2
    have hinvO : (o : K)⁻¹ ∈ O := by
      rw [← hV]
      simpa using hinvV
    apply hno
    refine isUnit_iff_exists_inv.mpr ⟨⟨(o : K)⁻¹, hinvO⟩, ?_⟩
    ext
    simp [ho0]
  · intro hu
    exact hu.map _

private lemma incl_mem_maximalIdeal_iff (O : ValuationSubring K) (V : ValuationSubring L)
    (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) (o : O) :
    incl O V hV o ∈ maximalIdeal V ↔ o ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_incl_iff]

private lemma isIntegral_inv_of_valuation_eq_one (O : ValuationSubring K) [HenselianLocalRing O]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O)
    {s : L} (hs : IsIntegral O s) (hs1 : V.valuation s = 1) : IsIntegral O s⁻¹ := by

  set S : Subalgebra O L := Algebra.adjoin O {s} with hSdef
  haveI : Module.Finite O S := Algebra.finite_adjoin_simple_of_isIntegral hs
  haveI : Algebra.IsIntegral O S := Algebra.IsIntegral.of_finite O S
  haveI : IsLocalRing S :=
    S17Hens.isLocalRing_of_isDomain_of_moduleFinite (R := O) (S := S)

  have hSle : S ≤ integralClosure O L := by
    refine Algebra.adjoin_le ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (mem_integralClosure_iff O L).mpr hs
  have hSV : ∀ y : S, (y : L) ∈ V := fun y =>
    mem_of_isIntegral O V hV ((mem_integralClosure_iff O L).mp (hSle y.2))

  let φ : S →+* V :=
    { toFun := fun y => ⟨(y : L), hSV y⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hφO : φ.comp (algebraMap O S) = incl O V hV := by
    ext o
    rfl

  let P : Ideal S := Ideal.comap φ (maximalIdeal V)
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime φ (maximalIdeal V)
  have hPO : Ideal.comap (algebraMap O S) P = maximalIdeal O := by
    ext o
    change φ (algebraMap O S o) ∈ maximalIdeal V ↔ _
    rw [show φ (algebraMap O S o) = incl O V hV o from by rw [← hφO]; rfl]
    exact incl_mem_maximalIdeal_iff O V hV o
  have hPmax : P.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) P ?_
    rw [Ideal.under_def, hPO]
    exact IsLocalRing.maximalIdeal.isMaximal O
  have hPeq : P = maximalIdeal S := IsLocalRing.eq_maximalIdeal hPmax

  let sS : S := ⟨s, Algebra.self_mem_adjoin_singleton O s⟩
  have hsunit : IsUnit sS := by
    by_contra hns
    have hmem : sS ∈ maximalIdeal S := by
      rw [IsLocalRing.mem_maximalIdeal]
      exact hns
    rw [← hPeq] at hmem
    change φ sS ∈ maximalIdeal V at hmem
    rw [ValuationSubring.valuation_lt_one_iff] at hmem
    change V.valuation s < 1 at hmem
    rw [hs1] at hmem
    exact lt_irrefl _ hmem
  obtain ⟨t, ht⟩ := isUnit_iff_exists_inv.mp hsunit
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hs1
    exact zero_ne_one hs1
  have htL : (t : L) = s⁻¹ := by
    have h1 : s * (t : L) = 1 := by
      have := congrArg (fun z : S => (z : L)) ht
      simpa using this
    field_simp
    simpa [mul_comm] using h1
  rw [← htL]
  exact (mem_integralClosure_iff O L).mp (hSle t.2)

private lemma isIntegral_of_mem (O : ValuationSubring K) [HenselianLocalRing O]
    [Algebra.IsAlgebraic K L]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O)
    {x : L} (hx : x ∈ V) : IsIntegral O x := by
  obtain ⟨hfrac, -⟩ :=
    mem_iff_exists_integralClosure_valuation_eq_one_mul_eq O V hV
  obtain ⟨b, s, hs1, hxs⟩ := (hfrac x).mp hx
  have hsint : IsIntegral O (s : L) := (mem_integralClosure_iff O L).mp s.2
  have hbint : IsIntegral O (b : L) := (mem_integralClosure_iff O L).mp b.2
  have hs0 : (s : L) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hs1
    exact zero_ne_one hs1
  have hx' : x = (b : L) * (s : L)⁻¹ := by
    rw [← hxs]
    field_simp
  rw [hx']
  exact hbint.mul (isIntegral_inv_of_valuation_eq_one O V hV hsint hs1)

private theorem main (O : ValuationSubring K) [HenselianLocalRing O] [Algebra.IsAlgebraic K L]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) :
    (∀ x : L, x ∈ V ↔ IsIntegral O x) ∧
      ∀ V' : ValuationSubring L, (∀ x : K, algebraMap K L x ∈ V' ↔ x ∈ O) → V' = V := by
  have key : ∀ (W : ValuationSubring L), (∀ x : K, algebraMap K L x ∈ W ↔ x ∈ O) →
      ∀ x : L, x ∈ W ↔ IsIntegral O x := fun W hW x =>
    ⟨fun hx => isIntegral_of_mem O W hW hx, fun hx => mem_of_isIntegral O W hW hx⟩
  refine ⟨key V hV, fun V' hV' => ?_⟩
  ext x
  rw [key V' hV' x, key V hV x]

end HensUniq

namespace ValuationSubring

/-- A valuation subring of an algebraic field extension that extends a
Henselian valuation ring is exactly its integral closure, and it is the
unique such extension: membership is integrality over the base ring, and
any two extensions with the same pullback coincide.

This does not assert that an extension exists; it characterizes and
compares extensions that are given. -/
public theorem forall_mem_iff_isIntegral_and_eq_of_henselianLocalRing
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (O : ValuationSubring K) [HenselianLocalRing O]
    (V : ValuationSubring L) (hV : ∀ x : K, algebraMap K L x ∈ V ↔ x ∈ O) :
    (∀ x : L, x ∈ V ↔ IsIntegral O x) ∧
      ∀ V' : ValuationSubring L, (∀ x : K, algebraMap K L x ∈ V' ↔ x ∈ O) → V' = V :=
  HensUniq.main O V hV

end ValuationSubring
