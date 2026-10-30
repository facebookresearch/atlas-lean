/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible.lean`,
`P2M/Sol/S_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible.lean`,
`Theorems/Thm_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible.lean` and
`P2M/Sol/S_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible.lean`
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
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Discrete valuation ring quotients of power series

Modulo `X - ϖ ^ e`, a power series ring over a discrete valuation ring is a
discrete valuation ring with uniformizer the image of `ϖ`; for `e = 1` it is
also adically complete at its maximal ideal.
-/

@[expose] public section

namespace PowerSeriesDVRQuotientAux

private theorem mem_smul_top_of_mem {R : Type*} [CommRing R] {I : Ideal R} {x : R}
    (hx : x ∈ I) : x ∈ (I • ⊤ : Submodule R R) := by
  have h := Submodule.smul_mem_smul hx (Submodule.mem_top : (1 : R) ∈ ⊤)
  simpa only [smul_eq_mul, mul_one] using h

private theorem smul_top_le {R : Type*} [CommRing R] (I : Ideal R) :
    (I • ⊤ : Submodule R R) ≤ I :=
  Submodule.smul_le.mpr fun _r hr x _ => Ideal.mul_mem_right x I hr

private theorem isPrecomplete_quotient {R : Type*} [CommRing R] (I P : Ideal R)
    [IsPrecomplete I R] : IsPrecomplete I (R ⧸ P) := by
  classical
  refine ⟨fun f hf => ?_⟩
  have hstep : ∀ n, ∃ r : R, r ∈ I ^ n ∧ Ideal.Quotient.mk P r = f (n + 1) - f n := by
    intro n
    have h := hf (Nat.le_succ n)
    rw [SModEq.sub_mem, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
      Ideal.Quotient.algebraMap_eq, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
      at h
    obtain ⟨r, hr, hr'⟩ := h
    exact ⟨-r, neg_mem hr, by rw [map_neg, hr', neg_sub]⟩
  choose r hrI hrq using hstep
  obtain ⟨g0, hg0⟩ := Ideal.Quotient.mk_surjective (f 0)
  let g : ℕ → R := fun n => Nat.rec g0 (fun k acc => acc + r k) n
  have hg_succ : ∀ n, g (n + 1) = g n + r n := fun n => rfl
  have hgq : ∀ n, Ideal.Quotient.mk P (g n) = f n := by
    intro n
    induction n with
    | zero => exact hg0
    | succ n ih => rw [hg_succ, map_add, ih, hrq]; abel
  have hgc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    induction hmn with
    | refl => rw [sub_self]; exact Submodule.zero_mem _
    | @step k hle ih =>
      rw [hg_succ, show g m - (g k + r k) = (g m - g k) - r k by ring]
      exact Submodule.sub_mem _ ih (mem_smul_top_of_mem (Ideal.pow_le_pow_right hle (hrI k)))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' g (fun hmn => hgc hmn)
  refine ⟨Ideal.Quotient.mk P L, fun n => ?_⟩
  have h1 : g n - L ∈ I ^ n := smul_top_le _ ((SModEq.sub_mem).mp (hL n))
  rw [SModEq.sub_mem, ← hgq n, ← map_sub]
  have h2 := Submodule.smul_mem_smul h1 (Submodule.mem_top : (1 : R ⧸ P) ∈ ⊤)
  rwa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one] at h2

end PowerSeriesDVRQuotientAux

/-- Modulo `X - ϖ ^ e`, a power series ring over a discrete valuation ring
is a principal ideal ring and a local ring, and the image of `ϖ` is
irreducible. -/
theorem PowerSeries.quotient_span_X_sub_C_pow_of_irreducible
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}).IsPrime ∧
    IsPrincipalIdealRing (PowerSeries W ⧸
      Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}) ∧
    IsLocalRing (PowerSeries W ⧸
      Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)}) ∧
    Irreducible (Ideal.Quotient.mk
      (Ideal.span {(PowerSeries.X : PowerSeries W) - PowerSeries.C (ϖ ^ e)})
      (PowerSeries.C ϖ)) := by
  have hmW : IsLocalRing.maximalIdeal W = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖu : ¬IsUnit ϖ := hϖ.not_isUnit
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal W := hϖu
  set c : W := ϖ ^ e with hc
  have hcu : ¬IsUnit c := by
    rw [hc]; exact fun h => hϖu (isUnit_pow_iff (by omega) |>.mp h)
  have hc0 : c ≠ 0 := pow_ne_zero e hϖ0
  set g : PowerSeries W := PowerSeries.X - PowerSeries.C c with hg
  have hg0 : PowerSeries.constantCoeff g = -c := by
    simp [hg]
  have hg1 : PowerSeries.coeff 1 g = 1 := by
    simp [hg, PowerSeries.coeff_X]
  have hgirr : Irreducible g := by
    refine irreducible_iff.mpr ⟨?_, ?_⟩
    · intro hu
      rw [PowerSeries.isUnit_iff_constantCoeff, hg0] at hu
      exact hcu (by simpa using hu)
    · intro a b hab
      by_contra hnot
      push Not at hnot
      obtain ⟨ha, hb⟩ := hnot
      rw [PowerSeries.isUnit_iff_constantCoeff] at ha hb
      have ha' : PowerSeries.constantCoeff a ∈ IsLocalRing.maximalIdeal W := ha
      have hb' : PowerSeries.constantCoeff b ∈ IsLocalRing.maximalIdeal W := hb
      have h1 := congrArg (PowerSeries.coeff 1) hab
      rw [hg1] at h1
      simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h1
      norm_num at h1
      apply (IsLocalRing.maximalIdeal.isMaximal W).ne_top
      rw [Ideal.eq_top_iff_one, h1]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha') (Ideal.mul_mem_left _ _ hb')
  have hgne : g ≠ 0 := hgirr.ne_zero
  have : UniqueFactorizationMonoid (PowerSeries W) := inferInstance
  have hgprime : Prime g := UniqueFactorizationMonoid.irreducible_iff_prime.mp hgirr
  set I : Ideal (PowerSeries W) := Ideal.span {g} with hI
  have hIprime : I.IsPrime := (Ideal.span_singleton_prime hgne).mpr hgprime
  have _ := hIprime
  set D := PowerSeries W ⧸ I
  have : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr hIprime.ne_top
  have : IsDomain D := Ideal.Quotient.isDomain I
  have hDloc : IsLocalRing D :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have _ : IsNoetherianRing D := inferInstance
  set π : D := Ideal.Quotient.mk I (PowerSeries.C ϖ) with hπ
  have hXc : Ideal.Quotient.mk I PowerSeries.X = Ideal.Quotient.mk I (PowerSeries.C c) := by
    rw [Ideal.Quotient.eq, hI]
    exact Ideal.subset_span rfl
  have hXπ : Ideal.Quotient.mk I PowerSeries.X = π ^ e := by
    rw [hXc, hπ, ← map_pow, ← map_pow]
  have hπu : ¬IsUnit π := by
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hπ, ← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, hI,
      Ideal.mem_span_singleton] at hy
    obtain ⟨H, hH⟩ := hy
    have h0 := congrArg PowerSeries.constantCoeff hH
    simp only [map_sub, map_mul, map_one, PowerSeries.constantCoeff_C, hg0] at h0
    apply hϖu
    apply isUnit_of_dvd_one
    refine ⟨PowerSeries.constantCoeff G + ϖ ^ (e - 1) * PowerSeries.constantCoeff H, ?_⟩
    have hthis : ϖ ^ e = ϖ * ϖ ^ (e - 1) := by
      rw [← pow_succ']; congr 1; omega
    linear_combination (-1 : W) * h0 + (PowerSeries.constantCoeff H) * hthis
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [hπ, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton] at h0
    obtain ⟨H, hH⟩ := h0
    have e0 := congrArg PowerSeries.constantCoeff hH
    have e1 := congrArg (PowerSeries.coeff 1) hH
    simp only [PowerSeries.constantCoeff_C, map_mul, hg0] at e0
    simp only [PowerSeries.coeff_C, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, hg1] at e1
    norm_num at e1
    rw [hg0] at e1
    have h2 : ϖ ^ (2 * e) = ϖ * ϖ ^ (2 * e - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h3 : c * c = ϖ ^ (2 * e) := by rw [hc, ← pow_add]; congr 1; omega
    have key : ϖ * (1 + ϖ ^ (2 * e - 1) * PowerSeries.coeff 1 H) = 0 := by
      linear_combination e0 + c * e1 - (PowerSeries.coeff 1 H) * h2 -
        (PowerSeries.coeff 1 H) * h3
    have hxm : -(ϖ ^ (2 * e - 1) * PowerSeries.coeff 1 H) ∈ IsLocalRing.maximalIdeal W :=
      Submodule.neg_mem _ (Ideal.mul_mem_right _ _
        (Ideal.pow_mem_of_mem _ hϖm _ (by omega)))
    have hunit : IsUnit (1 + ϖ ^ (2 * e - 1) * PowerSeries.coeff 1 H) := by
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add
          (a := 1 + ϖ ^ (2 * e - 1) * PowerSeries.coeff 1 H)
          (b := -(ϖ ^ (2 * e - 1) * PowerSeries.coeff 1 H)) (by simp) with h | h
      · exact h
      · exact absurd h hxm
    rcases mul_eq_zero.mp key with h | h
    · exact hϖ0 h
    · exact hunit.ne_zero h
  have hπm : π ∈ IsLocalRing.maximalIdeal D := hπu
  have hmax : IsLocalRing.maximalIdeal D = Ideal.span {π} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hFu : ¬IsUnit F := fun h => hx (h.map _)
      rw [PowerSeries.isUnit_iff_constantCoeff] at hFu
      have hF0 : PowerSeries.constantCoeff F ∈ IsLocalRing.maximalIdeal W := hFu
      rw [hmW, Ideal.mem_span_singleton] at hF0
      obtain ⟨w, hw⟩ := hF0
      have hF := PowerSeries.eq_X_mul_shift_add_const F
      rw [Ideal.mem_span_singleton]
      refine ⟨π ^ (e - 1) * Ideal.Quotient.mk I
        (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) F) +
        Ideal.Quotient.mk I (PowerSeries.C w), ?_⟩
      conv_lhs => rw [hF]
      rw [map_add, map_mul, hXπ, hw, map_mul, map_mul, ← hπ]
      have hthis : π ^ e = π * π ^ (e - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hthis]; ring
    · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hπm
  have hnf : ¬IsField D := by
    intro hF
    have hthis := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hF
    rw [hthis] at hπm
    exact hπ0 hπm
  have hprinc : (IsLocalRing.maximalIdeal D).IsPrincipal := ⟨⟨π, hmax⟩⟩
  have hDVR : IsDiscreteValuationRing D :=
    ((IsDiscreteValuationRing.TFAE D hnf).out 5 1).mp hprinc
  refine ⟨hIprime, inferInstance, hDloc, ?_⟩
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hmax

/-- Modulo `X - ϖ`, a power series ring over a discrete valuation ring is a
discrete valuation ring, adically complete at its maximal ideal, with
uniformizer the image of `ϖ`. -/
theorem PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : Irreducible ϖ) :
    ∃ (_ : IsDomain (PowerSeries O ⧸
        Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
      (_ : IsDiscreteValuationRing (PowerSeries O ⧸
        Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
      (_ : IsAdicComplete
        (IsLocalRing.maximalIdeal (PowerSeries O ⧸
          Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
        (PowerSeries O ⧸
          Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})),
      Irreducible (Ideal.Quotient.mk
        (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})
        (PowerSeries.C ϖ)) := by
  classical
  set P : Ideal (PowerSeries O) :=
    Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ} with hPdef
  obtain ⟨hprime, hPIR, hloc, hirr⟩ : P.IsPrime ∧ IsPrincipalIdealRing (PowerSeries O ⧸ P) ∧
      IsLocalRing (PowerSeries O ⧸ P) ∧
      Irreducible (Ideal.Quotient.mk P (PowerSeries.C ϖ)) := by
    have h := PowerSeries.quotient_span_X_sub_C_pow_of_irreducible ϖ hϖ 1 le_rfl
    rw [pow_one] at h
    exact h
  have _ : P.IsPrime := hprime
  have hdom : IsDomain (PowerSeries O ⧸ P) := Ideal.Quotient.isDomain P
  have _ := hPIR
  have _ := hloc
  have hne : Ideal.Quotient.mk P (PowerSeries.C ϖ) ≠ 0 := hirr.ne_zero
  have hnu : ¬ IsUnit (Ideal.Quotient.mk P (PowerSeries.C ϖ)) := hirr.not_isUnit
  have hdvr : IsDiscreteValuationRing (PowerSeries O ⧸ P) := by
    refine ⟨fun hbot => hne ?_⟩
    have hm : Ideal.Quotient.mk P (PowerSeries.C ϖ) ∈
        IsLocalRing.maximalIdeal (PowerSeries O ⧸ P) :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    rw [hbot] at hm
    exact (Submodule.mem_bot _).mp hm
  have hX : Ideal.Quotient.mk P (PowerSeries.X : PowerSeries O) =
      Ideal.Quotient.mk P (PowerSeries.C ϖ) := by
    rw [Ideal.Quotient.eq, hPdef]
    exact Ideal.subset_span rfl
  have hmax : IsLocalRing.maximalIdeal (PowerSeries O ⧸ P)
      = (Ideal.span {(PowerSeries.X : PowerSeries O)}).map (Ideal.Quotient.mk P) := by
    rw [Ideal.map_span, Set.image_singleton, hX]
    exact hirr.maximalIdeal_eq
  have hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries O ⧸ P))
      (PowerSeries O ⧸ P) := by
    rw [hmax]
    have hH : IsHausdorff ((Ideal.span {(PowerSeries.X : PowerSeries O)}).map
        (Ideal.Quotient.mk P)) (PowerSeries O ⧸ P) := by
      refine IsHausdorff.of_isLocalRing _ _ ?_
      rw [← hmax]
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    have hPc : IsPrecomplete ((Ideal.span {(PowerSeries.X : PowerSeries O)}).map
        (Ideal.Quotient.mk P)) (PowerSeries O ⧸ P) := by
      rw [← Ideal.Quotient.algebraMap_eq, IsPrecomplete.map_algebraMap_iff]
      exact PowerSeriesDVRQuotientAux.isPrecomplete_quotient _ _
    exact ⟨⟩
  exact ⟨hdom, hdvr, hcomplete, hirr⟩
