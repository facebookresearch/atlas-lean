/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le.lean`
and
`P2M/Sol/S_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le.lean`
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

public import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

/-!
# Vanishing at the cusp after multiplying by the discriminant

This file reads off vanishing at the cusp of `F Δ` from the q-expansion of `F Δ ^ M`.

## Main statement

* `ModularForm.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le`
-/
namespace FrickeFunctions.DiscriminantCuspOrder

noncomputable section

open Complex
open Real
open UpperHalfPlane
open Function
open Filter
open Polynomial
open Real.Polynomial
open scoped Topology Manifold MatrixGroups ModularForm

namespace Aux

section Division

private theorem powerSeries_coeff_mem_of_mul_eq {K : Type*} [Field K] (k : Subfield K)
    {g h f : PowerSeries K} (heq : g * h = f) (hg0 : PowerSeries.constantCoeff g ≠ 0)
    (hg : ∀ n, PowerSeries.coeff n g ∈ k) (hf : ∀ n, PowerSeries.coeff n f ∈ k) :
    ∀ n, PowerSeries.coeff n h ∈ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hcm := PowerSeries.coeff_mul n g h
  rw [heq] at hcm
  have h0n : (0, n) ∈ Finset.HasAntidiagonal.antidiagonal n :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add n)
  rw [← Finset.add_sum_erase _ _ h0n] at hcm
  have hg0' : PowerSeries.coeff 0 g ≠ 0 := by
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hrest : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
      PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 h) ∈ k := by
    refine sum_mem fun p hp ↦ mul_mem (hg p.1) (ih p.2 ?_)
    obtain ⟨hpne, hpmem⟩ := Finset.mem_erase.mp hp
    have hpsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hpmem
    rcases p with ⟨p1, p2⟩
    simp only [Prod.mk.injEq, not_and, ne_eq] at hpne
    dsimp only at hpsum
    omega
  have hn : PowerSeries.coeff n h = (PowerSeries.coeff 0 g)⁻¹ *
      (PowerSeries.coeff n f - ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n),
        PowerSeries.coeff p.1 g * PowerSeries.coeff p.2 h) := by
    rw [eq_inv_mul_iff_mul_eq₀ hg0', eq_sub_iff_add_eq]
    exact hcm.symm
  rw [hn]
  exact mul_mem (inv_mem (hg 0)) (sub_mem (hf n) hrest)

private theorem powerSeries_coeff_mem_of_mul_eq' {K : Type*} [Field K] (k : Subfield K)
    {g h f : PowerSeries K} (heq : g * h = f) (hg0 : g ≠ 0)
    (hg : ∀ n, PowerSeries.coeff n g ∈ k) (hf : ∀ n, PowerSeries.coeff n f ∈ k) :
    ∀ n, PowerSeries.coeff n h ∈ k := by
  set r := (PowerSeries.order g).toNat with hr_def
  obtain ⟨g', hg'⟩ : (PowerSeries.X : PowerSeries K) ^ r ∣ g := PowerSeries.X_pow_dvd_iff.mpr
    (fun m hm ↦ PowerSeries.coeff_of_lt_order_toNat (φ := g) m hm)
  have hg'_coeff : ∀ n, PowerSeries.coeff n g' ∈ k := fun n ↦ by
    have h1 := hg (n + r)
    rwa [hg', PowerSeries.coeff_X_pow_mul g' r n] at h1
  have hg'_cc : PowerSeries.constantCoeff g' ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    intro habs
    refine (PowerSeries.coeff_order hg0) ?_
    change PowerSeries.coeff r g = 0
    rw [hg', PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, habs]
  obtain ⟨f', hf'⟩ : PowerSeries.X ^ r ∣ f := ⟨g' * h, by rw [← heq, hg', mul_assoc]⟩
  have hf'_coeff : ∀ n, PowerSeries.coeff n f' ∈ k := fun n ↦ by
    have h1 := hf (n + r); rwa [hf', PowerSeries.coeff_X_pow_mul f' r n] at h1
  have heq' : g' * h = f' := by
    have hX : (PowerSeries.X : PowerSeries K) ^ r ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
    have h2 := hf' ▸ hg' ▸ heq
    rw [mul_assoc] at h2
    exact mul_left_cancel₀ hX h2
  exact powerSeries_coeff_mem_of_mul_eq k heq' hg'_cc hg'_coeff hf'_coeff

private theorem norm_le_of_monicRel {K : Type*} [NormedField K] {z : K} {a : ℕ → K} {d : ℕ}
    (h : z ^ d + ∑ n ∈ Finset.range d, a n * z ^ n = 0) :
    ‖z‖ ≤ 1 + ∑ n ∈ Finset.range d, ‖a n‖ := by
  have hsum : ‖z‖ ^ d ≤ ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ n := by
    calc ‖z‖ ^ d = ‖z ^ d‖ := (norm_pow _ _).symm
      _ = ‖-∑ n ∈ Finset.range d, a n * z ^ n‖ :=
          congrArg _ (eq_neg_of_add_eq_zero_left h)
      _ = ‖∑ n ∈ Finset.range d, a n * z ^ n‖ := norm_neg _
      _ ≤ ∑ n ∈ Finset.range d, ‖a n * z ^ n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ n :=
          Finset.sum_congr rfl fun n _ ↦ by rw [norm_mul, norm_pow]
  rcases le_or_gt ‖z‖ 1 with h1 | h1
  · exact h1.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _))
  · have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos h1.le
    have hd : 0 < d := by
      by_contra hd0
      simp only [Nat.eq_zero_of_not_pos hd0, pow_zero, Finset.range_zero,
        Finset.sum_empty] at hsum
      exact absurd hsum (not_le.mpr one_pos)
    have hpow : ∀ n ∈ Finset.range d, ‖z‖ ^ n ≤ ‖z‖ ^ (d - 1) := fun n hn ↦
      pow_le_pow_right₀ h1.le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hn))
    have : ‖z‖ ^ d ≤ (∑ n ∈ Finset.range d, ‖a n‖) * ‖z‖ ^ (d - 1) := by
      calc ‖z‖ ^ d ≤ ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ n := hsum
        _ ≤ ∑ n ∈ Finset.range d, ‖a n‖ * ‖z‖ ^ (d - 1) :=
            Finset.sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_left (hpow n hn) (norm_nonneg _)
        _ = (∑ n ∈ Finset.range d, ‖a n‖) * ‖z‖ ^ (d - 1) := (Finset.sum_mul ..).symm
    have hzd : ‖z‖ ^ d = ‖z‖ * ‖z‖ ^ (d - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hd]
    rw [hzd] at this
    have := le_of_mul_le_mul_right (a := ‖z‖ ^ (d - 1)) this (pow_pos hzpos _)
    linarith

open Asymptotics in
private theorem isBoundedAtImInfty_of_monicRel {H : ℍ → ℂ} {c : ℕ → ℍ → ℂ} {d : ℕ}
    (hc : ∀ n < d, IsBoundedAtImInfty (c n))
    (hrel : ∀ τ : ℍ, H τ ^ d + ∑ n ∈ Finset.range d, c n τ * H τ ^ n = 0) :
    IsBoundedAtImInfty H := by
  classical
  choose! C hC using fun n (hn : n < d) ↦ isBigO_iff.mp (hc n hn)
  simp only [Pi.one_apply, norm_one, mul_one] at hC
  have hCev : ∀ᶠ τ in atImInfty, ∀ n ∈ Finset.range d, ‖c n τ‖ ≤ C n :=
    eventually_all_finset (Finset.range d) |>.mpr fun n hn ↦ hC n (Finset.mem_range.mp hn)
  refine IsBigO.of_bound (1 + ∑ n ∈ Finset.range d, C n) (hCev.mono fun τ hτ ↦ ?_)
  rw [Pi.one_apply, norm_one, mul_one]
  calc ‖H τ‖ ≤ 1 + ∑ n ∈ Finset.range d, ‖c n τ‖ :=
        norm_le_of_monicRel (a := fun n ↦ c n τ) (hrel τ)
    _ ≤ 1 + ∑ n ∈ Finset.range d, C n := by gcongr with n hn; exact hτ n hn

end Division

section CuspCriterion

variable {N : ℕ}

private lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ →
    ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

private lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ Filter.const_boundedAtFilter _ (1 : ℂ)
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul isBoundedAtImInfty_discriminant

private lemma IsBoundedAtImInfty.mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
    (h : IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)) :
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m') := by
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  rw [hshape]
  exact h.mul (isBoundedAtImInfty_discPow (m' - m))

private def discPowForm (m : ℕ) : ModularForm 𝒮ℒ (12 * m) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow m)

private lemma discPowForm_coe (m : ℕ) : ⇑(discPowForm m) = ⇑CuspForm.discriminant ^ m := by
  funext z
  simp [discPowForm, ModularForm.coe_mcast, ModularForm.coe_pow,
    CuspForm.toModularFormₗ_apply]

private lemma periodic_one_fn (c : ℝ) : Function.Periodic ((1 : ℍ → ℂ) ∘ ofComplex) c :=
    fun _ => rfl

private lemma periodic_discPow_comp_ofComplex (k : ℕ) (N : ℕ) :
    Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) N := by
  have h1 : Function.Periodic (⇑CuspForm.discriminant ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL
  have hk : Function.Periodic ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) 1 := by
    induction k with
    | zero => exact periodic_one_fn 1
    | succ k ih =>
      intro x
      have hx := (ih.mul h1) x
      simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply] at hx ⊢
      rw [pow_succ, pow_succ]
      exact hx
  simpa using hk.nat_mul N

private lemma mdiff_discPow (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑CuspForm.discriminant ^ k : ℍ → ℂ) := by
  rw [← discPowForm_coe]
  exact (discPowForm k).holo'

private lemma mdiff_mul_discPow {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (m : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) :=
  hf.mul (mdiff_discPow m)

private lemma analyticAt_cuspFunction_zero_of [NeZero N] {g : ℍ → ℂ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Function.Periodic (g ∘ ofComplex) N) (hbd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction N g) 0 :=
  analyticAt_cuspFunction_zero
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd

private lemma qExpansion_one_discPowForm (k : ℕ) :
    qExpansion 1 (discPowForm k) = (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [discPowForm, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hco : (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) =
      ModularForm.discriminant := by
    funext z
    rw [CuspForm.toModularFormₗ_apply]
    exact congrFun CuspForm.coe_discriminant z
  rw [hco]

private lemma qExpansion_one_discPow (k : ℕ) :
    qExpansion 1 (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [← discPowForm_coe]
  exact qExpansion_one_discPowForm k

private lemma coeff_pow_eq_zero_of_lt {D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) {k n : ℕ}
    (hn : n < k) : (D ^ k).coeff n = 0 := by
  have hX : (PowerSeries.X : PowerSeries ℂ) ∣ D :=
    PowerSeries.X_dvd_iff.mpr (by rwa [← PowerSeries.coeff_zero_eq_constantCoeff])
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX k) n hn

private lemma discriminant_qExpansion_coeff_zero :
    (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

private lemma qParam_one_eq_pow {N : ℕ} (hN : N ≠ 0) (τ : ℂ) :
    Function.Periodic.qParam 1 τ = Function.Periodic.qParam N τ ^ N := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one, Complex.ofReal_natCast]
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

private theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperN : Function.Periodic (f ∘ ofComplex) N := by
    simpa using hper.nat_mul N
  let f' : C(ℍ, ℂ) := ⟨f, hhol.continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN' hperN hhol hbd
  set c : ℕ → ℂ := fun n ↦ if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 with hc
  have hf : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam N τ ^ m) (f' τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos hper hhol hbd τ
    have hinj : Function.Injective fun m : ℕ ↦ N * m := fun a b h ↦ by
      simpa [Nat.mul_right_inj hN] using h
    refine (hinj.hasSum_iff (f := fun m ↦ c m • Function.Periodic.qParam N τ ^ m) ?_).mp ?_
    · intro x hx
      have : ¬ N ∣ x := fun ⟨k, hk⟩ ↦ hx ⟨k, hk.symm⟩
      simp [hc, this]
    · refine h1.congr_fun fun m ↦ ?_
      simp only [Function.comp_apply, hc, Nat.dvd_mul_right, ite_true,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN), qParam_one_eq_pow hN, ← pow_mul]
  exact (qExpansion_coeff_unique f' hN' hfan hf n).symm

private theorem isZeroAtImInfty_iff_qExpansion_coeff_zero_eq_zero {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfbdd : IsBoundedAtImInfty f) :
    IsZeroAtImInfty f ↔ (qExpansion h f).coeff 0 = 0 := by
  have hanal := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  rw [qExpansion_coeff_zero hh hanal hfper]
  refine ⟨fun hf ↦ hf.valueAtInfty_eq_zero, fun hv ↦ ?_⟩
  rw [IsZeroAtImInfty, ZeroAtFilter, ← hv, ← cuspFunction_apply_zero hh hanal hfper]
  exact (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr
    (fun τ ↦ eq_cuspFunction τ hh.ne' hfper)

open Asymptotics in
private theorem isBigO_qParam_pow_of_qExpansion_coeff_eq_zero {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ}
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hfbdd : IsBoundedAtImInfty f)
    {k : ℕ} (hcoeff : ∀ n ≤ k, (qExpansion h f).coeff n = 0) :
    f =O[atImInfty] fun τ ↦ (Periodic.qParam h τ) ^ (k + 1) := by
  have hanal := analyticAt_cuspFunction_zero hh hfper hfhol hfbdd
  have hideriv : ∀ i < k + 1, iteratedDeriv i (cuspFunction h f) 0 = 0 := by
    intro i hi
    have hci := hcoeff i (Nat.lt_succ_iff.mp hi)
    rw [qExpansion_coeff] at hci
    have hfac : ((i.factorial : ℂ))⁻¹ ≠ 0 :=
      inv_ne_zero (Nat.cast_ne_zero.mpr i.factorial_ne_zero)
    exact (mul_eq_zero.mp hci).resolve_left hfac
  have hord : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (cuspFunction h f) 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanal).mpr hideriv
  obtain ⟨g, hgan, hfac⟩ := (natCast_le_analyticOrderAt hanal).mp hord
  have hOcf : (cuspFunction h f) =O[𝓝 0] fun q : ℂ ↦ q ^ (k + 1) := by
    have hg1 : g =O[𝓝 (0 : ℂ)] (fun _ : ℂ ↦ (1 : ℂ)) := hgan.continuousAt.isBigO_one ℂ
    refine ((isBigO_refl (fun q : ℂ ↦ q ^ (k + 1)) (𝓝 0)).mul hg1).congr' ?_
      (.of_forall fun q ↦ mul_one _)
    filter_upwards [hfac] with q hq
    rw [hq, sub_zero, smul_eq_mul]
  refine (hOcf.comp_tendsto (qParam_tendsto_atImInfty hh)).congr' ?_ (.of_forall fun τ ↦ rfl)
  exact .of_forall fun τ ↦ eq_cuspFunction τ hh.ne' hfper

open Asymptotics ModularForm in
private theorem qParam_pow_isBigO_discPow {N : ℕ} (hN : N ≠ 0) (k : ℕ) :
    (fun τ : ℍ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * k)) =O[atImInfty]
      (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ k) := by
  refine .trans (IsBigO.of_bound 1 (.of_forall fun τ ↦ le_of_eq ?_)) (exp_isBigO_discriminant.pow k)
  rw [one_mul, norm_pow, norm_pow, Real.norm_of_nonneg (Real.exp_pos _).le,
    pow_mul, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, UpperHalfPlane.coe_im]
  congr 2
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp

open Asymptotics ModularForm in
private theorem isZeroAtImInfty_mul_disc_of_coeff_le {N : ℕ} (hN : N ≠ 0) {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M)
    (hfhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F * ⇑CuspForm.discriminant ^ M))
    (hfper : Periodic ((F * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N)
    (hfbd : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ M))
    (hcoeff : ∀ n ≤ N * (M - 1), (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0) :
    IsZeroAtImInfty (F * ⇑CuspForm.discriminant) := by
  set G : ℍ → ℂ := F * ⇑CuspForm.discriminant ^ M with hGdef
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hGO : G =O[atImInfty]
      fun τ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * (M - 1) + 1) :=
    isBigO_qParam_pow_of_qExpansion_coeff_eq_zero hN' hfper hfhol hfbd hcoeff
  have hqO : (fun τ : ℍ ↦ (Periodic.qParam (N : ℝ) (τ : ℂ)) ^ (N * (M - 1) + 1))
      =O[atImInfty]
        (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ (M - 1) *
          Periodic.qParam (N : ℝ) (τ : ℂ)) :=
    ((qParam_pow_isBigO_discPow hN (M - 1)).mul
        (isBigO_refl (fun τ : ℍ ↦ Periodic.qParam (N : ℝ) (τ : ℂ)) atImInfty)).congr_left
      (fun τ ↦ (pow_succ _ _).symm)
  have hGO' : G =O[atImInfty]
      (fun τ ↦ (ModularForm.discriminant τ : ℂ) ^ (M - 1) *
        Periodic.qParam (N : ℝ) (τ : ℂ)) := hGO.trans hqO
  have hfdeq : ∀ τ : ℍ, (F * ⇑CuspForm.discriminant) τ
      = G τ / (ModularForm.discriminant τ) ^ (M - 1) := fun τ ↦ by
    have hΔ := ModularForm.discriminant_ne_zero τ
    simp only [hGdef, Pi.mul_apply, Pi.pow_apply, CuspForm.coe_discriminant]
    rw [eq_div_iff (pow_ne_zero _ hΔ), mul_assoc, ← pow_succ', Nat.sub_add_cancel hM]
  have hfneq : (fun τ : ℍ ↦ ‖G τ / ((ModularForm.discriminant τ : ℂ) ^ (M - 1) *
        Periodic.qParam (N : ℝ) (τ : ℂ))‖)
      = (fun τ ↦ ‖(F * ⇑CuspForm.discriminant) τ / Periodic.qParam (N : ℝ) (τ : ℂ)‖) :=
    funext fun τ ↦ by rw [hfdeq, div_div]
  have hbnd : IsBoundedUnder (· ≤ ·) atImInfty
      (fun τ : ℍ ↦ ‖(F * ⇑CuspForm.discriminant) τ / Periodic.qParam (N : ℝ) (τ : ℂ)‖) :=
    hfneq ▸ div_isBoundedUnder_of_isBigO hGO'
  have hq_ne : ∀ τ : ℍ, Periodic.qParam (N : ℝ) (τ : ℂ) ≠ 0 := fun τ ↦
    Complex.exp_ne_zero _
  have hFDO : (F * ⇑CuspForm.discriminant) =O[atImInfty]
      (fun τ : ℍ ↦ Periodic.qParam (N : ℝ) (τ : ℂ)) :=
    (isBigO_iff_div_isBoundedUnder (.of_forall fun τ h ↦ absurd h (hq_ne τ))).mpr hbnd
  exact hFDO.trans_tendsto (qParam_tendsto_atImInfty hN')

open ModularForm in
private lemma qExpansion_discPow_coeff_eq_zero_of_lt [NeZero N] (k : ℕ) {j : ℕ} (hj : j < N * k) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff j = 0 := by
  have hper : Function.Periodic
      ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
    have h := periodic_discPow_comp_ofComplex k 1
    simpa only [Nat.cast_one] using h
  rw [qExpansion_coeff_width _ (NeZero.ne N) hper
    (mdiff_discPow k) (isBoundedAtImInfty_discPow k), qExpansion_one_discPow]
  split_ifs with hN
  · exact coeff_pow_eq_zero_of_lt discriminant_qExpansion_coeff_zero
      (Nat.div_lt_of_lt_mul (Nat.mul_comm N k ▸ hj))
  · rfl

open ModularForm in
private theorem qExpansion_coeff_eq_zero_of_isZeroAtImInfty_mul_disc [NeZero N] {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M) (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ ofComplex) N)
    (hz : IsZeroAtImInfty (F * ⇑CuspForm.discriminant)) :
    ∀ n ≤ N * (M - 1), (qExpansion N (F * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hFDhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F * ⇑CuspForm.discriminant) := by
    have := mdiff_mul_discPow hFhol 1; rwa [pow_one] at this
  have hFDper : Function.Periodic ((F * ⇑CuspForm.discriminant) ∘ ofComplex) N := by
    have := hFper.mul (periodic_discPow_comp_ofComplex 1 N); rwa [pow_one] at this
  have hFDbd : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant) := hz.isBoundedAtImInfty
  have hc0 : (qExpansion N (F * ⇑CuspForm.discriminant)).coeff 0 = 0 :=
    (isZeroAtImInfty_iff_qExpansion_coeff_zero_eq_zero hN' hFDper hFDhol hFDbd).mp hz
  have hshape : (F * ⇑CuspForm.discriminant ^ M : ℍ → ℂ)
      = (F * ⇑CuspForm.discriminant) * ⇑CuspForm.discriminant ^ (M - 1) := by
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hM]
  intro n hn
  rw [hshape, qExpansion_mul (analyticAt_cuspFunction_zero_of hFDhol hFDper hFDbd)
      (analyticAt_cuspFunction_zero_of (mdiff_discPow (M - 1))
        (periodic_discPow_comp_ofComplex (M - 1) N) (isBoundedAtImInfty_discPow (M - 1))),
    PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rcases lt_or_eq_of_le (show j ≤ N * (M - 1) by omega) with hlt | heq
  · rw [qExpansion_discPow_coeff_eq_zero_of_lt (M - 1) hlt, mul_zero]
  · have : i = 0 := by omega
    rw [this, hc0, zero_mul]

end CuspCriterion

end Aux

open Aux in
/-- Let `F` be holomorphic and `N`-periodic with `F Δ ^ M` bounded at `i∞`, `1 ≤ M`. Then `F Δ`
vanishes at `i∞` if and only if the width-`N` q-coefficients of `F Δ ^ M` of index at most `N
(M - 1)` vanish. -/
public theorem _root_.ModularForm.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le (N : ℕ) [NeZero
    N] {F : ℍ → ℂ} {M : ℕ}
    (hM : 1 ≤ M) (hFhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) N)
    (hFbd : IsBoundedAtImInfty (F * ModularForm.discriminant ^ M)) :
    IsZeroAtImInfty (F * ModularForm.discriminant) ↔
      ∀ n ≤ N * (M - 1),
        (UpperHalfPlane.qExpansion N (F * ModularForm.discriminant ^ M)).coeff n = 0 := by
  rw [show (ModularForm.discriminant : ℍ → ℂ) = ⇑CuspForm.discriminant from
    CuspForm.coe_discriminant.symm]
  have hFbd' : IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ M) := by
    rwa [show (⇑CuspForm.discriminant : ℍ → ℂ) = ModularForm.discriminant from
      CuspForm.coe_discriminant]
  exact ⟨qExpansion_coeff_eq_zero_of_isZeroAtImInfty_mul_disc hM hFhol hFper,
    isZeroAtImInfty_mul_disc_of_coeff_le (NeZero.ne N) hM (mdiff_mul_discPow hFhol M)
      (hFper.mul (periodic_discPow_comp_ofComplex M N)) hFbd'⟩

end

end DiscriminantCuspOrder

end FrickeFunctions
