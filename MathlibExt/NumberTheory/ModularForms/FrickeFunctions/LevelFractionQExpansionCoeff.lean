/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction.lean`
and
`P2M/Sol/S_WLight_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction.lean`
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

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.FrickeModularity

/-!
# Rational q-expansion coefficients of holomorphic Fricke quotients

This file proves `ℚ(ζ_N)`-rationality of the q-expansions of holomorphic Fricke quotients.
Throughout, `j = E₄³ / Δ` and, for `v : Fin 2 → ZMod N`, the Fricke function is `f_v τ = -(E₄ τ
E₆ τ / Δ τ) / 2592 · (2πi)⁻² ℘_τ((v₀ τ + v₁) / N)`, where `℘_τ` is the Weierstrass function of
the lattice `ℤτ + ℤ`.

## Main statement

* `ModularForm.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction`
-/
namespace FrickeFunctions.LevelFractionQExpansionCoeff

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
open Aux

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

section RatCoeff

open UpperHalfPlane
open ModularForm
open SlashInvariantForm
open ModularFormClass
open CuspForm
open ModularForm.CuspForm
open EisensteinSeries
open scoped MatrixGroups ArithmeticFunction.sigma

private lemma ratCoeff_mul {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p * q).coeff n = (a : ℂ) := by
  choose F hF using hp
  choose G hG using hq
  intro n
  refine ⟨∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, F ij.1 * G ij.2, ?_⟩
  rw [PowerSeries.coeff_mul]
  push_cast
  exact Finset.sum_congr rfl fun ij _ => by rw [hF, hG]

private lemma ratCoeff_sub {p q : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (hq : ∀ n : ℕ, ∃ a : ℚ, q.coeff n = (a : ℂ)) :
    ∀ n : ℕ, ∃ a : ℚ, (p - q).coeff n = (a : ℂ) := by
  intro n
  obtain ⟨a, ha⟩ := hp n
  obtain ⟨b, hb⟩ := hq n
  exact ⟨a - b, by rw [map_sub, ha, hb]; push_cast; ring⟩

private lemma ratCoeff_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 (E hk)).coeff n = (q : ℂ) := by
  intro n
  rw [E_qExpansion_coeff hk hk2]
  by_cases hn : n = 0
  · exact ⟨1, by simp [hn]⟩
  · refine ⟨-(2 * k / _root_.bernoulli k) * (σ (k - 1) n : ℚ), ?_⟩
    rw [ite_eq_right hn]
    push_cast
    ring

private lemma ratCoeff_pow {p : PowerSeries ℂ}
    (hp : ∀ n : ℕ, ∃ a : ℚ, p.coeff n = (a : ℂ)) (k : ℕ) :
    ∀ n : ℕ, ∃ a : ℚ, (p ^ k).coeff n = (a : ℂ) := by
  induction k with
  | zero =>
    intro n
    rw [pow_zero]
    by_cases hn : n = 0
    · exact ⟨1, by simp [hn, PowerSeries.coeff_one]⟩
    · exact ⟨0, by simp [PowerSeries.coeff_one, hn]⟩
  | succ k ih =>
    rw [pow_succ]
    exact ratCoeff_mul ih hp

private def eCubeSubESq : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

private lemma eCubeSubESq_qExpansion :
    qExpansion 1 eCubeSubESq = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ -
      qExpansion 1 E₆ * qExpansion 1 E₆ := by
  simp only [eCubeSubESq, FunLike.coe_sub, ModularForm.coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

private lemma discriminant_eq_smul_eCubeSubESq :
    ModularForm.discriminant = (1 / 1728 : ℂ) • eCubeSubESq := by
  ext z
  have h := discriminant_eq_E₄_cube_sub_E₆_sq z
  simp only [Pi.smul_apply, eCubeSubESq, FunLike.coe_sub, Pi.sub_apply,
    ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul]
  rw [h]
  ring

private lemma ratCoeff_discriminant :
    ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 ModularForm.discriminant).coeff n = (q : ℂ) := by
  have h4 : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 E₄).coeff n = (q : ℂ) :=
    ratCoeff_E (by norm_num) (by decide)
  have h6 : ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 E₆).coeff n = (q : ℂ) :=
    ratCoeff_E (by norm_num) (by decide)
  have hmain := ratCoeff_sub (ratCoeff_mul (ratCoeff_mul h4 h4) h4) (ratCoeff_mul h6 h6)
  intro n
  obtain ⟨a, ha⟩ := hmain n
  refine ⟨(1 / 1728 : ℚ) * a, ?_⟩
  rw [discriminant_eq_smul_eCubeSubESq,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, eCubeSubESq_qExpansion, smul_eq_mul, ha]
  push_cast
  ring

end RatCoeff

section KPoleAlgebra

open ModularForm

variable {N : ℕ}

private lemma mem_of_rat (K : IntermediateField ℚ ℂ) {x : ℂ} (h : ∃ q : ℚ, x = (q : ℂ)) : x ∈ K :=
    by
  obtain ⟨q, rfl⟩ := h
  exact SubfieldClass.ratCast_mem K q

private def KPoleAt (K : IntermediateField ℚ ℂ) (N m : ℕ) (f : ℍ → ℂ) : Prop :=
  Function.Periodic ((f * ⇑CuspForm.discriminant ^ m) ∘ ofComplex) N ∧
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m) ∧
    ∀ n : ℕ, (qExpansion N (f * ⇑CuspForm.discriminant ^ m)).coeff n ∈ K

private def KPole (K : IntermediateField ℚ ℂ) (N : ℕ) (f : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ ∃ m : ℕ, KPoleAt K N m f

private lemma qExpansion_discPow_coeff_mem (K : IntermediateField ℚ ℂ) [NeZero N] (k n : ℕ) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff n ∈ K := by
  have hper : Function.Periodic
      ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
    have h := periodic_discPow_comp_ofComplex k 1
    simpa only [Nat.cast_one] using h
  rw [qExpansion_coeff_width _ (NeZero.ne N) hper (mdiff_discPow k)
    (isBoundedAtImInfty_discPow k), qExpansion_one_discPow]
  split
  · exact mem_of_rat K (ratCoeff_pow ratCoeff_discriminant k _)
  · exact zero_mem _

private lemma KPoleAt.pad {K : IntermediateField ℚ ℂ} [NeZero N] {f : ℍ → ℂ} {m m' : ℕ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hm : m ≤ m') (h : KPoleAt K N m f) :
    KPoleAt K N m' f := by
  obtain ⟨hper, hbd, hmem⟩ := h
  have hshape : (f * ⇑CuspForm.discriminant ^ m' : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m) * ⇑CuspForm.discriminant ^ (m' - m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
  refine ⟨?_, ?_, ?_⟩
  · rw [hshape]
    exact hper.mul (periodic_discPow_comp_ofComplex (m' - m) N)
  · exact IsBoundedAtImInfty.mul_discPow_mono hm hbd
  · intro n
    rw [hshape, qExpansion_mul
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hhol m) hper hbd)
      (analyticAt_cuspFunction_zero_of (mdiff_discPow (m' - m))
        (periodic_discPow_comp_ofComplex (m' - m) N) (isBoundedAtImInfty_discPow (m' - m))),
      PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hmem ij.1) (qExpansion_discPow_coeff_mem K _ ij.2)

private lemma kPole_algebraMap {K : IntermediateField ℚ ℂ} [NeZero N] (c : ↥K) :
    KPole K N (algebraMap ↥K (ℍ → ℂ) c) := by
  have hshape : ((algebraMap ↥K (ℍ → ℂ) c) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      (c : ℂ) • (1 : ℍ → ℂ) := by
    funext τ
    simp only [Pi.mul_apply, pow_zero, mul_one, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul]
    rfl
  have hone_bd : IsBoundedAtImInfty (1 : ℍ → ℂ) := by
    have h1 : (1 : ℍ → ℂ) = fun _ : ℍ => (1 : ℂ) := rfl
    rw [h1]
    exact Filter.const_boundedAtFilter _ _
  refine ⟨mdifferentiable_const, 0, ?_, ?_, ?_⟩
  · rw [hshape]
    intro x
    rfl
  · rw [hshape]
    have hc : ((c : ℂ) • (1 : ℍ → ℂ)) = fun _ : ℍ => (c : ℂ) := by
      funext τ
      simp
    rw [hc]
    exact Filter.const_boundedAtFilter _ _
  · intro n
    have han : AnalyticAt ℂ (cuspFunction N (1 : ℍ → ℂ)) 0 :=
      analyticAt_cuspFunction_zero_of (g := (1 : ℍ → ℂ)) mdifferentiable_const
        (periodic_one_fn N) hone_bd
    rw [hshape, qExpansion_smul han,
      qExpansion_one, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_one]
    split
    · rw [mul_one]
      exact c.2
    · rw [mul_zero]
      exact zero_mem _

private lemma KPole.add {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f + g) := by
  obtain ⟨hf1, m1, hfd⟩ := hf
  obtain ⟨hg1, m2, hgd⟩ := hg
  obtain ⟨hfper, hfbd, hfmem⟩ := hfd.pad hf1 (le_max_left m1 m2)
  obtain ⟨hgper, hgbd, hgmem⟩ := hgd.pad hg1 (le_max_right m1 m2)
  have hshape : ((f + g) * ⇑CuspForm.discriminant ^ max m1 m2 : ℍ → ℂ) =
      f * ⇑CuspForm.discriminant ^ max m1 m2 + g * ⇑CuspForm.discriminant ^ max m1 m2 := by
    funext τ
    simp [add_mul]
  refine ⟨hf1.add hg1, max m1 m2, ?_, ?_, ?_⟩
  · rw [hshape]
    exact hfper.add hgper
  · rw [hshape]
    exact hfbd.add hgbd
  · intro n
    rw [hshape, qExpansion_add
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hf1 _) hfper hfbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg1 _) hgper hgbd),
      map_add]
    exact add_mem (hfmem n) (hgmem n)

private lemma KPole.mul {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f * g) := by
  obtain ⟨hf1, m1, hfper, hfbd, hfmem⟩ := hf
  obtain ⟨hg1, m2, hgper, hgbd, hgmem⟩ := hg
  have hshape : ((f * g) * ⇑CuspForm.discriminant ^ (m1 + m2) : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m1) * (g * ⇑CuspForm.discriminant ^ m2) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  refine ⟨hf1.mul hg1, m1 + m2, ?_, ?_, ?_⟩
  · rw [hshape]
    exact hfper.mul hgper
  · rw [hshape]
    exact hfbd.mul hgbd
  · intro n
    rw [hshape, qExpansion_mul
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hf1 _) hfper hfbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg1 _) hgper hgbd),
      PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (hfmem ij.1) (hgmem ij.2)

private lemma kPole_jf (K : IntermediateField ℚ ℂ) [NeZero N] {jf : ℍ → ℂ}
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    KPole K N jf := by
  have hshape : (jf * ⇑CuspForm.discriminant ^ 1 : ℍ → ℂ) = ⇑(ModularForm.E₄.pow 3) := by
    funext τ
    rw [congrFun (ModularForm.coe_pow ModularForm.E₄ 3) τ, Pi.pow_apply]
    simp only [Pi.mul_apply, pow_one, hjf τ]
    rw [congrFun CuspForm.coe_discriminant τ]
    exact div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)
  have hhol3 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) :=
    (ModularForm.E₄.pow 3).holo'
  have hbd3 : IsBoundedAtImInfty (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) :=
    ModularFormClass.bdd_at_infty (ModularForm.E₄.pow 3)
  have hper3 : Function.Periodic ((⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E₄.pow 3)
      one_mem_strictPeriods_SL
  have hjmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
    have : jf = fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := funext hjf
    rw [this]
    exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  refine ⟨hjmd, 1, ?_, ?_, ?_⟩
  · rw [hshape]
    simpa using hper3.nat_mul N
  · rw [hshape]
    exact hbd3
  · intro n
    rw [hshape, qExpansion_coeff_width (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) (NeZero.ne N)
      hper3 hhol3 hbd3]
    split
    · have he : qExpansion 1 (⇑(ModularForm.E₄.pow 3) : ℍ → ℂ) =
          (qExpansion 1 ModularForm.E₄) ^ 3 :=
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3
      rw [he]
      exact mem_of_rat K (ratCoeff_pow (ratCoeff_E (by norm_num) (by decide)) 3 _)
    · exact zero_mem _

end KPoleAlgebra

section HeadTwo

open ModularForm

variable {N : ℕ}

private lemma analyticOnNhd_comp_ofComplex {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet

private theorem mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero {f g : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hfg : f * g = 0) : f = 0 ∨ g = 0 := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf hg
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have key := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (hf.analyticOnNhd hU)
    (hg.analyticOnNhd hU) (fun z hz ↦ by
      have := congrFun hfg (ofComplex z)
      simpa using this) (convex_halfSpace_im_gt 0).isPreconnected
  rcases key with k | k
  · left; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos
  · right; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos

private lemma jf_smul {jf : ℍ → ℂ}
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ) : jf (γ • τ) = jf τ := by
  have hγ : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  rw [CuspForm.coe_discriminant] at hΔ
  rw [show (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ = γ • τ from rfl] at h4 hΔ
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  rw [hjf, hjf, h4, hΔ, zpow_ofNat, zpow_ofNat]
  field_simp

private lemma map_castRingHom_eq_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem'] at hγ
  rw [hγ, Matrix.SpecialLinearGroup.coe_one]

private def precompSmul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (ℍ → ℂ) →ₐ[ℂ] (ℍ → ℂ) where
  toFun f := f ∘ (γ • ·)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private lemma KPole.pow {K : IntermediateField ℚ ℂ} [NeZero N] {g : ℍ → ℂ}
    (hg : KPole K N g) (e : ℕ) : KPole K N (g ^ e) := by
  induction e with
  | zero =>
    have h1 : (g ^ 0 : ℍ → ℂ) = algebraMap ↥K (ℍ → ℂ) 1 := by
      funext τ; simp
    rw [h1]
    exact kPole_algebraMap 1
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul hg

private lemma KPole.finsetSum {K : IntermediateField ℚ ℂ} [NeZero N] {ι : Type*}
    (s : Finset ι) {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, KPole K N (f i)) :
    KPole K N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    have h0 : (0 : ℍ → ℂ) = algebraMap ↥K (ℍ → ℂ) 0 := by funext τ; simp
    rw [h0]
    exact kPole_algebraMap 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma KPole.finsetProd {K : IntermediateField ℚ ℂ} [NeZero N] {ι : Type*}
    (s : Finset ι) {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, KPole K N (f i)) :
    KPole K N (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have h1 : (1 : ℍ → ℂ) = algebraMap ↥K (ℍ → ℂ) 1 := by funext τ; simp
    rw [h1]
    exact kPole_algebraMap 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma kPole_polyEval {K : IntermediateField ℚ ℂ} [NeZero N] {g : ℍ → ℂ}
    (hg : KPole K N g) {P : Polynomial ℂ} (hP : ∀ n, P.coeff n ∈ K) :
    KPole K N (fun τ => P.eval (g τ)) := by
  classical
  have hfun : (fun τ => P.eval (g τ)) =
      ∑ e ∈ P.support, (fun τ => P.coeff e * g τ ^ e) := by
    funext τ
    rw [Finset.sum_apply, Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [hfun]
  refine KPole.finsetSum _ fun e _ => ?_
  have hconst : KPole K N (algebraMap ↥K (ℍ → ℂ) ⟨P.coeff e, hP e⟩) := kPole_algebraMap _
  have := hconst.mul (hg.pow e)
  have hshape : algebraMap ↥K (ℍ → ℂ) ⟨P.coeff e, hP e⟩ * g ^ e =
      fun τ => P.coeff e * g τ ^ e := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rfl
  rwa [hshape] at this

private lemma kPole_aeval {K : IntermediateField ℚ ℂ} [NeZero N] {σ : Type*}
    {gen : σ → ℍ → ℂ} (hgen : ∀ i, KPole K N (gen i))
    {P : MvPolynomial σ ℂ} (hP : ∀ m, P.coeff m ∈ K) :
    KPole K N (MvPolynomial.aeval gen P) := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine KPole.finsetSum _ fun d _ => ?_
  have hconst : KPole K N ((algebraMap ℂ (ℍ → ℂ)) (P.coeff d)) := by
    have h1 : (algebraMap ℂ (ℍ → ℂ)) (P.coeff d) =
        algebraMap ↥K (ℍ → ℂ) ⟨P.coeff d, hP d⟩ := rfl
    rw [h1]
    exact kPole_algebraMap _
  exact hconst.mul (KPole.finsetProd _ fun i _ => (hgen i).pow (d i))

private theorem exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction_of_deps
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (hR2 : ∀ v : Fin 2 → ZMod N, v ≠ 0 → ∃ m : ℕ,
      Function.Periodic ((fricke v * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (fricke v * ModularForm.discriminant ^ m)).coeff n ∈ K)
    (hR4a : ∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v))
    (hR4c : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ)
    {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ)
    (hPK : ∀ m, P.coeff m ∈ K) (hQK : ∀ m, Q.coeff m ∈ K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) Q ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) Q =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) P)
    (hint : ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0) :
    ∃ m : ℕ, Function.Periodic ((G * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (G * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n ∈ K := by
  classical
  have _hL := hL
  have _hW := hW
  have _hfricke := hfricke
  have _hK := hK
  rw [show (ModularForm.discriminant : ℍ → ℂ) = ⇑CuspForm.discriminant from
    CuspForm.coe_discriminant.symm]
  simp only [show (ModularForm.discriminant : ℍ → ℂ) = ⇑CuspForm.discriminant from
    CuspForm.coe_discriminant.symm] at hR2
  set gen : Option {v : Fin 2 → ZMod N // v ≠ 0} → ℍ → ℂ :=
    fun o => o.elim jf fun v => fricke v.1 with hgen_def
  have hgenKP : ∀ o, KPole K N (gen o) := by
    intro o
    cases o with
    | none => exact kPole_jf K hjf
    | some v =>
      obtain ⟨m, hper, hbd, hmem⟩ := hR2 v.1 v.2
      exact ⟨hR4a v.1 v.2, m, hper, hbd, hmem⟩
  set Ptil : ℍ → ℂ := MvPolynomial.aeval gen P with hPtil_def
  set Qtil : ℍ → ℂ := MvPolynomial.aeval gen Q with hQtil_def
  have hPKP : KPole K N Ptil := kPole_aeval hgenKP hPK
  have hQKP : KPole K N Qtil := kPole_aeval hgenKP hQK
  obtain ⟨hPmd, mP, hPat⟩ := hPKP
  obtain ⟨hQmd, mQ, hQat⟩ := hQKP
  have hgen_inv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ o, gen o ∘ (γ • ·) = gen o := by
    intro γ hγ o
    cases o with
    | none =>
      funext τ
      exact jf_smul hjf γ τ
    | some v =>
      funext τ
      change fricke v.1 (γ • τ) = fricke v.1 τ
      rw [hR4c v.1 γ τ, map_castRingHom_eq_one hγ, Matrix.vecMul_one]
  have haeval_inv : ∀ γ ∈ CongruenceSubgroup.Gamma N,
      ∀ R : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ,
        MvPolynomial.aeval gen R ∘ (γ • ·) = MvPolynomial.aeval gen R := by
    intro γ hγ R
    have h1 : MvPolynomial.aeval gen R ∘ (γ • ·) = precompSmul γ (MvPolynomial.aeval gen R) := rfl
    rw [h1, MvPolynomial.comp_aeval_apply]
    have hfam : (fun i => precompSmul γ (gen i)) = gen :=
      funext fun o => hgen_inv γ hγ o
    rw [hfam]
  have hGinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, G ∘ (γ • ·) = G := by
    intro γ hγ
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G ∘ (γ • ·) - G) := by
      refine MDifferentiable.sub ?_ hG
      have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G ∣[(0 : ℤ)] γ) := hG.slash 0 _
      have h2 : G ∣[(0 : ℤ)] γ = G ∘ (γ • ·) := by
        funext τ
        simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
        rfl
      rwa [h2] at h1
    have hprod : (G ∘ (γ • ·) - G) * Qtil = 0 := by
      funext τ
      have h1 : G (γ • τ) * Qtil (γ • τ) = Ptil (γ • τ) := congrFun hGQ (γ • τ)
      have h2 : G τ * Qtil τ = Ptil τ := congrFun hGQ τ
      have hQγ : Qtil (γ • τ) = Qtil τ := congrFun (haeval_inv γ hγ Q) τ
      have hPγ : Ptil (γ • τ) = Ptil τ := congrFun (haeval_inv γ hγ P) τ
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, Function.comp_apply]
      rw [sub_mul, h2]
      rw [show G (γ • τ) * Qtil τ = G (γ • τ) * Qtil (γ • τ) by rw [hQγ], h1, hPγ, sub_self]
    rcases mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero hdiff hQmd hprod with h | h
    · funext τ
      have := congrFun h τ
      simpa [sub_eq_zero] using this
    · exact absurd h hQ0
  have hGper : Function.Periodic (G ∘ ofComplex) N := by
    have hT : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
      have := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma N N (dvd_refl _)
      rwa [Int.natAbs_natCast] at this
    intro w
    by_cases hw : 0 < Complex.im w
    · have hw' : 0 < Complex.im (w + N) := by simpa using hw
      simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw',
        ofComplex_apply_of_im_pos hw]
      have := congrFun (hGinv _ hT) ⟨w, hw⟩
      simp only [Function.comp_apply] at this
      rw [UpperHalfPlane.modular_T_zpow_smul] at this
      rw [← this]
      congr 1
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.coe_vadd, add_comm]
    · have hw0 : Complex.im w ≤ 0 := not_lt.mp hw
      have hw' : Complex.im (w + N) ≤ 0 := by simpa using hw0
      simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw',
        ofComplex_apply_of_im_nonpos hw0]
  obtain ⟨d, p, hpK, hprel⟩ := hint
  have hcKP : ∀ i : Fin d, KPole K N (fun τ => (p i).eval (jf τ)) := fun i =>
    kPole_polyEval (kPole_jf K hjf) (hpK i)
  choose mc hmc using fun i : Fin d => (hcKP i).2
  set M₀ : ℕ := 1 + Finset.univ.sup mc with hM₀_def
  have hbdG : IsBoundedAtImInfty (G * ⇑CuspForm.discriminant ^ M₀) := by
    refine isBoundedAtImInfty_of_monicRel
      (c := fun n => if hn : n < d then
        (fun τ => (p ⟨n, hn⟩).eval (jf τ)) * ⇑CuspForm.discriminant ^ (M₀ * (d - n)) else 0)
      (d := d) ?_ ?_
    · intro n hn
      simp only [dite_eq_left hn]
      have h1 : IsBoundedAtImInfty ((fun τ => (p ⟨n, hn⟩).eval (jf τ)) *
          ⇑CuspForm.discriminant ^ mc ⟨n, hn⟩) := (hmc ⟨n, hn⟩).2.1
      refine IsBoundedAtImInfty.mul_discPow_mono ?_ h1
      calc mc ⟨n, hn⟩ ≤ Finset.univ.sup mc := Finset.le_sup (Finset.mem_univ _)
        _ ≤ M₀ * 1 := by omega
        _ ≤ M₀ * (d - n) := by
            have : 1 ≤ d - n := by omega
            exact Nat.mul_le_mul_left M₀ this
    · intro τ
      have h0 := hprel τ
      have hΔ : CuspForm.discriminant τ ≠ 0 := by
        rw [congrFun CuspForm.coe_discriminant τ]
        exact ModularForm.discriminant_ne_zero τ
      have hkey : (G τ * CuspForm.discriminant τ ^ M₀) ^ d
          + ∑ n ∈ Finset.range d, ((if hn : n < d then
              ((fun τ' => (p ⟨n, hn⟩).eval (jf τ')) * ⇑CuspForm.discriminant ^ (M₀ * (d - n)))
            else 0) τ) * (G τ * CuspForm.discriminant τ ^ M₀) ^ n
          = CuspForm.discriminant τ ^ (M₀ * d) *
            (G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ)) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        · rw [mul_pow, ← pow_mul]
          ring
        · rw [← Fin.sum_univ_eq_sum_range (fun n => ((if hn : n < d then
              ((fun τ' => (p ⟨n, hn⟩).eval (jf τ')) *
                ⇑CuspForm.discriminant ^ (M₀ * (d - n)))
            else 0) τ) * (G τ * CuspForm.discriminant τ ^ M₀) ^ n) d]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [dite_eq_left i.isLt]
          simp only [Pi.mul_apply, Pi.pow_apply]
          rw [mul_pow, ← pow_mul]
          have hexp : M₀ * (d - (i : ℕ)) + M₀ * (i : ℕ) = M₀ * d := by
            rw [← Nat.mul_add, Nat.sub_add_cancel i.isLt.le]
          calc (p i).eval (jf τ) * CuspForm.discriminant τ ^ (M₀ * (d - (i : ℕ))) *
                (G τ ^ (i : ℕ) * CuspForm.discriminant τ ^ (M₀ * (i : ℕ)))
              = CuspForm.discriminant τ ^ (M₀ * (d - (i : ℕ)) + M₀ * (i : ℕ)) *
                ((p i).eval (jf τ) * G τ ^ (i : ℕ)) := by ring
            _ = CuspForm.discriminant τ ^ (M₀ * d) *
                ((p i).eval (jf τ) * G τ ^ (i : ℕ)) := by rw [hexp]
      simp only [Pi.mul_apply, Pi.pow_apply]
      rw [hkey, h0, mul_zero]
  set M : ℕ := M₀ + mP with hM_def
  have hbdGM : IsBoundedAtImInfty (G * ⇑CuspForm.discriminant ^ M) :=
    IsBoundedAtImInfty.mul_discPow_mono (by omega) hbdG
  have hperGM : Function.Periodic ((G * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N :=
    hGper.mul (periodic_discPow_comp_ofComplex M N)
  refine ⟨M, hperGM, hbdGM, ?_⟩
  have hPat' : ∀ n : ℕ, (qExpansion N (Ptil * ⇑CuspForm.discriminant ^ (mQ + M))).coeff n ∈ K :=
    (hPat.pad hPmd (by omega)).2.2
  obtain ⟨hQper, hQbd, hQmem⟩ := hQat
  have hprod : (Qtil * ⇑CuspForm.discriminant ^ mQ) * (G * ⇑CuspForm.discriminant ^ M)
      = Ptil * ⇑CuspForm.discriminant ^ (mQ + M) := by
    funext τ
    have h2 : G τ * Qtil τ = Ptil τ := congrFun hGQ τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    calc Qtil τ * CuspForm.discriminant τ ^ mQ * (G τ * CuspForm.discriminant τ ^ M)
        = G τ * Qtil τ * (CuspForm.discriminant τ ^ mQ * CuspForm.discriminant τ ^ M) := by ring
      _ = Ptil τ * (CuspForm.discriminant τ ^ mQ * CuspForm.discriminant τ ^ M) := by rw [h2]
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hqmul : qExpansion N (Qtil * ⇑CuspForm.discriminant ^ mQ) *
      qExpansion N (G * ⇑CuspForm.discriminant ^ M)
        = qExpansion N (Ptil * ⇑CuspForm.discriminant ^ (mQ + M)) := by
    rw [← qExpansion_mul (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hQmd mQ)
        hQper hQbd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hG M) hperGM hbdGM), hprod]
  have hg_ne : qExpansion N (Qtil * ⇑CuspForm.discriminant ^ mQ) ≠ 0 := by
    rw [ne_eq, qExpansion_eq_zero_iff hN' hQper (mdiff_mul_discPow hQmd mQ) hQbd]
    intro h0
    refine hQ0 ?_
    funext τ
    have hτ := congrFun h0 τ
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at hτ
    have hΔ : CuspForm.discriminant τ ≠ 0 := by
      rw [congrFun CuspForm.coe_discriminant τ]
      exact ModularForm.discriminant_ne_zero τ
    exact (mul_eq_zero.mp hτ).resolve_right (pow_ne_zero mQ hΔ)
  exact fun n ↦ powerSeries_coeff_mem_of_mul_eq' K.toSubfield hqmul hg_ne
    (fun n' ↦ hQmem n') (fun n' ↦ hPat' n') n

end HeadTwo

end Aux

open _root_.FrickeFunctions.LevelFractionQExpansionCoeff.Aux in
/-- Let `K = ℚ(ζ_N)`, let `P`, `Q` be complex polynomials in `j` and the Fricke functions with
coefficients in `K` and `Q ≠ 0` after evaluation, and let `G` be holomorphic with `G Q = P`
after evaluation and satisfying a monic equation over `K[j]`. Then for some `m`, `G Δ ^ m` is
`N`-periodic, bounded at `i∞`, and has width-`N` q-coefficients in `K`. -/
public theorem _root_.ModularForm.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ)
    (hPK : ∀ m, P.coeff m ∈ K) (hQK : ∀ m, Q.coeff m ∈ K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) Q ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) Q =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) P)
    (hint : ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0) :
    ∃ m : ℕ, Function.Periodic ((G * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (G * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n ∈ K := by
  subst hK
  refine Aux.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction_of_deps
    N L hL W hW fricke hfricke jf hjf _ rfl ?_ ?_ ?_ hG P Q hPK hQK hQ0 hGQ hint
  · intro v hv
    refine ⟨1, ?_, ?_, ?_⟩ <;> rw [pow_one]
    · exact ModularForm.periodic_frickeFunction_mul_discriminant N L hL W hW fricke hfricke hv
    · exact ModularForm.isBoundedAtImInfty_frickeFunction_mul_discriminant N L hL W hW fricke
        hfricke hv
    · exact ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_mem N L hL W hW fricke
        hfricke hv
  · exact fun v hv => ModularForm.mdifferentiable_frickeFunction N L hL W hW fricke hfricke hv
  · exact fun v γ τ => ModularForm.frickeFunction_smul N L hL W hW fricke hfricke v γ τ

end

end LevelFractionQExpansionCoeff

end FrickeFunctions
