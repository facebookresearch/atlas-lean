/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_qExpansion_sigmaTransport_package.lean`
and
`P2M/Sol/S_WLight_qExpansion_sigmaTransport_package.lean`
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
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Transport of q-expansion coefficients along a field embedding

This file transports q-expansion coefficients along a field embedding through polynomial
expressions in holomorphic functions with moderate growth at the cusp.

## Main statement

* `ModularForm.qExpansion_sigmaTransport_package`
-/
namespace FrickeFunctions.QExpansionSigmaTransport

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

end KPoleAlgebra

section Transport

open ModularForm

variable {N : ℕ} {K : IntermediateField ℚ ℂ} {φ : ↥K →+* ℂ}

private def TransAt (K : IntermediateField ℚ ℂ) (φ : ↥K →+* ℂ) (N m : ℕ)
    (g g' : ℍ → ℂ) : Prop :=
  KPoleAt K N m g ∧ KPoleAt K N m g' ∧
  ∀ (n : ℕ) (z : ↥K), (z : ℂ) = (qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n →
    (qExpansion N (g' * ⇑CuspForm.discriminant ^ m)).coeff n = φ z

private def Trans (K : IntermediateField ℚ ℂ) (φ : ↥K →+* ℂ) (N : ℕ)
    (g g' : ℍ → ℂ) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g' ∧ ∃ m, TransAt K φ N m g g'

private lemma TransAt.of_eq {m m₂ : ℕ} {g₁ g₁' g₂ g₂' : ℍ → ℂ}
    (h : TransAt K φ N m g₁ g₁')
    (e : g₁ * ⇑CuspForm.discriminant ^ m = g₂ * ⇑CuspForm.discriminant ^ m₂)
    (e' : g₁' * ⇑CuspForm.discriminant ^ m = g₂' * ⇑CuspForm.discriminant ^ m₂) :
    TransAt K φ N m₂ g₂ g₂' := by
  obtain ⟨⟨h1, h2, h3⟩, ⟨h1', h2', h3'⟩, hrel⟩ := h
  rw [e] at h1 h2 h3
  rw [e'] at h1' h2' h3'
  refine ⟨⟨h1, h2, h3⟩, ⟨h1', h2', h3'⟩, ?_⟩
  intro n z hz
  rw [← e']
  rw [← e] at hz
  exact hrel n z hz

private lemma qExpansion_mul_pad [NeZero N] {m₁ m₂ : ℕ} {g₁ g₂ : ℍ → ℂ}
    (hg₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁) (hg₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂)
    (h₁per : Function.Periodic ((g₁ * ⇑CuspForm.discriminant ^ m₁) ∘ ofComplex) N)
    (h₁bd : IsBoundedAtImInfty (g₁ * ⇑CuspForm.discriminant ^ m₁))
    (h₂per : Function.Periodic ((g₂ * ⇑CuspForm.discriminant ^ m₂) ∘ ofComplex) N)
    (h₂bd : IsBoundedAtImInfty (g₂ * ⇑CuspForm.discriminant ^ m₂)) :
    qExpansion N ((g₁ * g₂) * ⇑CuspForm.discriminant ^ (m₁ + m₂)) =
      qExpansion N (g₁ * ⇑CuspForm.discriminant ^ m₁) *
        qExpansion N (g₂ * ⇑CuspForm.discriminant ^ m₂) := by
  have hshape : ((g₁ * g₂) * ⇑CuspForm.discriminant ^ (m₁ + m₂) : ℍ → ℂ) =
      (g₁ * ⇑CuspForm.discriminant ^ m₁) * (g₂ * ⇑CuspForm.discriminant ^ m₂) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  rw [hshape, qExpansion_mul
    (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₁ m₁) h₁per h₁bd)
    (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₂ m₂) h₂per h₂bd)]

private lemma KPoleAt.mulAt [NeZero N] {m₁ m₂ : ℕ} {g₁ g₂ : ℍ → ℂ}
    (hg₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁) (hg₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂)
    (h₁ : KPoleAt K N m₁ g₁) (h₂ : KPoleAt K N m₂ g₂) :
    KPoleAt K N (m₁ + m₂) (g₁ * g₂) := by
  obtain ⟨h₁per, h₁bd, h₁mem⟩ := h₁
  obtain ⟨h₂per, h₂bd, h₂mem⟩ := h₂
  have hshape : ((g₁ * g₂) * ⇑CuspForm.discriminant ^ (m₁ + m₂) : ℍ → ℂ) =
      (g₁ * ⇑CuspForm.discriminant ^ m₁) * (g₂ * ⇑CuspForm.discriminant ^ m₂) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hshape]
    exact h₁per.mul h₂per
  · rw [hshape]
    exact h₁bd.mul h₂bd
  · intro n
    rw [qExpansion_mul_pad hg₁ hg₂ h₁per h₁bd h₂per h₂bd, PowerSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (h₁mem ij.1) (h₂mem ij.2)

private lemma TransAt.mulT [NeZero N] {m₁ m₂ : ℕ} {g₁ g₁' g₂ g₂' : ℍ → ℂ}
    (hg₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁) (hg₁' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁')
    (hg₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂) (hg₂' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂')
    (h₁ : TransAt K φ N m₁ g₁ g₁') (h₂ : TransAt K φ N m₂ g₂ g₂') :
    TransAt K φ N (m₁ + m₂) (g₁ * g₂) (g₁' * g₂') := by
  obtain ⟨hK₁, hK₁', hrel₁⟩ := h₁
  obtain ⟨hK₂, hK₂', hrel₂⟩ := h₂
  refine ⟨KPoleAt.mulAt hg₁ hg₂ hK₁ hK₂, KPoleAt.mulAt hg₁' hg₂' hK₁' hK₂', ?_⟩
  intro n z hz
  rw [qExpansion_mul_pad hg₁ hg₂ hK₁.1 hK₁.2.1 hK₂.1 hK₂.2.1, PowerSeries.coeff_mul] at hz
  rw [qExpansion_mul_pad hg₁' hg₂' hK₁'.1 hK₁'.2.1 hK₂'.1 hK₂'.2.1, PowerSeries.coeff_mul]
  have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      (qExpansion N (g₁' * ⇑CuspForm.discriminant ^ m₁)).coeff ij.1 *
        (qExpansion N (g₂' * ⇑CuspForm.discriminant ^ m₂)).coeff ij.2 =
      φ (⟨(qExpansion N (g₁ * ⇑CuspForm.discriminant ^ m₁)).coeff ij.1, hK₁.2.2 ij.1⟩ *
        ⟨(qExpansion N (g₂ * ⇑CuspForm.discriminant ^ m₂)).coeff ij.2, hK₂.2.2 ij.2⟩) := by
    intro ij _
    rw [map_mul, hrel₁ ij.1 ⟨_, hK₁.2.2 ij.1⟩ rfl, hrel₂ ij.2 ⟨_, hK₂.2.2 ij.2⟩ rfl]
  rw [Finset.sum_congr rfl hterm, ← map_sum]
  congr 1
  apply Subtype.ext
  rw [hz, AddSubmonoidClass.coe_finsetSum]
  exact Finset.sum_congr rfl fun ij _ => rfl

private lemma transAt_self_of_rat [NeZero N] {m : ℕ} {g : ℍ → ℂ}
    (hper : Function.Periodic ((g * ⇑CuspForm.discriminant ^ m) ∘ ofComplex) N)
    (hbd : IsBoundedAtImInfty (g * ⇑CuspForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ q : ℚ, (qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n = (q : ℂ)) :
    TransAt K φ N m g g := by
  have hmem : ∀ n : ℕ, (qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n ∈ K :=
    fun n => mem_of_rat K (hrat n)
  refine ⟨⟨hper, hbd, hmem⟩, ⟨hper, hbd, hmem⟩, ?_⟩
  intro n z hz
  obtain ⟨q, hq⟩ := hrat n
  have hzq : z = (q : ↥K) := by
    apply Subtype.ext
    rw [hz, hq]
    push_cast
    rfl
  rw [hzq, map_ratCast, ← hq]

private lemma TransAt.padT [NeZero N] {m m' : ℕ} {g g' : ℍ → ℂ}
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hg' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g')
    (hm : m ≤ m') (h : TransAt K φ N m g g') : TransAt K φ N m' g g' := by
  have hone : ∀ k : ℕ, ((⇑CuspForm.discriminant ^ k : ℍ → ℂ) *
      ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) = ⇑CuspForm.discriminant ^ k := by
    intro k; funext τ; simp
  have hΔ : TransAt K φ N 0 ((⇑CuspForm.discriminant : ℍ → ℂ) ^ (m' - m))
      ((⇑CuspForm.discriminant : ℍ → ℂ) ^ (m' - m)) := by
    refine transAt_self_of_rat ?_ ?_ ?_
    · rw [hone]
      exact periodic_discPow_comp_ofComplex (m' - m) N
    · rw [hone]
      exact isBoundedAtImInfty_discPow (m' - m)
    · intro n
      rw [hone]
      have hper1 : Function.Periodic
          ((⇑CuspForm.discriminant ^ (m' - m) : ℍ → ℂ) ∘ ofComplex) (1 : ℂ) := by
        have h2 := periodic_discPow_comp_ofComplex (m' - m) 1
        simpa only [Nat.cast_one] using h2
      rw [qExpansion_coeff_width _ (NeZero.ne N) hper1 (mdiff_discPow (m' - m))
        (isBoundedAtImInfty_discPow (m' - m)), qExpansion_one_discPow]
      split
      · exact ratCoeff_pow ratCoeff_discriminant (m' - m) _
      · exact ⟨0, by push_cast; ring⟩
  have hmul := TransAt.mulT hg hg' (mdiff_discPow (m' - m)) (mdiff_discPow (m' - m)) h hΔ
  refine hmul.of_eq ?_ ?_
  · funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, show m' - m + (m + 0) = m' by omega]
  · funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [mul_assoc, ← pow_add, show m' - m + (m + 0) = m' by omega]

private lemma TransAt.addT [NeZero N] {m : ℕ} {g₁ g₁' g₂ g₂' : ℍ → ℂ}
    (hg₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁) (hg₁' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₁')
    (hg₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂) (hg₂' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g₂')
    (h₁ : TransAt K φ N m g₁ g₁') (h₂ : TransAt K φ N m g₂ g₂') :
    TransAt K φ N m (g₁ + g₂) (g₁' + g₂') := by
  obtain ⟨⟨h₁per, h₁bd, h₁mem⟩, ⟨h₁per', h₁bd', h₁mem'⟩, hrel₁⟩ := h₁
  obtain ⟨⟨h₂per, h₂bd, h₂mem⟩, ⟨h₂per', h₂bd', h₂mem'⟩, hrel₂⟩ := h₂
  have hshape : ∀ a b : ℍ → ℂ, ((a + b) * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) =
      a * ⇑CuspForm.discriminant ^ m + b * ⇑CuspForm.discriminant ^ m := by
    intro a b; funext τ; simp only [Pi.add_apply, Pi.mul_apply]; ring
  have hq : qExpansion N ((g₁ + g₂) * ⇑CuspForm.discriminant ^ m) =
      qExpansion N (g₁ * ⇑CuspForm.discriminant ^ m) +
        qExpansion N (g₂ * ⇑CuspForm.discriminant ^ m) := by
    rw [hshape, qExpansion_add
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₁ m) h₁per h₁bd)
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₂ m) h₂per h₂bd)]
  have hq' : qExpansion N ((g₁' + g₂') * ⇑CuspForm.discriminant ^ m) =
      qExpansion N (g₁' * ⇑CuspForm.discriminant ^ m) +
        qExpansion N (g₂' * ⇑CuspForm.discriminant ^ m) := by
    rw [hshape, qExpansion_add
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₁' m) h₁per' h₁bd')
      (analyticAt_cuspFunction_zero_of (mdiff_mul_discPow hg₂' m) h₂per' h₂bd')]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hshape]; exact h₁per.add h₂per
  · rw [hshape]; exact h₁bd.add h₂bd
  · intro n
    rw [hq, map_add]
    exact add_mem (h₁mem n) (h₂mem n)
  · rw [hshape]; exact h₁per'.add h₂per'
  · rw [hshape]; exact h₁bd'.add h₂bd'
  · intro n
    rw [hq', map_add]
    exact add_mem (h₁mem' n) (h₂mem' n)
  · intro n z hz
    rw [hq, map_add] at hz
    rw [hq', map_add, hrel₁ n ⟨_, h₁mem n⟩ rfl, hrel₂ n ⟨_, h₂mem n⟩ rfl, ← map_add]
    congr 1
    apply Subtype.ext
    rw [hz]
    rfl

private lemma Trans.addF [NeZero N] {g₁ g₁' g₂ g₂' : ℍ → ℂ}
    (h₁ : Trans K φ N g₁ g₁') (h₂ : Trans K φ N g₂ g₂') :
    Trans K φ N (g₁ + g₂) (g₁' + g₂') := by
  obtain ⟨hm₁, hm₁', m₁, hT₁⟩ := h₁
  obtain ⟨hm₂, hm₂', m₂, hT₂⟩ := h₂
  exact ⟨hm₁.add hm₂, hm₁'.add hm₂', max m₁ m₂,
    TransAt.addT hm₁ hm₁' hm₂ hm₂'
      (hT₁.padT hm₁ hm₁' (le_max_left m₁ m₂))
      (hT₂.padT hm₂ hm₂' (le_max_right m₁ m₂))⟩

private lemma Trans.mulF [NeZero N] {g₁ g₁' g₂ g₂' : ℍ → ℂ}
    (h₁ : Trans K φ N g₁ g₁') (h₂ : Trans K φ N g₂ g₂') :
    Trans K φ N (g₁ * g₂) (g₁' * g₂') := by
  obtain ⟨hm₁, hm₁', m₁, hT₁⟩ := h₁
  obtain ⟨hm₂, hm₂', m₂, hT₂⟩ := h₂
  exact ⟨hm₁.mul hm₂, hm₁'.mul hm₂', m₁ + m₂, TransAt.mulT hm₁ hm₁' hm₂ hm₂' hT₁ hT₂⟩

private lemma qExpansion_const_coeff [NeZero N] (x : ℂ) (n : ℕ) :
    (qExpansion N ((fun _ : ℍ => x) * ⇑CuspForm.discriminant ^ 0)).coeff n =
      if n = 0 then x else 0 := by
  have hshape : ((fun _ : ℍ => x) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      x • (1 : ℍ → ℂ) := by
    funext τ; simp
  have hone_bd : IsBoundedAtImInfty (1 : ℍ → ℂ) := by
    have h1 : (1 : ℍ → ℂ) = fun _ : ℍ => (1 : ℂ) := rfl
    rw [h1]
    exact Filter.const_boundedAtFilter _ _
  have han : AnalyticAt ℂ (cuspFunction N (1 : ℍ → ℂ)) 0 :=
    analyticAt_cuspFunction_zero_of (g := (1 : ℍ → ℂ)) mdifferentiable_const
      (periodic_one_fn N) hone_bd
  rw [hshape, qExpansion_smul han, qExpansion_one, PowerSeries.coeff_smul, smul_eq_mul,
    PowerSeries.coeff_one]
  split <;> simp

private lemma transAt_const [NeZero N] (hφK : ∀ z : ↥K, φ z ∈ K) (c : ↥K) :
    TransAt K φ N 0 (fun _ : ℍ => (c : ℂ)) (fun _ : ℍ => φ c) := by
  have hdata : ∀ x : ℂ, Function.Periodic
      (((fun _ : ℍ => x) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) ∘ ofComplex) N ∧
      IsBoundedAtImInfty ((fun _ : ℍ => x) * ⇑CuspForm.discriminant ^ 0) := by
    intro x
    have hshape : ((fun _ : ℍ => x) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
        fun _ : ℍ => x := by
      funext τ; simp
    rw [hshape]
    exact ⟨fun t => rfl, Filter.const_boundedAtFilter _ _⟩
  refine ⟨⟨(hdata _).1, (hdata _).2, ?_⟩, ⟨(hdata _).1, (hdata _).2, ?_⟩, ?_⟩
  · intro n
    rw [qExpansion_const_coeff]
    split
    · exact c.2
    · exact zero_mem _
  · intro n
    rw [qExpansion_const_coeff]
    split
    · exact hφK c
    · exact zero_mem _
  · intro n z hz
    rw [qExpansion_const_coeff] at hz
    rw [qExpansion_const_coeff]
    split at hz
    · rename_i hn
      rw [ite_eq_left hn]
      have hzc : z = c := Subtype.ext hz
      rw [hzc]
    · rename_i hn
      rw [ite_eq_right hn]
      have hz0 : z = 0 := Subtype.ext (by rw [hz]; rfl)
      rw [hz0, map_zero]

private lemma trans_jf [NeZero N] {jf : ℍ → ℂ}
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    Trans K φ N jf jf := by
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
    have h1 : jf = fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := funext hjf
    rw [h1]
    exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  refine ⟨hjmd, hjmd, 1, transAt_self_of_rat ?_ ?_ ?_⟩
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
      exact ratCoeff_pow (ratCoeff_E (by norm_num) (by decide)) 3 _
    · exact ⟨0, by push_cast; ring⟩

private lemma trans_aeval [NeZero N] (hφK : ∀ z : ↥K, φ z ∈ K) {Idx : Type*}
    {gen gen' : Idx → ℍ → ℂ}
    (hgen : ∀ i, Trans K φ N (gen i) (gen' i)) (R : MvPolynomial Idx ↥K) :
    Trans K φ N (MvPolynomial.aeval gen (MvPolynomial.map (algebraMap ↥K ℂ) R))
      (MvPolynomial.aeval gen' (MvPolynomial.map (φ : ↥K →+* ℂ) R)) := by
  induction R using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    have e1 : (algebraMap ℂ (ℍ → ℂ)) ((algebraMap ↥K ℂ) c) = fun _ : ℍ => (c : ℂ) := rfl
    have e2 : (algebraMap ℂ (ℍ → ℂ)) (φ c) = fun _ : ℍ => φ c := rfl
    rw [e1, e2]
    exact ⟨mdifferentiable_const, mdifferentiable_const, 0, transAt_const hφK c⟩
  | add p q ihp ihq =>
    rw [map_add, map_add, map_add, map_add]
    exact Trans.addF ihp ihq
  | mul_X p i ih =>
    have e1 : MvPolynomial.map (algebraMap ↥K ℂ) (p * MvPolynomial.X i) =
        MvPolynomial.map (algebraMap ↥K ℂ) p * MvPolynomial.X i := by
      rw [map_mul, MvPolynomial.map_X]
    have e2 : MvPolynomial.map (φ : ↥K →+* ℂ) (p * MvPolynomial.X i) =
        MvPolynomial.map (φ : ↥K →+* ℂ) p * MvPolynomial.X i := by
      rw [map_mul, MvPolynomial.map_X]
    rw [e1, e2, map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact Trans.mulF ih (hgen i)

end Transport

section IdentityTransport

open ModularForm

variable {N : ℕ} {K : IntermediateField ℚ ℂ} {φ : ↥K →+* ℂ}

private lemma analyticAt_zero_fn [NeZero N] :
    AnalyticAt ℂ (cuspFunction N (0 : ℍ → ℂ)) 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine analyticAt_cuspFunction_zero hN' (fun x => rfl) mdifferentiable_const ?_
  have h0 : (0 : ℍ → ℂ) = fun _ : ℍ => (0 : ℂ) := rfl
  rw [h0]
  exact Filter.const_boundedAtFilter _ _

private lemma qExpansion_zero_fn [NeZero N] : qExpansion N (0 : ℍ → ℂ) = 0 := by
  have h0 : (0 : ℍ → ℂ) = (0 : ℂ) • (0 : ℍ → ℂ) := by rw [zero_smul]
  rw [h0, qExpansion_smul analyticAt_zero_fn, zero_smul]

private lemma discPow_ne_zero (m : ℕ) (τ : ℍ) :
    ((⇑CuspForm.discriminant : ℍ → ℂ) ^ m) τ ≠ 0 := by
  simp only [Pi.pow_apply]
  refine pow_ne_zero m ?_
  rw [congrFun CuspForm.coe_discriminant τ]
  exact ModularForm.discriminant_ne_zero τ

private lemma Trans.eq_zero_fwd [NeZero N] {g g' : ℍ → ℂ}
    (h : Trans K φ N g g') (hg0 : g = 0) : g' = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hm, hm', m, ⟨hK1, hK1', hrel⟩⟩ := h
  have hq0 : qExpansion N (g * ⇑CuspForm.discriminant ^ m) = 0 := by
    have h1 : (g * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = 0 := by
      rw [hg0]; funext τ; simp
    rw [h1, qExpansion_zero_fn]
  have hq0' : qExpansion N (g' * ⇑CuspForm.discriminant ^ m) = 0 := by
    ext n
    have hcoeff : (qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n = 0 := by
      rw [hq0, map_zero]
    have h2 := hrel n ⟨_, hK1.2.2 n⟩ rfl
    rw [h2]
    have hz0 : (⟨(qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n, hK1.2.2 n⟩ : ↥K)
        = 0 := Subtype.ext hcoeff
    rw [hz0, map_zero, map_zero]
  have hfn0 : (g' * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = 0 := by
    rw [qExpansion_eq_zero_iff hN' hK1'.1 (mdiff_mul_discPow hm' m) hK1'.2.1] at hq0'
    exact hq0'
  funext τ
  have h3 := congrFun hfn0 τ
  simp only [Pi.mul_apply, Pi.zero_apply] at h3 ⊢
  exact (mul_eq_zero.mp h3).resolve_right (discPow_ne_zero m τ)

private lemma Trans.eq_zero_rev [NeZero N] {g g' : ℍ → ℂ}
    (h : Trans K φ N g g') (hg0' : g' = 0) : g = 0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hm, hm', m, ⟨hK1, hK1', hrel⟩⟩ := h
  have hq0' : qExpansion N (g' * ⇑CuspForm.discriminant ^ m) = 0 := by
    have h1 : (g' * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = 0 := by
      rw [hg0']; funext τ; simp
    rw [h1, qExpansion_zero_fn]
  have hq0 : qExpansion N (g * ⇑CuspForm.discriminant ^ m) = 0 := by
    ext n
    have h2 := hrel n ⟨_, hK1.2.2 n⟩ rfl
    have h3 : φ (⟨(qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n, hK1.2.2 n⟩ : ↥K)
        = 0 := by
      rw [← h2, hq0', map_zero]
    have h4 := φ.injective (by rw [h3, map_zero] :
      φ (⟨(qExpansion N (g * ⇑CuspForm.discriminant ^ m)).coeff n, hK1.2.2 n⟩ : ↥K) = φ 0)
    have h5 := congrArg (fun z : ↥K => (z : ℂ)) h4
    simpa using h5
  have hfn0 : (g * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = 0 := by
    rw [qExpansion_eq_zero_iff hN' hK1.1 (mdiff_mul_discPow hm m) hK1.2.1] at hq0
    exact hq0
  funext τ
  have h3 := congrFun hfn0 τ
  simp only [Pi.mul_apply, Pi.zero_apply] at h3 ⊢
  exact (mul_eq_zero.mp h3).resolve_right (discPow_ne_zero m τ)

end IdentityTransport

end Aux

open Aux in
/-- Let `K` be a subfield of `ℂ` and `φ : K →+* ℂ` with values in `K`, and let `T g g'` say that
`g`, `g'` are holomorphic and for some `m` both `g Δ ^ m` and `g' Δ ^ m` are `N`-periodic,
bounded at `i∞`, with q-coefficients in `K`, and `φ` maps the coefficients of `g Δ ^ m` to
those of `g' Δ ^ m`. Then `T` is preserved by evaluating a polynomial over `K` (with `φ`
applied to its coefficients on the right), `T g g'` implies `g = 0 ↔ g' = 0`, and `T j j`
holds. -/
public theorem _root_.ModularForm.qExpansion_sigmaTransport_package (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ ℂ) (φ : ↥K →+* ℂ) (hφK : ∀ z : ↥K, φ z ∈ K)
    (T : (ℍ → ℂ) → (ℍ → ℂ) → Prop)
    (hT : ∀ g g' : ℍ → ℂ, T g g' ↔
        (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g' ∧
          ∃ m : ℕ,
            (Function.Periodic ((g * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
              IsBoundedAtImInfty (g * ModularForm.discriminant ^ m) ∧
              ∀ n : ℕ,
                (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
            (Function.Periodic ((g' * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
              IsBoundedAtImInfty (g' * ModularForm.discriminant ^ m) ∧
              ∀ n : ℕ,
                (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
            ∀ (n : ℕ) (z : ↥K),
              (z : ℂ) = (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n →
              (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n = φ z)) :
    (∀ {ι : Type*} (g g' : ι → ℍ → ℂ), (∀ i : ι, T (g i) (g' i)) → ∀ R : MvPolynomial ι ↥K,
        T (MvPolynomial.aeval g (MvPolynomial.map (algebraMap ↥K ℂ) R))
          (MvPolynomial.aeval g' (MvPolynomial.map φ R))) ∧
    (∀ g g' : ℍ → ℂ, T g g' → (g = 0 ↔ g' = 0)) ∧
    ∀ jf : ℍ → ℂ, (∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) → T jf jf :=
        by
  have hT' : ∀ g g' : ℍ → ℂ, T g g' ↔ Trans K φ N g g' := fun g g' => hT g g'
  refine ⟨fun g g' hg R => ?_, fun g g' h => ?_, fun jf hjf => (hT' jf jf).mpr (trans_jf hjf)⟩
  · exact (hT' _ _).mpr (trans_aeval hφK (fun i => (hT' _ _).mp (hg i)) R)
  · have h' := (hT' g g').mp h
    exact ⟨fun h0 => h'.eq_zero_fwd h0, fun h0 => h'.eq_zero_rev h0⟩

end

end QExpansionSigmaTransport

end FrickeFunctions
