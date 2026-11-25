/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem.lean`
and
`P2M/Sol/S_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem.lean`
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
# Linear independence over `ℂ` from linear independence over a coefficient field

This file upgrades `K`-linear independence of functions with `K`-rational q-expansions to
`ℂ`-linear independence.

## Main statement

* `UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem`
-/
namespace FrickeFunctions.QExpansionLinearIndependent

noncomputable section

open Complex Real

namespace Aux

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
  · refine ⟨-(2 * k / bernoulli k) * (σ (k - 1) n : ℚ), ?_⟩
    rw [ite_eq_right hn]
    push_cast
    ring

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

private lemma ratCoeff_pow {p : PowerSeries ℂ} (hp : ∀ n : ℕ, ∃ a : ℚ,
    p.coeff n = (a : ℂ)) (k : ℕ) :
    ∀ n : ℕ, ∃ a : ℚ, (p ^ k).coeff n = (a : ℂ) := by
  induction k with
  | zero =>
    intro n
    refine ⟨if n = 0 then 1 else 0, ?_⟩
    rw [pow_zero, PowerSeries.coeff_one]
    split <;> simp
  | succ k ih =>
    rw [pow_succ]
    exact ratCoeff_mul ih hp

end RatCoeff

section DiscPow

open UpperHalfPlane
open ModularForm
open SlashInvariantForm
open ModularFormClass
open CuspForm
open ModularForm.CuspForm
open EisensteinSeries
open OnePoint
open Matrix.SpecialLinearGroup

open scoped MatrixGroups Manifold

private def discPowForm (m : ℕ) : ModularForm 𝒮ℒ (12 * m) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow m)

private lemma discPowForm_coe (m : ℕ) : ⇑(discPowForm m) = ⇑CuspForm.discriminant ^ m := by
  funext z
  simp [discPowForm, ModularForm.coe_mcast, ModularForm.coe_pow,
    CuspForm.toModularFormₗ_apply]

end DiscPow

section Width

open scoped UpperHalfPlane Manifold
open UpperHalfPlane hiding I

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

end Width

section WidthMF

open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open SlashInvariantFormClass ModularFormClass

namespace ModularFormClass
private theorem ModularFormClass.qExpansion_coeff_width {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods) {N : ℕ} (hN : N ≠ 0) (n : ℕ) :
    (qExpansion N f).coeff n = if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos h1⟩
  exact Aux.qExpansion_coeff_width f hN (by simpa using periodic_comp_ofComplex f h1)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) n

end ModularFormClass
end WidthMF

section BSix

open UpperHalfPlane
open ModularForm
open SlashInvariantForm
open FrickeFunctions.QExpansionLinearIndependent.Aux.ModularFormClass
open CuspForm
open ModularForm.CuspForm
open Polynomial
open Real.Polynomial
open Filter
open scoped MatrixGroups Manifold

private lemma isBoundedAtImInfty_discriminant : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ →
    ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).boundedAtFilter

private lemma isBoundedAtImInfty_discPow (n : ℕ) :
    IsBoundedAtImInfty (⇑CuspForm.discriminant ^ n : ℍ → ℂ) := by
  induction n with
  | zero => exact pow_zero (⇑CuspForm.discriminant : ℍ → ℂ) ▸ const_boundedAtFilter _ (1 : ℂ)
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

end BSix

section KPoleSec

open UpperHalfPlane
open ModularForm
open FrickeFunctions.QExpansionLinearIndependent.Aux.ModularFormClass
open CuspForm
open ModularForm.CuspForm
open Polynomial
open Real.Polynomial
open Filter
open scoped MatrixGroups Manifold

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
  MDiff f ∧ ∃ m : ℕ, KPoleAt K N m f

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

private lemma mdiff_discPow (k : ℕ) : MDiff (⇑CuspForm.discriminant ^ k : ℍ → ℂ) := by
  rw [← discPowForm_coe]
  exact (discPowForm k).holo'

private lemma mdiff_mul_discPow {f : ℍ → ℂ} (hf : MDiff f) (m : ℕ) :
    MDiff (f * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) :=
  hf.mul (mdiff_discPow m)

private lemma analyticAt_cuspFunction_zero_of [NeZero N] {g : ℍ → ℂ} (hhol : MDiff g)
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

private lemma qExpansion_discPow_coeff_mem (K : IntermediateField ℚ ℂ) [NeZero N] (k n : ℕ) :
    (qExpansion N (⇑CuspForm.discriminant ^ k : ℍ → ℂ)).coeff n ∈ K := by
  have h1 : qExpansion (N : ℝ) (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      qExpansion (N : ℝ) (discPowForm k) := by
    rw [← discPowForm_coe]
  rw [h1, ModularFormClass.qExpansion_coeff_width (discPowForm k)
    one_mem_strictPeriods_SL (NeZero.ne N)]
  split
  · rw [qExpansion_one_discPowForm]
    exact mem_of_rat K (ratCoeff_pow ratCoeff_discriminant k _)
  · exact zero_mem _

private lemma KPoleAt.pad {K : IntermediateField ℚ ℂ} [NeZero N] {f : ℍ → ℂ} {m m' : ℕ}
    (hhol : MDiff f) (hm : m ≤ m') (h : KPoleAt K N m f) : KPoleAt K N m' f := by
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

end KPoleSec

section BEightEngine

open Function

private theorem linearIndependent_pi_algebraMap_of_field {k K σ ι : Type*}
    [Field k] [CommRing K] [Nontrivial K] [Algebra k K]
    {v : ι → σ → k} (hv : LinearIndependent k v) :
    LinearIndependent K (fun i n ↦ algebraMap k K (v i n)) := by
  classical
  obtain ⟨⟨β, b⟩⟩ := Module.Free.exists_basis (R := k) (M := K)
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hc i hi
  have key : ∀ n : σ, (∑ j ∈ s, (v j n) • c j) = 0 := by
    intro n
    have := congrFun hc n
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  have key2 : ∀ (α : β) (n : σ), (∑ j ∈ s, (v j n) * (b.repr (c j) α)) = 0 := by
    intro α n
    have h1 := congrArg b.repr (key n)
    rw [map_sum, map_zero] at h1
    have h2 := congrFun (congrArg DFunLike.coe h1) α
    simpa only [Finsupp.coe_finsetSum, Finset.sum_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] using h2
  have key3 : ∀ (α : β) (j : ι), j ∈ s → b.repr (c j) α = 0 := by
    intro α
    refine hv s (fun j ↦ b.repr (c j) α) ?_
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← key2 α n]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hzero : b.repr (c i) = 0 := Finsupp.ext fun α ↦ key3 α i hi
  exact b.repr.injective (by rw [hzero, map_zero])

end BEightEngine

section BEightHelper

open UpperHalfPlane Function Filter
open scoped Manifold

variable {N : ℕ}

private lemma mdpb_finsetSum_smul [NeZero N] {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {g : ι → ℍ → ℂ}
    (hhol : ∀ i ∈ s, MDiff (g i)) (hper : ∀ i ∈ s, Periodic ((g i) ∘ ofComplex) N)
    (hbd : ∀ i ∈ s, IsBoundedAtImInfty (g i)) :
    MDiff (∑ j ∈ s, c j • g j) ∧ Periodic ((∑ j ∈ s, c j • g j) ∘ ofComplex) N
      ∧ IsBoundedAtImInfty (∑ j ∈ s, c j • g j) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    refine ⟨?_, fun _ ↦ rfl, const_boundedAtFilter _ 0⟩
    have h__af := (mdifferentiable_const : MDiff (fun _ : ℍ ↦ (0 : ℂ)))
    simp at h__af ⊢
    exact h__af
  | cons a t hat ih =>
    have ⟨hh, hp, hb⟩ := ih (fun i hi ↦ hhol i (Finset.mem_cons_of_mem hi))
      (fun i hi ↦ hper i (Finset.mem_cons_of_mem hi))
      (fun i hi ↦ hbd i (Finset.mem_cons_of_mem hi))
    have haS : a ∈ Finset.cons a t hat := Finset.mem_cons_self a t
    simp only [Finset.sum_cons]
    refine ⟨((hhol a haS).const_smul _).add hh, ?_, ((hbd a haS).smul (c a)).add hb⟩
    intro z
    have h1 := hper a haS z; have h2 := hp z
    simp only [comp_apply] at h1 h2
    simp only [comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2]

private theorem qExpansion_finsetSum_smul [NeZero N] {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    {g : ι → ℍ → ℂ} (hhol : ∀ i ∈ s, MDiff (g i))
    (hper : ∀ i ∈ s, Periodic ((g i) ∘ ofComplex) N) (hbd : ∀ i ∈ s, IsBoundedAtImInfty (g i)) :
    qExpansion N (∑ j ∈ s, c j • g j) = ∑ j ∈ s, c j • qExpansion N (g j) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using qExpansion_zero (N : ℝ)
  | cons a t hat ih =>
    have haS : a ∈ Finset.cons a t hat := Finset.mem_cons_self a t
    have htS : ∀ i ∈ t, i ∈ Finset.cons a t hat := fun i hi ↦ Finset.mem_cons_of_mem hi
    obtain ⟨hhS, hpS, hbS⟩ := mdpb_finsetSum_smul t c
      (fun i hi ↦ hhol i (htS i hi)) (fun i hi ↦ hper i (htS i hi))
      (fun i hi ↦ hbd i (htS i hi))
    have hper_a : Periodic ((c a • g a) ∘ ofComplex) N := fun z ↦ by
      have h1 := hper a haS z; simp only [comp_apply] at h1
      simp only [comp_apply, Pi.smul_apply, smul_eq_mul, h1]
    have han_a : AnalyticAt ℂ (cuspFunction N (c a • g a)) 0 :=
      analyticAt_cuspFunction_zero_of ((hhol a haS).const_smul _) hper_a ((hbd a haS).smul (c a))
    have han_t : AnalyticAt ℂ (cuspFunction N (∑ j ∈ t, c j • g j)) 0 :=
      analyticAt_cuspFunction_zero_of hhS hpS hbS
    rw [Finset.sum_cons, Finset.sum_cons, qExpansion_add han_a han_t,
      qExpansion_smul (analyticAt_cuspFunction_zero_of (hhol a haS) (hper a haS) (hbd a haS)),
      ih (fun i hi ↦ hhol i (htS i hi)) (fun i hi ↦ hper i (htS i hi))
        (fun i hi ↦ hbd i (htS i hi))]

end BEightHelper

section QNonzero

open scoped UpperHalfPlane Manifold MatrixGroups IntermediateField
open UpperHalfPlane hiding I

variable {N : ℕ} [NeZero N]

private lemma exists_qExpansion_coeff_ne_zero {g : ℍ → ℂ} (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Function.Periodic (g ∘ ofComplex) N) (hbd : IsBoundedAtImInfty g) (hg : g ≠ 0) :
    ∃ n, (qExpansion N g).coeff n ≠ 0 := by
  by_contra h
  push Not at h
  apply hg
  funext τ
  have hs := hasSum_qExpansion (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd τ
  simp only [h, zero_smul] at hs
  exact (hs.unique hasSum_zero)

end QNonzero

section BEightStageTwo

open UpperHalfPlane Function Filter
open scoped Manifold

variable {N : ℕ}

private lemma eq_zero_of_mul_discPow_eq_zero (M : ℕ) {h : ℍ → ℂ}
    (h0 : h * (⇑CuspForm.discriminant ^ M : ℍ → ℂ) = 0) : h = 0 := by
  funext τ
  have := congrFun h0 τ
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at this
  refine (mul_eq_zero.mp this).resolve_right ?_
  rw [congrFun CuspForm.coe_discriminant τ]
  exact pow_ne_zero M (ModularForm.discriminant_ne_zero τ)

private lemma finsetSum_smul_eq_zero_iff_qCoeff [NeZero N] {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {f : ι → ℍ → ℂ} (M : ℕ)
    (hhol : ∀ j ∈ s, MDiff (f j))
    (hper : ∀ j ∈ s, Periodic ((f j * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N)
    (hbd : ∀ j ∈ s, IsBoundedAtImInfty (f j * ⇑CuspForm.discriminant ^ M)) :
    (∑ j ∈ s, c j • f j = 0)
      ↔ ∀ n, ∑ j ∈ s, c j * (qExpansion N (f j * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
  set g : ι → ℍ → ℂ := fun j ↦ f j * ⇑CuspForm.discriminant ^ M with hg_def
  have hghol : ∀ j ∈ s, MDiff (g j) := fun j hj ↦ mdiff_mul_discPow (hhol j hj) M
  have hpull : ∑ j ∈ s, c j • g j = (∑ j ∈ s, c j • f j) * ⇑CuspForm.discriminant ^ M := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ (smul_mul_assoc (c j) (f j) _).symm
  have hq := qExpansion_finsetSum_smul s c hghol hper hbd
  constructor
  · intro h0 n
    rw [hpull, h0, zero_mul, qExpansion_zero (N : ℝ)] at hq
    have := congrArg (fun p : PowerSeries ℂ ↦ p.coeff n) hq.symm
    simpa only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, map_zero] using this
  · intro h0
    have hqeq : qExpansion N (∑ j ∈ s, c j • g j) = 0 := by
      rw [hq]; ext n
      simpa only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, map_zero] using h0 n
    obtain ⟨hh, hp, hb⟩ := mdpb_finsetSum_smul s c hghol hper hbd
    apply eq_zero_of_mul_discPow_eq_zero M
    rw [← hpull]
    by_contra hne
    obtain ⟨n, hn⟩ := exists_qExpansion_coeff_ne_zero hh hp hb hne
    rw [hqeq] at hn; simp at hn

private theorem linearIndependent_complex_of_kPole [NeZero N] (K : IntermediateField ℚ ℂ)
    {ι : Type*} {f : ι → ℍ → ℂ} (hKP : ∀ i, KPole K N (f i))
    (hli : LinearIndependent ↥K f) : LinearIndependent ℂ f := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi
  set m : ι → ℕ := fun j ↦ (hKP j).2.choose
  set M : ℕ := s.sup m
  have hKPM : ∀ j ∈ s, KPoleAt K N M (f j) := fun j hj ↦
    KPoleAt.pad (hKP j).1 (Finset.le_sup hj) (hKP j).2.choose_spec
  have hhol : ∀ (j : s), MDiff (f j) := fun j ↦ (hKP j).1
  have hper : ∀ (j : s), Periodic ((f j * ⇑CuspForm.discriminant ^ M) ∘ ofComplex) N :=
    fun j ↦ (hKPM j j.2).1
  have hbd : ∀ (j : s), IsBoundedAtImInfty (f j * ⇑CuspForm.discriminant ^ M) :=
    fun j ↦ (hKPM j j.2).2.1
  have hiff : ∀ (t : Finset s) (c' : s → ℂ),
      (∑ j ∈ t, c' j • f j = 0)
        ↔ ∀ n, ∑ j ∈ t, c' j * (qExpansion N (f j * ⇑CuspForm.discriminant ^ M)).coeff n = 0 :=
    fun t c' ↦ finsetSum_smul_eq_zero_iff_qCoeff t c' M (fun j _ ↦ hhol j)
      (fun j _ ↦ hper j) (fun j _ ↦ hbd j)
  set vK : s → ℕ → ↥K := fun j n ↦
    ⟨(qExpansion N (f j * ⇑CuspForm.discriminant ^ M)).coeff n, (hKPM j j.2).2.2 n⟩ with hvK_def
  have halg : ∀ x : ↥K, (x : ℂ) = algebraMap ↥K ℂ x := fun _ ↦ rfl
  have hvKcoe : ∀ (j : s) n, algebraMap ↥K ℂ (vK j n)
      = (qExpansion N (f j * ⇑CuspForm.discriminant ^ M)).coeff n := fun _ _ ↦ rfl
  have hli_s := hli.comp (Subtype.val : s → ι) Subtype.val_injective
  have hvKli : LinearIndependent ↥K vK := by
    rw [linearIndependent_iff']
    intro t d hd j hj
    have hcoeff : ∀ n, ∑ j' ∈ t, (d j' : ℂ)
        * (qExpansion N (f j' * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
      intro n
      have h1 := congrFun hd n
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h1
      have h2 := congrArg (fun x : ↥K ↦ (x : ℂ)) h1
      simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
        ZeroMemClass.coe_zero] at h2
      simp only [halg, hvKcoe] at h2; exact h2
    have hsumC : ∑ j' ∈ t, (d j' : ℂ) • f j' = 0 :=
      (hiff t (fun j' ↦ (d j' : ℂ))).mpr hcoeff
    have hsumK : ∑ j' ∈ t, d j' • (fun j'' : s ↦ f j'') j' = 0 := by
      rw [← hsumC]
      exact Finset.sum_congr rfl fun j' _ ↦ (algebraMap_smul ℂ (d j') (f j')).symm
    exact linearIndependent_iff'.mp hli_s t d hsumK j hj
  have hvCli := linearIndependent_pi_algebraMap_of_field (K := ℂ) hvKli
  have hcoeff' : ∀ n, ∑ j' ∈ (Finset.univ : Finset s), c j'
      * (qExpansion N (f j' * ⇑CuspForm.discriminant ^ M)).coeff n = 0 := by
    intro n
    have := (hiff Finset.univ (fun j' ↦ c j')).mp ?_ n
    · exact this
    · rw [Finset.sum_coe_sort s (fun j' ↦ c j' • f j')]; exact hc
  have hsum0 : ∑ j' ∈ (Finset.univ : Finset s), (fun j'' : s ↦ c j''.1) j'
      • (fun n ↦ (algebraMap ↥K ℂ) (vK j' n)) = 0 := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hvKcoe]
    exact hcoeff' n
  exact linearIndependent_iff'.mp hvCli Finset.univ (fun j'' ↦ c j''.1) hsum0 ⟨i, hi⟩
    (Finset.mem_univ _)

end BEightStageTwo

end Aux

open scoped Manifold in
/-- Let `f i` be holomorphic functions on the upper half-plane such that some `f i Δ ^ m` is
`N`-periodic and bounded at `i∞` with width-`N` q-coefficients in a subfield `K` of `ℂ`. If the
`f i` are linearly independent over `K`, they are linearly independent over `ℂ`. -/
public theorem _root_.UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem (N : ℕ)
    [NeZero N]
    (K : IntermediateField ℚ ℂ) {ι : Type*} (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i) ∧ ∃ m : ℕ,
      Function.Periodic ((f i * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
      UpperHalfPlane.IsBoundedAtImInfty (f i * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N (f i * ModularForm.discriminant ^ m)).coeff n ∈ K)
    (hli : LinearIndependent ↥K f) : LinearIndependent ℂ f :=
  Aux.linearIndependent_complex_of_kPole K
    (fun i => ⟨(hf i).1, by
      obtain ⟨m, hm⟩ := (hf i).2
      exact ⟨m, by simpa only [Aux.KPoleAt, CuspForm.coe_discriminant] using hm⟩⟩) hli

end

end QExpansionLinearIndependent

end FrickeFunctions
