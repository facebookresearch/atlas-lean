/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_levelOne_hauptmodul_package.lean`
and
`P2M/Sol/S_WLight_levelOne_hauptmodul_package.lean`
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
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# The `j`-function as a Hauptmodul in level one

This file proves that `j` is a Hauptmodul for `SL(2, ℤ)`, with rationality of the polynomial
expressions.

## Main statement

* `ModularForm.levelOne_hauptmodul_package`
-/
namespace FrickeFunctions.LevelOneHauptmodul

noncomputable section

open Complex Real
namespace Aux

section A1_levelOne_ratSpan

open UpperHalfPlane
open ModularForm
open SlashInvariantForm
open ModularFormClass
open CuspForm
open ModularForm.CuspForm
open EisensteinSeries
open scoped MatrixGroups ArithmeticFunction.sigma

private def RatQExp {k : ℤ} (f : ModularForm 𝒮ℒ k) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, (qExpansion 1 f).coeff n = (q : ℂ)

section RatCoeffClosure

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

end RatCoeffClosure

section RatGenerators

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

private lemma ratQExp_one : RatQExp (1 : ModularForm 𝒮ℒ 0) := by
  intro n
  refine ⟨if n = 0 then 1 else 0, ?_⟩
  rw [ModularForm.qExpansion_one, PowerSeries.coeff_one]
  split <;> simp

end RatGenerators

section SpanTop

private lemma span_ratQExp_eq_top_of_forall_eq_zero {k : ℤ}
    (h : ∀ f : ModularForm 𝒮ℒ k, f = 0) :
    Submodule.span ℂ {f : ModularForm 𝒮ℒ k | RatQExp f} = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  rw [h f]
  exact Submodule.zero_mem _

private theorem levelOne_ratSpan (k : ℤ) :
    Submodule.span ℂ {f : ModularForm 𝒮ℒ k | RatQExp f} = ⊤ := by
  suffices H : ∀ n : ℕ, ∀ k : ℤ, k.toNat = n →
      Submodule.span ℂ {f : ModularForm 𝒮ℒ k | RatQExp f} = ⊤ from H k.toNat k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro k hk
  rcases lt_or_ge k 0 with hneg | hpos
  · exact span_ratQExp_eq_top_of_forall_eq_zero fun f => by
      ext z
      simpa using congrFun (ModularFormClass.levelOne_neg_weight_eq_zero hneg f) z
  rcases Int.even_or_odd k with hev | hodd
  swap
  · exact span_ratQExp_eq_top_of_forall_eq_zero fun f =>
      ModularForm.levelOne_odd_weight_eq_zero hodd f
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [eq_top_iff]
    rintro f -
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const f
    have hf : f = c • (1 : ModularForm 𝒮ℒ 0) := by
      ext z
      simp [congrFun hc z, ModularForm.one_coe_eq_one]
    rw [hf]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ratQExp_one)
  rcases eq_or_ne k 2 with rfl | hk2
  · refine span_ratQExp_eq_top_of_forall_eq_zero fun f => ?_
    have : Subsingleton (ModularForm 𝒮ℒ 2) :=
      rank_zero_iff.mp ModularForm.levelOne_weight_two_rank_zero
    exact Subsingleton.elim f 0
  have hk2' : k % 2 = 0 := Int.even_iff.mp hev
  have hk4 : 4 ≤ k := by omega
  have hm3 : 3 ≤ k.toNat := by omega
  have hm2 : Even k.toNat := by rw [Nat.even_iff]; omega
  set Ek : ModularForm 𝒮ℒ k := ModularForm.mcast (show ((k.toNat : ℤ)) = k by omega) (E hm3)
    with hEkdef
  have hEk_rat : RatQExp Ek := by
    intro n
    exact ratCoeff_E hm3 hm2 n
  rw [eq_top_iff]
  rintro f -
  set c₀ := (qExpansion 1 f).coeff 0 with hc₀
  have hcoe_sub : (⇑(f - c₀ • Ek) : ℍ → ℂ) = ⇑f - ⇑(c₀ • Ek) := by
    simp [FunLike.coe_sub]
  have hcusp : (qExpansion 1 (⇑(f - c₀ • Ek) : ℍ → ℂ)).coeff 0 = 0 := by
    rw [hcoe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      map_sub, PowerSeries.coeff_smul, hEkdef, ModularForm.qExpansion_mcast,
      E_qExpansion_coeff_zero hm3 hm2, ← hc₀]
    simp
  set g : ModularForm 𝒮ℒ (k - 12) :=
    CuspForm.discriminantEquiv (ModularForm.toCuspForm (f - c₀ • Ek) hcusp) with hgdef
  set Ψ : ModularForm 𝒮ℒ (k - 12) →ₗ[ℂ] ModularForm 𝒮ℒ k :=
    CuspForm.toModularFormₗ.comp CuspForm.discriminantEquiv.symm.toLinearMap with hΨdef
  have hsymm : ∀ u : ModularForm 𝒮ℒ (k - 12),
      CuspForm.discriminantEquiv.symm u = CuspForm.ofMulDiscriminant u := fun u =>
    CuspForm.discriminantEquiv.symm_apply_eq.mpr (by
      ext z
      rw [CuspForm.discriminantEquiv_apply, CuspForm.ofMulDiscriminant_apply,
        mul_div_cancel_left₀ _ (ModularForm.discriminant_ne_zero z)])
  have hΨg : Ψ g = f - c₀ • Ek := by
    rw [hΨdef, hgdef, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    ext z
    simp [CuspForm.toModularFormₗ_apply, ModularForm.toCuspForm_apply]
  have hΨrat : ∀ u : ModularForm 𝒮ℒ (k - 12), RatQExp u → RatQExp (Ψ u) := by
    intro u hu
    have hcoe : ⇑(Ψ u) = ⇑CuspForm.discriminant * ⇑u := by
      funext z
      rw [hΨdef, LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm u]
      simp [CuspForm.toModularFormₗ_apply, CuspForm.ofMulDiscriminant_apply,
        CuspForm.coe_discriminant]
    have hq : qExpansion 1 (Ψ u) = qExpansion 1 ModularForm.discriminant * qExpansion 1 u := by
      calc qExpansion 1 (Ψ u) = qExpansion 1 (⇑CuspForm.discriminant * ⇑u) := by rw [hcoe]
        _ = _ := ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL _ _
    intro n
    rw [hq]
    exact ratCoeff_mul ratCoeff_discriminant hu n
  have hg_mem : g ∈ Submodule.span ℂ {u : ModularForm 𝒮ℒ (k - 12) | RatQExp u} := by
    rw [IH (k - 12).toNat (by omega) (k - 12) rfl]
    exact Submodule.mem_top
  have hΨg_mem : Ψ g ∈ Submodule.span ℂ {f : ModularForm 𝒮ℒ k | RatQExp f} := by
    have h1 : Ψ g ∈ Submodule.map Ψ (Submodule.span ℂ {u : ModularForm 𝒮ℒ (k - 12) | RatQExp u}) :=
      Submodule.mem_map_of_mem hg_mem
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨u, hu, rfl⟩
    exact hΨrat u hu
  have hsplit : c₀ • Ek + Ψ g = f := by
    rw [hΨg]
    abel
  rw [← hsplit]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span hEk_rat)) hΨg_mem

end SpanTop

end A1_levelOne_ratSpan

section A2_polynomial_j

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

private def j : ℍ → ℂ := fun z => E₄ z ^ 3 / ModularForm.discriminant z

private lemma j_mul_discriminant (z : ℍ) : j z * ModularForm.discriminant z = E₄ z ^ 3 :=
  div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero z)

private theorem modularForm_eq_poly_j_mul_discriminant_pow (m : ℕ) (F : ModularForm 𝒮ℒ (12 * m)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
      ⇑F = fun z => Polynomial.eval (j z) P * ModularForm.discriminant z ^ m := by
  induction m with
  | zero =>
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const
      (ModularForm.mcast (by norm_num) F : ModularForm 𝒮ℒ 0)
    have hcoe : ⇑F = Function.const ℍ c := by rw [← hc]; rfl
    refine ⟨Polynomial.C c, by simp, funext fun z => ?_⟩
    rw [show F z = Function.const ℍ c z from congrFun hcoe z]
    simp
  | succ m IH =>
    set G : ModularForm 𝒮ℒ (12 * ((m + 1 : ℕ) : ℤ)) :=
      ModularForm.mcast (by push_cast; ring) (E₄.pow (3 * (m + 1))) with hGdef
    have hG0 : (qExpansion 1 G).coeff 0 = 1 := by
      rw [hGdef, ModularForm.qExpansion_mcast,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
        PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩, one_pow]
    set c₀ := (qExpansion 1 F).coeff 0 with hc₀
    have hcoe_sub : (⇑(F - c₀ • G) : ℍ → ℂ) = ⇑F - ⇑(c₀ • G) :=
      FunLike.coe_sub F (c₀ • G)
    have hcusp : (qExpansion 1 (⇑(F - c₀ • G) : ℍ → ℂ)).coeff 0 = 0 := by
      rw [hcoe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
        FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
        map_sub, PowerSeries.coeff_smul, hG0, ← hc₀]
      simp
    set F' : ModularForm 𝒮ℒ (12 * (m : ℤ)) :=
      ModularForm.mcast (by push_cast; ring)
        (CuspForm.discriminantEquiv (ModularForm.toCuspForm (F - c₀ • G) hcusp)) with hF'def
    obtain ⟨P', hP'deg, hP'⟩ := IH F'
    refine ⟨Polynomial.C c₀ * Polynomial.X ^ (m + 1) + P', ?_, funext fun z => ?_⟩
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (hP'deg.trans (by omega)))
      exact Polynomial.natDegree_C_mul_X_pow_le c₀ (m + 1)
    · have hdecomp : F z = c₀ * G z + (F - c₀ • G) z := by
        rw [sub_apply, smul_apply]
        simp
      have hGcoe : (⇑G : ℍ → ℂ) = (⇑E₄) ^ (3 * (m + 1)) := by
        rw [show (⇑G : ℍ → ℂ) = ⇑(E₄.pow (3 * (m + 1))) from rfl, ModularForm.coe_pow]
      have hGz : G z = E₄ z ^ (3 * (m + 1)) :=
        (congrFun hGcoe z).trans (Pi.pow_apply _ _ _)
      have hcusppart : (F - c₀ • G) z =
          ModularForm.discriminant z * (Polynomial.eval (j z) P' *
            ModularForm.discriminant z ^ m) := by
        have hF'z : (CuspForm.discriminantEquiv
            (ModularForm.toCuspForm (F - c₀ • G) hcusp)) z =
            Polynomial.eval (j z) P' * ModularForm.discriminant z ^ m := by
          rw [show (CuspForm.discriminantEquiv
              (ModularForm.toCuspForm (F - c₀ • G) hcusp)) z = F' z from rfl]
          exact congrFun hP' z
        calc (F - c₀ • G) z
            = (ModularForm.toCuspForm (F - c₀ • G) hcusp) z := rfl
          _ = ModularForm.discriminant z * (CuspForm.discriminantEquiv
              (ModularForm.toCuspForm (F - c₀ • G) hcusp)) z :=
            (ModularForm.discriminant_mul_discriminantEquiv_apply _ z).symm
          _ = _ := by rw [hF'z]
      rw [hdecomp, hGz, hcusppart, pow_mul, show E₄ z ^ 3 = j z * ModularForm.discriminant z from
        (j_mul_discriminant z).symm]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      ring

private def discPowForm (m : ℕ) : ModularForm 𝒮ℒ (12 * m) :=
  ModularForm.mcast (by ring) ((CuspForm.toModularFormₗ CuspForm.discriminant).pow m)

private lemma discPowForm_coe (m : ℕ) : ⇑(discPowForm m) = ⇑CuspForm.discriminant ^ m := by
  funext z
  simp [discPowForm, ModularForm.coe_mcast, ModularForm.coe_pow,
    CuspForm.toModularFormₗ_apply]

private lemma holMulDiscPow_slash (m : ℕ) (h : ℍ → ℂ)
    (hinv : ∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) (γ : SL(2, ℤ)) :
    (h * ⇑CuspForm.discriminant ^ m) ∣[(12 * m : ℤ)] γ =
      h * ⇑CuspForm.discriminant ^ m := by
  have hD : (⇑(discPowForm m) : ℍ → ℂ) ∣[(12 * m : ℤ)] (γ : GL (Fin 2) ℝ) = ⇑(discPowForm m) :=
    (discPowForm m).slash_action_eq' _ ⟨γ, rfl⟩
  rw [discPowForm_coe] at hD
  calc (h * ⇑CuspForm.discriminant ^ m) ∣[(12 * m : ℤ)] γ
      = (h * ⇑CuspForm.discriminant ^ m) ∣[((0 : ℤ) + 12 * m)] γ := by rw [zero_add]
    _ = h ∣[(0 : ℤ)] γ * (⇑CuspForm.discriminant ^ m) ∣[(12 * m : ℤ)] γ :=
        mul_slash_SL2 0 (12 * m) γ h _
    _ = h * ⇑CuspForm.discriminant ^ m := by rw [hinv γ, SL_slash, hD]

private def holMulDiscPow (m : ℕ) (h : ℍ → ℂ) (hol : MDiff h)
    (hinv : ∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h)
    (hbd : IsBoundedAtImInfty (h * ⇑CuspForm.discriminant ^ m)) :
    ModularForm 𝒮ℒ (12 * m) where
  toFun := h * ⇑CuspForm.discriminant ^ m
  slash_action_eq' := fun _ hγ => by
    obtain ⟨γ, rfl⟩ := hγ
    have h1 := holMulDiscPow_slash m h hinv γ
    rw [SL_slash, show ((γ : GL (Fin 2) ℝ)) = mapGL ℝ γ from rfl] at h1
    exact h1
  holo' := hol.mul (by rw [← discPowForm_coe]; exact (discPowForm m).holo')
  bdd_at_cusps' := fun {c} hc => by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [holMulDiscPow_slash m h hinv γ]
    exact hbd

private theorem levelOne_holFn_eq_polynomial_j (m : ℕ) (h : ℍ → ℂ) (hol : MDiff h)
    (hinv : ∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h)
    (hbd : IsBoundedAtImInfty (h * ⇑CuspForm.discriminant ^ m)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ h = fun z => Polynomial.eval (j z) P := by
  obtain ⟨P, hdeg, hP⟩ := modularForm_eq_poly_j_mul_discriminant_pow m
    (holMulDiscPow m h hol hinv hbd)
  refine ⟨P, hdeg, funext fun z => ?_⟩
  have hz := congrFun hP z
  have hΔ : ModularForm.discriminant z ^ m ≠ 0 :=
    pow_ne_zero _ (ModularForm.discriminant_ne_zero z)
  have hcancel : h z * ModularForm.discriminant z ^ m =
      Polynomial.eval (j z) P * ModularForm.discriminant z ^ m := hz
  exact mul_right_cancel₀ hΔ hcancel

end A2_polynomial_j

section A3_qexp_principle

open UpperHalfPlane
open ModularForm
open ModularFormClass
open CuspForm
open ModularForm.CuspForm
open EisensteinSeries
open scoped MatrixGroups

private lemma coeff_pow_eq_zero_of_lt {D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) {k n : ℕ}
    (hn : n < k) : (D ^ k).coeff n = 0 := by
  have hX : (PowerSeries.X : PowerSeries ℂ) ∣ D :=
    PowerSeries.X_dvd_iff.mpr (by rwa [← PowerSeries.coeff_zero_eq_constantCoeff])
  exact PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd hX k) n hn

private lemma coeff_pow_self {D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) (k : ℕ) :
    (D ^ k).coeff k = (D.coeff 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    rw [Finset.sum_eq_single (k, 1)]
    · rw [ih, pow_succ]
    · rintro ⟨a, b⟩ hab hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      have hab' : a + b = k + 1 := hab
      rcases lt_or_ge a k with ha | ha
      · rw [coeff_pow_eq_zero_of_lt hD0 ha, zero_mul]
      · have hb : b = 0 ∨ b = 1 := by omega
        rcases hb with rfl | rfl
        · rw [hD0, mul_zero]
        · have hak : a = k := by omega
          exact absurd (by rw [hak]) hne
    · intro hmem
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr
        (show (k, 1).1 + (k, 1).2 = k + 1 from rfl)) hmem

private lemma coeff_mul_pow_at_order {p D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) (k : ℕ) :
    (p * D ^ k).coeff k = p.coeff 0 * (D.coeff 1) ^ k := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, k)]
  · rw [coeff_pow_self hD0]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    have hab' : a + b = k := hab
    rcases Nat.lt_or_ge b k with h | h
    · rw [coeff_pow_eq_zero_of_lt hD0 h, mul_zero]
    · have ha0 : a = 0 := by omega
      have hbk : b = k := by omega
      subst ha0 hbk
      exact absurd rfl hne
  · intro hmem
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr
      (show (0, k).1 + (0, k).2 = k from Nat.zero_add k)) hmem

private lemma coeff_mul_pow_eq_zero_of_lt {p D : PowerSeries ℂ} (hD0 : D.coeff 0 = 0) {k n : ℕ}
    (hn : n < k) : (p * D ^ k).coeff n = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ⟨a, b⟩ hab => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
  have hab' : a + b = n := hab
  rw [coeff_pow_eq_zero_of_lt hD0 (show b < k by omega), mul_zero]

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

private def polyDiscSeries (m : ℕ) (P : Polynomial ℂ) : PowerSeries ℂ :=
  ∑ i ∈ Finset.range (m + 1),
    PowerSeries.C (P.coeff i) * (qExpansion 1 E₄) ^ (3 * i) *
      (qExpansion 1 ModularForm.discriminant) ^ (m - i)

private lemma discriminant_qExpansion_coeff_zero :
    (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL

private lemma triangular_aux (m : ℕ) :
    ∀ d : ℕ, d ≤ m → ∀ c : ℕ → ℂ,
      (∀ n : ℕ, ∃ q : ℚ, (∑ i ∈ Finset.range (d + 1),
        PowerSeries.C (c i) * (qExpansion 1 E₄) ^ (3 * i) *
          (qExpansion 1 ModularForm.discriminant) ^ (m - i)).coeff n = (q : ℂ)) →
      ∀ i : ℕ, i ≤ d → ∃ q : ℚ, c i = (q : ℂ) := by
  intro d
  induction d with
  | zero =>
    intro _ c hser i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    obtain ⟨q, hq⟩ := hser m
    refine ⟨q, ?_⟩
    rw [Finset.sum_range_one, Nat.mul_zero, pow_zero, mul_one, Nat.sub_zero,
      coeff_mul_pow_at_order discriminant_qExpansion_coeff_zero,
      ModularForm.discriminant_qExpansion_coeff_one, one_pow, mul_one,
      PowerSeries.coeff_zero_C] at hq
    exact hq
  | succ d ihd =>
    intro hd1 c hser
    have htop : ∃ q : ℚ, c (d + 1) = (q : ℂ) := by
      obtain ⟨q, hq⟩ := hser (m - (d + 1))
      refine ⟨q, ?_⟩
      rw [Finset.sum_range_succ, map_add] at hq
      have hlow : (∑ i ∈ Finset.range (d + 1),
          PowerSeries.C (c i) * (qExpansion 1 E₄) ^ (3 * i) *
            (qExpansion 1 ModularForm.discriminant) ^ (m - i)).coeff (m - (d + 1)) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun i hi' => ?_
        rw [Finset.mem_range] at hi'
        exact coeff_mul_pow_eq_zero_of_lt discriminant_qExpansion_coeff_zero (by omega)
      rw [hlow, zero_add, coeff_mul_pow_at_order discriminant_qExpansion_coeff_zero,
        ModularForm.discriminant_qExpansion_coeff_one, one_pow, mul_one,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩, one_pow, mul_one] at hq
      exact hq
    intro i hi
    rcases Nat.lt_or_ge i (d + 1) with hil | hig
    · obtain ⟨qt, hqt⟩ := htop
      refine ihd (by omega) c (fun n => ?_) i (by omega)
      obtain ⟨q, hq⟩ := hser n
      have hterm : ∀ n' : ℕ, ∃ q' : ℚ, (PowerSeries.C (c (d + 1)) *
          (qExpansion 1 E₄) ^ (3 * (d + 1)) *
          (qExpansion 1 ModularForm.discriminant) ^ (m - (d + 1))).coeff n' = (q' : ℂ) := by
        refine ratCoeff_mul (ratCoeff_mul ?_
          (ratCoeff_pow (ratCoeff_E (by norm_num) (by decide)) _))
          (ratCoeff_pow ratCoeff_discriminant _)
        intro n'
        refine ⟨if n' = 0 then qt else 0, ?_⟩
        rw [PowerSeries.coeff_C]
        split <;> simp [hqt]
      obtain ⟨q', hq'⟩ := hterm n
      refine ⟨q - q', ?_⟩
      rw [Finset.sum_range_succ, map_add, hq'] at hq
      rw [eq_sub_of_add_eq hq]
      push_cast
      ring
    · obtain rfl : i = d + 1 := by omega
      exact htop

private theorem levelOne_qexp_principle (m : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ m)
    (hrat : ∀ n : ℕ, ∃ q : ℚ, (polyDiscSeries m P).coeff n = (q : ℂ)) :
    ∀ i : ℕ, ∃ q : ℚ, P.coeff i = (q : ℂ) := by
  intro i
  rcases Nat.lt_or_ge m i with him | him
  · exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp⟩
  · refine triangular_aux m m le_rfl (fun i => P.coeff i) (fun n => ?_) i him
    simpa [polyDiscSeries] using hrat n

end A3_qexp_principle

section A4_j_surjective

open UpperHalfPlane
open ModularForm
open SlashInvariantForm
open SlashInvariantFormClass
open ModularFormClass
open CuspForm
open ModularForm.CuspForm
open EisensteinSeries
open OnePoint
open Matrix.SpecialLinearGroup
open Filter

open scoped MatrixGroups Manifold Topology

private lemma toModularFormDisc_coe :
    (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) = ModularForm.discriminant := by
  funext z
  rw [CuspForm.toModularFormₗ_apply]
  exact congrFun CuspForm.coe_discriminant z

private theorem j_surjective : Function.Surjective j := by
  intro c
  by_contra hc
  push Not at hc
  set Fc : ModularForm 𝒮ℒ 12 :=
    ModularForm.mcast (by decide) (E₄.pow 3) -
      c • CuspForm.toModularFormₗ CuspForm.discriminant with hFdef
  have hFapp : ∀ z : ℍ, Fc z = E₄ z ^ 3 - c * ModularForm.discriminant z := by
    intro z
    rw [hFdef, sub_apply, smul_apply, smul_eq_mul,
      CuspForm.toModularFormₗ_apply, congrFun CuspForm.coe_discriminant z,
      show (ModularForm.mcast (by decide) (E₄.pow 3) : ModularForm 𝒮ℒ 12) z = E₄ z ^ 3 from
        (congrFun (ModularForm.coe_pow E₄ 3) z).trans (Pi.pow_apply _ _ _)]
  have hnv : ∀ z : ℍ, Fc z ≠ 0 := by
    intro z h0
    rw [hFapp z, sub_eq_zero] at h0
    refine hc z ?_
    change E₄ z ^ 3 / ModularForm.discriminant z = c
    rw [h0, mul_div_cancel_right₀ _ (ModularForm.discriminant_ne_zero z)]
  have hF0 : (qExpansion 1 Fc).coeff 0 = 1 := by
    rw [hFdef, FunLike.coe_sub,
      ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      map_sub, PowerSeries.coeff_smul, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
      ← PowerSeries.coeff_zero_eq_constantCoeff,
      E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩, one_pow]
    rw [show (qExpansion 1 (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ)).coeff 0
        = 0 from toModularFormDisc_coe ▸ discriminant_qExpansion_coeff_zero]
    simp
  set hfn : ℍ → ℂ := ⇑CuspForm.discriminant / ⇑Fc with hhdef
  have hol : MDiff hfn := CuspForm.discriminant.holo'.div Fc.holo' hnv
  have hinv : ∀ γ : SL(2, ℤ), hfn ∣[(0 : ℤ)] γ = hfn := by
    intro γ
    have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
    rw [hhdef, show (0 : ℤ) = 12 - 12 by norm_num, div_slash_SL2, SL_slash, SL_slash,
      slash_action_eqn _ _ hγ, slash_action_eqn _ _ hγ]
  have hper := periodic_comp_ofComplex Fc one_mem_strictPeriods_SL
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero Fc one_pos one_mem_strictPeriods_SL
  have htends : Tendsto ⇑Fc atImInfty (𝓝 (cuspFunction 1 ⇑Fc 0)) :=
    (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
      (fun τ => SlashInvariantFormClass.eq_cuspFunction Fc τ one_mem_strictPeriods_SL one_ne_zero)
  have hcusp0 : cuspFunction 1 ⇑Fc 0 = 1 := by
    have h1 := qExpansion_coeff_zero one_pos hanal hper
    have h2 := cuspFunction_apply_zero one_pos hanal hper
    rw [h2, ← h1]
    exact hF0
  rw [hcusp0] at htends
  have hbd : IsBoundedAtImInfty hfn := by
    have hΔ0 : IsZeroAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
      CuspFormClass.zero_at_infty CuspForm.discriminant
    have hFinv : Tendsto (fun z : ℍ => (Fc z)⁻¹) atImInfty (𝓝 (1 : ℂ)⁻¹) :=
      htends.inv₀ one_ne_zero
    have h1 : ((⇑CuspForm.discriminant : ℍ → ℂ)) =O[atImInfty] (fun _ => (1 : ℝ)) :=
      hΔ0.boundedAtFilter
    have h2 : (fun z : ℍ => (Fc z)⁻¹) =O[atImInfty] (fun _ => (1 : ℝ)) :=
      hFinv.isBigO_one ℝ
    have h3 : hfn = fun z => CuspForm.discriminant z * (Fc z)⁻¹ := by
      funext z
      rw [hhdef, Pi.div_apply, div_eq_mul_inv]
    rw [IsBoundedAtImInfty, BoundedAtFilter, h3, Pi.one_def]
    simpa only [one_mul] using h1.mul h2
  have hbd' : IsBoundedAtImInfty (hfn * ⇑CuspForm.discriminant ^ 0) := by
    rw [show hfn * ⇑CuspForm.discriminant ^ 0 = hfn from by funext z; simp]
    exact hbd
  obtain ⟨c', hc'⟩ := ModularFormClass.levelOne_weight_zero_const
    (ModularForm.mcast (by norm_num) (holMulDiscPow 0 hfn hol hinv hbd') : ModularForm 𝒮ℒ 0)
  have hconst : ∀ z : ℍ, CuspForm.discriminant z / Fc z = c' := by
    intro z
    have := congrFun hc' z
    rw [show (ModularForm.mcast (by norm_num) (holMulDiscPow 0 hfn hol hinv hbd') :
        ModularForm 𝒮ℒ 0) z = (hfn * ⇑CuspForm.discriminant ^ 0) z from rfl] at this
    simpa [hhdef] using this
  have hΔI : CuspForm.discriminant UpperHalfPlane.I ≠ 0 := by
    rw [congrFun CuspForm.coe_discriminant UpperHalfPlane.I]
    exact ModularForm.discriminant_ne_zero _
  have hc'0 : c' ≠ 0 := by
    intro h0
    rw [h0] at hconst
    exact hΔI (by
      have := hconst UpperHalfPlane.I
      rwa [div_eq_zero_iff, or_iff_left (hnv UpperHalfPlane.I)] at this)
  have hFceq : (⇑Fc : ℍ → ℂ) = c'⁻¹ • ⇑CuspForm.discriminant := by
    funext z
    have := hconst z
    rw [div_eq_iff (hnv z)] at this
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp [hc'0]
    linear_combination -this
  have hcontra : (qExpansion 1 Fc).coeff 0 = 0 := by
    rw [hFceq, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero
        CuspForm.discriminant one_pos one_mem_strictPeriods_SL) c'⁻¹,
      PowerSeries.coeff_smul, CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant
        one_pos one_mem_strictPeriods_SL]
    simp
  rw [hF0] at hcontra
  exact one_ne_zero hcontra

end A4_j_surjective

section R2WidthCopy

open UpperHalfPlane
open ModularForm
open ModularFormClass
open CuspForm
open ModularForm.CuspForm
open Polynomial
open Real.Polynomial
open Filter
open scoped Manifold MatrixGroups

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

end R2WidthCopy

section C6_width

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
end C6_width

section BoundedFurniture

open UpperHalfPlane
open ModularForm
open FrickeFunctions.LevelOneHauptmodul.Aux.ModularFormClass
open CuspForm
open ModularForm.CuspForm
open Polynomial
open Real.Polynomial
open Filter
open scoped Manifold MatrixGroups

private def PoleBounded (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ ∃ m : ℕ, IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m)

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

end BoundedFurniture

section A3K

open UpperHalfPlane
open ModularForm
open FrickeFunctions.LevelOneHauptmodul.Aux.ModularFormClass
open CuspForm
open ModularForm.CuspForm
open EisensteinSeries
open scoped MatrixGroups

variable (k : Subfield ℂ)

private lemma kCoeff_mul {p q : PowerSeries ℂ} (hp : ∀ n : ℕ, p.coeff n ∈ k)
    (hq : ∀ n : ℕ, q.coeff n ∈ k) : ∀ n : ℕ, (p * q).coeff n ∈ k := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun ij _ => mul_mem (hp ij.1) (hq ij.2)

private lemma kCoeff_pow {p : PowerSeries ℂ} (hp : ∀ n : ℕ, p.coeff n ∈ k) (m : ℕ) :
    ∀ n : ℕ, (p ^ m).coeff n ∈ k := by
  induction m with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split <;> simp [one_mem, zero_mem]
  | succ m ih =>
    rw [pow_succ]
    exact kCoeff_mul k ih hp

private lemma kCoeff_of_rat {p : PowerSeries ℂ} (hp : ∀ n : ℕ, ∃ q : ℚ, p.coeff n = (q : ℂ)) :
    ∀ n : ℕ, p.coeff n ∈ k := by
  intro n
  obtain ⟨q, hq⟩ := hp n
  rw [hq]
  exact SubfieldClass.ratCast_mem k q

private lemma kCoeff_E4 : ∀ n : ℕ, (qExpansion 1 E₄).coeff n ∈ k :=
  kCoeff_of_rat k (ratCoeff_E (by norm_num) (by decide))

private lemma kCoeff_discriminant : ∀ n : ℕ, (qExpansion 1 ModularForm.discriminant).coeff n ∈ k :=
  kCoeff_of_rat k ratCoeff_discriminant

private lemma triangular_aux_mem (m : ℕ) :
    ∀ d : ℕ, d ≤ m → ∀ c : ℕ → ℂ,
      (∀ n : ℕ, (∑ i ∈ Finset.range (d + 1),
        PowerSeries.C (c i) * (qExpansion 1 E₄) ^ (3 * i) *
          (qExpansion 1 ModularForm.discriminant) ^ (m - i)).coeff n ∈ k) →
      ∀ i : ℕ, i ≤ d → c i ∈ k := by
  intro d
  induction d with
  | zero =>
    intro _ c hser i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    have hq := hser m
    rwa [Finset.sum_range_one, Nat.mul_zero, pow_zero, mul_one, Nat.sub_zero,
      coeff_mul_pow_at_order discriminant_qExpansion_coeff_zero,
      ModularForm.discriminant_qExpansion_coeff_one, one_pow, mul_one,
      PowerSeries.coeff_zero_C] at hq
  | succ d ihd =>
    intro hd1 c hser
    have htop : c (d + 1) ∈ k := by
      have hq := hser (m - (d + 1))
      rw [Finset.sum_range_succ, map_add] at hq
      have hlow : (∑ i ∈ Finset.range (d + 1),
          PowerSeries.C (c i) * (qExpansion 1 E₄) ^ (3 * i) *
            (qExpansion 1 ModularForm.discriminant) ^ (m - i)).coeff (m - (d + 1)) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun i hi' => ?_
        rw [Finset.mem_range] at hi'
        exact coeff_mul_pow_eq_zero_of_lt discriminant_qExpansion_coeff_zero (by omega)
      rwa [hlow, zero_add, coeff_mul_pow_at_order discriminant_qExpansion_coeff_zero,
        ModularForm.discriminant_qExpansion_coeff_one, one_pow, mul_one,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff,
        E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩, one_pow, mul_one] at hq
    intro i hi
    rcases Nat.lt_or_ge i (d + 1) with hil | hig
    · refine ihd (by omega) c (fun n => ?_) i (by omega)
      have hq := hser n
      have hterm : (PowerSeries.C (c (d + 1)) *
          (qExpansion 1 E₄) ^ (3 * (d + 1)) *
          (qExpansion 1 ModularForm.discriminant) ^ (m - (d + 1))).coeff n ∈ k := by
        refine kCoeff_mul k (kCoeff_mul k ?_ (kCoeff_pow k (kCoeff_E4 k) _))
          (kCoeff_pow k (kCoeff_discriminant k) _) n
        intro n'
        rw [PowerSeries.coeff_C]
        split
        · exact htop
        · exact zero_mem k
      rw [Finset.sum_range_succ, map_add] at hq
      have := sub_mem hq hterm
      rwa [add_sub_cancel_right] at this
    · obtain rfl : i = d + 1 := by omega
      exact htop

private theorem levelOne_qexp_principle_mem (m : ℕ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ m)
    (hrat : ∀ n : ℕ, (polyDiscSeries m P).coeff n ∈ k) :
    ∀ i : ℕ, P.coeff i ∈ k := by
  intro i
  rcases Nat.lt_or_ge m i with him | him
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact zero_mem k
  · refine triangular_aux_mem k m m le_rfl (fun i => P.coeff i) (fun n => ?_) i him
    simpa [polyDiscSeries] using hrat n

end A3K

section KBridge

open UpperHalfPlane
open ModularForm
open FrickeFunctions.LevelOneHauptmodul.Aux.ModularFormClass
open CuspForm
open ModularForm.CuspForm
open Polynomial
open Real.Polynomial
open scoped MatrixGroups

private noncomputable def polyDiscForm (m : ℕ) (P : Polynomial ℂ) : ModularForm 𝒮ℒ (12 * m) :=
  ∑ i ∈ (Finset.range (m + 1)).attach,
    P.coeff i.1 • ModularForm.mcast
      (by
        have hi := Finset.mem_range.mp i.2
        rw [Nat.cast_sub (by omega : i.1 ≤ m)]
        push_cast
        ring)
      ((E₄.pow (3 * i.1)).mul (discPowForm (m - i.1)))

private lemma polyDiscForm_term_apply {m i : ℕ} (c : ℂ)
    (h : ((3 * i : ℕ) : ℤ) * 4 + 12 * ((m - i : ℕ) : ℤ) = 12 * (m : ℤ)) (τ : ℍ) :
    (c • ModularForm.mcast h ((E₄.pow (3 * i)).mul (discPowForm (m - i)))) τ =
      c * (E₄ τ ^ (3 * i) * CuspForm.discriminant τ ^ (m - i)) := by
  rw [smul_apply, smul_eq_mul,
    congrFun (ModularForm.coe_mcast h _) τ,
    congrFun (ModularForm.coe_mul _ _) τ, Pi.mul_apply,
    congrFun (ModularForm.coe_pow E₄ (3 * i)) τ, Pi.pow_apply,
    congrFun (discPowForm_coe (m - i)) τ, Pi.pow_apply]

private lemma polyDiscForm_coe {m : ℕ} {P : Polynomial ℂ} (hdeg : P.natDegree ≤ m) :
    ⇑(polyDiscForm m P) =
      (fun τ : ℍ => Polynomial.eval (j τ) P) * ⇑CuspForm.discriminant ^ m := by
  funext τ
  have hΔ0 : CuspForm.discriminant τ ≠ 0 := by
    rw [congrFun CuspForm.coe_discriminant τ]
    exact ModularForm.discriminant_ne_zero τ
  have hsum : (polyDiscForm m P) τ = ∑ i ∈ (Finset.range (m + 1)).attach,
      P.coeff i.1 * (E₄ τ ^ (3 * i.1) * CuspForm.discriminant τ ^ (m - i.1)) := by
    rw [polyDiscForm, ← FunLike.coeAddMonoidHom_apply (F := ModularForm 𝒮ℒ (12 * m)), map_sum]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => polyDiscForm_term_apply _ _ τ
  rw [hsum, Pi.mul_apply, Pi.pow_apply]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_mul,
    Finset.sum_attach (Finset.range (m + 1))
      (fun i => P.coeff i * (E₄ τ ^ (3 * i) * CuspForm.discriminant τ ^ (m - i)))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have him : i ≤ m := by
    rw [Finset.mem_range] at hi
    omega
  have hj : j τ = E₄ τ ^ 3 / CuspForm.discriminant τ := by
    rw [j, congrFun CuspForm.coe_discriminant τ]
  rw [hj, div_pow, ← pow_mul, mul_comm 3 i,
    show CuspForm.discriminant τ ^ m = CuspForm.discriminant τ ^ i *
      CuspForm.discriminant τ ^ (m - i) from by rw [← pow_add, Nat.add_sub_cancel' him]]
  have hcancel : E₄ τ ^ (i * 3) / CuspForm.discriminant τ ^ i *
      (CuspForm.discriminant τ ^ i * CuspForm.discriminant τ ^ (m - i)) =
      E₄ τ ^ (i * 3) * CuspForm.discriminant τ ^ (m - i) := by
    rw [div_mul_eq_mul_div, mul_comm (CuspForm.discriminant τ ^ i) _, ← mul_assoc,
      mul_div_assoc, div_self (pow_ne_zero i hΔ0), mul_one]
  rw [mul_assoc, hcancel]

private lemma qExpansion_finset_sum {ι : Type*} (s : Finset ι) {w : ℤ}
    (f : ι → ModularForm 𝒮ℒ w) :
    qExpansion 1 ((∑ i ∈ s, f i : ModularForm 𝒮ℒ w)) = ∑ i ∈ s, qExpansion 1 (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using qExpansion_zero 1
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, ← ih]
    exact ModularForm.qExpansion_add one_pos one_mem_strictPeriods_SL (f a) (∑ i ∈ s, f i)

private theorem qExpansion_polyDiscForm (m : ℕ) (P : Polynomial ℂ) :
    qExpansion 1 (polyDiscForm m P) = polyDiscSeries m P := by
  rw [polyDiscForm, qExpansion_finset_sum, polyDiscSeries,
    ← Finset.sum_attach (Finset.range (m + 1))
      (fun i => PowerSeries.C (P.coeff i) * (qExpansion 1 E₄) ^ (3 * i) *
        (qExpansion 1 ModularForm.discriminant) ^ (m - i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hdisc : qExpansion 1 (discPowForm (m - i.1)) =
      (qExpansion 1 ModularForm.discriminant) ^ (m - i.1) := by
    rw [discPowForm, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
    have hco : (⇑(CuspForm.toModularFormₗ CuspForm.discriminant) : ℍ → ℂ) =
        ModularForm.discriminant := by
      funext z
      rw [CuspForm.toModularFormₗ_apply]
      exact congrFun CuspForm.coe_discriminant z
    rw [hco]
  rw [hdisc]
  ext n
  rw [PowerSeries.coeff_smul, smul_eq_mul, mul_assoc, PowerSeries.coeff_C_mul]

end KBridge

section KPoleSec

open UpperHalfPlane
open ModularForm
open FrickeFunctions.LevelOneHauptmodul.Aux.ModularFormClass
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

private lemma qExpansion_one_discPow (k : ℕ) :
    qExpansion 1 (⇑CuspForm.discriminant ^ k : ℍ → ℂ) =
      (qExpansion 1 ModularForm.discriminant) ^ k := by
  rw [← discPowForm_coe]
  exact qExpansion_one_discPowForm k

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
    exact const_boundedAtFilter _ _
  refine ⟨mdifferentiable_const, 0, ?_, ?_, ?_⟩
  · rw [hshape]
    intro x
    rfl
  · rw [hshape]
    have hc : ((c : ℂ) • (1 : ℍ → ℂ)) = fun _ : ℍ => (c : ℂ) := by
      funext τ
      simp
    rw [hc]
    exact const_boundedAtFilter _ _
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

private lemma KPole.add {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ} (hf : KPole K N f)
    (hg : KPole K N g) : KPole K N (f + g) := by
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

private lemma KPole.mul {K : IntermediateField ℚ ℂ} [NeZero N] {f g : ℍ → ℂ} (hf : KPole K N f)
    (hg : KPole K N g) : KPole K N (f * g) := by
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

private theorem kPole_invariant_eq_polynomial_j_mem {K : IntermediateField ℚ ℂ} [NeZero N]
    {a : ℍ → ℂ} (hk : KPole K N a) (hinv : ∀ γ : SL(2, ℤ), a ∣[(0 : ℤ)] γ = a) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ K) ∧ a = fun τ => Polynomial.eval (j τ) P := by
  obtain ⟨hhol, m, hper, hbd, hmem⟩ := hk
  obtain ⟨P, hdeg, hP⟩ := levelOne_holFn_eq_polynomial_j m a hhol hinv hbd
  have hfn : (a * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) = ⇑(polyDiscForm m P) := by
    rw [hP]
    exact (polyDiscForm_coe hdeg).symm
  have h1 : ∀ n, (qExpansion 1 (polyDiscForm m P)).coeff n ∈ K := by
    intro n
    have hw := qExpansion_coeff_width (⇑(polyDiscForm m P) : ℍ → ℂ) (NeZero.ne N)
      (SlashInvariantFormClass.periodic_comp_ofComplex _ one_mem_strictPeriods_SL)
      (polyDiscForm m P).holo' (ModularFormClass.bdd_at_infty _) (N * n)
    rw [ite_eq_left ⟨n, rfl⟩, Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero (NeZero.ne N))] at hw
    rw [← hw]
    have hm := hmem (N * n)
    rwa [hfn] at hm
  refine ⟨P, fun i => ?_, hP⟩
  have hmem1 := levelOne_qexp_principle_mem K.toSubfield m P hdeg (fun n => by
    rw [← qExpansion_polyDiscForm]
    exact h1 n) i
  exact hmem1

end KPoleSec

end Aux

section R3Bridge

open FrickeFunctions.LevelOneHauptmodul.Aux
open Polynomial
open Real.Polynomial
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

open Aux in
/-- Level-one Hauptmodul: a holomorphic `SL(2, ℤ)`-invariant `h` with `h Δ ^ m` bounded at `i∞` is
`P (j τ)` for a polynomial `P` of degree at most `m`, whose coefficients lie in `K` when the
width-`N` q-coefficients of `h Δ ^ m` lie in `K`; `j` is surjective onto `ℂ`; and if the
q-coefficients of `∑_{i ≤ m} P_i E₄ ^ (3i) Δ ^ (m - i)` are rational (respectively lie in `K`),
so are the coefficients of `P`. -/
public theorem _root_.ModularForm.levelOne_hauptmodul_package :
    (∀ (m : ℕ) (h : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
      (∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) →
      IsBoundedAtImInfty (h * ModularForm.discriminant ^ m) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
        h = fun τ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P) ∧
    (∀ (k : IntermediateField ℚ ℂ) (N : ℕ), N ≠ 0 → ∀ (m : ℕ) (h : ℍ → ℂ),
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h →
      (∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h) →
      Function.Periodic ((h * ModularForm.discriminant ^ m) ∘ ofComplex) N →
      IsBoundedAtImInfty (h * ModularForm.discriminant ^ m) →
      (∀ n : ℕ, (qExpansion N (h * ModularForm.discriminant ^ m)).coeff n ∈ k) →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ (∀ i, P.coeff i ∈ k) ∧
        h = fun τ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P) ∧
    Function.Surjective (fun τ : ℍ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) ∧
    (∀ (m : ℕ) (P : Polynomial ℂ), P.natDegree ≤ m →
      (∀ n : ℕ, ∃ q : ℚ, (∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (P.coeff i) * qExpansion 1 ⇑ModularForm.E₄ ^ (3 * i) *
            qExpansion 1 ModularForm.discriminant ^ (m - i)).coeff n = (q : ℂ)) →
      ∀ i : ℕ, ∃ q : ℚ, P.coeff i = (q : ℂ)) ∧
    (∀ (k : IntermediateField ℚ ℂ) (m : ℕ) (P : Polynomial ℂ), P.natDegree ≤ m →
      (∀ n : ℕ, (∑ i ∈ Finset.range (m + 1),
          PowerSeries.C (P.coeff i) * qExpansion 1 ⇑ModularForm.E₄ ^ (3 * i) *
            qExpansion 1 ModularForm.discriminant ^ (m - i)).coeff n ∈ k) →
      ∀ i : ℕ, P.coeff i ∈ k) := by
  have hdisc : (ModularForm.discriminant : ℍ → ℂ) = ⇑CuspForm.discriminant :=
    CuspForm.coe_discriminant.symm
  refine ⟨?_, ?_, j_surjective, ?_, ?_⟩
  · intro m h hol hinv hbd
    rw [hdisc] at hbd
    exact levelOne_holFn_eq_polynomial_j m h hol hinv hbd
  · intro k N hN m h hol hinv hper hbd hmem
    have : NeZero N := ⟨hN⟩
    rw [hdisc] at hper hbd hmem
    obtain ⟨P, hdeg, hP⟩ := levelOne_holFn_eq_polynomial_j m h hol hinv hbd
    obtain ⟨P', hP'k, hP'⟩ := kPole_invariant_eq_polynomial_j_mem
      (K := k) ⟨hol, m, hper, hbd, hmem⟩ hinv
    have hPP' : P = P' := by
      apply Polynomial.funext
      intro c
      obtain ⟨τ, rfl⟩ := j_surjective c
      have h1 := congrFun hP τ
      have h2 := congrFun hP' τ
      rw [← h1, h2]
    exact ⟨P, hdeg, hPP' ▸ hP'k, hP⟩
  · intro m P hdeg hrat
    exact levelOne_qexp_principle m P hdeg (by simpa [polyDiscSeries] using hrat)
  · intro k m P hdeg hmem
    exact levelOne_qexp_principle_mem k.toSubfield m P hdeg
      (by simpa [polyDiscSeries] using hmem)

end R3Bridge

end

end LevelOneHauptmodul

end FrickeFunctions
