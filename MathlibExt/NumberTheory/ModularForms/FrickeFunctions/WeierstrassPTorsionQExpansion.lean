/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularForm_weierstrassP_torsion_qExpansion_package.lean`
and
`P2M/Sol/S_ModularForm_weierstrassP_torsion_qExpansion_package.lean`
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
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.RingTheory.RootsOfUnity.Complex
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.WeierstrassPQExpansion

/-!
# Rationality of torsion values of the Weierstrass function

This file studies the torsion values of the Weierstrass function as functions of `τ`: their
holomorphy, periodicity, injectivity and the Galois action on their q-expansions.

## Main statement

* `ModularForm.weierstrassP_torsion_qExpansion_package`
-/
namespace FrickeFunctions.WeierstrassPTorsionQExpansion

noncomputable section

open Complex Real

namespace AuxR2

section Floor
open scoped UpperHalfPlane Manifold
open PeriodPair

private def periodPairOfTau (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := LinearIndependent.pair_iff.mpr fun s t hst ↦ by
    have him : s * (τ : ℂ).im = 0 := by
      have := congrArg Complex.im hst
      simpa [Complex.add_im, Complex.smul_im, smul_eq_mul] using this
    have hs : s = 0 :=
      (mul_eq_zero.mp him).resolve_right (UpperHalfPlane.coe_im τ ▸ τ.im_ne_zero)
    subst hs
    simpa using hst

@[scoped simp] private lemma periodPairOfTau_ω₁ (τ : ℍ) : (periodPairOfTau τ).ω₁ = (τ : ℂ) := rfl
@[scoped simp] private lemma periodPairOfTau_ω₂ (τ : ℍ) : (periodPairOfTau τ).ω₂ = 1 := rfl

private def zetaN (N : ℕ) : ℂ := cexp (2 * π * I / N)

private def qN (N : ℕ) (τ : ℂ) : ℂ := cexp (2 * π * I * τ / N)

private lemma zetaN_ne_zero (N : ℕ) : zetaN N ≠ 0 := Complex.exp_ne_zero _
private lemma qN_ne_zero (N : ℕ) (τ : ℂ) : qN N τ ≠ 0 := Complex.exp_ne_zero _

private lemma qN_pow_self {N : ℕ} (hN : N ≠ 0) (τ : ℂ) : qN N τ ^ N = cexp (2 * π * I * τ) := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [qN, ← Complex.exp_nat_mul]
  congr 1
  field_simp

private lemma cexp_two_pi_I_mul_torsionPt {N : ℕ} (hN : N ≠ 0) (a₁ a₂ : ℕ) (τ : ℂ) :
    cexp (2 * π * I * ((a₁ * τ + a₂) / N)) = zetaN N ^ a₂ * qN N τ ^ a₁ := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [zetaN, qN, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  field_simp
  ring

private lemma norm_qN (N : ℕ) (τ : ℂ) : ‖qN N τ‖ = Real.exp (-(2 * π * τ.im / N)) := by
  rw [qN, Complex.norm_exp]
  congr 1
  rw [show 2 * (π : ℂ) * I * τ / N = (2 * π * I * τ) / (N : ℕ) from rfl, Complex.div_natCast_re]
  simp [mul_comm]
  ring

private lemma norm_zetaN (N : ℕ) : ‖zetaN N‖ = 1 := by
  rw [zetaN, Complex.norm_exp, show 2 * (π : ℂ) * I / N = (2 * π * I) / (N : ℕ) from rfl,
    Complex.div_natCast_re]
  simp

private lemma norm_qN_le_one (N : ℕ) {τ : ℂ} (hτ : 0 ≤ τ.im) : ‖qN N τ‖ ≤ 1 := by
  rw [norm_qN, Real.exp_le_one_iff, neg_nonpos]
  positivity

private lemma norm_qN_lt_one {N : ℕ} (hN : 0 < N) {τ : ℂ} (hτ : 0 < τ.im) : ‖qN N τ‖ < 1 := by
  rw [norm_qN, Real.exp_lt_one_iff, neg_lt_zero]
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

private lemma norm_qN_le_of_le_im (N : ℕ) {B : ℝ} {τ : ℂ} (hτ : B ≤ τ.im) :
    ‖qN N τ‖ ≤ Real.exp (-(2 * π * B / N)) := by
  rw [norm_qN, Real.exp_le_exp, neg_le_neg_iff]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · simp [hN]
  · have : (0 : ℝ) < N := by exact_mod_cast hN
    gcongr

private def wpTail (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℂ) : ℂ :=
  ((p.2 : ℕ) : ℂ) *
    (zetaN N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
        2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ)))

private lemma norm_wpTail_le {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) (p : ℕ+ × ℕ+) {τ : ℂ} (hτ : 0
    ≤ τ.im) :
    ‖wpTail N a₁ a₂ p τ‖ ≤ 4 * ((p.2 : ℕ) * ‖qN N τ‖ ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  obtain ⟨c, m⟩ := p
  have hq1 := norm_qN_le_one N hτ
  have hcN : (c : ℕ) ≤ (c : ℕ) * N - a₁ := by
    have h1 : (c : ℕ) * (a₁ + 1) ≤ (c : ℕ) * N := Nat.mul_le_mul_left _ ha₁
    have h2 : a₁ ≤ (c : ℕ) * a₁ := Nat.le_mul_of_pos_left _ c.pos
    rw [mul_add, mul_one] at h1
    omega
  have e1 : (c : ℕ) * (m : ℕ) ≤ ((c : ℕ) * N + a₁) * (m : ℕ) :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have e2 : (c : ℕ) * (m : ℕ) ≤ ((c : ℕ) * N - a₁) * (m : ℕ) := Nat.mul_le_mul_right _ hcN
  have e3 : (c : ℕ) * (m : ℕ) ≤ (c : ℕ) * N * (m : ℕ) := Nat.mul_le_mul_right _ (by nlinarith)
  have b1 : ‖qN N τ‖ ^ (((c : ℕ) * N + a₁) * (m : ℕ)) ≤ ‖qN N τ‖ ^ ((c : ℕ) * (m : ℕ)) :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 e1
  have b2 : ‖qN N τ‖ ^ (((c : ℕ) * N - a₁) * (m : ℕ)) ≤ ‖qN N τ‖ ^ ((c : ℕ) * (m : ℕ)) :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 e2
  have b3 : ‖qN N τ‖ ^ ((c : ℕ) * N * (m : ℕ)) ≤ ‖qN N τ‖ ^ ((c : ℕ) * (m : ℕ)) :=
    pow_le_pow_of_le_one (norm_nonneg _) hq1 e3
  have hz : ‖zetaN N‖ = 1 := norm_zetaN N
  set ρ : ℝ := ‖qN N τ‖ with hρ
  set A : ℂ := zetaN N ^ (a₂ * (m : ℕ)) * qN N τ ^ (((c : ℕ) * N + a₁) * (m : ℕ)) with hAdef
  set B : ℂ := (zetaN N)⁻¹ ^ (a₂ * (m : ℕ)) * qN N τ ^ (((c : ℕ) * N - a₁) * (m : ℕ)) with hBdef
  set C : ℂ := qN N τ ^ ((c : ℕ) * N * (m : ℕ)) with hCdef
  have hA : ‖A‖ ≤ ρ ^ ((c : ℕ) * (m : ℕ)) := by
    rw [hAdef, norm_mul, norm_pow, hz, one_pow, one_mul, norm_pow]; exact b1
  have hB : ‖B‖ ≤ ρ ^ ((c : ℕ) * (m : ℕ)) := by
    rw [hBdef, norm_mul, norm_pow, norm_inv, hz, inv_one, one_pow, one_mul, norm_pow]; exact b2
  have hC : ‖(2 : ℂ) * C‖ ≤ 2 * ρ ^ ((c : ℕ) * (m : ℕ)) := by
    rw [norm_mul, Complex.norm_ofNat, hCdef, norm_pow]; linarith
  have hst : ‖A + B - 2 * C‖ ≤ 4 * ρ ^ ((c : ℕ) * (m : ℕ)) := by
    linarith [norm_sub_le (A + B) (2 * C), norm_add_le A B]
  change ‖((m : ℕ) : ℂ) * (A + B - 2 * C)‖ ≤ 4 * ((m : ℕ) * ρ ^ ((c : ℕ) * (m : ℕ)))
  rw [norm_mul, Complex.norm_natCast]
  calc ((m : ℕ) : ℝ) * ‖A + B - 2 * C‖ ≤ (m : ℕ) * (4 * ρ ^ ((c : ℕ) * (m : ℕ))) := by gcongr
    _ = 4 * ((m : ℕ) * ρ ^ ((c : ℕ) * (m : ℕ))) := by ring

private lemma summable_wpTail_majorant {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun p : ℕ+ × ℕ+ ↦ 4 * ((p.2 : ℕ) * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  have h := summable_prod_mul_pow 1 (r := r) (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
  refine (h.mul_left 4).congr fun p ↦ ?_
  simp

private def wpTorsion (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ :=
  PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N)

private def wpTorsionSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  (2 * π * I) ^ 2 *
    (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
      ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ)

end Floor

section R1_glue

open scoped UpperHalfPlane Manifold
open PeriodPair

private lemma periodPair_eq_of_ω (L L' : PeriodPair) (h1 : L.ω₁ = L'.ω₁) (h2 : L.ω₂ = L'.ω₂) :
    L = L' := by
  rcases L with ⟨_, _, _⟩; rcases L' with ⟨_, _, _⟩
  simp only [PeriodPair.mk.injEq]; exact ⟨h1, h2⟩

private lemma L_eq_periodPairOfTau (L : ℍ → PeriodPair)
    (hL : ∀ τ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) : L = periodPairOfTau :=
  funext fun τ ↦ periodPair_eq_of_ω _ _ (hL τ).1 (hL τ).2

private lemma hL_ppT : ∀ τ : ℍ, (periodPairOfTau τ).ω₁ = (τ : ℂ) ∧ (periodPairOfTau τ).ω₂ = 1 :=
  fun _ ↦ ⟨rfl, rfl⟩

private lemma wpTorsion_eq_wpTorsionSeries {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (τ : ℍ) :
    wpTorsion N a₁ a₂ τ = wpTorsionSeries N a₁ a₂ τ :=
  (ModularForm.weierstrassP_qExpansion_package.2.2.2.1 periodPairOfTau hL_ppT N a₁ a₂ ha₁ ha₂ h0).1
      τ

private theorem mdifferentiable_wpTorsion {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpTorsion N a₁ a₂) :=
  (ModularForm.weierstrassP_qExpansion_package.2.2.2.1 periodPairOfTau hL_ppT N a₁ a₂ ha₁ ha₂ h0).2

end R1_glue

section RatGen
open UpperHalfPlane hiding I
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

end RatGen

section B4_qexp

open scoped UpperHalfPlane Manifold
open UpperHalfPlane hiding I

private def kN (N : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zetaN N}

private lemma zetaN_mem_kN (N : ℕ) : zetaN N ∈ kN N :=
  IntermediateField.mem_adjoin_simple_self ℚ _

private lemma zetaN_pow_mem_kN (N k : ℕ) : zetaN N ^ k ∈ kN N := pow_mem (zetaN_mem_kN N) k

private lemma zetaN_inv_pow_mem_kN (N k : ℕ) : (zetaN N)⁻¹ ^ k ∈ kN N :=
  pow_mem (inv_mem (zetaN_mem_kN N)) k

private lemma natCast_mem_kN (N m : ℕ) : (m : ℂ) ∈ kN N := natCast_mem _ m

private lemma one_div_twelve_mem_kN (N : ℕ) : (1 / 12 : ℂ) ∈ kN N :=
  div_mem (one_mem _) (by exact_mod_cast natCast_mem_kN N 12)

private def wpNormSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
    ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ

private lemma wpTorsionSeries_eq (N a₁ a₂ : ℕ) (τ : ℂ) :
    wpTorsionSeries N a₁ a₂ τ = (2 * π * I) ^ 2 * wpNormSeries N a₁ a₂ τ := rfl

private def wpNorm (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ := ((2 * π * I) ^ 2)⁻¹ * wpTorsion N a₁ a₂ τ

private lemma wpNorm_eq {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (τ : ℍ) :
    wpNorm N a₁ a₂ τ = wpNormSeries N a₁ a₂ τ := by
  rw [wpNorm, wpTorsion_eq_wpTorsionSeries ha₁ ha₂ h0, wpTorsionSeries_eq,
    inv_mul_cancel_left₀ (pow_ne_zero 2 Complex.two_pi_I_ne_zero)]

private lemma qN_add_natCast (N : ℕ) (hN : N ≠ 0) (τ : ℂ) : qN N (τ + N) = qN N τ := by
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [qN, qN, mul_add, add_div, Complex.exp_add, mul_div_cancel_right₀ _ this,
    Complex.exp_two_pi_mul_I, mul_one]

private lemma wpTail_add_natCast {N : ℕ} (hN : N ≠ 0) (a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℂ) :
    wpTail N a₁ a₂ p (τ + N) = wpTail N a₁ a₂ p τ := by
  simp only [wpTail, qN_add_natCast N hN]

private lemma wpNormSeries_add_natCast {N : ℕ} (hN : N ≠ 0) (a₁ a₂ : ℕ) (τ : ℂ) :
    wpNormSeries N a₁ a₂ (τ + N) = wpNormSeries N a₁ a₂ τ := by
  simp only [wpNormSeries, qN_add_natCast N hN, wpTail_add_natCast hN]

private theorem periodic_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    Function.Periodic (wpNorm N a₁ a₂ ∘ ofComplex) N := by
  have hN : N ≠ 0 := by omega
  intro τ
  simp only [Function.comp_apply]
  rcases le_or_gt τ.im 0 with hτ | hτ
  · rw [ofComplex_apply_eq_of_im_nonpos (by simpa using hτ) hτ]
  · have hτ' : 0 < (τ + N).im := by simpa using hτ
    rw [ofComplex_apply_of_im_pos hτ', ofComplex_apply_of_im_pos hτ, wpNorm_eq ha₁ ha₂ h0,
      wpNorm_eq ha₁ ha₂ h0]
    push_cast
    exact wpNormSeries_add_natCast hN a₁ a₂ τ

private theorem mdifferentiable_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpNorm N a₁ a₂) :=
  (mdifferentiable_wpTorsion ha₁ ha₂ h0).const_smul ((2 * π * I) ^ 2)⁻¹

private lemma norm_wpNormSeries_le {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) :
    ∃ M : ℝ, ∀ τ : ℂ, 1 ≤ τ.im → ‖wpNormSeries N a₁ a₂ τ‖ ≤ M := by
  have hN : 0 < N := by omega
  set ρ : ℝ := Real.exp (-(2 * π * 1 / N)) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    rw [hρ, Real.exp_lt_one_iff, neg_lt_zero]
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  obtain ⟨T, hT⟩ := summable_wpTail_majorant hρ0 hρ1
  set K : ℂ := zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 with hK
  refine ⟨‖K‖ + 1 / (1 - ρ) ^ 2 + ‖(1 / 12 : ℂ)‖ + T, fun τ hτ ↦ ?_⟩
  have hq : ‖qN N τ‖ ≤ ρ := norm_qN_le_of_le_im N hτ
  have hqa : ‖zetaN N ^ a₂ * qN N τ ^ a₁‖ ≤ ρ ^ a₁ := by
    rw [norm_mul, norm_pow, norm_zetaN, one_pow, one_mul, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hq a₁
  have hhead : ‖zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2‖ ≤
      ‖K‖ + 1 / (1 - ρ) ^ 2 := by
    have hKn : 0 ≤ ‖K‖ := norm_nonneg _
    have hρn : (0 : ℝ) ≤ 1 / (1 - ρ) ^ 2 := by positivity
    rcases Nat.eq_zero_or_pos a₁ with ha | ha
    · subst ha
      simp only [pow_zero, mul_one, ← hK]
      linarith
    · set r := zetaN N ^ a₂ * qN N τ ^ a₁ with hr
      have hr1 : ‖r‖ ≤ ρ := hqa.trans (pow_le_of_le_one hρ0 hρ1.le ha.ne')
      have h1r : 1 - ρ ≤ ‖1 - r‖ := by
        have := norm_sub_norm_le (1 : ℂ) r
        rw [norm_one] at this
        linarith
      have hpos : 0 < 1 - ρ := by linarith
      have : ‖r / (1 - r) ^ 2‖ ≤ 1 / (1 - ρ) ^ 2 := by
        rw [norm_div, norm_pow]
        have hr' : ‖r‖ ≤ 1 := hr1.trans hρ1.le
        have hden : (1 - ρ) ^ 2 ≤ ‖1 - r‖ ^ 2 := pow_le_pow_left₀ hpos.le h1r 2
        have hden0 : 0 < ‖1 - r‖ ^ 2 := lt_of_lt_of_le (by positivity) hden
        rw [div_le_div_iff₀ hden0 (by positivity), one_mul]
        nlinarith [norm_nonneg r]
      linarith
  have htail : ‖∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ‖ ≤ T :=
    tsum_of_norm_bounded hT fun p ↦ (norm_wpTail_le ha₁ a₂ p (by linarith)).trans (by gcongr)
  unfold wpNormSeries
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  linarith

private theorem isBoundedAtImInfty_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : IsBoundedAtImInfty (wpNorm N a₁ a₂) := by
  obtain ⟨M, hM⟩ := norm_wpNormSeries_le ha₁ a₂
  rw [isBoundedAtImInfty_iff]
  exact ⟨M, 1, fun τ hτ ↦ by rw [wpNorm_eq ha₁ ha₂ h0]; exact hM τ hτ⟩

private abbrev WpIdx : Type := Unit ⊕ ℕ+ ⊕ ((ℕ+ × ℕ+) × Fin 3)

private def wpMonCoeff (N a₁ a₂ : ℕ) : WpIdx → ℂ
  | Sum.inl _ => 1 / 12 + if a₁ = 0 then zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 else 0
  | Sum.inr (Sum.inl m) => if a₁ = 0 then 0 else ((m : ℕ) : ℂ) * zetaN N ^ (a₂ * (m : ℕ))
  | Sum.inr (Sum.inr (p, i)) =>
      ![((p.2 : ℕ) : ℂ) * zetaN N ^ (a₂ * (p.2 : ℕ)),
        ((p.2 : ℕ) : ℂ) * (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)),
        -2 * ((p.2 : ℕ) : ℂ)] i

private def wpMonExp (N a₁ : ℕ) : WpIdx → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl m) => if a₁ = 0 then (m : ℕ) else a₁ * (m : ℕ)
  | Sum.inr (Sum.inr (p, i)) =>
      ![((p.1 : ℕ) * N + a₁) * (p.2 : ℕ), ((p.1 : ℕ) * N - a₁) * (p.2 : ℕ),
        (p.1 : ℕ) * N * (p.2 : ℕ)] i

private def wpQCoeff (N a₁ a₂ : ℕ) (n : ℕ) : ℂ :=
  ∑' i : (wpMonExp N a₁ ⁻¹' {n}), wpMonCoeff N a₁ a₂ i

private lemma wpMonCoeff_mem_kN (N a₁ a₂ : ℕ) (i : WpIdx) : wpMonCoeff N a₁ a₂ i ∈ kN N := by
  rcases i with u | m | ⟨p, i⟩
  · simp only [wpMonCoeff]
    split_ifs
    · exact add_mem (one_div_twelve_mem_kN N) (div_mem (zetaN_pow_mem_kN N _)
        (pow_mem (sub_mem (one_mem _) (zetaN_pow_mem_kN N _)) 2))
    · exact add_mem (one_div_twelve_mem_kN N) (zero_mem _)
  · simp only [wpMonCoeff]
    split_ifs
    · exact zero_mem _
    · exact mul_mem (natCast_mem_kN N _) (zetaN_pow_mem_kN N _)
  · simp only [wpMonCoeff]
    fin_cases i
    · exact mul_mem (natCast_mem_kN N _) (zetaN_pow_mem_kN N _)
    · exact mul_mem (natCast_mem_kN N _) (zetaN_inv_pow_mem_kN N _)
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      exact mul_mem (neg_mem (by exact_mod_cast natCast_mem_kN N 2)) (natCast_mem_kN N _)

private lemma le_mul_sub_of_lt {N a₁ : ℕ} (ha₁ : a₁ < N) (c : ℕ+) : (c : ℕ) ≤ (c : ℕ) * N - a₁ := by
  have h1 : (c : ℕ) * (a₁ + 1) ≤ (c : ℕ) * N := Nat.mul_le_mul_left _ ha₁
  have h2 : a₁ ≤ (c : ℕ) * a₁ := Nat.le_mul_of_pos_left _ c.pos
  rw [mul_add, mul_one] at h1
  omega

private lemma le_wpMonExp_tail {N a₁ : ℕ} (ha₁ : a₁ < N) (p : ℕ+ × ℕ+) (i : Fin 3) :
    (p.1 : ℕ) ≤ wpMonExp N a₁ (Sum.inr (Sum.inr (p, i))) ∧
      (p.2 : ℕ) ≤ wpMonExp N a₁ (Sum.inr (Sum.inr (p, i))) := by
  have hc := le_mul_sub_of_lt ha₁ p.1
  have hm : 1 ≤ (p.2 : ℕ) := p.2.pos
  have hc1 : 1 ≤ (p.1 : ℕ) := p.1.pos
  have key : ∀ A : ℕ, (p.1 : ℕ) ≤ A → (p.1 : ℕ) ≤ A * (p.2 : ℕ) ∧ (p.2 : ℕ) ≤ A * (p.2 : ℕ) :=
    fun A hA ↦ ⟨hA.trans (Nat.le_mul_of_pos_right _ p.2.pos),
      Nat.le_mul_of_pos_left _ (lt_of_lt_of_le p.1.pos hA)⟩
  have hN : 0 < N := by omega
  fin_cases i
  · exact key _ (le_add_right (Nat.le_mul_of_pos_right _ hN))
  · exact key _ hc
  · exact key _ (Nat.le_mul_of_pos_right _ hN)

private lemma finite_wpMonExp_fiber {N a₁ : ℕ} (ha₁ : a₁ < N) (n : ℕ) :
    (wpMonExp N a₁ ⁻¹' {n}).Finite := by
  classical
  let φ : Unit ⊕ Fin (n + 1) ⊕ ((Fin (n + 1) × Fin (n + 1)) × Fin 3) → WpIdx :=
    Sum.map id (Sum.map (fun k ↦ Nat.toPNat' k)
      (Prod.map (Prod.map (fun k ↦ Nat.toPNat' k) (fun k ↦ Nat.toPNat' k)) id))
  refine (Set.finite_range φ).subset ?_
  rintro (u | m | ⟨⟨c, m⟩, i⟩) hi <;>
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi
  · exact ⟨Sum.inl u, rfl⟩
  · have hm : (m : ℕ) ≤ n := by
      simp only [wpMonExp] at hi
      split_ifs at hi with h
      · omega
      · have : 1 ≤ a₁ := Nat.pos_of_ne_zero h
        nlinarith
    refine ⟨Sum.inr (Sum.inl ⟨m, by omega⟩), ?_⟩
    simp [φ, PNat.coe_toPNat']
  · obtain ⟨hc, hm⟩ := le_wpMonExp_tail ha₁ (c, m) i
    dsimp only at hc hm
    rw [hi] at hc hm
    refine ⟨Sum.inr (Sum.inr ((⟨c, Nat.lt_succ_of_le hc⟩, ⟨m, Nat.lt_succ_of_le hm⟩), i)), ?_⟩
    simp [φ, PNat.coe_toPNat']

private theorem wpQCoeff_mem_kN {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ n : ℕ) : wpQCoeff N a₁ a₂ n ∈ kN N :=
    by
  have := (finite_wpMonExp_fiber ha₁ n).to_subtype
  have := Fintype.ofFinite (wpMonExp N a₁ ⁻¹' {n})
  rw [wpQCoeff, tsum_fintype]
  exact sum_mem fun i _ ↦ wpMonCoeff_mem_kN N a₁ a₂ i

private lemma summable_comp_fst_fin {β : Type*} {g : β → ℝ} (hg0 : ∀ b, 0 ≤ g b) (hg : Summable g)
    (k : ℕ) : Summable fun x : β × Fin k ↦ g x.1 := by
  classical
  refine summable_of_sum_le (fun x ↦ hg0 x.1) (c := k * ∑' b, g b) fun u ↦ ?_
  calc ∑ x ∈ u, g x.1 ≤ ∑ x ∈ (u.image Prod.fst) ×ˢ (Finset.univ : Finset (Fin k)), g x.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun x hx ↦ Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_univ _⟩)
          (fun _ _ _ ↦ hg0 _)
    _ = ∑ b ∈ u.image Prod.fst, (k : ℝ) * g b := by
        rw [Finset.sum_product]
        simp
    _ = k * ∑ b ∈ u.image Prod.fst, g b := (Finset.mul_sum _ _ _).symm
    _ ≤ k * ∑' b, g b := by
        gcongr
        exact hg.sum_le_tsum _ fun b _ ↦ hg0 b

set_option maxHeartbeats 400000 in
-- This summation proof elaborates slowly on this Mathlib version.
private theorem hasSum_wpMon {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun i : WpIdx ↦ wpMonCoeff N a₁ a₂ i * qN N τ ^ wpMonExp N a₁ i)
      (wpNormSeries N a₁ a₂ τ) := by
  have hN : 0 < N := by omega
  set q : ℂ := qN N τ with hqdef
  have hq : ‖q‖ < 1 := norm_qN_lt_one hN hτ
  set G : WpIdx → ℂ := fun i ↦ wpMonCoeff N a₁ a₂ i * q ^ wpMonExp N a₁ i with hG
  set r : ℂ := zetaN N ^ a₂ * q ^ a₁ with hr
  have h1 : HasSum (G ∘ Sum.inl)
      (1 / 12 + if a₁ = 0 then zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 else 0) := by
    have := hasSum_fintype (G ∘ Sum.inl)
    simpa [hG, wpMonCoeff, wpMonExp] using this
  have h2 : HasSum (G ∘ Sum.inr ∘ Sum.inl) (if a₁ = 0 then 0 else r / (1 - r) ^ 2) := by
    by_cases ha : a₁ = 0
    · simp only [ha, ite_true]
      convert hasSum_zero with m
      simp [hG, wpMonCoeff, ha]
    · simp only [ha, ite_false]
      have hr1 : ‖r‖ < 1 := by
        rw [hr, norm_mul, norm_pow, norm_zetaN, one_pow, one_mul, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hq ha
      have hgeo := hasSum_coe_mul_geometric_of_norm_lt_one hr1
      have hs : Summable fun m : ℕ+ ↦ ((m : ℕ) : ℂ) * r ^ (m : ℕ) :=
        summable_pnat_iff_summable_nat.mpr hgeo.summable
      have h2' : HasSum (fun m : ℕ+ ↦ ((m : ℕ) : ℂ) * r ^ (m : ℕ)) (r / (1 - r) ^ 2) := by
        rw [hs.hasSum_iff, ← hgeo.tsum_eq, ← tsum_zero_pnat_eq_tsum_nat hgeo.summable]
        simp
      refine h2'.congr_fun fun m ↦ ?_
      simp only [hG, Function.comp_apply, wpMonCoeff, wpMonExp, ha, ite_false, hr]
      rw [mul_pow, ← pow_mul, ← pow_mul]
      ring
  have hmaj := summable_comp_fst_fin (fun p ↦ by positivity)
    (summable_wpTail_majorant (norm_nonneg q) hq) 3
  have hq1 : ‖q‖ ≤ 1 := hq.le
  have hbound : ∀ x : (ℕ+ × ℕ+) × Fin 3, ‖(G ∘ Sum.inr ∘ Sum.inr) x‖ ≤
      4 * ((x.1.2 : ℕ) * ‖q‖ ^ ((x.1.1 : ℕ) * (x.1.2 : ℕ))) := by
    rintro ⟨⟨c, m⟩, i⟩
    obtain ⟨hc, hm⟩ := le_wpMonExp_tail ha₁ (c, m) i
    have hcm : (c : ℕ) * (m : ℕ) ≤ wpMonExp N a₁ (Sum.inr (Sum.inr ((c, m), i))) := by
      fin_cases i
      · exact Nat.mul_le_mul_right _ (le_add_right (Nat.le_mul_of_pos_right _ hN))
      · exact Nat.mul_le_mul_right _ (le_mul_sub_of_lt ha₁ c)
      · exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hN)
    have hpow : ‖q‖ ^ wpMonExp N a₁ (Sum.inr (Sum.inr ((c, m), i))) ≤ ‖q‖ ^ ((c : ℕ) * (m : ℕ)) :=
      pow_le_pow_of_le_one (norm_nonneg _) hq1 hcm
    have hz : ‖zetaN N‖ = 1 := norm_zetaN N
    have hcoef : ‖wpMonCoeff N a₁ a₂ (Sum.inr (Sum.inr ((c, m), i)))‖ ≤ 2 * (m : ℕ) := by
      fin_cases i <;> simp [wpMonCoeff, hz]
    simp only [Function.comp_apply, hG, norm_mul, norm_pow]
    have hm0 : (0 : ℝ) ≤ (m : ℕ) := by positivity
    calc ‖wpMonCoeff N a₁ a₂ (Sum.inr (Sum.inr ((c, m), i)))‖ *
          ‖q‖ ^ wpMonExp N a₁ (Sum.inr (Sum.inr ((c, m), i)))
        ≤ (2 * (m : ℕ)) * ‖q‖ ^ ((c : ℕ) * (m : ℕ)) := by gcongr
      _ ≤ 4 * ((m : ℕ) * ‖q‖ ^ ((c : ℕ) * (m : ℕ))) :=
          by nlinarith [pow_nonneg (norm_nonneg q) ((c : ℕ) * (m : ℕ))]
  have hs3 : Summable (G ∘ Sum.inr ∘ Sum.inr) := Summable.of_norm_bounded hmaj hbound
  have h3 : HasSum (G ∘ Sum.inr ∘ Sum.inr) (∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ) := by
    rw [hs3.hasSum_iff, hs3.tsum_prod]
    refine tsum_congr fun p ↦ ?_
    rw [tsum_fintype, Fin.sum_univ_three]
    simp only [Function.comp_apply, hG, wpMonCoeff, wpMonExp, wpTail, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, hqdef]
    ring
  have hall := h1.sum (h2.sum h3)
  have heq : (1 / 12 + if a₁ = 0 then zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 else 0) +
      ((if a₁ = 0 then 0 else r / (1 - r) ^ 2) + ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ) =
      wpNormSeries N a₁ a₂ τ := by
    by_cases ha : a₁ = 0
    · subst ha
      rw [ite_eq_left rfl, ite_eq_left rfl]
      unfold wpNormSeries
      rw [← hqdef, pow_zero, mul_one]
      ring
    · rw [ite_eq_right ha, ite_eq_right ha]
      unfold wpNormSeries
      rw [← hqdef, ← hr]
      ring
  rw [← heq]
  exact hall

private theorem hasSum_wpQCoeff {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n ↦ wpQCoeff N a₁ a₂ n * qN N τ ^ n) (wpNormSeries N a₁ a₂ τ) := by
  refine ((hasSum_wpMon (a₂ := a₂) ha₁ hτ).tsum_fiberwise (wpMonExp N a₁)).congr_fun fun n ↦ ?_
  rw [wpQCoeff, ← tsum_mul_right]
  exact tsum_congr fun i ↦ by rw [show wpMonExp N a₁ i = n from i.2]

private theorem qExpansion_wpNorm_coeff {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) :
    (qExpansion N (wpNorm N a₁ a₂)).coeff n = wpQCoeff N a₁ a₂ n := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let f' : C(ℍ, ℂ) := ⟨wpNorm N a₁ a₂, (mdifferentiable_wpNorm ha₁ ha₂ h0).continuous⟩
  have hfan : AnalyticAt ℂ (cuspFunction N f') 0 :=
    analyticAt_cuspFunction_zero hN (periodic_wpNorm ha₁ ha₂ h0)
      (mdifferentiable_wpNorm ha₁ ha₂ h0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0)
  have hf : ∀ τ : ℍ, HasSum (fun m ↦ wpQCoeff N a₁ a₂ m • Function.Periodic.qParam N τ ^ m)
      (f' τ) := by
    intro τ
    have h := hasSum_wpQCoeff (a₂ := a₂) ha₁ (τ := (τ : ℂ)) τ.im_pos
    rw [← wpNorm_eq ha₁ ha₂ h0] at h
    refine h.congr_fun fun m ↦ ?_
    simp only [smul_eq_mul, Function.Periodic.qParam, qN, Complex.ofReal_natCast]
  exact (qExpansion_coeff_unique f' hN hfan hf n).symm

private theorem qExpansion_wpNorm_coeff_mem_kN {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) :
    (qExpansion N (wpNorm N a₁ a₂)).coeff n ∈ kN N := by
  rw [qExpansion_wpNorm_coeff ha₁ ha₂ h0]
  exact wpQCoeff_mem_kN ha₁ a₂ n

private theorem hasSum_qExpansion_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion N (wpNorm N a₁ a₂)).coeff m •
      Function.Periodic.qParam N τ ^ m) (wpNorm N a₁ a₂ τ) :=
  hasSum_qExpansion (by exact_mod_cast (show 0 < N by omega)) (periodic_wpNorm ha₁ ha₂ h0)
    (mdifferentiable_wpNorm ha₁ ha₂ h0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0) τ

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

private def wpFib (N a₁ a₂ n : ℕ) (i : WpIdx) : ℂ :=
  if wpMonExp N a₁ i = n then wpMonCoeff N a₁ a₂ i else 0

private lemma wpQCoeff_eq_tsum_wpFib (N a₁ a₂ n : ℕ) :
    wpQCoeff N a₁ a₂ n = ∑' i, wpFib N a₁ a₂ n i := by
  rw [wpQCoeff, tsum_subtype]
  refine tsum_congr fun i ↦ ?_
  unfold wpFib
  split_ifs with h
  · exact Set.indicator_of_mem (by simpa using h) _
  · exact Set.indicator_of_notMem (by simpa using h) _

private lemma summable_wpFib_all {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ n : ℕ) :
    Summable (wpFib N a₁ a₂ n) := by
  apply summable_of_hasFiniteSupport
  change (Function.support (wpFib N a₁ a₂ n)).Finite
  apply (finite_wpMonExp_fiber ha₁ n).subset
  intro i hi
  rw [Set.mem_preimage, Set.mem_singleton_iff]
  by_contra h'
  apply hi
  change (if wpMonExp N a₁ i = n then wpMonCoeff N a₁ a₂ i else 0) = 0
  rw [ite_eq_right h']

private lemma summable_wpFib {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ n : ℕ) {ι : Type} (e : ι → WpIdx)
    (he : Function.Injective e) : Summable (wpFib N a₁ a₂ n ∘ e) :=
  (summable_wpFib_all ha₁ a₂ n).comp_injective he

private lemma tsum_wpFib_split {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ n : ℕ) :
    ∑' i, wpFib N a₁ a₂ n i = wpFib N a₁ a₂ n (Sum.inl ()) +
      ((∑' m : ℕ+, wpFib N a₁ a₂ n (Sum.inr (Sum.inl m))) +
        ∑' x : (ℕ+ × ℕ+) × Fin 3, wpFib N a₁ a₂ n (Sum.inr (Sum.inr x))) := by
  set F : WpIdx → ℂ := wpFib N a₁ a₂ n with hF
  have h1 : Summable (F ∘ Sum.inl) := summable_wpFib ha₁ a₂ n Sum.inl Sum.inl_injective
  have h2 : Summable ((F ∘ Sum.inr) ∘ Sum.inl) :=
    summable_wpFib ha₁ a₂ n (fun m ↦ Sum.inr (Sum.inl m))
      (Sum.inr_injective.comp Sum.inl_injective)
  have h3 : Summable ((F ∘ Sum.inr) ∘ Sum.inr) :=
    summable_wpFib ha₁ a₂ n (fun x ↦ Sum.inr (Sum.inr x))
      (Sum.inr_injective.comp Sum.inr_injective)
  have h23 : Summable (F ∘ Sum.inr) := Summable.sum (F ∘ Sum.inr) h2 h3
  have e1 : ∑' i, F i = (∑' u, F (Sum.inl u)) + ∑' j, F (Sum.inr j) := Summable.tsum_sum h1 h23
  have e2 : ∑' j, (F ∘ Sum.inr) j = (∑' m, (F ∘ Sum.inr) (Sum.inl m)) +
      ∑' x, (F ∘ Sum.inr) (Sum.inr x) := Summable.tsum_sum h2 h3
  have e3 : ∑' u : Unit, F (Sum.inl u) = F (Sum.inl ()) := by
    rw [tsum_fintype, Fintype.sum_unique]
  rw [e1, e3]
  exact congrArg _ e2

private theorem wpQCoeff_zero {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) :
    wpQCoeff N a₁ a₂ 0 =
      1 / 12 + if a₁ = 0 then zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 else 0 := by
  rw [wpQCoeff_eq_tsum_wpFib, tsum_wpFib_split ha₁]
  have e1 : wpFib N a₁ a₂ 0 (Sum.inl ()) =
      1 / 12 + if a₁ = 0 then zetaN N ^ a₂ / (1 - zetaN N ^ a₂) ^ 2 else 0 := by
    simp [wpFib, wpMonExp, wpMonCoeff]
  have e2 : ∀ m : ℕ+, wpFib N a₁ a₂ 0 (Sum.inr (Sum.inl m)) = 0 := by
    intro m
    have : wpMonExp N a₁ (Sum.inr (Sum.inl m)) ≠ 0 := by
      simp only [wpMonExp]
      split_ifs with h
      · exact m.ne_zero
      · exact Nat.mul_ne_zero h m.ne_zero
    simp [wpFib, this]
  have e3 : ∀ x : (ℕ+ × ℕ+) × Fin 3, wpFib N a₁ a₂ 0 (Sum.inr (Sum.inr x)) = 0 := by
    rintro ⟨p, i⟩
    have := (le_wpMonExp_tail ha₁ p i).2
    have hne : wpMonExp N a₁ (Sum.inr (Sum.inr (p, i))) ≠ 0 := by
      have := p.2.pos; omega
    simp [wpFib, hne]
  simp [e1, e2, e3]

private theorem wpQCoeff_of_lt {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) {n : ℕ} (hn0 : 0 < n) (hn : n
    < N) :
    wpQCoeff N a₁ a₂ n =
      (if a₁ ≠ 0 ∧ a₁ ∣ n then ((n / a₁ : ℕ) : ℂ) * zetaN N ^ (a₂ * (n / a₁)) else 0) +
        (if (N - a₁) ∣ n then
          ((n / (N - a₁) : ℕ) : ℂ) * (zetaN N)⁻¹ ^ (a₂ * (n / (N - a₁))) else 0) := by
  rw [wpQCoeff_eq_tsum_wpFib, tsum_wpFib_split ha₁]
  have hNa : 0 < N - a₁ := Nat.sub_pos_of_lt ha₁
  have e1 : wpFib N a₁ a₂ n (Sum.inl ()) = 0 := by
    simp [wpFib, wpMonExp, hn0.ne]
  have e2 : ∑' m : ℕ+, wpFib N a₁ a₂ n (Sum.inr (Sum.inl m)) =
      if a₁ ≠ 0 ∧ a₁ ∣ n then ((n / a₁ : ℕ) : ℂ) * zetaN N ^ (a₂ * (n / a₁)) else 0 := by
    by_cases ha : a₁ = 0
    · simp [wpFib, wpMonCoeff, ha]
    · set m₁ : ℕ+ := (n / a₁).toPNat' with hm₁
      rw [tsum_eq_single m₁]
      · by_cases hd : a₁ ∣ n
        · have hq : 0 < n / a₁ := Nat.div_pos (Nat.le_of_dvd hn0 hd) (Nat.pos_of_ne_zero ha)
          have hm₁v : (m₁ : ℕ) = n / a₁ := by rw [hm₁, Nat.toPNat'_coe, ite_eq_left hq]
          have hE : wpMonExp N a₁ (Sum.inr (Sum.inl m₁)) = n := by
            simp only [wpMonExp, ha, ite_false, hm₁v, Nat.mul_div_cancel' hd]
          simp [wpFib, hE, wpMonCoeff, ha, hd, hm₁v]
        · have hE : wpMonExp N a₁ (Sum.inr (Sum.inl m₁)) ≠ n := by
            simp only [wpMonExp, ha, ite_false]
            exact fun h ↦ hd ⟨m₁, h.symm⟩
          simp [wpFib, hE, ha, hd]
      · intro m hm
        have hE : wpMonExp N a₁ (Sum.inr (Sum.inl m)) ≠ n := by
          simp only [wpMonExp, ha, ite_false]
          intro h
          apply hm
          apply PNat.coe_injective
          have : (m : ℕ) = n / a₁ := by
            rw [← h, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha)]
          rw [this, hm₁, Nat.toPNat'_coe, ite_eq_left]
          rw [← this]; exact m.pos
        simp [wpFib, hE]
  have e3 : ∑' x : (ℕ+ × ℕ+) × Fin 3, wpFib N a₁ a₂ n (Sum.inr (Sum.inr x)) =
      if (N - a₁) ∣ n then
        ((n / (N - a₁) : ℕ) : ℂ) * (zetaN N)⁻¹ ^ (a₂ * (n / (N - a₁))) else 0 := by
    set m₀ : ℕ+ := (n / (N - a₁)).toPNat' with hm₀
    set x₀ : (ℕ+ × ℕ+) × Fin 3 := ((1, m₀), 1) with hx₀
    have key : ∀ x : (ℕ+ × ℕ+) × Fin 3, wpMonExp N a₁ (Sum.inr (Sum.inr x)) = n →
        x = x₀ ∧ (N - a₁) ∣ n := by
      rintro ⟨⟨c, m⟩, i⟩ hE
      have hc := c.pos
      have hm := m.pos
      have hcN : N ≤ (c : ℕ) * N := Nat.le_mul_of_pos_left _ hc
      fin_cases i
      · exfalso
        simp only [wpMonExp, Fin.zero_eta, Matrix.cons_val_zero] at hE
        nlinarith
      · simp only [wpMonExp, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] at hE
        have hc1 : (c : ℕ) = 1 := by
          by_contra hc1
          have hc2 : 2 ≤ (c : ℕ) := by omega
          have : 2 * N ≤ (c : ℕ) * N := Nat.mul_le_mul_right _ hc2
          have h3 : N + 1 ≤ (c : ℕ) * N - a₁ := by omega
          nlinarith
        rw [hc1, one_mul] at hE
        have hd : (N - a₁) ∣ n := ⟨m, hE.symm⟩
        have hmv : (m : ℕ) = n / (N - a₁) := by
          rw [← hE, Nat.mul_div_cancel_left _ hNa]
        refine ⟨?_, hd⟩
        rw [hx₀]
        congr
        · exact PNat.coe_injective hc1
        · apply PNat.coe_injective
          rw [hmv, hm₀, Nat.toPNat'_coe, ite_eq_left (hmv ▸ hm)]
      · exfalso
        simp only [wpMonExp, Fin.reduceFinMk, Matrix.cons_val] at hE
        nlinarith
    rw [tsum_eq_single x₀]
    · by_cases hd : (N - a₁) ∣ n
      · have hq : 0 < n / (N - a₁) := Nat.div_pos (Nat.le_of_dvd hn0 hd) hNa
        have hm₀v : (m₀ : ℕ) = n / (N - a₁) := by rw [hm₀, Nat.toPNat'_coe, ite_eq_left hq]
        have hE : wpMonExp N a₁ (Sum.inr (Sum.inr x₀)) = n := by
          simp only [wpMonExp, hx₀, PNat.one_coe, one_mul, Matrix.cons_val_one,
            Matrix.cons_val_zero, hm₀v, Nat.mul_div_cancel' hd]
        rw [wpFib, ite_eq_left hE, ite_eq_left hd, hx₀]
        simp only [wpMonCoeff, Matrix.cons_val_one, Matrix.cons_val_zero, hm₀v]
      · have hE : wpMonExp N a₁ (Sum.inr (Sum.inr x₀)) ≠ n := fun h ↦ hd (key x₀ h).2
        simp [wpFib, hE, hd]
    · intro x hx
      have hE : wpMonExp N a₁ (Sum.inr (Sum.inr x)) ≠ n := fun h ↦ hx (key x h).1
      simp [wpFib, hE]
  rw [e1, e2, e3, zero_add]

private lemma isPrimitiveRoot_zetaN {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zetaN N) N := by
  simpa [zetaN] using Complex.isPrimitiveRoot_exp N hN

private theorem wpQCoeff_eq_iff_neg {N a₁ a₂ b₁ b₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (ha0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (hb₁ : b₁ < N) (hb₂ : b₂ < N) (hb0 : b₁ ≠ 0 ∨ b₂ ≠ 0)
    (h : ∀ n, wpQCoeff N a₁ a₂ n = wpQCoeff N b₁ b₂ n) :
    (b₁ = a₁ ∧ b₂ = a₂) ∨ (b₁ = (N - a₁) % N ∧ b₂ = (N - a₂) % N) := by
  have hN : N ≠ 0 := by omega
  have hζ := isPrimitiveRoot_zetaN hN
  set ζ := zetaN N with hζdef
  have hζ0 : ζ ≠ 0 := zetaN_ne_zero N
  have powinj : ∀ {x y : ℕ}, x < N → y < N → ζ ^ x = ζ ^ y → x = y :=
    fun hx hy e ↦ hζ.pow_inj hx hy e
  have powmul : ∀ {x y : ℕ}, x < N → y < N → ζ ^ x * ζ ^ y = 1 → y = (N - x) % N := by
    intro x y hx hy e
    rw [← pow_add, hζ.pow_eq_one_iff_dvd] at e
    obtain ⟨c, hc⟩ := e
    have hc2 : c < 2 := by nlinarith
    interval_cases c
    · rw [mul_zero, Nat.add_eq_zero_iff] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp
    · rw [mul_one] at hc
      have hx0 : 0 < x := by omega
      have : (N - x) % N = N - x := Nat.mod_eq_of_lt (by omega)
      rw [this]; omega
  have invpow : ∀ y : ℕ, ζ⁻¹ ^ y * ζ ^ y = 1 := fun y ↦ by
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hζ0)]
  have powne1 : ∀ {x : ℕ}, 0 < x → x < N → ζ ^ x ≠ 1 := by
    intro x hx0 hx e
    rw [← pow_zero ζ] at e
    have := powinj hx (by omega) e
    omega
  have match_uu : ζ ^ a₂ = ζ ^ b₂ → b₂ = a₂ := fun e ↦ (powinj ha₂ hb₂ e).symm
  have match_uv : ζ ^ a₂ = ζ⁻¹ ^ b₂ → b₂ = (N - a₂) % N := fun e ↦
    powmul ha₂ hb₂ (by rw [e]; exact invpow b₂)
  have match_vu : ζ⁻¹ ^ a₂ = ζ ^ b₂ → b₂ = (N - a₂) % N := fun e ↦
    powmul ha₂ hb₂ (by rw [mul_comm, ← e]; exact invpow a₂)
  have match_vv : ζ⁻¹ ^ a₂ = ζ⁻¹ ^ b₂ → b₂ = a₂ := fun e ↦ by
    have : ζ ^ a₂ = ζ ^ b₂ := by
      rw [inv_pow, inv_pow, inv_inj] at e; exact e
    exact (powinj ha₂ hb₂ this).symm
  have h0 := h 0
  rw [wpQCoeff_zero ha₁, wpQCoeff_zero hb₁, add_right_inj, ← hζdef] at h0
  have Kne : ∀ {x : ℕ}, 0 < x → x < N → ζ ^ x / (1 - ζ ^ x) ^ 2 ≠ 0 := fun hx0 hx ↦
    div_ne_zero (pow_ne_zero _ hζ0) (pow_ne_zero _ (sub_ne_zero.mpr (powne1 hx0 hx).symm))
  by_cases hA : a₁ = 0
  · have ha₂0 : 0 < a₂ := Nat.pos_of_ne_zero (ha0.resolve_left (not_not.mpr hA))
    have hB : b₁ = 0 := by
      by_contra hB
      rw [ite_eq_left hA, ite_eq_right hB] at h0
      exact Kne ha₂0 ha₂ h0
    have hb₂0 : 0 < b₂ := Nat.pos_of_ne_zero (hb0.resolve_left (not_not.mpr hB))
    rw [ite_eq_left hA, ite_eq_left hB] at h0
    subst hA; subst hB
    set t := ζ ^ a₂ with ht
    set u := ζ ^ b₂ with hu
    have ht1 : 1 - t ≠ 0 := sub_ne_zero.mpr (powne1 ha₂0 ha₂).symm
    have hu1 : 1 - u ≠ 0 := sub_ne_zero.mpr (powne1 hb₂0 hb₂).symm
    rw [div_eq_div_iff (pow_ne_zero 2 ht1) (pow_ne_zero 2 hu1)] at h0
    have key : (t - u) * (1 - t * u) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp key with e | e
    · left; exact ⟨rfl, match_uu (sub_eq_zero.mp e)⟩
    · right
      refine ⟨by simp, powmul ha₂ hb₂ ?_⟩
      rw [← ht, ← hu]; linear_combination -e
  · have hB : b₁ ≠ 0 := by
      intro hB
      have hb₂0 : 0 < b₂ := Nat.pos_of_ne_zero (hb0.resolve_left (not_not.mpr hB))
      rw [ite_eq_right hA, ite_eq_left hB] at h0
      exact Kne hb₂0 hb₂ h0.symm
    have hmodA : (N - a₁) % N = N - a₁ := Nat.mod_eq_of_lt (by omega)
    rw [hmodA]
    set ka := min a₁ (N - a₁) with hka
    set kb := min b₁ (N - b₁) with hkb
    have hka0 : 0 < ka := lt_min (Nat.pos_of_ne_zero hA) (Nat.sub_pos_of_lt ha₁)
    have hkb0 : 0 < kb := lt_min (Nat.pos_of_ne_zero hB) (Nat.sub_pos_of_lt hb₁)
    have hkaN : ka < N := lt_of_le_of_lt (min_le_left _ _) ha₁
    have hkbN : kb < N := lt_of_le_of_lt (min_le_left _ _) hb₁
    have eval : ∀ {x₁ : ℕ} (x₂ : ℕ), x₁ < N → x₁ ≠ 0 → ∀ {n : ℕ}, 0 < n → n ≤ min x₁ (N - x₁) →
        wpQCoeff N x₁ x₂ n =
          (if x₁ = n then ζ ^ x₂ else 0) + (if N - x₁ = n then ζ⁻¹ ^ x₂ else 0) := by
      intro x₁ x₂ hx₁ hx0 n hn0 hn
      have hnN : n < N := lt_of_le_of_lt (le_trans hn (min_le_left _ _)) hx₁
      rw [wpQCoeff_of_lt hx₁ x₂ hn0 hnN, ← hζdef]
      have hn1 : n ≤ x₁ := le_trans hn (min_le_left _ _)
      have hn2 : n ≤ N - x₁ := le_trans hn (min_le_right _ _)
      congr 1
      · by_cases e : x₁ = n
        · subst e
          simp [hx0, Nat.div_self hn0]
        · have : ¬ (x₁ ∣ n) := fun hd ↦ e (le_antisymm (Nat.le_of_dvd hn0 hd) hn1)
          simp [e, this]
      · by_cases e : N - x₁ = n
        · rw [ite_eq_left e, ite_eq_left (e ▸ dvd_refl _), e, Nat.div_self hn0]
          simp
        · have : ¬ (N - x₁ ∣ n) := fun hd ↦ e (le_antisymm (Nat.le_of_dvd hn0 hd) hn2)
          rw [ite_eq_right e, ite_eq_right this]
    have hkk : ka = kb := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hb := eval b₂ hb₁ hB hka0 hlt.le
        rw [ite_eq_right (by omega : ¬ b₁ = ka), ite_eq_right (by omega : ¬ N - b₁ = ka),
                                                                    add_zero] at hb
        have ha := eval a₂ ha₁ hA hka0 le_rfl
        rw [h ka, hb] at ha
        have : a₁ = ka ∨ N - a₁ = ka := by omega
        rcases this with e | e
        · by_cases e' : N - a₁ = ka
          · omega
          · rw [ite_eq_left e, ite_eq_right e', add_zero] at ha
            exact pow_ne_zero _ hζ0 ha.symm
        · by_cases e' : a₁ = ka
          · omega
          · rw [ite_eq_right e', ite_eq_left e, zero_add] at ha
            exact pow_ne_zero _ (inv_ne_zero hζ0) ha.symm
      · have ha := eval a₂ ha₁ hA hkb0 hlt.le
        rw [ite_eq_right (by omega : ¬ a₁ = kb), ite_eq_right (by omega : ¬ N - a₁ = kb),
                                                                    add_zero] at ha
        have hb := eval b₂ hb₁ hB hkb0 le_rfl
        rw [← h kb, ha] at hb
        have : b₁ = kb ∨ N - b₁ = kb := by omega
        rcases this with e | e
        · by_cases e' : N - b₁ = kb
          · omega
          · rw [ite_eq_left e, ite_eq_right e', add_zero] at hb
            exact pow_ne_zero _ hζ0 hb.symm
        · by_cases e' : b₁ = kb
          · omega
          · rw [ite_eq_right e', ite_eq_left e, zero_add] at hb
            exact pow_ne_zero _ (inv_ne_zero hζ0) hb.symm
    have ha := eval a₂ ha₁ hA hka0 le_rfl
    have hb := eval b₂ hb₁ hB hkb0 le_rfl
    rw [← hkk, ← h ka, ha] at hb
    have haon : a₁ = ka ∨ N - a₁ = ka := by omega
    have hbon : b₁ = ka ∨ N - b₁ = ka := by omega
    by_cases hmid : a₁ = ka ∧ N - a₁ = ka
    · obtain ⟨e1, e2⟩ := hmid
      have hb12 : b₁ = ka ∧ N - b₁ = ka := by omega
      rw [ite_eq_left e1, ite_eq_left e2, ite_eq_left hb12.1, ite_eq_left hb12.2] at hb
      set u := ζ ^ a₂ with hu
      set u' := ζ ^ b₂ with hu'
      have hu0 : u ≠ 0 := pow_ne_zero _ hζ0
      have hu'0 : u' ≠ 0 := pow_ne_zero _ hζ0
      rw [inv_pow, inv_pow] at hb
      have e3 : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
      have e4 : u' * u'⁻¹ = 1 := mul_inv_cancel₀ hu'0
      have key : (u - u') * (u * u' - 1) = 0 := by
        linear_combination (u * u') * hb + u * e4 - u' * e3
      rcases mul_eq_zero.mp key with e | e
      · left; exact ⟨by omega, match_uu (sub_eq_zero.mp e)⟩
      · right; exact ⟨by omega, powmul ha₂ hb₂ (by rw [← hu, ← hu']; linear_combination e)⟩
    · rcases haon with e1 | e2
      · have e2 : ¬ N - a₁ = ka := fun e2 ↦ hmid ⟨e1, e2⟩
        rw [ite_eq_left e1, ite_eq_right e2, add_zero] at hb
        rcases hbon with f1 | f2
        · have f2 : ¬ N - b₁ = ka := by omega
          rw [ite_eq_left f1, ite_eq_right f2, add_zero] at hb
          left; exact ⟨by omega, match_uu hb⟩
        · have f1 : ¬ b₁ = ka := by omega
          rw [ite_eq_right f1, ite_eq_left f2, zero_add] at hb
          right; exact ⟨by omega, match_uv hb⟩
      · have e1 : ¬ a₁ = ka := fun e1 ↦ hmid ⟨e1, e2⟩
        rw [ite_eq_right e1, ite_eq_left e2, zero_add] at hb
        rcases hbon with f1 | f2
        · have f2 : ¬ N - b₁ = ka := by omega
          rw [ite_eq_left f1, ite_eq_right f2, add_zero] at hb
          right; exact ⟨by omega, match_vu hb⟩
        · have f1 : ¬ b₁ = ka := by omega
          rw [ite_eq_right f1, ite_eq_left f2, zero_add] at hb
          left; exact ⟨by omega, match_vv hb⟩

private theorem wpNorm_eq_imp {N a₁ a₂ b₁ b₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (ha0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (hb₁ : b₁ < N) (hb₂ : b₂ < N) (hb0 : b₁ ≠ 0 ∨ b₂ ≠ 0)
    (h : wpNorm N a₁ a₂ = wpNorm N b₁ b₂) :
    (b₁ = a₁ ∧ b₂ = a₂) ∨ (b₁ = (N - a₁) % N ∧ b₂ = (N - a₂) % N) := by
  refine wpQCoeff_eq_iff_neg ha₁ ha₂ ha0 hb₁ hb₂ hb0 fun n ↦ ?_
  rw [← qExpansion_wpNorm_coeff ha₁ ha₂ ha0, ← qExpansion_wpNorm_coeff hb₁ hb₂ hb0, h]

private def zetaK (N : ℕ) : kN N := ⟨zetaN N, zetaN_mem_kN N⟩

@[scoped simp] private lemma coe_zetaK (N : ℕ) : (zetaK N : ℂ) = zetaN N := rfl

private lemma zetaN_pow_N {N : ℕ} (hN : N ≠ 0) : zetaN N ^ N = 1 :=
  (isPrimitiveRoot_zetaN hN).pow_eq_one

private lemma pow_mul_eq_pow_mod_mul {M : Type*} [Monoid M] {x : M} {N : ℕ} (hx : x ^ N = 1)
    (k m : ℕ) : x ^ (k * m) = x ^ (k % N * m) := by
  rw [pow_eq_pow_mod (k * m) hx, pow_eq_pow_mod (k % N * m) hx, Nat.mod_mul_mod]

private def wpMonCoeffK (N a₁ a₂ : ℕ) (i : WpIdx) : kN N :=
    ⟨wpMonCoeff N a₁ a₂ i, wpMonCoeff_mem_kN N a₁ a₂ i⟩

private def wpQCoeffK {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ n : ℕ) : kN N :=
  ⟨wpQCoeff N a₁ a₂ n, wpQCoeff_mem_kN ha₁ a₂ n⟩

@[scoped simp] private lemma coe_wpQCoeffK {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ n : ℕ) :
    (wpQCoeffK ha₁ a₂ n : ℂ) = wpQCoeff N a₁ a₂ n := rfl

private lemma ringHom_wpMonCoeffK {N : ℕ} (hN : N ≠ 0) (φ : kN N →+* ℂ) {s : ℕ}
    (hφ : φ (zetaK N) = zetaN N ^ s) (a₁ a₂ : ℕ) (i : WpIdx) :
    φ (wpMonCoeffK N a₁ a₂ i) = wpMonCoeff N a₁ (s * a₂ % N) i := by
  have hζN := zetaN_pow_N hN
  have hpow : ∀ k : ℕ, φ ⟨zetaN N ^ k, zetaN_pow_mem_kN N k⟩ = (zetaN N ^ s) ^ k := fun k ↦ by
    rw [← hφ, ← map_pow]; rfl
  have hinvpow : ∀ k : ℕ, φ ⟨(zetaN N)⁻¹ ^ k, zetaN_inv_pow_mem_kN N k⟩ = ((zetaN N ^ s)⁻¹) ^ k :=
    fun k ↦ by
    rw [← hφ, ← map_inv₀, ← map_pow]; rfl
  have hnatK : ∀ m : ℕ, (⟨(m : ℂ), natCast_mem_kN N m⟩ : kN N) = (m : kN N) := fun m ↦
    Subtype.ext (by simp)
  have hnat : ∀ m : ℕ, φ ⟨(m : ℂ), natCast_mem_kN N m⟩ = m := fun m ↦ by
    rw [hnatK, map_natCast]
  have htw : φ ⟨1 / 12, one_div_twelve_mem_kN N⟩ = 1 / 12 := by
    have h12 : (⟨1 / 12, one_div_twelve_mem_kN N⟩ : kN N) *
        ⟨((12 : ℕ) : ℂ), natCast_mem_kN N 12⟩ = 1 :=
      Subtype.ext (by change (1 / 12 : ℂ) * ((12 : ℕ) : ℂ) = 1; norm_num)
    have := congrArg φ h12
    rw [map_mul, map_one, hnat] at this
    rw [eq_one_div_of_mul_eq_one_left this]
    norm_num
  have hexp1 : (zetaN N ^ s) ^ a₂ = zetaN N ^ (s * a₂ % N) := by
    rw [← pow_mul, pow_eq_pow_mod (s * a₂) hζN]
  have hexp : ∀ m : ℕ, (zetaN N ^ s) ^ (a₂ * m) = zetaN N ^ (s * a₂ % N * m) := fun m ↦ by
    rw [← pow_mul, ← mul_assoc, pow_mul_eq_pow_mod_mul hζN]
  have hexpinv : ∀ m : ℕ, ((zetaN N ^ s)⁻¹) ^ (a₂ * m) = (zetaN N)⁻¹ ^ (s * a₂ % N * m) :=
    fun m ↦ by
    have hζN' : (zetaN N)⁻¹ ^ N = 1 := by rw [inv_pow, hζN, inv_one]
    rw [← inv_pow, ← pow_mul, ← mul_assoc, pow_mul_eq_pow_mod_mul hζN']
  rcases i with u | m | ⟨p, i⟩
  · have e : wpMonCoeffK N a₁ a₂ (Sum.inl u) = ⟨1 / 12, one_div_twelve_mem_kN N⟩ +
        (if a₁ = 0 then ⟨zetaN N ^ a₂, zetaN_pow_mem_kN N a₂⟩ /
          (1 - ⟨zetaN N ^ a₂, zetaN_pow_mem_kN N a₂⟩) ^ 2 else 0) := by
      apply Subtype.ext
      simp only [wpMonCoeffK, wpMonCoeff]
      split_ifs <;> simp
    rw [e, map_add, htw]
    simp only [wpMonCoeff]
    split_ifs with h
    · rw [map_div₀, map_pow, map_sub, map_one, hpow, hexp1]
    · rw [map_zero]
  · have e : wpMonCoeffK N a₁ a₂ (Sum.inr (Sum.inl m)) =
        (if a₁ = 0 then 0 else ⟨((m : ℕ) : ℂ), natCast_mem_kN N m⟩ *
          ⟨zetaN N ^ (a₂ * m), zetaN_pow_mem_kN N _⟩) := by
      apply Subtype.ext
      simp only [wpMonCoeffK, wpMonCoeff]
      split_ifs <;> simp
    rw [e]
    simp only [wpMonCoeff]
    split_ifs with h
    · rw [map_zero]
    · rw [map_mul, hnat, hpow, hexp]
  · fin_cases i
    · have e : wpMonCoeffK N a₁ a₂ (Sum.inr (Sum.inr (p, 0))) =
          ⟨((p.2 : ℕ) : ℂ), natCast_mem_kN N _⟩ * ⟨zetaN N ^ (a₂ * p.2), zetaN_pow_mem_kN N _⟩ :=
        Subtype.ext (by simp [wpMonCoeffK, wpMonCoeff])
      simp only [Fin.zero_eta, Fin.isValue]
      rw [e, map_mul, hnat, hpow, hexp]
      simp [wpMonCoeff]
    · have e : wpMonCoeffK N a₁ a₂ (Sum.inr (Sum.inr (p, 1))) =
          ⟨((p.2 : ℕ) : ℂ), natCast_mem_kN N _⟩ *
            ⟨(zetaN N)⁻¹ ^ (a₂ * p.2), zetaN_inv_pow_mem_kN N _⟩ :=
        Subtype.ext (by simp [wpMonCoeffK, wpMonCoeff])
      simp only [Fin.mk_one, Fin.isValue]
      rw [e, map_mul, hnat, hinvpow, hexpinv]
      simp [wpMonCoeff]
    · have e : wpMonCoeffK N a₁ a₂ (Sum.inr (Sum.inr (p, 2))) =
          -⟨((2 : ℕ) : ℂ), natCast_mem_kN N 2⟩ * ⟨((p.2 : ℕ) : ℂ), natCast_mem_kN N _⟩ :=
        Subtype.ext (by
          change wpMonCoeff N a₁ a₂ (Sum.inr (Sum.inr (p, 2))) = -((2 : ℕ) : ℂ) * ((p.2 : ℕ) : ℂ)
          simp [wpMonCoeff])
      simp only [Fin.reduceFinMk, Fin.isValue]
      rw [e, map_mul, map_neg, hnat, hnat]
      simp [wpMonCoeff]

private theorem ringHom_wpQCoeffK {N a₁ : ℕ} (ha₁ : a₁ < N) (φ : kN N →+* ℂ) {s : ℕ}
    (hφ : φ (zetaK N) = zetaN N ^ s) (a₂ n : ℕ) :
    φ (wpQCoeffK ha₁ a₂ n) = wpQCoeff N a₁ (s * a₂ % N) n := by
  have hN : N ≠ 0 := by omega
  have hfin := (finite_wpMonExp_fiber ha₁ n).to_subtype
  have := Fintype.ofFinite (wpMonExp N a₁ ⁻¹' {n})
  have e : wpQCoeffK ha₁ a₂ n = ∑ i : (wpMonExp N a₁ ⁻¹' {n}), wpMonCoeffK N a₁ a₂ i := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum, coe_wpQCoeffK, wpQCoeff, tsum_fintype]
    rfl
  rw [e, map_sum, wpQCoeff, tsum_fintype]
  exact Finset.sum_congr rfl fun i _ ↦ ringHom_wpMonCoeffK hN φ hφ a₁ a₂ i

end B4_qexp

section B4_assembly

open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open ModularForm SlashInvariantFormClass ModularFormClass

private lemma mem_kN_of_rat {N : ℕ} {x : ℂ} (h : ∃ q : ℚ, x = (q : ℂ)) : x ∈ kN N := by
  obtain ⟨q, rfl⟩ := h
  exact (kN N).algebraMap_mem q

private lemma qExpansion_E4E6_coeff_mem_kN {N : ℕ} (hN : N ≠ 0) (n : ℕ) :
    (qExpansion N (⇑E₄ * ⇑E₆ : ℍ → ℂ)).coeff n ∈ kN N := by
  have hper : Function.Periodic ((⇑E₄ * ⇑E₆ : ℍ → ℂ) ∘ ofComplex) 1 := by
    have h4 := periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL
    have h6 := periodic_comp_ofComplex E₆ one_mem_strictPeriods_SL
    intro τ
    have e4 := h4 τ
    have e6 := h6 τ
    simp only [Function.comp_apply, Pi.mul_apply, Complex.ofReal_one] at e4 e6 ⊢
    rw [e4, e6]
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑E₄ * ⇑E₆ : ℍ → ℂ) := E₄.holo'.mul E₆.holo'
  have hbd : IsBoundedAtImInfty (⇑E₄ * ⇑E₆ : ℍ → ℂ) :=
    (ModularFormClass.bdd_at_infty E₄).mul (ModularFormClass.bdd_at_infty E₆)
  rw [qExpansion_coeff_width _ hN hper hhol hbd]
  split_ifs with hd
  · apply mem_kN_of_rat
    rw [ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL]
    exact ratCoeff_mul (ratCoeff_E (by norm_num) (by decide)) (ratCoeff_E (by norm_num) (by decide))
      _
  · exact zero_mem _

private def frickeH (N a₁ a₂ : ℕ) : ℍ → ℂ := (⇑E₄ * ⇑E₆ : ℍ → ℂ) * wpNorm N a₁ a₂

private theorem periodic_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨
    a₂ ≠ 0) :
    Function.Periodic (frickeH N a₁ a₂ ∘ ofComplex) N := by
  have h4 := (periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL).nat_mul N
  have h6 := (periodic_comp_ofComplex E₆ one_mem_strictPeriods_SL).nat_mul N
  have hw := periodic_wpNorm ha₁ ha₂ h0
  intro τ
  have e4 := h4 τ; have e6 := h6 τ; have ew := hw τ
  simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6 ew
  simp only [Function.comp_apply, frickeH, Pi.mul_apply, e4, e6, ew]

private theorem mdifferentiable_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (frickeH N a₁ a₂) :=
  (E₄.holo'.mul E₆.holo').mul (mdifferentiable_wpNorm ha₁ ha₂ h0)

private theorem isBoundedAtImInfty_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : IsBoundedAtImInfty (frickeH N a₁ a₂) :=
  ((ModularFormClass.bdd_at_infty E₄).mul (ModularFormClass.bdd_at_infty E₆)).mul
    (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0)

private theorem qExpansion_frickeH_coeff_mem_kN {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) :
    (qExpansion N (frickeH N a₁ a₂)).coeff n ∈ kN N := by
  have hN : N ≠ 0 := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperE : Function.Periodic ((⇑E₄ * ⇑E₆ : ℍ → ℂ) ∘ ofComplex) N := by
    have h4 := (periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL).nat_mul N
    have h6 := (periodic_comp_ofComplex E₆ one_mem_strictPeriods_SL).nat_mul N
    intro τ
    have e4 := h4 τ; have e6 := h6 τ
    simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6
    simp only [Function.comp_apply, Pi.mul_apply, e4, e6]
  have hE : AnalyticAt ℂ (cuspFunction N (⇑E₄ * ⇑E₆ : ℍ → ℂ)) 0 :=
    analyticAt_cuspFunction_zero hN' hperE (E₄.holo'.mul E₆.holo')
      ((ModularFormClass.bdd_at_infty E₄).mul (ModularFormClass.bdd_at_infty E₆))
  have hW : AnalyticAt ℂ (cuspFunction N (wpNorm N a₁ a₂)) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm ha₁ ha₂ h0)
      (mdifferentiable_wpNorm ha₁ ha₂ h0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0)
  rw [frickeH, qExpansion_mul hE hW, PowerSeries.coeff_mul]
  exact sum_mem fun ij _ ↦ mul_mem (qExpansion_E4E6_coeff_mem_kN hN _)
    (qExpansion_wpNorm_coeff_mem_kN ha₁ ha₂ h0 _)

private theorem hasSum_qExpansion_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (qExpansion N (frickeH N a₁ a₂)).coeff m •
      Function.Periodic.qParam N τ ^ m) (frickeH N a₁ a₂ τ) :=
  hasSum_qExpansion (by exact_mod_cast (show 0 < N by omega)) (periodic_frickeH ha₁ ha₂ h0)
    (mdifferentiable_frickeH ha₁ ha₂ h0) (isBoundedAtImInfty_frickeH ha₁ ha₂ h0) τ

end B4_assembly

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
  exact AuxR2.qExpansion_coeff_width f hN (by simpa using periodic_comp_ofComplex f h1)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) n

end ModularFormClass
end C6_width

section Solution

open UpperHalfPlane hiding I
open scoped Manifold

end Solution

end AuxR2
open scoped FrickeFunctions.WeierstrassPTorsionQExpansion.AuxR2

open UpperHalfPlane hiding I in
open scoped UpperHalfPlane Manifold in
open AuxR2 in
/-- Torsion values of the Weierstrass function. For `N ≠ 0` let `W a₁ a₂ τ = (2πi)⁻² ℘_τ ((a₁ τ +
a₂) / N)` and `ζ = exp (2πi / N)`. For `(a₁, a₂) ≠ 0` with `a₁, a₂ < N`, `W a₁ a₂` is
holomorphic, `N`-periodic and bounded at `i∞` with width-`N` q-expansion coefficients in
`ℚ(ζ)`; `W` determines `(a₁, a₂)` up to sign; the q-expansions come from power series over
`ℚ(ζ)` on which an embedding with `ζ ↦ ζ ^ s` (`s` coprime to `N`) acts by `a₂ ↦ s a₂ mod N`;
the width-`N` expansion of a `1`-periodic function is its width-`1` expansion spread out; and
`E₄`, `E₆` and `Δ` have rational q-coefficients. -/
public theorem _root_.ModularForm.weierstrassP_torsion_qExpansion_package (N : ℕ) (hN : N ≠ 0) (L :
    ℍ → PeriodPair)
    (hL : ∀ τ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) :
    let ζ : ℂ := Complex.exp (2 * π * I / N)
    let k : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {ζ}
    let ζk : k := IntermediateField.AdjoinSimple.gen ℚ ζ
    let W : ℕ → ℕ → ℍ → ℂ := fun a₁ a₂ τ ↦ ((2 * π * I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * (τ : ℂ) + (a₂ : ℂ)) / (N : ℂ))
    (∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (W a₁ a₂)
        ∧ Function.Periodic ((W a₁ a₂) ∘ UpperHalfPlane.ofComplex) (N : ℂ)
        ∧ IsBoundedAtImInfty (W a₁ a₂)
        ∧ ∀ n, (qExpansion N (W a₁ a₂)).coeff n ∈ k)
    ∧ (∀ a₁ a₂ b₁ b₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        b₁ < N → b₂ < N → (b₁ ≠ 0 ∨ b₂ ≠ 0) →
        W a₁ a₂ = W b₁ b₂ →
        (b₁ = a₁ ∧ b₂ = a₂) ∨ (b₁ = (N - a₁) % N ∧ b₂ = (N - a₂) % N))
    ∧ (∃ S : ℕ → ℕ → PowerSeries k,
        (∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
          (S a₁ a₂).map (algebraMap k ℂ) = qExpansion N (W a₁ a₂))
        ∧ ∀ s : ℕ, s.Coprime N → ∀ φ : k →+* ℂ, φ ζk = ζ ^ s →
            ∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
              (S a₁ a₂).map φ = qExpansion N (W a₁ (s * a₂ % N)))
    ∧ (∀ f : ℍ → ℂ, Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℂ) →
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsBoundedAtImInfty f →
        ∀ n, (qExpansion N f).coeff n =
          if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0)
    ∧ (∀ n, ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff n = (q : ℂ))
    ∧ (∀ n, ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff n = (q : ℂ))
    ∧ (∀ n, ∃ q : ℚ,
        (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff n = (q : ℂ)) := by
  intro ζ k ζk W
  obtain rfl := L_eq_periodPairOfTau L hL
  have hW : W = wpNorm N := by
    funext a₁ a₂ τ; rfl
  have hk : k = kN N := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a₁ a₂ ha₁ ha₂ h0
    rw [hW]
    exact ⟨mdifferentiable_wpNorm ha₁ ha₂ h0, periodic_wpNorm ha₁ ha₂ h0,
      isBoundedAtImInfty_wpNorm ha₁ ha₂ h0,
          fun n ↦ hk ▸ qExpansion_wpNorm_coeff_mem_kN ha₁ ha₂ h0 n⟩
  · intro a₁ a₂ b₁ b₂ ha₁ ha₂ ha0 hb₁ hb₂ hb0 heq
    exact wpNorm_eq_imp ha₁ ha₂ ha0 hb₁ hb₂ hb0 (hW ▸ heq)
  · have hζk : ζk = zetaK N := rfl
    refine ⟨fun a₁ a₂ ↦ if ha₁ : a₁ < N then PowerSeries.mk (wpQCoeffK ha₁ a₂) else 0, ?_, ?_⟩
    · intro a₁ a₂ ha₁ ha₂ h0
      simp only
      rw [dite_eq_left ha₁, hW]
      refine PowerSeries.ext fun n ↦ ?_
      rw [PowerSeries.coeff_map]
      erw [PowerSeries.coeff_mk]
      rw [qExpansion_wpNorm_coeff ha₁ ha₂ h0]
      rfl
    · intro s hs φ hφ a₁ a₂ ha₁ ha₂ h0
      have hφ' : φ (zetaK N) = zetaN N ^ s := hζk ▸ hφ
      have hsa₂ : s * a₂ % N < N := Nat.mod_lt _ (Nat.pos_of_ne_zero hN)
      have h0' : a₁ ≠ 0 ∨ s * a₂ % N ≠ 0 := by
        refine h0.imp id fun ha₂0 hc ↦ ha₂0 ?_
        rw [← Nat.dvd_iff_mod_eq_zero] at hc
        exact Nat.eq_zero_of_dvd_of_lt (hs.symm.dvd_of_dvd_mul_left hc) ha₂
      simp only
      rw [dite_eq_left ha₁, hW]
      refine PowerSeries.ext fun n ↦ ?_
      rw [PowerSeries.coeff_map]
      erw [PowerSeries.coeff_mk]
      exact (ringHom_wpQCoeffK ha₁ φ hφ' a₂ n).trans
        (qExpansion_wpNorm_coeff ha₁ hsa₂ h0' n).symm
  · intro f hper hhol hbd n
    exact qExpansion_coeff_width f hN (by simpa using hper) hhol hbd n
  · exact ratCoeff_E (by norm_num) (by decide)
  · exact ratCoeff_E (by norm_num) (by decide)
  · exact ratCoeff_discriminant

end

end WeierstrassPTorsionQExpansion

end FrickeFunctions
