/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_frickeFunction_modularity_package.lean`
and
`P2M/Sol/S_WLight_frickeFunction_modularity_package.lean`
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
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.WeierstrassPTorsionQExpansion

/-!
# Modularity of the Fricke functions

This file proves the modularity properties of the Fricke functions of level `N`. Throughout, `j
= E₄³ / Δ` and, for `v : Fin 2 → ZMod N`, the Fricke function is `f_v τ = -(E₄ τ E₆ τ / Δ τ) /
2592 · (2πi)⁻² ℘_τ((v₀ τ + v₁) / N)`, where `℘_τ` is the Weierstrass function of the lattice
`ℤτ + ℤ`.

## Main statements

Each result below takes `W` and `fricke` with `W v τ = (2πi)⁻² ℘_τ((v₀ τ + v₁) / N)` and
`fricke v τ = -(E₄ τ E₆ τ / Δ τ) / 2592 · W v τ`, so `fricke v = f_v`.

* `ModularForm.frickeFunction_smul`: `SL(2, ℤ)` acts by `f_v (γ • τ) = f_{v γ} τ`.
* `ModularForm.frickeFunction_neg`: `f_{-v} = f_v`.
* `ModularForm.mdifferentiable_frickeFunction`: `f_v` is holomorphic for `v ≠ 0`.
* `ModularForm.isBoundedAtImInfty_frickeFunction_mul_discriminant`: `f_v Δ` is bounded at `i∞`.
* `ModularForm.periodic_frickeFunction_mul_discriminant`: `f_v Δ` is `N`-periodic.
* `ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_mem`: the q-coefficients of
  `f_v Δ` lie in `ℚ(ζ_N)`.
* `ModularForm.eq_or_eq_neg_of_frickeFunction_eq`: `f_v = f_w` forces `w = ± v`.
* `ModularForm.frickeFunction_smul_of_mem_Gamma`: `f_v` is `Γ(N)`-invariant.
* `ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_sigmaTransport`: an embedding
  of `ℚ(ζ_N)` with `ζ_N ↦ ζ_N ^ s` maps the q-coefficients of `f_v Δ` to those of
  `f_{(v₀, s v₁)} Δ`.
* `ModularForm.frickeFunction_modularity_package`: all of the above in one statement, with
  `f_v` written out.
-/
namespace FrickeFunctions.FrickeModularity

noncomputable section

open Complex Real
namespace Aux

section B1_homogeneity

open PeriodPair

private def smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) : PeriodPair where
  ω₁ := a * L.ω₁
  ω₂ := a * L.ω₂
  indep := LinearIndependent.pair_iff.mpr fun s t hst => by
    refine LinearIndependent.pair_iff.mp L.indep s t ?_
    have h0 : a * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [mul_add, mul_smul_comm, mul_smul_comm]; exact hst
    exact (mul_eq_zero.mp h0).resolve_left ha

@[scoped simp] private lemma smulPeriodPair_ω₁ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).ω₁ = a * L.ω₁ := rfl

@[scoped simp] private lemma smulPeriodPair_ω₂ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).ω₂ = a * L.ω₂ := rfl

private lemma mem_smulPeriodPair_lattice {a : ℂ} (ha : a ≠ 0) (L : PeriodPair) {x : ℂ} :
    x ∈ (smulPeriodPair a ha L).lattice ↔ ∃ y ∈ L.lattice, x = a * y := by
  simp only [mem_lattice, smulPeriodPair_ω₁, smulPeriodPair_ω₂]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨(m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂, ⟨m, n, rfl⟩, by rw [← h]; ring⟩
  · rintro ⟨y, ⟨m, n, h⟩, rfl⟩
    exact ⟨m, n, by rw [← h]; ring⟩

private def smulLatticeEquiv (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    L.lattice ≃ (smulPeriodPair a ha L).lattice where
  toFun l := ⟨a * l, (mem_smulPeriodPair_lattice ha L).mpr ⟨l, l.2, rfl⟩⟩
  invFun l := ⟨a⁻¹ * l, by
    obtain ⟨y, hy, hxy⟩ := (mem_smulPeriodPair_lattice ha L).mp l.2
    rw [hxy, inv_mul_cancel_left₀ ha]; exact hy⟩
  left_inv l := Subtype.ext (inv_mul_cancel_left₀ ha _)
  right_inv l := Subtype.ext (mul_inv_cancel_left₀ ha _)

@[scoped simp] private lemma smulLatticeEquiv_coe (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (l :
    L.lattice) :
    ((smulLatticeEquiv a ha L) l : ℂ) = a * l := rfl

private theorem weierstrassP_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (z : ℂ) :
    weierstrassP (smulPeriodPair a ha L) (a * z) = a⁻¹ ^ 2 * weierstrassP L z := by
  have key : ∀ u : ℂ, 1 / (a * u) ^ 2 = a⁻¹ ^ 2 * (1 / u ^ 2) := fun u => by
    simp [one_div, mul_pow, inv_pow, mul_comm]
  simp only [weierstrassP]
  rw [← (smulLatticeEquiv a ha L).tsum_eq, ← tsum_mul_left]
  congr with l
  simp only [smulLatticeEquiv_coe]
  rw [show a * z - a * (l : ℂ) = a * (z - l) by ring, key, key, mul_sub]

end B1_homogeneity

section R4aFloor
open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open ModularForm
open ModularFormClass
open CuspForm
open Polynomial
open Real.Polynomial
open Filter

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

private def wpTail (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℂ) : ℂ :=
  ((p.2 : ℕ) : ℂ) *
    (zetaN N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (zetaN N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
        2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ)))

private def wpTorsion (N a₁ a₂ : ℕ) (τ : ℍ) : ℂ :=
  PeriodPair.weierstrassP (periodPairOfTau τ) (((a₁ : ℂ) * τ + a₂) / N)

private def wpTorsionSeries (N a₁ a₂ : ℕ) (τ : ℂ) : ℂ :=
  (2 * π * I) ^ 2 *
    (zetaN N ^ a₂ * qN N τ ^ a₁ / (1 - zetaN N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 +
      ∑' p : ℕ+ × ℕ+, wpTail N a₁ a₂ p τ)

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

private def frickeH (N a₁ a₂ : ℕ) : ℍ → ℂ := (⇑E₄ * ⇑E₆ : ℍ → ℂ) * wpNorm N a₁ a₂

private theorem r2_package {N : ℕ} (hN : N ≠ 0) :
    (∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpNorm N a₁ a₂)
        ∧ Function.Periodic ((wpNorm N a₁ a₂) ∘ ofComplex) (N : ℂ)
        ∧ IsBoundedAtImInfty (wpNorm N a₁ a₂)
        ∧ ∀ n, (qExpansion N (wpNorm N a₁ a₂)).coeff n ∈ kN N)
    ∧ (∀ a₁ a₂ b₁ b₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        b₁ < N → b₂ < N → (b₁ ≠ 0 ∨ b₂ ≠ 0) →
        wpNorm N a₁ a₂ = wpNorm N b₁ b₂ →
        (b₁ = a₁ ∧ b₂ = a₂) ∨ (b₁ = (N - a₁) % N ∧ b₂ = (N - a₂) % N))
    ∧ (∃ S : ℕ → ℕ → PowerSeries ↑(kN N),
        (∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
          (S a₁ a₂).map (algebraMap ↑(kN N) ℂ) = qExpansion N (wpNorm N a₁ a₂))
        ∧ ∀ s : ℕ, s.Coprime N → ∀ φ : ↑(kN N) →+* ℂ,
            φ ⟨zetaN N, zetaN_mem_kN N⟩ = zetaN N ^ s →
            ∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
              (S a₁ a₂).map φ = qExpansion N (wpNorm N a₁ (s * a₂ % N)))
    ∧ (∀ f : ℍ → ℂ, Function.Periodic (f ∘ ofComplex) (1 : ℂ) →
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsBoundedAtImInfty f →
        ∀ n, (qExpansion N f).coeff n =
          if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0)
    ∧ (∀ n, ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff n = (q : ℂ))
    ∧ (∀ n, ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff n = (q : ℂ))
    ∧ (∀ n, ∃ q : ℚ,
        (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)).coeff n = (q : ℂ)) :=
  ModularForm.weierstrassP_torsion_qExpansion_package N hN periodPairOfTau fun _ ↦ ⟨rfl, rfl⟩

private theorem periodic_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    Function.Periodic (wpNorm N a₁ a₂ ∘ ofComplex) N :=
  ((r2_package (by omega)).1 a₁ a₂ ha₁ ha₂ h0).2.1

private theorem mdifferentiable_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpNorm N a₁ a₂) :=
  ((r2_package (by omega)).1 a₁ a₂ ha₁ ha₂ h0).1

private theorem isBoundedAtImInfty_wpNorm {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : IsBoundedAtImInfty (wpNorm N a₁ a₂) :=
  ((r2_package (by omega)).1 a₁ a₂ ha₁ ha₂ h0).2.2.1

private theorem qExpansion_wpNorm_coeff_mem_kN {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) : (qExpansion N (wpNorm N a₁ a₂)).coeff n ∈ kN N :=
  ((r2_package (by omega)).1 a₁ a₂ ha₁ ha₂ h0).2.2.2 n

private theorem wpNorm_eq_imp {N a₁ a₂ b₁ b₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (ha0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (hb₁ : b₁ < N) (hb₂ : b₂ < N) (hb0 : b₁ ≠ 0 ∨ b₂ ≠ 0)
    (h : wpNorm N a₁ a₂ = wpNorm N b₁ b₂) :
    (b₁ = a₁ ∧ b₂ = a₂) ∨ (b₁ = (N - a₁) % N ∧ b₂ = (N - a₂) % N) :=
  (r2_package (by omega)).2.1 a₁ a₂ b₁ b₂ ha₁ ha₂ ha0 hb₁ hb₂ hb0 h

private theorem isBoundedAtImInfty_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : IsBoundedAtImInfty (frickeH N a₁ a₂) :=
  ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul (ModularFormClass.bdd_at_infty
      ModularForm.E₆)).mul
    (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0)

private theorem qExpansion_coeff_width (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n =
      if N ∣ n then (qExpansion 1 f).coeff (n / N) else 0 :=
  (r2_package hN).2.2.2.1 f hper hhol hbd n

private theorem periodic_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h0 : a₁ ≠ 0 ∨
    a₂ ≠ 0) :
    Function.Periodic (frickeH N a₁ a₂ ∘ ofComplex) N := by
  have h4 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
    one_mem_strictPeriods_SL).nat_mul N
  have h6 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
    one_mem_strictPeriods_SL).nat_mul N
  have hw := periodic_wpNorm ha₁ ha₂ h0
  intro τ
  have e4 := h4 τ; have e6 := h6 τ; have ew := hw τ
  simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6 ew
  simp only [Function.comp_apply, frickeH, Pi.mul_apply, e4, e6, ew]

private theorem mdifferentiable_frickeH {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (frickeH N a₁ a₂) :=
  (ModularForm.E₄.holo'.mul ModularForm.E₆.holo').mul (mdifferentiable_wpNorm ha₁ ha₂ h0)

private theorem wpNorm_qExpansion_model {N : ℕ} (hN : N ≠ 0) :
    ∃ S : ℕ → ℕ → PowerSeries ↑(kN N),
      (∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        (S a₁ a₂).map (algebraMap ↑(kN N) ℂ) = qExpansion N (wpNorm N a₁ a₂)) ∧
      ∀ s : ℕ, s.Coprime N → ∀ φ : ↑(kN N) →+* ℂ,
        φ ⟨zetaN N, zetaN_mem_kN N⟩ = zetaN N ^ s →
        ∀ a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
          (S a₁ a₂).map φ = qExpansion N (wpNorm N a₁ (s * a₂ % N)) :=
  (r2_package hN).2.2.1

private theorem qExpansion_one_E4_rat (n : ℕ) :
    ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff n = (q : ℂ) :=
  (r2_package one_ne_zero).2.2.2.2.1 n

private theorem qExpansion_one_E6_rat (n : ℕ) :
    ∃ q : ℚ, (qExpansion 1 (⇑ModularForm.E₆ : ℍ → ℂ)).coeff n = (q : ℂ) :=
  (r2_package one_ne_zero).2.2.2.2.2.1 n

private lemma analyticAt_cuspFunction_zero_of {N : ℕ} [NeZero N] {g : ℍ → ℂ}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hper : Function.Periodic (g ∘ ofComplex) N)
    (hbd : IsBoundedAtImInfty g) :
    AnalyticAt ℂ (cuspFunction N g) 0 :=
  analyticAt_cuspFunction_zero (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hper hhol hbd

end R4aFloor

section B3_fricke

open PeriodPair
open scoped UpperHalfPlane MatrixGroups

private def latticeEquivOfEq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.lattice ≃ L'.lattice where
  toFun l := ⟨l.1, h.le l.2⟩
  invFun l := ⟨l.1, h.ge l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[scoped simp] private lemma latticeEquivOfEq_coe {L L' : PeriodPair} (h : L.lattice = L'.lattice)
    (l : L.lattice) : ((latticeEquivOfEq h l : L'.lattice) : ℂ) = (l : ℂ) := rfl

private theorem weierstrassP_of_lattice_eq {L L' : PeriodPair} (h : L.lattice
    = L'.lattice) (z : ℂ) :
    weierstrassP L z = weierstrassP L' z := by
  simp only [weierstrassP]
  rw [← (latticeEquivOfEq h).tsum_eq]
  rfl

private theorem G_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) :
    L.G n = L'.G n := by
  simp only [G]
  rw [← (latticeEquivOfEq h).tsum_eq]
  rfl

private theorem G_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (n : ℕ) :
    (smulPeriodPair a ha L).G n = a⁻¹ ^ n * L.G n := by
  simp only [G]
  rw [← (smulLatticeEquiv a ha L).tsum_eq, ← tsum_mul_left]
  congr with l
  simp only [smulLatticeEquiv_coe, mul_pow]
  rw [mul_inv, inv_pow]

private theorem g₂_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).g₂ = a⁻¹ ^ 4 * L.g₂ := by
  simp only [g₂, G_smulPeriodPair]; ring

private theorem g₃_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).g₃ = a⁻¹ ^ 6 * L.g₃ := by
  simp only [g₃, G_smulPeriodPair]; ring

private def latticeDisc (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

private theorem latticeDisc_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    latticeDisc (smulPeriodPair a ha L) = a⁻¹ ^ 12 * latticeDisc L := by
  simp only [latticeDisc, g₂_smulPeriodPair, g₃_smulPeriodPair]; ring

private theorem g₂_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : L.g₂ = L'.g₂ :=
    by
  simp [g₂, G_of_lattice_eq h]

private theorem g₃_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : L.g₃ = L'.g₃ :=
    by
  simp [g₃, G_of_lattice_eq h]

private theorem latticeDisc_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    latticeDisc L = latticeDisc L' := by
  simp [latticeDisc, g₂_of_lattice_eq h, g₃_of_lattice_eq h]

private def frickePrefactor (L : PeriodPair) : ℂ := L.g₂ * L.g₃ / latticeDisc L

private theorem frickePrefactor_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    frickePrefactor (smulPeriodPair a ha L) = a ^ 2 * frickePrefactor L := by
  have h12 : (a : ℂ)⁻¹ ^ 12 ≠ 0 := pow_ne_zero _ (inv_ne_zero ha)
  simp only [frickePrefactor, g₂_smulPeriodPair, g₃_smulPeriodPair, latticeDisc_smulPeriodPair]
  field_simp

private theorem frickePrefactor_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    frickePrefactor L = frickePrefactor L' := by
  simp [frickePrefactor, g₂_of_lattice_eq h, g₃_of_lattice_eq h, latticeDisc_of_lattice_eq h]

end B3_fricke

section B3_fricke_tier2

open PeriodPair Matrix
open scoped UpperHalfPlane MatrixGroups

private theorem span_SL2_basis_change {a b c d : ℤ} (hdet : a * d - b * c = 1) (ω₁ ω₂ : ℂ) :
    (Submodule.span ℤ {(a : ℂ) * ω₁ + (b : ℂ) * ω₂, (c : ℂ) * ω₁ + (d : ℂ) * ω₂} : Submodule ℤ ℂ)
      = Submodule.span ℤ {ω₁, ω₂} := by
  have hdetC : (a : ℂ) * d - b * c = 1 := by exact_mod_cast hdet
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Submodule.mem_span_pair.mpr ⟨a, b, by simp [zsmul_eq_mul]⟩,
           Submodule.mem_span_pair.mpr ⟨c, d, by simp [zsmul_eq_mul]⟩⟩
  · rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨Submodule.mem_span_pair.mpr ⟨d, -b, ?_⟩,
            Submodule.mem_span_pair.mpr ⟨-c, a, ?_⟩⟩
    · simp only [zsmul_eq_mul, Int.cast_neg]; linear_combination ω₁ * hdetC
    · simp only [zsmul_eq_mul, Int.cast_neg]; linear_combination ω₂ * hdetC

private def denomZ (γ : SL(2, ℤ)) (τ : ℂ) : ℂ := (γ 1 0 : ℤ) * τ + (γ 1 1 : ℤ)

private def numZ (γ : SL(2, ℤ)) (τ : ℂ) : ℂ := (γ 0 0 : ℤ) * τ + (γ 0 1 : ℤ)

private lemma denomZ_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : denomZ γ (τ : ℂ) ≠ 0 := by
  intro h
  have him : ((γ 1 0 : ℤ) : ℝ) * (τ : ℂ).im = 0 := by
    have := congrArg Complex.im h
    simp only [denomZ, Complex.add_im, Complex.mul_im, Complex.intCast_im, zero_mul,
      Complex.intCast_re, add_zero, Complex.zero_im] at this
    linarith
  have hc0 : (γ 1 0 : ℤ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact_mod_cast h
    · exact absurd h (UpperHalfPlane.coe_im τ ▸ τ.im_ne_zero)
  have hd0 : (γ 1 1 : ℤ) = 0 := by
    have := h
    rw [denomZ, hc0] at this
    simpa using this
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rwa [Matrix.det_fin_two] at this
  rw [hc0, hd0] at hdet
  simp at hdet

private lemma coe_SL2Z_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = numZ γ (τ : ℂ) / denomZ γ (τ : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, numZ, denomZ]
  have hcast : ∀ i j : Fin 2, ((algebraMap ℤ ℝ (γ i j) : ℝ) : ℂ) = ((γ i j : ℤ) : ℂ) := by
    intro i j; simp [eq_intCast]
  rw [hcast, hcast, hcast, hcast]

private theorem mem_lattice_smul_SL2 (γ : SL(2, ℤ)) (τ : ℍ) (x : ℂ) :
    x ∈ (periodPairOfTau (γ • τ)).lattice
      ↔ denomZ γ τ * x ∈ (periodPairOfTau τ).lattice := by
  have hd : denomZ γ (τ : ℂ) ≠ 0 := denomZ_ne_zero γ τ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rwa [Matrix.det_fin_two] at this
  have hspan := span_SL2_basis_change hdet (τ : ℂ) (1 : ℂ)
  simp only [mul_one] at hspan
  have hlatτ : (periodPairOfTau τ).lattice = Submodule.span ℤ {(τ : ℂ), 1} := rfl
  constructor
  · intro hx
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hx
    simp only [periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one, coe_SL2Z_smul] at hmn
    rw [hlatτ, ← hspan]
    refine Submodule.mem_span_pair.mpr ⟨m, n, ?_⟩
    have hdx : denomZ γ τ * x = (m : ℂ) * numZ γ τ + (n : ℂ) * denomZ γ τ := by
      rw [← hmn]; field_simp
    simp only [zsmul_eq_mul]
    rw [hdx, numZ, denomZ]
  · intro hx
    rw [hlatτ, ← hspan] at hx
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hx
    simp only [zsmul_eq_mul] at hpq
    refine PeriodPair.mem_lattice.mpr ⟨p, q, ?_⟩
    simp only [periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one, coe_SL2Z_smul]
    have key : (p : ℂ) * numZ γ τ + (q : ℂ) * denomZ γ τ = denomZ γ τ * x := by
      rw [← hpq, numZ, denomZ]
    field_simp
    linear_combination key

private theorem periodPairOfTau_smul_lattice_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    (periodPairOfTau (γ • τ)).lattice
      = (smulPeriodPair (denomZ γ τ)⁻¹ (inv_ne_zero (denomZ_ne_zero γ τ))
          (periodPairOfTau τ)).lattice := by
  have hd : denomZ γ (τ : ℂ) ≠ 0 := denomZ_ne_zero γ τ
  ext x
  rw [mem_lattice_smul_SL2, mem_smulPeriodPair_lattice]
  constructor
  · intro hx
    exact ⟨denomZ γ τ * x, hx, by field_simp⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [mul_inv_cancel_left₀ hd]

private def frickeTorsionPt (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  (((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ)

private lemma weierstrassP_torsionPt_lift_irrel {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (τ : ℍ)
    (b₁ b₂ : ℤ) (h₁ : (b₁ : ZMod N) = a 0) (h₂ : (b₂ : ZMod N) = a 1) :
    weierstrassP (periodPairOfTau τ) (((b₁ : ℂ) * τ + (b₂ : ℂ)) / (N : ℂ))
      = weierstrassP (periodPairOfTau τ) (frickeTorsionPt N a τ) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have cast_val : ∀ i : Fin 2, ((a i).val : ZMod N) = a i := fun i ↦ by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hdvd₁ : (N : ℤ) ∣ b₁ - ((a 0).val : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [h₁, cast_val, sub_self])
  have hdvd₂ : (N : ℤ) ∣ b₂ - ((a 1).val : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; rw [h₂, cast_val, sub_self])
  obtain ⟨k₁, hk₁⟩ := hdvd₁
  obtain ⟨k₂, hk₂⟩ := hdvd₂
  have hmem : ((k₁ : ℂ) * (τ : ℂ) + (k₂ : ℂ)) ∈ (periodPairOfTau τ).lattice :=
    PeriodPair.mem_lattice.mpr ⟨k₁, k₂, by
      simp only [periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one]⟩
  have e₁ : (b₁ : ℂ) = ((a 0).val : ℂ) + (N : ℂ) * (k₁ : ℂ) := by
    have hc : (b₁ : ℂ) - ((a 0).val : ℂ) = (N : ℂ) * (k₁ : ℂ) := by exact_mod_cast hk₁
    linear_combination hc
  have e₂ : (b₂ : ℂ) = ((a 1).val : ℂ) + (N : ℂ) * (k₂ : ℂ) := by
    have hc : (b₂ : ℂ) - ((a 1).val : ℂ) = (N : ℂ) * (k₂ : ℂ) := by exact_mod_cast hk₂
    linear_combination hc
  have step : ((b₁ : ℂ) * τ + (b₂ : ℂ)) / (N : ℂ)
      = frickeTorsionPt N a τ + ((k₁ : ℂ) * τ + (k₂ : ℂ)) := by
    unfold frickeTorsionPt; rw [e₁, e₂]; field_simp; ring
  rw [step, (periodPairOfTau τ).weierstrassP_add_coe _ ⟨_, hmem⟩]

private def frickeFn (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  frickePrefactor (periodPairOfTau τ) *
    weierstrassP (periodPairOfTau τ) (frickeTorsionPt N a τ)

private def vecMulSL (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : Fin 2 → ZMod N :=
  Matrix.vecMul a ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))

private lemma vecMulSL_apply (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (j : Fin 2) :
    vecMulSL N a γ j = a 0 * (γ 0 j : ℤ) + a 1 * (γ 1 j : ℤ) := by
  simp [vecMulSL, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.map_apply]

private theorem frickeFn_slash {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    frickeFn N a (γ • τ) = frickeFn N (vecMulSL N a γ) τ := by
  have hd : denomZ γ (τ : ℂ) ≠ 0 := denomZ_ne_zero γ τ
  have hdi : (denomZ γ τ)⁻¹ ≠ 0 := inv_ne_zero hd
  unfold frickeFn
  have hlat := periodPairOfTau_smul_lattice_eq γ τ
  rw [frickePrefactor_of_lattice_eq hlat, weierstrassP_of_lattice_eq hlat,
      frickePrefactor_smulPeriodPair,
      show frickeTorsionPt N a (γ • τ)
        = (denomZ γ τ)⁻¹ * (denomZ γ τ * frickeTorsionPt N a (γ • τ)) by
          rw [inv_mul_cancel_left₀ hd],
      weierstrassP_smulPeriodPair, inv_inv]
  rw [show ((denomZ γ τ)⁻¹ ^ 2 * frickePrefactor (periodPairOfTau τ))
          * ((denomZ γ τ) ^ 2 * weierstrassP (periodPairOfTau τ)
              (denomZ γ τ * frickeTorsionPt N a (γ • τ)))
        = frickePrefactor (periodPairOfTau τ)
          * weierstrassP (periodPairOfTau τ) (denomZ γ τ * frickeTorsionPt N a (γ • τ)) by
      field_simp]
  refine congrArg₂ (· * ·) rfl ?_
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpt : denomZ γ τ * frickeTorsionPt N a (γ • τ)
      = ((((a 0).val : ℤ) * γ 0 0 + ((a 1).val : ℤ) * γ 1 0 : ℤ) * (τ : ℂ)
          + (((a 0).val : ℤ) * γ 0 1 + ((a 1).val : ℤ) * γ 1 1 : ℤ)) / (N : ℂ) := by
    have e : denomZ γ τ * frickeTorsionPt N a (γ • τ)
        = (((a 0).val : ℂ) * numZ γ τ + ((a 1).val : ℂ) * denomZ γ τ) / (N : ℂ) := by
      unfold frickeTorsionPt; rw [coe_SL2Z_smul]; field_simp
    rw [e, numZ, denomZ]; push_cast; ring
  rw [hpt]
  refine weierstrassP_torsionPt_lift_irrel (vecMulSL N a γ) τ _ _ ?_ ?_
  · rw [vecMulSL_apply]; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id]
  · rw [vecMulSL_apply]; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id]

private theorem weierstrassP_frickeTorsionPt_slash {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    weierstrassP (periodPairOfTau (γ • τ)) (frickeTorsionPt N a (γ • τ))
      = (denomZ γ τ) ^ 2 *
          weierstrassP (periodPairOfTau τ) (frickeTorsionPt N (vecMulSL N a γ) τ) := by
  have hd := denomZ_ne_zero γ τ
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hlat := periodPairOfTau_smul_lattice_eq γ τ
  rw [weierstrassP_of_lattice_eq hlat,
      show frickeTorsionPt N a (γ • τ)
        = (denomZ γ τ)⁻¹ * (denomZ γ τ * frickeTorsionPt N a (γ • τ)) by
          rw [inv_mul_cancel_left₀ hd],
      weierstrassP_smulPeriodPair, inv_inv]
  refine congrArg (_ * ·) ?_
  have hpt : denomZ γ τ * frickeTorsionPt N a (γ • τ)
      = ((((a 0).val : ℤ) * γ 0 0 + ((a 1).val : ℤ) * γ 1 0 : ℤ) * (τ : ℂ)
          + (((a 0).val : ℤ) * γ 0 1 + ((a 1).val : ℤ) * γ 1 1 : ℤ)) / (N : ℂ) := by
    have e : denomZ γ τ * frickeTorsionPt N a (γ • τ)
        = (((a 0).val : ℂ) * numZ γ τ + ((a 1).val : ℂ) * denomZ γ τ) / (N : ℂ) := by
      unfold frickeTorsionPt; rw [coe_SL2Z_smul]; field_simp
    rw [e, numZ, denomZ]; push_cast; ring
  rw [hpt]
  refine weierstrassP_torsionPt_lift_irrel (vecMulSL N a γ) τ _ _ ?_ ?_
  · rw [vecMulSL_apply]; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id]
  · rw [vecMulSL_apply]; push_cast; simp only [ZMod.natCast_val, ZMod.cast_id]

private lemma vecMulSL_of_mem_Gamma {N : ℕ} (a : Fin 2 → ZMod N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) : vecMulSL N a γ = a := by
  obtain ⟨h₀₀, h₀₁, h₁₀, h₁₁⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  funext j
  fin_cases j <;> simp [vecMulSL_apply, h₀₀, h₀₁, h₁₀, h₁₁]

private theorem frickeFn_invariant_Gamma {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    frickeFn N a (γ • τ) = frickeFn N a τ := by
  rw [frickeFn_slash, vecMulSL_of_mem_Gamma a hγ]

private lemma weierstrassP_frickeTorsionPt_neg {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (τ : ℍ) :
    weierstrassP (periodPairOfTau τ) (frickeTorsionPt N (-a) τ)
      = weierstrassP (periodPairOfTau τ) (frickeTorsionPt N a τ) := by
  have h := weierstrassP_torsionPt_lift_irrel (N := N) (-a) τ
      (-((a 0).val : ℤ)) (-((a 1).val : ℤ))
      (by push_cast; simp [ZMod.natCast_val, ZMod.cast_id])
      (by push_cast; simp [ZMod.natCast_val, ZMod.cast_id])
  rw [← h, ← (periodPairOfTau τ).weierstrassP_neg]
  congr 1
  unfold frickeTorsionPt
  push_cast
  ring

private theorem frickeFn_neg {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (τ : ℍ) :
    frickeFn N (-a) τ = frickeFn N a τ := by
  unfold frickeFn; rw [weierstrassP_frickeTorsionPt_neg]

end B3_fricke_tier2

section B3_spelling2

open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open Matrix.SpecialLinearGroup

private lemma denom_mapGL_eq_denomZ (γ : SL(2, ℤ)) (τ : ℍ) :
    denom (mapGL ℝ γ) τ = denomZ γ τ := by
  simp [denom, denomZ]

private def wpNormZ (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ := wpNorm N (a 0).val (a 1).val τ

private lemma wpNormZ_eq (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) :
    wpNormZ N a τ = ((2 * π * I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (periodPairOfTau τ) (frickeTorsionPt N a τ) := by
  with_unfolding_all rfl

private theorem wpNormZ_slash {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    wpNormZ N a (γ • τ) = denomZ γ τ ^ 2 * wpNormZ N (vecMulSL N a γ) τ := by
  rw [wpNormZ_eq, wpNormZ_eq, weierstrassP_frickeTorsionPt_slash]
  ring

private def frickeF (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * wpNormZ N a τ

private theorem frickeF_slash {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    frickeF N a (γ • τ) = frickeF N (vecMulSL N a γ) τ := by
  have hγ : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ τ
  have h6 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₆ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  rw [CuspForm.coe_discriminant] at hΔ
  rw [show (mapGL ℝ γ) • τ = γ • τ from rfl, denom_mapGL_eq_denomZ] at h4 h6 hΔ
  have hd : denomZ γ τ ≠ 0 := denomZ_ne_zero γ τ
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  unfold frickeF
  rw [h4, h6, hΔ, wpNormZ_slash, zpow_ofNat, zpow_ofNat, zpow_ofNat]
  field_simp

private theorem frickeF_invariant_Gamma {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) : frickeF N a (γ • τ) = frickeF N a τ := by
  rw [frickeF_slash, vecMulSL_of_mem_Gamma a hγ]

private lemma vecMulSL_mul (N : ℕ) (a : Fin 2 → ZMod N) (γ δ : SL(2, ℤ)) :
    vecMulSL N a (γ * δ) = vecMulSL N (vecMulSL N a γ) δ := by
  have hmap : ((γ * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) *
        (δ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact Matrix.map_mul (f := Int.castRingHom (ZMod N))
  simp only [vecMulSL, hmap, Matrix.vecMul_vecMul]

private lemma vecMulSL_one (N : ℕ) (a : Fin 2 → ZMod N) : vecMulSL N a 1 = a := by
  simp [vecMulSL]

private def vecMulSLEquiv (N : ℕ) (γ : SL(2, ℤ)) : Equiv.Perm (Fin 2 → ZMod N) where
  toFun a := vecMulSL N a γ
  invFun a := vecMulSL N a γ⁻¹
  left_inv a := by
    change vecMulSL N (vecMulSL N a γ) γ⁻¹ = a
    rw [← vecMulSL_mul, mul_inv_cancel, vecMulSL_one]
  right_inv a := by
    change vecMulSL N (vecMulSL N a γ⁻¹) γ = a
    rw [← vecMulSL_mul, inv_mul_cancel, vecMulSL_one]

private lemma vecMulSL_zero (N : ℕ) (γ : SL(2, ℤ)) : vecMulSL N 0 γ = 0 := by
  funext j; simp [vecMulSL_apply]

private lemma vecMulSL_ne_zero {N : ℕ} {a : Fin 2 → ZMod N} (ha : a ≠ 0) (γ : SL(2, ℤ)) :
    vecMulSL N a γ ≠ 0 := by
  intro h
  apply ha
  have := congrArg (fun b ↦ vecMulSL N b γ⁻¹) h
  simpa [← vecMulSL_mul, vecMulSL_one, vecMulSL_zero] using this

private abbrev FrickeIdx (N : ℕ) : Type := {a : Fin 2 → ZMod N // a ≠ 0}

private scoped instance (N : ℕ) [NeZero N] : Fintype (FrickeIdx N) :=
    by unfold FrickeIdx; infer_instance

private def frickeIdxPerm (N : ℕ) (γ : SL(2, ℤ)) : Equiv.Perm (FrickeIdx N) :=
  (vecMulSLEquiv N γ).subtypeEquiv fun a ↦
    ⟨fun ha ↦ vecMulSL_ne_zero ha γ, fun h ha ↦ h (by rw [ha]; exact vecMulSL_zero N γ)⟩

private theorem frickeF_hperm {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) :
    ∃ σ : Equiv.Perm (FrickeIdx N), ∀ (i : FrickeIdx N) (τ : ℍ),
      frickeF N i.1 (γ • τ) = frickeF N (σ i).1 τ :=
  ⟨frickeIdxPerm N γ, fun i τ ↦ frickeF_slash i.1 γ τ⟩

private lemma frickeIdx_hyps {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    (i.1 0).val < N ∧ (i.1 1).val < N ∧ ((i.1 0).val ≠ 0 ∨ (i.1 1).val ≠ 0) := by
  refine ⟨ZMod.val_lt _, ZMod.val_lt _, ?_⟩
  by_contra h
  push Not at h
  apply i.2
  funext j
  fin_cases j
  · exact (ZMod.val_eq_zero _).mp h.1
  · exact (ZMod.val_eq_zero _).mp h.2

private theorem frickeF_mul_discriminant {N : ℕ} (a : Fin 2 → ZMod N) (τ : ℍ) :
    frickeF N a τ * CuspForm.discriminant τ = -(frickeH N (a 0).val (a 1).val τ) / 2592 := by
  rw [CuspForm.coe_discriminant]
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  simp only [frickeF, frickeH, wpNormZ, Pi.mul_apply]
  field_simp

private theorem mdifferentiable_frickeF {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (frickeF N i.1) := by
  obtain ⟨h1, h2, h0⟩ := frickeIdx_hyps i
  have hW : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpNormZ N i.1) := mdifferentiable_wpNorm h1 h2 h0
  have hE : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ ↦ ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) :=
    (ModularForm.E₄.holo'.mul ModularForm.E₆.holo').div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  have hc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun _ : ℍ ↦ (-1 / 2592 : ℂ)) := mdifferentiable_const
  have heq : frickeF N i.1 = (fun _ : ℍ ↦ (-1 / 2592 : ℂ)) *
      (fun τ ↦ ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) *
        wpNormZ N i.1 := by
    funext τ
    simp only [frickeF, Pi.mul_apply]
    ring
  rw [heq]
  exact (hc.mul hE).mul hW

private theorem isBoundedAtImInfty_frickeF_mul_discriminant {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    IsBoundedAtImInfty (frickeF N i.1 * ⇑CuspForm.discriminant) := by
  obtain ⟨h1, h2, h0⟩ := frickeIdx_hyps i
  have hH := isBoundedAtImInfty_frickeH h1 h2 h0
  have : (frickeF N i.1 * ⇑CuspForm.discriminant : ℍ → ℂ) =
      fun τ ↦ (-1 / 2592 : ℂ) * frickeH N (i.1 0).val (i.1 1).val τ := by
    funext τ
    rw [Pi.mul_apply, frickeF_mul_discriminant]
    ring
  rw [this]
  exact hH.const_mul_left _

private lemma qExpansion_E4E6_coeff_zero {N : ℕ} (hN : N ≠ 0) :
    (qExpansion N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ)).coeff 0 = 1 := by
  have hper : Function.Periodic ((⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ∘ ofComplex) 1 := by
    have h4 := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL
    have h6 := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL
    intro τ
    have e4 := h4 τ
    have e6 := h6 τ
    simp only [Function.comp_apply, Pi.mul_apply, Complex.ofReal_one] at e4 e6 ⊢
    rw [e4, e6]
  rw [qExpansion_coeff_width _ hN hper (ModularForm.E₄.holo'.mul ModularForm.E₆.holo')
    ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
      (ModularFormClass.bdd_at_infty ModularForm.E₆)) 0,
    ite_eq_left (dvd_zero N), Nat.zero_div,
    ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_zero_eq_constantCoeff, map_mul, ← PowerSeries.coeff_zero_eq_constantCoeff,
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide),
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) (by decide), mul_one]

private lemma qExpansion_wpNorm_eq_of_frickeH_eq {N a₁ a₂ b₁ b₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (ha0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (hb₁ : b₁ < N) (hb₂ : b₂ < N) (hb0 : b₁ ≠ 0 ∨ b₂ ≠ 0)
    (h : frickeH N a₁ a₂ = frickeH N b₁ b₂) :
    qExpansion N (wpNorm N a₁ a₂) = qExpansion N (wpNorm N b₁ b₂) := by
  have hN : N ≠ 0 := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperE : Function.Periodic ((⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ∘ ofComplex) N := by
    have h4 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL).nat_mul N
    have h6 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL).nat_mul N
    intro τ
    have e4 := h4 τ; have e6 := h6 τ
    simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6
    simp only [Function.comp_apply, Pi.mul_apply, e4, e6]
  have hE : AnalyticAt ℂ (cuspFunction N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ)) 0 :=
    analyticAt_cuspFunction_zero hN' hperE (ModularForm.E₄.holo'.mul ModularForm.E₆.holo')
      ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
        (ModularFormClass.bdd_at_infty ModularForm.E₆))
  have hWa : AnalyticAt ℂ (cuspFunction N (wpNorm N a₁ a₂)) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm ha₁ ha₂ ha0)
      (mdifferentiable_wpNorm ha₁ ha₂ ha0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ ha0)
  have hWb : AnalyticAt ℂ (cuspFunction N (wpNorm N b₁ b₂)) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm hb₁ hb₂ hb0)
      (mdifferentiable_wpNorm hb₁ hb₂ hb0) (isBoundedAtImInfty_wpNorm hb₁ hb₂ hb0)
  have hq := congrArg (qExpansion (N : ℝ)) h
  rw [frickeH, frickeH, qExpansion_mul hE hWa, qExpansion_mul hE hWb] at hq
  have hne : qExpansion N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ≠ 0 := by
    intro h0
    have := qExpansion_E4E6_coeff_zero hN
    rw [h0, map_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne hq

private lemma qExpansion_E4E6_rat {N : ℕ} (hN : N ≠ 0) (n : ℕ) :
    ∃ q : ℚ, (qExpansion N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ)).coeff n = (q : ℂ) := by
  have hper : Function.Periodic ((⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ∘ ofComplex) 1 := by
    have h4 := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL
    have h6 := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL
    intro τ
    have e4 := h4 τ
    have e6 := h6 τ
    simp only [Function.comp_apply, Pi.mul_apply, Complex.ofReal_one] at e4 e6 ⊢
    rw [e4, e6]
  rw [qExpansion_coeff_width _ hN hper (ModularForm.E₄.holo'.mul ModularForm.E₆.holo')
    ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
      (ModularFormClass.bdd_at_infty ModularForm.E₆)) n]
  by_cases hdvd : N ∣ n
  · rw [ite_eq_left hdvd, ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL,
      PowerSeries.coeff_mul]
    refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n / N),
      (qExpansion_one_E4_rat p.1).choose * (qExpansion_one_E6_rat p.2).choose, ?_⟩
    push_cast
    exact Finset.sum_congr rfl fun p _ =>
      congrArg₂ (· * ·) (qExpansion_one_E4_rat p.1).choose_spec
        (qExpansion_one_E6_rat p.2).choose_spec
  · exact ⟨0, by rw [ite_eq_right hdvd]; norm_num⟩

private theorem qExpansion_frickeH_coeff_mem_kN {N a₁ a₂ : ℕ} (ha₁ : a₁ < N) (ha₂ : a₂ < N)
    (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) :
    (qExpansion N (frickeH N a₁ a₂)).coeff n ∈ kN N := by
  have hN : N ≠ 0 := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hperE : Function.Periodic ((⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ∘ ofComplex) N := by
    have h4 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL).nat_mul N
    have h6 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL).nat_mul N
    intro τ
    have e4 := h4 τ
    have e6 := h6 τ
    simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6
    simp only [Function.comp_apply, Pi.mul_apply, e4, e6]
  have hE : AnalyticAt ℂ (cuspFunction N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ)) 0 :=
    analyticAt_cuspFunction_zero hN' hperE (ModularForm.E₄.holo'.mul ModularForm.E₆.holo')
      ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
        (ModularFormClass.bdd_at_infty ModularForm.E₆))
  have hW : AnalyticAt ℂ (cuspFunction N (wpNorm N a₁ a₂)) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm ha₁ ha₂ h0)
      (mdifferentiable_wpNorm ha₁ ha₂ h0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ h0)
  rw [frickeH, qExpansion_mul hE hW, PowerSeries.coeff_mul]
  refine sum_mem fun ij _ ↦ mul_mem ?_ (qExpansion_wpNorm_coeff_mem_kN ha₁ ha₂ h0 _)
  obtain ⟨q, hq⟩ := qExpansion_E4E6_rat hN ij.1
  rw [hq, ← SubfieldClass.coe_ratCast (kN N) q]
  exact SetLike.coe_mem _

private lemma qExpansion_frickeH_conj {N : ℕ} [NeZero N] {s : ℕ} (hs : s.Coprime N)
    (φ : ↑(kN N) →+* ℂ) (hφ : φ ⟨zetaN N, zetaN_mem_kN N⟩ = zetaN N ^ s)
    {a₁ a₂ : ℕ} (h1 : a₁ < N) (h2 : a₂ < N) (h0 : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ)
    (z : ↑(kN N)) (hz : (z : ℂ) = (qExpansion N (frickeH N a₁ a₂)).coeff n) :
    (qExpansion N (frickeH N a₁ (s * a₂ % N))).coeff n = φ z := by
  have hN : N ≠ 0 := NeZero.ne N
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have h2' : s * a₂ % N < N := Nat.mod_lt _ (Nat.pos_of_ne_zero hN)
  have h0' : a₁ ≠ 0 ∨ s * a₂ % N ≠ 0 := by
    rcases h0 with h | h
    · exact Or.inl h
    · refine Or.inr fun hmod => h ?_
      have hdvd0 : N ∣ s * a₂ := Nat.dvd_of_mod_eq_zero hmod
      have hdvd : N ∣ a₂ := Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hs) hdvd0
      exact Nat.eq_zero_of_dvd_of_lt hdvd h2
  obtain ⟨S, hSmap, hSconj⟩ := wpNorm_qExpansion_model hN
  have hESm := qExpansion_E4E6_rat hN
  have hESmap : (PowerSeries.mk fun m => (((hESm m).choose : ℚ) : ↑(kN N))).map
      (algebraMap ↑(kN N) ℂ) = qExpansion N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_ratCast]
    exact ((hESm m).choose_spec).symm
  have hESφ : (PowerSeries.mk fun m => (((hESm m).choose : ℚ) : ↑(kN N))).map φ =
      qExpansion N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) := by
    ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_ratCast]
    exact ((hESm m).choose_spec).symm
  have hperE : Function.Periodic ((⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ) ∘ ofComplex) N := by
    have h4 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL).nat_mul N
    have h6 := (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆
      one_mem_strictPeriods_SL).nat_mul N
    intro τ
    have e4 := h4 τ
    have e6 := h6 τ
    simp only [Complex.ofReal_one, mul_one, Function.comp_apply] at e4 e6
    simp only [Function.comp_apply, Pi.mul_apply, e4, e6]
  have hE : AnalyticAt ℂ (cuspFunction N (⇑ModularForm.E₄ * ⇑ModularForm.E₆ : ℍ → ℂ)) 0 :=
    analyticAt_cuspFunction_zero hN' hperE (ModularForm.E₄.holo'.mul ModularForm.E₆.holo')
      ((ModularFormClass.bdd_at_infty ModularForm.E₄).mul
        (ModularFormClass.bdd_at_infty ModularForm.E₆))
  have hWa : AnalyticAt ℂ (cuspFunction N (wpNorm N a₁ a₂)) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm h1 h2 h0)
      (mdifferentiable_wpNorm h1 h2 h0) (isBoundedAtImInfty_wpNorm h1 h2 h0)
  have hWa' : AnalyticAt ℂ (cuspFunction N (wpNorm N a₁ (s * a₂ % N))) 0 :=
    analyticAt_cuspFunction_zero hN' (periodic_wpNorm h1 h2' h0')
      (mdifferentiable_wpNorm h1 h2' h0') (isBoundedAtImInfty_wpNorm h1 h2' h0')
  have hHa : qExpansion N (frickeH N a₁ a₂) =
      ((PowerSeries.mk fun m => (((hESm m).choose : ℚ) : ↑(kN N))) * S a₁ a₂).map
        (algebraMap ↑(kN N) ℂ) := by
    rw [frickeH, qExpansion_mul hE hWa, map_mul, hESmap, hSmap a₁ a₂ h1 h2 h0]
  have hHa' : qExpansion N (frickeH N a₁ (s * a₂ % N)) =
      ((PowerSeries.mk fun m => (((hESm m).choose : ℚ) : ↑(kN N))) * S a₁ a₂).map φ := by
    rw [frickeH, qExpansion_mul hE hWa', map_mul, hESφ, hSconj s hs φ hφ a₁ a₂ h1 h2 h0]
  have hz2 : z = ((PowerSeries.mk fun m => (((hESm m).choose : ℚ) : ↑(kN N))) * S a₁ a₂).coeff n :=
      by
    have hinj : Function.Injective (algebraMap ↑(kN N) ℂ) := (algebraMap ↑(kN N) ℂ).injective
    apply hinj
    rw [← PowerSeries.coeff_map, ← hHa]
    exact_mod_cast hz
  rw [hHa', PowerSeries.coeff_map, ← hz2]

private theorem frickeF_eq_imp {N : ℕ} [NeZero N] (a b : FrickeIdx N)
    (h : frickeF N a.1 = frickeF N b.1) : b.1 = a.1 ∨ b.1 = -a.1 := by
  obtain ⟨ha₁, ha₂, ha0⟩ := frickeIdx_hyps a
  obtain ⟨hb₁, hb₂, hb0⟩ := frickeIdx_hyps b
  have hH : frickeH N (a.1 0).val (a.1 1).val = frickeH N (b.1 0).val (b.1 1).val := by
    funext τ
    have e := congrFun h τ
    have ea := frickeF_mul_discriminant a.1 τ
    have eb := frickeF_mul_discriminant b.1 τ
    rw [e] at ea
    rw [ea] at eb
    linear_combination (-2592) * eb
  have hq := qExpansion_wpNorm_eq_of_frickeH_eq ha₁ ha₂ ha0 hb₁ hb₂ hb0 hH
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hfun : wpNorm N (a.1 0).val (a.1 1).val = wpNorm N (b.1 0).val (b.1 1).val := by
    funext τ
    have hsa := hasSum_qExpansion hNpos (periodic_wpNorm ha₁ ha₂ ha0)
      (mdifferentiable_wpNorm ha₁ ha₂ ha0) (isBoundedAtImInfty_wpNorm ha₁ ha₂ ha0) τ
    have hsb := hasSum_qExpansion hNpos (periodic_wpNorm hb₁ hb₂ hb0)
      (mdifferentiable_wpNorm hb₁ hb₂ hb0) (isBoundedAtImInfty_wpNorm hb₁ hb₂ hb0) τ
    rw [← hq] at hsb
    exact hsa.unique hsb
  rcases wpNorm_eq_imp ha₁ ha₂ ha0 hb₁ hb₂ hb0 hfun with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · left
    have f0 : b.1 0 = a.1 0 := ZMod.val_injective N e0
    have f1 : b.1 1 = a.1 1 := ZMod.val_injective N e1
    funext j
    fin_cases j <;> simp [f0, f1]
  · right
    have f0 : b.1 0 = -a.1 0 := ZMod.val_injective N (by rw [e0, ZMod.neg_val'])
    have f1 : b.1 1 = -a.1 1 := ZMod.val_injective N (by rw [e1, ZMod.neg_val'])
    funext j
    fin_cases j <;> simp [f0, f1]

private theorem mem_Gamma_or_neg_mem_of_vecMulSL {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (h : ∀ a : Fin 2 → ZMod N, a ≠ 0 → vecMulSL N a γ = a ∨ vecMulSL N a γ = -a) :
    γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N := by
  rcases Nat.lt_or_ge 1 N with hN | hN
  · have : Fact (1 < N) := ⟨hN⟩
    have h10 : (1 : ZMod N) ≠ 0 := one_ne_zero
    have r1 := h ![1, 0] (fun e ↦ h10 (by simpa using congrFun e 0))
    have r2 := h ![0, 1] (fun e ↦ h10 (by simpa using congrFun e 1))
    have r3 := h ![1, 1] (fun e ↦ h10 (by simpa using congrFun e 0))
    simp only [funext_iff, Fin.forall_fin_two, vecMulSL_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero, zero_add,
      Pi.neg_apply, neg_zero] at r1 r2 r3
    have e01 : ((γ 0 1 : ℤ) : ZMod N) = 0 := by rcases r1 with ⟨_, e⟩ | ⟨_, e⟩ <;> exact e
    have e10 : ((γ 1 0 : ℤ) : ZMod N) = 0 := by rcases r2 with ⟨e, _⟩ | ⟨e, _⟩ <;> exact e
    have e0011 : ((γ 0 0 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) := by
      rcases r3 with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
        (rw [e10, add_zero] at c1; rw [e01, zero_add] at c2; rw [c1, c2])
    rw [CongruenceSubgroup.Gamma_mem, CongruenceSubgroup.Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero]
    rcases r1 with ⟨a1, _⟩ | ⟨a1, _⟩
    · left; exact ⟨a1, e01, e10, by rw [← e0011]; exact a1⟩
    · right; exact ⟨by rw [a1, neg_neg], e01, e10, by rw [← e0011, a1, neg_neg]⟩
  · have : N = 1 := by have := NeZero.ne N; omega
    subst this
    left
    simp [CongruenceSubgroup.Gamma_one_top]

private theorem frickeF_faithful {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (h : ∀ i : FrickeIdx N, ∀ τ : ℍ, frickeF N i.1 (γ • τ) = frickeF N i.1 τ) :
    γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N := by
  refine mem_Gamma_or_neg_mem_of_vecMulSL γ fun a ha ↦ ?_
  have hfun : frickeF N a = frickeF N (vecMulSL N a γ) := by
    funext τ; rw [← frickeF_slash, h ⟨a, ha⟩ τ]
  rcases frickeF_eq_imp ⟨a, ha⟩ ⟨vecMulSL N a γ, vecMulSL_ne_zero ha γ⟩ hfun with e | e
  · exact Or.inl e
  · exact Or.inr e

end B3_spelling2

section R4aBridge

open Aux
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

private lemma periodPair_ext' {L₁ L₂ : PeriodPair} (h₁ : L₁.ω₁ = L₂.ω₁)
    (h₂ : L₁.ω₂ = L₂.ω₂) : L₁ = L₂ := by
  cases L₁; cases L₂; simp_all

end R4aBridge

end Aux
open scoped FrickeFunctions.FrickeModularity.Aux

section NamedResults

open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm
open Aux

variable (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)

omit [NeZero N] in
include hL hW hfricke in
private theorem fricke_eq_frickeF : fricke = frickeF N := by
  have hLpp : ∀ τ : ℍ, L τ = periodPairOfTau τ := fun τ =>
    periodPair_ext' ((hL τ).1.trans (periodPairOfTau_ω₁ τ).symm)
      ((hL τ).2.trans (periodPairOfTau_ω₂ τ).symm)
  funext v τ
  rw [hfricke, hW, hLpp τ]
  with_unfolding_all rfl

omit [NeZero N] in
include hL hW hfricke in
private theorem fricke_mul_discriminant_eq (v : Fin 2 → ZMod N) :
    (fricke v * ModularForm.discriminant : ℍ → ℂ) =
      (-(1 / 2592) : ℂ) • frickeH N (v 0).val (v 1).val := by
  rw [fricke_eq_frickeF N L hL W hW fricke hfricke]
  funext τ
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [show ModularForm.discriminant τ = (⇑CuspForm.discriminant) τ from
    (congrFun CuspForm.coe_discriminant τ).symm, frickeF_mul_discriminant]
  ring

include hL hW hfricke in
public theorem _root_.ModularForm.frickeFunction_smul (v : Fin 2 → ZMod N) (γ : SL(2, ℤ))
    (τ : ℍ) :
    fricke v (γ • τ) =
      fricke (Matrix.vecMul v ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))) τ := by
  rw [fricke_eq_frickeF N L hL W hW fricke hfricke]
  exact frickeF_slash v γ τ

include hL hW hfricke in
public theorem _root_.ModularForm.frickeFunction_neg (v : Fin 2 → ZMod N) :
    fricke (-v) = fricke v := by
  rw [fricke_eq_frickeF N L hL W hW fricke hfricke]
  funext τ
  simp only [frickeF]
  refine congrArg₂ (· * ·) rfl ?_
  rw [wpNormZ_eq, wpNormZ_eq, weierstrassP_frickeTorsionPt_neg]

include hL hW hfricke in
public theorem _root_.ModularForm.mdifferentiable_frickeFunction {v : Fin 2 → ZMod N}
    (hv : v ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) := by
  rw [fricke_eq_frickeF N L hL W hW fricke hfricke]
  exact mdifferentiable_frickeF ⟨v, hv⟩

include hL hW hfricke in
public theorem _root_.ModularForm.isBoundedAtImInfty_frickeFunction_mul_discriminant
    {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    IsBoundedAtImInfty (fricke v * ModularForm.discriminant) := by
  rw [fricke_eq_frickeF N L hL W hW fricke hfricke, ← CuspForm.coe_discriminant]
  exact isBoundedAtImInfty_frickeF_mul_discriminant ⟨v, hv⟩

include hL hW hfricke in
public theorem _root_.ModularForm.periodic_frickeFunction_mul_discriminant
    {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    Function.Periodic ((fricke v * ModularForm.discriminant) ∘ ofComplex) N := by
  obtain ⟨h1, h2, h0⟩ := frickeIdx_hyps (⟨v, hv⟩ : FrickeIdx N)
  rw [fricke_mul_discriminant_eq N L hL W hW fricke hfricke]
  intro x
  have hx := periodic_frickeH h1 h2 h0 x
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢
  rw [hx]

include hL hW hfricke in
public theorem _root_.ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_mem
    {v : Fin 2 → ZMod N} (hv : v ≠ 0) (n : ℕ) :
    (qExpansion N (fricke v * ModularForm.discriminant)).coeff n ∈
      IntermediateField.adjoin ℚ {cexp (2 * π * I / N)} := by
  obtain ⟨h1, h2, h0⟩ := frickeIdx_hyps (⟨v, hv⟩ : FrickeIdx N)
  rw [fricke_mul_discriminant_eq N L hL W hW fricke hfricke, qExpansion_smul
      (analyticAt_cuspFunction_zero_of (mdifferentiable_frickeH h1 h2 h0)
        (periodic_frickeH h1 h2 h0) (isBoundedAtImInfty_frickeH h1 h2 h0)),
    PowerSeries.coeff_smul, smul_eq_mul]
  refine mul_mem ?_ (qExpansion_frickeH_coeff_mem_kN h1 h2 h0 n)
  show ((-(1 / 2592) : ℂ)) ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * ↑Real.pi * Complex.I
      / N)}
  simp

include hL hW hfricke in
public theorem _root_.ModularForm.eq_or_eq_neg_of_frickeFunction_eq {v w : Fin 2 → ZMod N}
    (hv : v ≠ 0) (hw : w ≠ 0) (h : fricke v = fricke w) : w = v ∨ w = -v := by
  rw [fricke_eq_frickeF N L hL W hW fricke hfricke] at h
  exact frickeF_eq_imp ⟨v, hv⟩ ⟨w, hw⟩ h

include hL hW hfricke in
public theorem _root_.ModularForm.frickeFunction_smul_of_mem_Gamma (v : Fin 2 → ZMod N)
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    fricke v (γ • τ) = fricke v τ := by
  rw [fricke_eq_frickeF N L hL W hW fricke hfricke]
  exact frickeF_invariant_Gamma v hγ τ

include hL hW hfricke in
public theorem _root_.ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_sigmaTransport
    {s : ℕ} (hs : s.Coprime N)
    (φ : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}) →+* ℂ)
    (hφ : ∀ z : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}),
      (z : ℂ) = cexp (2 * π * I / N) → φ z = cexp (2 * π * I / N) ^ s)
    {v : Fin 2 → ZMod N} (hv : v ≠ 0) (n : ℕ)
    (z : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}))
    (hz : (z : ℂ) = (qExpansion N (fricke v * ModularForm.discriminant)).coeff n) :
    (qExpansion N (fricke ![v 0, (s : ZMod N) * v 1] * ModularForm.discriminant)).coeff n =
      φ z := by
  obtain ⟨h1, h2, h0⟩ := frickeIdx_hyps (⟨v, hv⟩ : FrickeIdx N)
  have hN : N ≠ 0 := NeZero.ne N
  have h2' : s * (v 1).val % N < N := Nat.mod_lt _ (Nat.pos_of_ne_zero hN)
  have h0' : (v 0).val ≠ 0 ∨ s * (v 1).val % N ≠ 0 := by
    rcases h0 with h | h
    · exact Or.inl h
    · refine Or.inr fun hmod => h ?_
      have hdvd0 : N ∣ s * (v 1).val := Nat.dvd_of_mod_eq_zero hmod
      have hdvd : N ∣ (v 1).val :=
        Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hs) hdvd0
      exact Nat.eq_zero_of_dvd_of_lt hdvd h2
  have hval : ((s : ZMod N) * v 1).val = s * (v 1).val % N := by
    rw [ZMod.val_mul, ZMod.val_natCast]
    exact Nat.mod_mul_mod s (v 1).val N
  have hφg : φ ⟨zetaN N, zetaN_mem_kN N⟩ = zetaN N ^ s :=
    hφ ⟨zetaN N, zetaN_mem_kN N⟩ rfl
  have hshA' : (fricke ![v 0, (s : ZMod N) * v 1] * ModularForm.discriminant : ℍ → ℂ) =
      (-(1 / 2592) : ℂ) • frickeH N (v 0).val (s * (v 1).val % N) := by
    rw [fricke_mul_discriminant_eq N L hL W hW fricke hfricke]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hval]
  have hanA := analyticAt_cuspFunction_zero_of (mdifferentiable_frickeH h1 h2 h0)
    (periodic_frickeH h1 h2 h0) (isBoundedAtImInfty_frickeH h1 h2 h0)
  have hanA' := analyticAt_cuspFunction_zero_of (mdifferentiable_frickeH h1 h2' h0')
    (periodic_frickeH h1 h2' h0') (isBoundedAtImInfty_frickeH h1 h2' h0')
  rw [fricke_mul_discriminant_eq N L hL W hW fricke hfricke, qExpansion_smul hanA,
    PowerSeries.coeff_smul, smul_eq_mul] at hz
  rw [hshA', qExpansion_smul hanA', PowerSeries.coeff_smul, smul_eq_mul]
  have hmem := qExpansion_frickeH_coeff_mem_kN h1 h2 h0 n
  have htr := qExpansion_frickeH_conj hs φ hφg h1 h2 h0 n
    (⟨_, hmem⟩ : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)})) rfl
  have hzrel : z = ((-(1/2592) : ℚ) : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)})) *
      ⟨_, hmem⟩ := by
    apply Subtype.coe_injective
    change (z : ℂ) = ((-(1/2592) : ℚ) : ℂ) *
      (qExpansion N (frickeH N (v 0).val (v 1).val)).coeff n
    rw [hz]
    push_cast
    ring
  have hφz : φ z = ((-(1/2592) : ℚ) : ℂ) * φ ⟨_, hmem⟩ := by
    rw [hzrel, map_mul, map_ratCast]
  rw [htr, hφz]
  push_cast
  rfl

end NamedResults

open UpperHalfPlane hiding I in
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm in
open Aux in
/-- Modularity of the Fricke functions `f_a`, `a : Fin 2 → ZMod N`: `SL(2, ℤ)` acts by `f_a (γ • τ)
= f_{a γ} τ`; `f_{-a} = f_a`; for `a ≠ 0`, `f_a` is holomorphic, `f_a Δ` is bounded at `i∞`,
`N`-periodic and has q-coefficients in `ℚ(ζ_N)`; `f_a = f_b` forces `b = ± a`; each `f_a` is
`Γ(N)`-invariant; and an embedding of `ℚ(ζ_N)` with `ζ_N ↦ ζ_N ^ s` (`s` coprime to `N`) maps
the q-coefficients of `f_a Δ` to those of `f_{(a₀, s a₁)} Δ`. -/
public theorem _root_.ModularForm.frickeFunction_modularity_package (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) :
    let f : (Fin 2 → ZMod N) → ℍ → ℂ := fun a τ =>
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
        (((2 * π * I) ^ 2)⁻¹ *
          PeriodPair.weierstrassP (L τ)
            ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ)))
    (∀ (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ), f a (γ • τ) =
        f (Matrix.vecMul a ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))) τ) ∧
    (∀ a : Fin 2 → ZMod N, f (-a) = f a) ∧
    (∀ a : Fin 2 → ZMod N, a ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f a)) ∧
    (∀ a : Fin 2 → ZMod N, a ≠ 0 →
      IsBoundedAtImInfty (f a * ModularForm.discriminant)) ∧
    (∀ a : Fin 2 → ZMod N, a ≠ 0 →
      Function.Periodic ((f a * ModularForm.discriminant) ∘ ofComplex) N ∧
      ∀ n : ℕ, (qExpansion N (f a * ModularForm.discriminant)).coeff n ∈
        IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}) ∧
    (∀ a b : Fin 2 → ZMod N, a ≠ 0 → b ≠ 0 → f a = f b → b = a ∨ b = -a) ∧
    (∀ a : Fin 2 → ZMod N, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ,
      f a (γ • τ) = f a τ) ∧
    (∀ s : ℕ, s.Coprime N →
      ∀ φ : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}) →+* ℂ,
        (∀ z : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)}),
            (z : ℂ) = cexp (2 * π * I / N) → φ z = cexp (2 * π * I / N) ^ s) →
        ∀ a : Fin 2 → ZMod N, a ≠ 0 →
          ∀ (n : ℕ) (z : ↑(IntermediateField.adjoin ℚ {cexp (2 * π * I / N)})),
            (z : ℂ) = (qExpansion N (f a * ModularForm.discriminant)).coeff n →
            (qExpansion N (f ![a 0,
                (s : ZMod N) * a 1] * ModularForm.discriminant)).coeff n = φ z) := by
  intro f
  let W : (Fin 2 → ZMod N) → ℍ → ℂ := fun a τ => ((2 * π * I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (L τ) ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ))
  have hW : ∀ (a : Fin 2 → ZMod N) (τ : ℍ), W a τ = ((2 * π * I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ)) :=
    fun _ _ => rfl
  have hf : ∀ (a : Fin 2 → ZMod N) (τ : ℍ), f a τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W a τ :=
    fun _ _ => rfl
  exact ⟨ModularForm.frickeFunction_smul N L hL W hW f hf,
    ModularForm.frickeFunction_neg N L hL W hW f hf,
    fun _ ha => ModularForm.mdifferentiable_frickeFunction N L hL W hW f hf ha,
    fun _ ha =>
      ModularForm.isBoundedAtImInfty_frickeFunction_mul_discriminant N L hL W hW f hf ha,
    fun _ ha => ⟨ModularForm.periodic_frickeFunction_mul_discriminant N L hL W hW f hf ha,
      ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_mem N L hL W hW f hf ha⟩,
    fun _ _ ha hb => ModularForm.eq_or_eq_neg_of_frickeFunction_eq N L hL W hW f hf ha hb,
    fun a _ hγ τ => ModularForm.frickeFunction_smul_of_mem_Gamma N L hL W hW f hf a hγ τ,
    fun _ hs φ hφ _ ha n z hz =>
      ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_sigmaTransport
        N L hL W hW f hf hs φ hφ ha n z hz⟩

end

end FrickeModularity

end FrickeFunctions
