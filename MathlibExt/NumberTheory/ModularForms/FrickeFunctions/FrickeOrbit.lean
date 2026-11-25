/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_frickeFunction_orbit_package.lean`
and
`P2M/Sol/S_WLight_frickeFunction_orbit_package.lean`
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
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.FrickeModularity
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.LevelOneHauptmodul
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.WeierstrassPTorsionQExpansion

/-!
# Orbit polynomials of the Fricke functions

This file builds the orbit polynomial of the Fricke functions over `ℚ(ζ_N)[j]`. Throughout, `j
= E₄³ / Δ` and, for `v : Fin 2 → ZMod N`, the Fricke function is `f_v τ = -(E₄ τ E₆ τ / Δ τ) /
2592 · (2πi)⁻² ℘_τ((v₀ τ + v₁) / N)`, where `℘_τ` is the Weierstrass function of the lattice
`ℤτ + ℤ`.

## Main statement

* `ModularForm.frickeFunction_orbit_package`
-/
namespace FrickeFunctions.FrickeOrbit

noncomputable section

open Complex Real
namespace Aux
open Aux

section R4bFloor
open scoped UpperHalfPlane Manifold MatrixGroups
open UpperHalfPlane hiding I
open ModularForm
open ModularFormClass
open CuspForm
open Polynomial
open Real.Polynomial
open Filter
variable {N : ℕ}

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

private def j : ℍ → ℂ := fun z => E₄ z ^ 3 / ModularForm.discriminant z

private def frickeTorsionPt (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  (((a 0).val : ℂ) * (τ : ℂ) + ((a 1).val : ℂ)) / (N : ℂ)

private def vecMulSL (N : ℕ) (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : Fin 2 → ZMod N :=
  Matrix.vecMul a ((γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N))

private def wpNormZ (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ := wpNorm N (a 0).val (a 1).val τ

private def frickeF (N : ℕ) (a : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * wpNormZ N a τ

private abbrev FrickeIdx (N : ℕ) : Type := {a : Fin 2 → ZMod N // a ≠ 0}

private def KPoleAt (K : IntermediateField ℚ ℂ) (N m : ℕ) (f : ℍ → ℂ) : Prop :=
  Function.Periodic ((f * ⇑CuspForm.discriminant ^ m) ∘ ofComplex) N ∧
    IsBoundedAtImInfty (f * ⇑CuspForm.discriminant ^ m) ∧
    ∀ n : ℕ, (qExpansion N (f * ⇑CuspForm.discriminant ^ m)).coeff n ∈ K

private def KPole (K : IntermediateField ℚ ℂ) (N : ℕ) (f : ℍ → ℂ) : Prop :=
  MDiff f ∧ ∃ m : ℕ, KPoleAt K N m f

open UpperHalfPlane hiding I

private scoped instance slFnAction : MulSemiringAction SL(2, ℤ) (ℍ → ℂ) where
  smul γ f := fun τ ↦ f (γ⁻¹ • τ)
  one_smul f := by funext τ; change f ((1 : SL(2, ℤ))⁻¹ • τ) = f τ; rw [inv_one, one_smul]
  mul_smul γ δ f := by
    funext τ
    change f ((γ * δ)⁻¹ • τ) = f (δ⁻¹ • (γ⁻¹ • τ))
    rw [mul_inv_rev, mul_smul]
  smul_zero γ := rfl
  smul_add γ f g := rfl
  smul_one γ := rfl
  smul_mul γ f g := rfl

private lemma sl_smul_apply (γ : SL(2, ℤ)) (f : ℍ → ℂ) (τ : ℍ) : (γ • f) τ = f (γ⁻¹ • τ) := rfl

private lemma sl_smul_def (γ : SL(2, ℤ)) (f : ℍ → ℂ) : γ • f = fun τ ↦ f (γ⁻¹ • τ) := rfl

private scoped instance slFn_smulCommClass : SMulCommClass SL(2, ℤ) ℂ (ℍ → ℂ) where
  smul_comm _ _ _ := rfl

private lemma sl_smul_const (γ : SL(2, ℤ)) (c : ℂ) : γ • (fun _ : ℍ ↦ c) = fun _ ↦ c := rfl

private lemma sl_smul_eq_self_iff (f : ℍ → ℂ) :
    (∀ γ : SL(2, ℤ), γ • f = f) ↔ ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ := by
  constructor
  · intro h γ τ
    have := congrFun (h γ⁻¹) τ
    rwa [sl_smul_apply, inv_inv] at this
  · intro h γ
    funext τ
    rw [sl_smul_apply, h]

private def levelGen (N : ℕ) : Set (ℍ → ℂ) :=
    insert j (Set.range fun i : FrickeIdx N ↦ frickeF N i.1)

private lemma hppT : ∀ τ : ℍ, (periodPairOfTau τ).ω₁ = (τ : ℂ) ∧ (periodPairOfTau τ).ω₂ = 1 :=
  fun τ => ⟨periodPairOfTau_ω₁ τ, periodPairOfTau_ω₂ τ⟩

private lemma coe_cuspDisc : ⇑CuspForm.discriminant = ModularForm.discriminant := rfl

private lemma hW_wpNormZ (N : ℕ) : ∀ (v : Fin 2 → ZMod N) (τ : ℍ),
    wpNormZ N v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (periodPairOfTau τ)
        ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)) :=
  fun _ _ => rfl

private lemma hfricke_frickeF (N : ℕ) : ∀ (v : Fin 2 → ZMod N) (τ : ℍ),
    frickeF N v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 *
        wpNormZ N v τ :=
  fun _ _ => rfl

private theorem levelOne_holFn_eq_polynomial_j (m : ℕ) (h : ℍ → ℂ) (hol : MDiff h)
    (hinv : ∀ γ : SL(2, ℤ), h ∣[(0 : ℤ)] γ = h)
    (hbd : IsBoundedAtImInfty (h * ⇑CuspForm.discriminant ^ m)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧ h = fun z => Polynomial.eval (j z) P := by
  rw [coe_cuspDisc] at hbd
  obtain ⟨P, hdeg, heq⟩ := ModularForm.levelOne_hauptmodul_package.1 m h hol hinv hbd
  exact ⟨P, hdeg, by simpa only [j] using heq⟩

private theorem kPole_invariant_eq_polynomial_j_mem {K : IntermediateField ℚ ℂ} [NeZero N]
    {a : ℍ → ℂ} (hk : KPole K N a) (hinv : ∀ γ : SL(2, ℤ), a ∣[(0 : ℤ)] γ = a) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ K) ∧ a = fun τ => Polynomial.eval (j τ) P := by
  obtain ⟨hmd, m, hper, hbd, hcoef⟩ := hk
  rw [coe_cuspDisc] at hper hbd hcoef
  obtain ⟨P, _, hcoefP, heq⟩ :=
    ModularForm.levelOne_hauptmodul_package.2.1 K N (NeZero.ne N) m a hmd hinv hper hbd hcoef
  exact ⟨P, hcoefP, by simpa only [j] using heq⟩

private theorem mdifferentiable_frickeF {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (frickeF N i.1) :=
  ModularForm.mdifferentiable_frickeFunction N periodPairOfTau hppT _ (hW_wpNormZ N) _
    (hfricke_frickeF N) i.2

private theorem isBoundedAtImInfty_frickeF_mul_discriminant {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    IsBoundedAtImInfty (frickeF N i.1 * ⇑CuspForm.discriminant) := by
  rw [coe_cuspDisc]
  exact ModularForm.isBoundedAtImInfty_frickeFunction_mul_discriminant N periodPairOfTau hppT _
    (hW_wpNormZ N) _ (hfricke_frickeF N) i.2

private lemma vecMulSL_mul (N : ℕ) (a : Fin 2 → ZMod N) (γ δ : SL(2, ℤ)) :
    vecMulSL N (vecMulSL N a γ) δ = vecMulSL N a (γ * δ) := by
  simp only [vecMulSL, Matrix.vecMul_vecMul]
  congr 1
  ext i k
  simp [Matrix.map_apply, Matrix.mul_apply, Matrix.SpecialLinearGroup.coe_mul]

private lemma vecMulSL_one (N : ℕ) (a : Fin 2 → ZMod N) : vecMulSL N a 1 = a := by
  simp only [vecMulSL, Matrix.SpecialLinearGroup.coe_one,
    Matrix.map_one ((↑) : ℤ → ZMod N) Int.cast_zero Int.cast_one, Matrix.vecMul_one]

private lemma vecMulSL_zero (N : ℕ) (γ : SL(2, ℤ)) : vecMulSL N (0 : Fin 2 → ZMod N) γ = 0 := by
  simp [vecMulSL]

private lemma vecMulSL_ne_zero {N : ℕ} {a : Fin 2 → ZMod N} (ha : a ≠ 0) (γ : SL(2, ℤ)) :
    vecMulSL N a γ ≠ 0 := by
  intro h0
  apply ha
  have h1 : vecMulSL N (vecMulSL N a γ) γ⁻¹ = a := by
    rw [vecMulSL_mul, mul_inv_cancel, vecMulSL_one]
  rw [← h1, h0, vecMulSL_zero]

private theorem frickeF_hperm {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) :
    ∃ σ : Equiv.Perm (FrickeIdx N), ∀ (i : FrickeIdx N) (τ : ℍ),
      frickeF N i.1 (γ • τ) = frickeF N (σ i).1 τ := by
  refine ⟨⟨fun i => ⟨vecMulSL N i.1 γ, vecMulSL_ne_zero i.2 γ⟩,
          fun i => ⟨vecMulSL N i.1 γ⁻¹, vecMulSL_ne_zero i.2 γ⁻¹⟩, ?_, ?_⟩, ?_⟩
  · intro i
    apply Subtype.ext
    simp only [vecMulSL_mul, mul_inv_cancel, vecMulSL_one]
  · intro i
    apply Subtype.ext
    simp only [vecMulSL_mul, inv_mul_cancel, vecMulSL_one]
  · intro i τ
    exact ModularForm.frickeFunction_smul N periodPairOfTau hppT _ (hW_wpNormZ N) _
      (hfricke_frickeF N) i.1 γ τ

private lemma smul_frickeF {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (a : Fin 2 → ZMod N) :
    γ • frickeF N a = frickeF N (vecMulSL N a γ⁻¹) := by
  funext τ
  rw [sl_smul_apply]
  exact ModularForm.frickeFunction_smul N periodPairOfTau hppT _ (hW_wpNormZ N) _
    (hfricke_frickeF N) a γ⁻¹ τ

private lemma smul_j (γ : SL(2, ℤ)) : γ • j = j := by
  refine (sl_smul_eq_self_iff j).mpr (fun δ τ => ?_) γ
  have hδ : (δ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨δ, rfl⟩
  have hE := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hδ τ
  have hD := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hδ τ
  have hd0 : denom (δ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  simp only [j]
  rw [show ModularForm.E₄ (δ • τ) = denom (↑δ : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * ModularForm.E₄ τ
        from hE,
      show ModularForm.discriminant (δ • τ)
          = denom (↑δ : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * ModularForm.discriminant τ from hD,
      mul_pow, show (denom (↑δ : GL (Fin 2) ℝ) τ ^ (4 : ℤ)) ^ (3 : ℕ)
      = denom (↑δ : GL (Fin 2) ℝ) τ ^ (12 : ℤ) from by
    rw [← zpow_natCast (denom (↑δ : GL (Fin 2) ℝ) τ ^ (4 : ℤ)) 3, ← zpow_mul]; norm_num]
  exact mul_div_mul_left _ _ (zpow_ne_zero _ hd0)

section KPoleClosure

private lemma ratCast_mem_K (K : IntermediateField ℚ ℂ) (q : ℚ) : (q : ℂ) ∈ K :=
  eq_ratCast (algebraMap ℚ ℂ) q ▸ IntermediateField.algebraMap_mem K q

private lemma hNposR (N : ℕ) [NeZero N] : (0 : ℝ) < N := by
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

private lemma disc_hol : MDiff (⇑CuspForm.discriminant : ℍ → ℂ) := CuspForm.discriminant.holo'

private lemma disc_bdd : IsBoundedAtImInfty (⇑CuspForm.discriminant : ℍ → ℂ) :=
  (CuspFormClass.zero_at_infty CuspForm.discriminant).isBoundedAtImInfty

private lemma disc_per1 :
    Function.Periodic ((⇑CuspForm.discriminant : ℍ → ℂ) ∘ ofComplex) 1 := by
  simpa using SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL

private lemma E4_per1 :
    Function.Periodic ((⇑ModularForm.E₄ : ℍ → ℂ) ∘ ofComplex) 1 := by
  simpa using SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄
      one_mem_strictPeriods_SL

private lemma E4_hol : MDiff (⇑ModularForm.E₄ : ℍ → ℂ) := ModularForm.E₄.holo'

private lemma E4_bdd : IsBoundedAtImInfty (⇑ModularForm.E₄ : ℍ → ℂ) :=
  ModularFormClass.bdd_at_infty ModularForm.E₄

private def NiceK (K : IntermediateField ℚ ℂ) (N : ℕ) (f : ℍ → ℂ) : Prop :=
  Function.Periodic (f ∘ ofComplex) (N : ℂ) ∧ MDiff f ∧ IsBoundedAtImInfty f ∧
    ∀ n, (qExpansion N f).coeff n ∈ K

private lemma NiceK.analytic {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f : ℍ → ℂ}
    (hf : NiceK K N f) : AnalyticAt ℂ (cuspFunction N f) 0 :=
  analyticAt_cuspFunction_zero (hNposR N) (by exact_mod_cast hf.1) hf.2.1 hf.2.2.1

private lemma perN_of_per1 {f : ℍ → ℂ} (hp : Function.Periodic (f ∘ ofComplex) 1) (N : ℕ) :
    Function.Periodic (f ∘ ofComplex) (N : ℂ) := by
  simpa using hp.nat_mul N

private lemma NiceK.mul {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f g : ℍ → ℂ}
    (hf : NiceK K N f) (hg : NiceK K N g) : NiceK K N (f * g) := by
  refine ⟨hf.1.mul hg.1, hf.2.1.mul hg.2.1, hf.2.2.1.mul hg.2.2.1, fun n => ?_⟩
  rw [qExpansion_mul hf.analytic hg.analytic, PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hf.2.2.2 p.1) (hg.2.2.2 p.2)

private lemma NiceK.pow {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f : ℍ → ℂ}
    (hf : NiceK K N f) : ∀ k : ℕ, k ≠ 0 → NiceK K N (f ^ k)
  | 1, _ => by simpa using hf
  | (k + 2), _ => by
      rw [pow_succ]
      exact (NiceK.pow hf (k + 1) k.succ_ne_zero).mul hf

private lemma NiceK.add {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f g : ℍ → ℂ}
    (hf : NiceK K N f) (hg : NiceK K N g) : NiceK K N (f + g) := by
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.1.add hg.2.2.1, fun n => ?_⟩
  rw [qExpansion_add hf.analytic hg.analytic, map_add]
  exact add_mem (hf.2.2.2 n) (hg.2.2.2 n)

private lemma NiceK.disc {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] :
    NiceK K N (⇑CuspForm.discriminant : ℍ → ℂ) := by
  refine ⟨perN_of_per1 disc_per1 N, disc_hol, disc_bdd, fun n => ?_⟩
  have hd := (weierstrassP_torsion_qExpansion_package N (NeZero.ne N) periodPairOfTau
      hppT).2.2.2.1 (⇑CuspForm.discriminant : ℍ → ℂ) (by simpa using disc_per1) disc_hol disc_bdd n
  rw [hd]
  split_ifs
  · obtain ⟨q, hq⟩ := (weierstrassP_torsion_qExpansion_package N (NeZero.ne N) periodPairOfTau
        hppT).2.2.2.2.2.2 (n / N)
    rw [show (⇑CuspForm.discriminant : ℍ → ℂ) = (ModularForm.discriminant : ℍ → ℂ) from
      coe_cuspDisc, hq]
    exact ratCast_mem_K K q
  · exact zero_mem K

private lemma NiceK.E4 {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] :
    NiceK K N (⇑ModularForm.E₄ : ℍ → ℂ) := by
  refine ⟨perN_of_per1 E4_per1 N, E4_hol, E4_bdd, fun n => ?_⟩
  have hd := (weierstrassP_torsion_qExpansion_package N (NeZero.ne N) periodPairOfTau
      hppT).2.2.2.1 (⇑ModularForm.E₄ : ℍ → ℂ) (by simpa using E4_per1) E4_hol E4_bdd n
  rw [hd]
  split_ifs
  · obtain ⟨q, hq⟩ := (weierstrassP_torsion_qExpansion_package N (NeZero.ne N) periodPairOfTau
        hppT).2.2.2.2.1 (n / N)
    rw [hq]
    exact ratCast_mem_K K q
  · exact zero_mem K

private lemma cuspFunction_const (N : ℕ) (c : ℂ) :
    cuspFunction N (fun _ : ℍ => c) = fun _ => c := by
  funext q
  rcases eq_or_ne q 0 with rfl | hq
  · change Function.Periodic.cuspFunction N ((fun _ : ℍ => c) ∘ ofComplex) 0 = c
    rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
    refine Filter.Tendsto.limUnder_eq ?_
    refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℂ => (c : ℂ)) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (c : ℂ)))
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (Function.Periodic.cuspFunction_eq_of_ne_zero (N : ℝ)
      ((fun _ : ℍ => (c : ℂ)) ∘ ofComplex) hq).symm
  · change Function.Periodic.cuspFunction N ((fun _ : ℍ => c) ∘ ofComplex) q = c
    rw [Function.Periodic.cuspFunction_eq_of_ne_zero _ _ hq]
    rfl

private lemma NiceK.const {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] (c : ↥K) :
    NiceK K N (fun _ : ℍ => (c : ℂ)) := by
  refine ⟨fun x => rfl, ?_, ?_, fun n => ?_⟩
  · exact mdifferentiable_const
  · exact Filter.const_boundedAtFilter _ _
  · have hq : qExpansion N (fun _ : ℍ => (c : ℂ)) = PowerSeries.C (c : ℂ) := by
      ext m
      simp only [qExpansion_coeff, cuspFunction_const, iteratedDeriv_const, PowerSeries.coeff_C]
      rcases eq_or_ne m 0 with rfl | hm
      · simp
      · simp [hm]
    rw [hq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [PowerSeries.coeff_C, hn]

private lemma kPoleAt_of_niceK {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f : ℍ → ℂ} {m : ℕ}
    (h : NiceK K N (f * ⇑CuspForm.discriminant ^ m)) : KPoleAt K N m f :=
  ⟨by exact_mod_cast h.1, h.2.2.1, h.2.2.2⟩

private lemma niceK_mul_disc_pow {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f : ℍ → ℂ} {m : ℕ}
    (hmd : MDiff f) (hf : KPoleAt K N m f) : NiceK K N (f * ⇑CuspForm.discriminant ^ m) :=
  ⟨by exact_mod_cast hf.1, hmd.mul (disc_hol.pow m), hf.2.1, hf.2.2⟩

private lemma kPole_const {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] (c : ↥K) :
    KPole K N (algebraMap ↥K (ℍ → ℂ) c) := by
  have hc : algebraMap ↥K (ℍ → ℂ) c = fun _ : ℍ => (c : ℂ) := rfl
  rw [hc]
  refine ⟨mdifferentiable_const, 0, kPoleAt_of_niceK ?_⟩
  simpa using NiceK.const c

private lemma kPole_add {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f + g) := by
  obtain ⟨hfm, mf, hfa⟩ := hf
  obtain ⟨hgm, mg, hga⟩ := hg
  have hf' : NiceK K N (f * ⇑CuspForm.discriminant ^ (mf + mg)) := by
    have : f * ⇑CuspForm.discriminant ^ (mf + mg)
        = (f * ⇑CuspForm.discriminant ^ mf) * ⇑CuspForm.discriminant ^ mg := by
      rw [mul_assoc, ← pow_add]
    rcases Nat.eq_zero_or_pos mg with rfl | hmg
    · simpa using niceK_mul_disc_pow hfm hfa
    · rw [this]
      exact (niceK_mul_disc_pow hfm hfa).mul (NiceK.disc.pow mg hmg.ne')
  have hg' : NiceK K N (g * ⇑CuspForm.discriminant ^ (mf + mg)) := by
    have : g * ⇑CuspForm.discriminant ^ (mf + mg)
        = (g * ⇑CuspForm.discriminant ^ mg) * ⇑CuspForm.discriminant ^ mf := by
      rw [mul_assoc, ← pow_add, Nat.add_comm]
    rcases Nat.eq_zero_or_pos mf with rfl | hmf
    · simpa using niceK_mul_disc_pow hgm hga
    · rw [this]
      exact (niceK_mul_disc_pow hgm hga).mul (NiceK.disc.pow mf hmf.ne')
  refine ⟨hfm.add hgm, mf + mg, kPoleAt_of_niceK ?_⟩
  have : (f + g) * ⇑CuspForm.discriminant ^ (mf + mg)
      = f * ⇑CuspForm.discriminant ^ (mf + mg) + g * ⇑CuspForm.discriminant ^ (mf + mg) :=
    add_mul f g _
  rw [this]
  exact hf'.add hg'

private lemma kPole_mul {K : IntermediateField ℚ ℂ} {N : ℕ} [NeZero N] {f g : ℍ → ℂ}
    (hf : KPole K N f) (hg : KPole K N g) : KPole K N (f * g) := by
  obtain ⟨hfm, mf, hfa⟩ := hf
  obtain ⟨hgm, mg, hga⟩ := hg
  refine ⟨hfm.mul hgm, mf + mg, kPoleAt_of_niceK ?_⟩
  have : (f * g) * ⇑CuspForm.discriminant ^ (mf + mg)
      = (f * ⇑CuspForm.discriminant ^ mf) * (g * ⇑CuspForm.discriminant ^ mg) := by
    rw [pow_add]; ring
  rw [this]
  exact (niceK_mul_disc_pow hfm hfa).mul (niceK_mul_disc_pow hgm hga)

private theorem kPole_of_mem_adjoin {K : IntermediateField ℚ ℂ} [NeZero N] {S : Set (ℍ → ℂ)}
    (hS : ∀ f ∈ S, KPole K N f) {a : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ↥K S) : KPole K N a := by
  induction ha using Algebra.adjoin_induction with
  | mem f hf => exact hS f hf
  | algebraMap c => exact kPole_const c
  | add f g _ _ ihf ihg => exact kPole_add ihf ihg
  | mul f g _ _ ihf ihg => exact kPole_mul ihf ihg

private lemma kPole_j (K : IntermediateField ℚ ℂ) [NeZero N] : KPole K N j := by
  have hmd : MDiff j := by
    intro τ
    exact (((E4_hol τ).pow 3).div (disc_hol τ) (ModularForm.discriminant_ne_zero τ))
  refine ⟨hmd, 1, kPoleAt_of_niceK ?_⟩
  have hjd : j * ⇑CuspForm.discriminant ^ 1 = (⇑ModularForm.E₄ : ℍ → ℂ) ^ 3 := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_one, j, coe_cuspDisc]
    field_simp [ModularForm.discriminant_ne_zero τ]
  rw [hjd]
  exact NiceK.E4.pow 3 (by norm_num)

private lemma kPole_frickeF {K : IntermediateField ℚ ℂ} [NeZero N] (hK : kN N
    ≤ K) (i : FrickeIdx N) :
    KPole K N (frickeF N i.1) := by
  have hmd : MDiff (frickeF N i.1) := mdifferentiable_frickeF i
  refine ⟨hmd, 1, ?_, ?_, ?_⟩
  · have hper := ModularForm.periodic_frickeFunction_mul_discriminant N periodPairOfTau hppT _
      (hW_wpNormZ N) _ (hfricke_frickeF N) i.2
    rw [coe_cuspDisc]
    simpa [pow_one] using hper
  · have hbd := ModularForm.isBoundedAtImInfty_frickeFunction_mul_discriminant N periodPairOfTau
      hppT _ (hW_wpNormZ N) _ (hfricke_frickeF N) i.2
    rw [coe_cuspDisc]
    simpa [pow_one] using hbd
  · intro n
    have hco := ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_mem N periodPairOfTau
      hppT _ (hW_wpNormZ N) _ (hfricke_frickeF N) i.2 n
    rw [coe_cuspDisc]
    refine hK ?_
    simpa [pow_one, kN, zetaN] using hco

end KPoleClosure

end R4bFloor

section B6_fixedFrac

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G A]

private lemma smul_prod_smul_eq (v : A) (g₀ : G) : g₀ • (∏ g : G, g • v) = ∏ g : G, g • v := by
  rw [show g₀ • (∏ g : G, g • v) = MulSemiringAction.toRingHom G A g₀ (∏ g : G, g • v) from rfl,
    map_prod]
  simp only [MulSemiringAction.toRingHom_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g₀) _ _ fun g ↦ rfl

variable [IsDomain A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  [MulSemiringAction G K]

private theorem exists_fixed_div_of_fixed
    (hcompat : ∀ (g : G) (a : A), g • algebraMap A K a = algebraMap A K (g • a))
    (x : K) (hx : ∀ g : G, g • x = x) :
    ∃ a b : A, (∀ g : G, g • a = a) ∧ (∀ g : G, g • b = b) ∧ algebraMap A K b ≠ 0 ∧
      x * algebraMap A K b = algebraMap A K a := by
  classical
  obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  set b : A := ∏ g : G, g • v with hb
  set a : A := u * ∏ g ∈ (Finset.univ : Finset G).erase 1, g • v with ha
  have hbfix : ∀ g : G, g • b = b := fun g ↦ smul_prod_smul_eq v g
  have hb0 : algebraMap A K b ≠ 0 := by
    rw [map_ne_zero_iff _ hinj, hb]
    exact Finset.prod_ne_zero_iff.mpr fun g _ ↦ (smul_ne_zero_iff_ne g).mpr hv0
  have hxb : algebraMap A K u / algebraMap A K v * algebraMap A K b = algebraMap A K a := by
    have hv0' : algebraMap A K v ≠ 0 := (map_ne_zero_iff _ hinj).mpr hv0
    rw [hb, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (1 : G)), one_smul, ha, map_mul,
      map_mul]
    field_simp
  refine ⟨a, b, fun g ↦ ?_, hbfix, hb0, hxb⟩
  apply hinj
  rw [← hcompat, ← hxb, smul_mul', hx, hcompat, hbfix]

end B6_fixedFrac

section B6Engine

open UpperHalfPlane
open ModularForm
open SlashInvariantForm
open ModularFormClass
open CuspForm
open Polynomial
open Real.Polynomial
open scoped MatrixGroups Manifold

variable {I : Type*} [Fintype I] (h : I → ℍ → ℂ) (m : ℕ)

private def orbitCoeff (k : ℕ) : ℍ → ℂ := fun τ => (∏ i, (X - C (h i τ))).coeff k

private lemma coeff_X_sub_C_mul (a : ℂ) (p : Polynomial ℂ) (k : ℕ) :
    ((X - C a) * p).coeff k = (if k = 0 then 0 else p.coeff (k - 1)) - a * p.coeff k := by
  rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  congr 1
  cases k with
  | zero => simp [Polynomial.mul_coeff_zero]
  | succ k' => simp [Polynomial.coeff_X_mul]

omit [Fintype I] in
private lemma mdiff_orbitCoeff_prod (hhol : ∀ i, MDiff (h i)) (s : Finset I) (k : ℕ) :
    MDiff ((fun τ : ℍ => (∏ i ∈ s, (X - C (h i τ))).coeff k) : ℍ → ℂ) := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    exact mdifferentiable_const
  | cons a s ha ih =>
    have hrw : ∀ τ : ℍ, (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff k =
        (if k = 0 then 0 else (∏ i ∈ s, (X - C (h i τ))).coeff (k - 1)) -
          h a τ * (∏ i ∈ s, (X - C (h i τ))).coeff k := by
      intro τ
      rw [Finset.prod_cons, coeff_X_sub_C_mul]
    simp only [hrw]
    cases k with
    | zero =>
      exact mdifferentiable_const.sub ((hhol a).mul (ih 0))
    | succ k' =>
      simp only [ite_eq_right (Nat.succ_ne_zero k'), Nat.add_sub_cancel]
      exact (ih k').sub ((hhol a).mul (ih (k' + 1)))

omit [Fintype I] in
private lemma bounded_orbitCoeff_prod
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) (s : Finset I) (k : ℕ) :
    IsBoundedAtImInfty (fun τ =>
      (∏ i ∈ s, (X - C (h i τ))).coeff k * CuspForm.discriminant τ ^ ((s.card - k) * m)) := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one, Finset.card_empty, Nat.zero_sub,
      Nat.zero_mul, pow_zero, mul_one]
    exact Filter.const_boundedAtFilter _ _
  | cons a s ha ih =>
    have hdeg : ∀ τ : ℍ, (∏ i ∈ s, (X - C (h i τ))).natDegree = s.card := by
      intro τ
      rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (h i τ))]
      simp
    cases k with
    | zero =>
      have hshape : (fun τ : ℍ =>
          (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff 0 *
            CuspForm.discriminant τ ^ (((Finset.cons a s ha).card - 0) * m)) = fun τ : ℍ =>
          -((h a τ * CuspForm.discriminant τ ^ m) *
            ((∏ i ∈ s, (X - C (h i τ))).coeff 0 *
              CuspForm.discriminant τ ^ ((s.card - 0) * m))) := by
        funext τ
        rw [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_left rfl, Finset.card_cons, Nat.sub_zero,
          Nat.sub_zero, zero_sub, show (s.card + 1) * m = m + s.card * m by ring, pow_add]
        ring
      rw [hshape]
      exact ((hbd a).mul (ih 0)).neg
    | succ k' =>
      rcases Nat.lt_or_ge s.card (k' + 1) with hk | hk
      · have hzero : ∀ τ : ℍ, (∏ i ∈ s, (X - C (h i τ))).coeff (k' + 1) = 0 := fun τ =>
          coeff_eq_zero_of_natDegree_lt (by rw [hdeg τ]; exact hk)
        have hshape : (fun τ : ℍ =>
            (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff (k' + 1) *
              CuspForm.discriminant τ ^ (((Finset.cons a s ha).card - (k' + 1)) * m)) =
            fun τ : ℍ =>
            (∏ i ∈ s, (X - C (h i τ))).coeff k' *
              CuspForm.discriminant τ ^ ((s.card - k') * m) := by
          funext τ
          rw [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_right (Nat.succ_ne_zero k'),
            Nat.add_sub_cancel, hzero τ, mul_zero, sub_zero, Finset.card_cons,
            Nat.succ_sub_succ]
        rw [hshape]
        exact ih k'
      · have he2 : (s.card - k') * m = m + (s.card - (k' + 1)) * m := by
          have h1 : s.card - k' = 1 + (s.card - (k' + 1)) := by omega
          rw [h1]
          ring
        have hshape : (fun τ : ℍ =>
            (∏ i ∈ Finset.cons a s ha, (X - C (h i τ))).coeff (k' + 1) *
              CuspForm.discriminant τ ^ (((Finset.cons a s ha).card - (k' + 1)) * m)) =
            fun τ : ℍ =>
            ((∏ i ∈ s, (X - C (h i τ))).coeff k' *
              CuspForm.discriminant τ ^ ((s.card - k') * m)) -
            ((h a τ * CuspForm.discriminant τ ^ m) *
              ((∏ i ∈ s, (X - C (h i τ))).coeff (k' + 1) *
                CuspForm.discriminant τ ^ ((s.card - (k' + 1)) * m))) := by
          funext τ
          rw [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_right (Nat.succ_ne_zero k'),
            Nat.add_sub_cancel, Finset.card_cons, Nat.succ_sub_succ, sub_mul]
          congr 1
          rw [he2, pow_add]
          ring
        rw [hshape]
        exact (ih k').sub ((hbd a).mul (ih (k' + 1)))

private theorem orbitCoeff_slash_invariant
    (hperm : ∀ γ : SL(2, ℤ), ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (k : ℕ) (γ : SL(2, ℤ)) : orbitCoeff h k ∣[(0 : ℤ)] γ = orbitCoeff h k := by
  obtain ⟨σ, hσ⟩ := hperm γ
  funext τ
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]
  change (∏ i, (X - C (h i (γ • τ)))).coeff k = (∏ i, (X - C (h i τ))).coeff k
  refine congrArg (fun p : Polynomial ℂ => p.coeff k) ?_
  calc ∏ i, (X - C (h i (γ • τ)))
      = ∏ i, (X - C (h (σ i) τ)) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hσ i τ]
    _ = ∏ i, (X - C (h i τ)) := Equiv.prod_comp σ (fun i' => X - C (h i' τ))

private theorem exists_poly_j_orbitCoeff
    (hperm : ∀ γ : SL(2, ℤ), ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (hhol : ∀ i, MDiff (h i))
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) (k : ℕ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ (Fintype.card I - k) * m ∧
      orbitCoeff h k = fun τ => Polynomial.eval (j τ) P := by
  refine levelOne_holFn_eq_polynomial_j ((Fintype.card I - k) * m) (orbitCoeff h k)
    (mdiff_orbitCoeff_prod h hhol Finset.univ k)
    (orbitCoeff_slash_invariant h hperm k) ?_
  have hb := bounded_orbitCoeff_prod h m hbd Finset.univ k
  rw [Finset.card_univ] at hb
  have hshape : ((orbitCoeff h k * ⇑CuspForm.discriminant ^ ((Fintype.card I - k) * m)
      : ℍ → ℂ)) =
      fun τ : ℍ => (∏ i, (X - C (h i τ))).coeff k *
        CuspForm.discriminant τ ^ ((Fintype.card I - k) * m) := by
    funext τ
    simp [orbitCoeff]
  rw [hshape]
  exact hb

private theorem orbit_integral_over_j
    (hperm : ∀ γ : SL(2, ℤ), ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (hhol : ∀ i, MDiff (h i))
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) :
    ∃ P : ℕ → Polynomial ℂ, (∀ k, (P k).natDegree ≤ (Fintype.card I - k) * m) ∧
      ∀ (i : I) (τ : ℍ), h i τ ^ Fintype.card I +
        ∑ k ∈ Finset.range (Fintype.card I),
          Polynomial.eval (j τ) (P k) * h i τ ^ k = 0 := by
  choose P hPdeg hP using fun k => exists_poly_j_orbitCoeff h m hperm hhol hbd k
  refine ⟨P, hPdeg, fun i τ => ?_⟩
  set Q : Polynomial ℂ := ∏ i', (X - C (h i' τ)) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun i' _ => monic_X_sub_C (h i' τ)
  have hQdeg : Q.natDegree = Fintype.card I := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun i' _ => monic_X_sub_C (h i' τ))]
    simp
  have hroot : Polynomial.eval (h i τ) Q = 0 := by
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hexp := Polynomial.eval_eq_sum_range' (n := Fintype.card I + 1)
    (by rw [hQdeg]; exact Nat.lt_succ_self _) (h i τ) (p := Q)
  rw [Finset.sum_range_succ] at hexp
  have hlead : Q.coeff (Fintype.card I) = 1 := by
    have := hQmonic.coeff_natDegree
    rwa [hQdeg] at this
  have hcoeffs : ∀ k, Q.coeff k = Polynomial.eval (j τ) (P k) := by
    intro k
    have := congrFun (hP k) τ
    simpa [orbitCoeff, hQ] using this
  rw [hroot.symm, hexp, hlead, one_mul, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hcoeffs k]

end B6Engine

section B6Instance

open UpperHalfPlane
open ModularForm
open CuspForm
open Polynomial
open Real.Polynomial
open scoped MatrixGroups Manifold

private theorem frickeF_integral_over_j (N : ℕ) [NeZero N] :
    ∃ P : ℕ → Polynomial ℂ,
      (∀ k, (P k).natDegree ≤ Fintype.card (FrickeIdx N) - k) ∧
      ∀ (i : FrickeIdx N) (τ : ℍ),
        frickeF N i.1 τ ^ Fintype.card (FrickeIdx N) +
          ∑ k ∈ Finset.range (Fintype.card (FrickeIdx N)),
            Polynomial.eval (j τ) (P k) * frickeF N i.1 τ ^ k = 0 := by
  have h := orbit_integral_over_j (fun i : FrickeIdx N => frickeF N i.1) 1
    (fun γ => frickeF_hperm γ)
    (fun i => mdifferentiable_frickeF i)
    (fun i => by rw [pow_one]; exact isBoundedAtImInfty_frickeF_mul_discriminant i)
  simpa [mul_one] using h

end B6Instance

section B6Ring

open UpperHalfPlane
open ModularForm
open SlashInvariantForm
open ModularFormClass
open CuspForm
open Polynomial
open Real.Polynomial
open Filter
open scoped MatrixGroups Manifold

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

private lemma poleBounded_algebraMap (r : ℂ) : PoleBounded (algebraMap ℂ (ℍ → ℂ) r) := by
  refine ⟨mdifferentiable_const, 0, ?_⟩
  have hshape : ((algebraMap ℂ (ℍ → ℂ) r) * ⇑CuspForm.discriminant ^ 0 : ℍ → ℂ) =
      fun _ => r := by
    funext τ
    simp
  rw [hshape]
  exact const_boundedAtFilter _ r

private lemma PoleBounded.add {f g : ℍ → ℂ} (hf : PoleBounded f) (hg : PoleBounded g) :
    PoleBounded (f + g) := by
  obtain ⟨hf1, m1, hf2⟩ := hf
  obtain ⟨hg1, m2, hg2⟩ := hg
  refine ⟨hf1.add hg1, max m1 m2, ?_⟩
  have hshape : ((f + g) * ⇑CuspForm.discriminant ^ max m1 m2 : ℍ → ℂ) =
      f * ⇑CuspForm.discriminant ^ max m1 m2 + g * ⇑CuspForm.discriminant ^ max m1 m2 := by
    funext τ
    simp [add_mul]
  rw [hshape]
  exact (IsBoundedAtImInfty.mul_discPow_mono (le_max_left _ _) hf2).add
    (IsBoundedAtImInfty.mul_discPow_mono (le_max_right _ _) hg2)

private lemma PoleBounded.mul {f g : ℍ → ℂ} (hf : PoleBounded f) (hg : PoleBounded g) :
    PoleBounded (f * g) := by
  obtain ⟨hf1, m1, hf2⟩ := hf
  obtain ⟨hg1, m2, hg2⟩ := hg
  refine ⟨hf1.mul hg1, m1 + m2, ?_⟩
  have hshape : ((f * g) * ⇑CuspForm.discriminant ^ (m1 + m2) : ℍ → ℂ) =
      (f * ⇑CuspForm.discriminant ^ m1) * (g * ⇑CuspForm.discriminant ^ m2) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, pow_add]
    ring
  rw [hshape]
  exact hf2.mul hg2

private theorem poleBounded_of_mem_adjoin {S : Set (ℍ → ℂ)} (hS : ∀ f ∈ S, PoleBounded f)
    {a : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ S) : PoleBounded a := by
  induction ha using Algebra.adjoin_induction with
  | mem f hf => exact hS f hf
  | algebraMap r => exact poleBounded_algebraMap r
  | add x y hx hy ihx ihy => exact ihx.add ihy
  | mul x y hx hy ihx ihy => exact ihx.mul ihy

private lemma poleBounded_j : PoleBounded j := by
  constructor
  · exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  · refine ⟨1, ?_⟩
    have hshape : (j * ⇑CuspForm.discriminant ^ 1 : ℍ → ℂ) = ⇑ModularForm.E₄ ^ 3 := by
      funext τ
      simp only [Pi.mul_apply, Pi.pow_apply, pow_one, j]
      rw [congrFun CuspForm.coe_discriminant τ]
      exact div_mul_cancel₀ _ (ModularForm.discriminant_ne_zero τ)
    rw [hshape]
    have h4 : IsBoundedAtImInfty (⇑ModularForm.E₄ : ℍ → ℂ) := ModularFormClass.bdd_at_infty _
    have hpow : (⇑ModularForm.E₄ ^ 3 : ℍ → ℂ) =
        ⇑ModularForm.E₄ * (⇑ModularForm.E₄ * ⇑ModularForm.E₄) := by
      funext τ
      simp only [Pi.pow_apply, Pi.mul_apply]
      ring
    rw [hpow]
    exact h4.mul (h4.mul h4)

private lemma poleBounded_frickeF {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    PoleBounded (frickeF N i.1) := by
  refine ⟨mdifferentiable_frickeF i, 1, ?_⟩
  have hshape : (frickeF N i.1 * ⇑CuspForm.discriminant ^ 1 : ℍ → ℂ) =
      frickeF N i.1 * ⇑CuspForm.discriminant := by
    funext τ
    simp
  rw [hshape]
  exact isBoundedAtImInfty_frickeF_mul_discriminant i

private theorem eq_polynomial_j_of_invariant_of_mem_adjoin {S : Set (ℍ → ℂ)}
    (hS : ∀ f ∈ S, PoleBounded f) {a : ℍ → ℂ} (ha : a ∈ Algebra.adjoin ℂ S)
    (hinv : ∀ γ : SL(2, ℤ), a ∣[(0 : ℤ)] γ = a) :
    ∃ P : Polynomial ℂ, a = fun τ => Polynomial.eval (j τ) P := by
  obtain ⟨hol, m, hbd⟩ := poleBounded_of_mem_adjoin hS ha
  obtain ⟨P, -, hP⟩ := levelOne_holFn_eq_polynomial_j m a hol hinv hbd
  exact ⟨P, hP⟩

end B6Ring

section LevelRingK

open UpperHalfPlane
open ModularForm
open CuspForm
open Polynomial
open Real.Polynomial
open scoped MatrixGroups Manifold

variable {N : ℕ}

private noncomputable def levelRingK (K : IntermediateField ℚ ℂ) (N : ℕ) : Subalgebra ↥K (ℍ → ℂ) :=
  Algebra.adjoin ↥K (levelGen N)

private lemma j_mem_levelRingK {K : IntermediateField ℚ ℂ} : j ∈ levelRingK K N :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

private lemma frickeF_mem_levelRingK {K : IntermediateField ℚ ℂ} [NeZero N] (i : FrickeIdx N) :
    frickeF N i.1 ∈ levelRingK K N :=
  Algebra.subset_adjoin (Set.mem_insert_iff.mpr (Or.inr ⟨i, rfl⟩))

private theorem smul_mem_levelRingK {K : IntermediateField ℚ ℂ} [NeZero N] (γ : SL(2,
    ℤ)) {f : ℍ → ℂ}
    (hf : f ∈ levelRingK K N) : γ • f ∈ levelRingK K N := by
  induction hf using Algebra.adjoin_induction with
  | mem g hg =>
    rcases hg with rfl | ⟨i, rfl⟩
    · rw [smul_j]
      exact j_mem_levelRingK
    · rw [smul_frickeF]
      exact frickeF_mem_levelRingK ⟨vecMulSL N i.1 γ⁻¹, vecMulSL_ne_zero i.2 γ⁻¹⟩
  | algebraMap r =>
    have h : γ • (algebraMap ↥K (ℍ → ℂ) r) = algebraMap ↥K (ℍ → ℂ) r :=
      sl_smul_const γ (r : ℂ)
    rw [h]
    exact Subalgebra.algebraMap_mem _ r
  | add x y hx hy ihx ihy =>
    rw [smul_add]
    exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
    rw [smul_mul']
    exact mul_mem ihx ihy

private theorem kPole_of_mem_levelRingK {K : IntermediateField ℚ ℂ} [NeZero N] (hK : kN N ≤ K)
    {f : ℍ → ℂ} (hf : f ∈ levelRingK K N) : KPole K N f :=
  kPole_of_mem_adjoin (fun g hg => by
    rcases hg with rfl | ⟨i, rfl⟩
    · exact kPole_j K
    · exact kPole_frickeF hK i) hf

private theorem levelRingK_invariant_eq_polynomial_j {K : IntermediateField ℚ ℂ} [NeZero N]
    (hK : kN N ≤ K) {f : ℍ → ℂ} (hf : f ∈ levelRingK K N)
    (hinv : ∀ γ : SL(2, ℤ), ∀ τ : ℍ, f (γ • τ) = f τ) :
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ K) ∧ f = fun τ => Polynomial.eval (j τ) P := by
  refine kPole_invariant_eq_polynomial_j_mem (kPole_of_mem_levelRingK hK hf) ?_
  intro γ
  funext τ
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]
  exact hinv γ τ

end LevelRingK

section B6InstanceK

open UpperHalfPlane
open ModularForm
open CuspForm
open Polynomial
open Real.Polynomial
open scoped MatrixGroups Manifold

variable {N : ℕ}

private lemma orbitCoeffOn_frickeF_mem_levelRingK [NeZero N] (s : Finset (FrickeIdx N)) (k : ℕ) :
    (fun τ : ℍ => (∏ i ∈ s, (X - C (frickeF N i.1 τ))).coeff k) ∈ levelRingK (kN N) N := by
  induction s using Finset.cons_induction generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    cases k with
    | zero => exact one_mem (levelRingK (kN N) N)
    | succ k' => exact zero_mem (levelRingK (kN N) N)
  | cons a s ha ih =>
    cases k with
    | zero =>
      have hrw : (fun τ : ℍ =>
          (∏ i ∈ Finset.cons a s ha, (X - C (frickeF N i.1 τ))).coeff 0) =
          -(frickeF N a.1 * fun τ : ℍ => (∏ i ∈ s, (X - C (frickeF N i.1 τ))).coeff 0) := by
        funext τ
        simp only [Finset.prod_cons, coeff_X_sub_C_mul, ite_true, Pi.neg_apply, Pi.mul_apply]
        ring
      rw [hrw]
      exact neg_mem (mul_mem (frickeF_mem_levelRingK a) (ih 0))
    | succ k' =>
      have hrw : (fun τ : ℍ =>
          (∏ i ∈ Finset.cons a s ha, (X - C (frickeF N i.1 τ))).coeff (k' + 1)) =
          ((fun τ : ℍ => (∏ i ∈ s, (X - C (frickeF N i.1 τ))).coeff k') -
            frickeF N a.1 * fun τ : ℍ =>
              (∏ i ∈ s, (X - C (frickeF N i.1 τ))).coeff (k' + 1)) := by
        funext τ
        simp only [Finset.prod_cons, coeff_X_sub_C_mul, ite_eq_right (Nat.succ_ne_zero k'),
          Nat.add_sub_cancel, Pi.sub_apply, Pi.mul_apply]
      rw [hrw]
      exact sub_mem (ih k') (mul_mem (frickeF_mem_levelRingK a) (ih (k' + 1)))

private theorem frickeF_integral_over_j_mem_kN (N : ℕ) [NeZero N] :
    ∃ P : ℕ → Polynomial ℂ,
      (∀ k i, (P k).coeff i ∈ kN N) ∧
      ∀ (i : FrickeIdx N) (τ : ℍ),
        frickeF N i.1 τ ^ Fintype.card (FrickeIdx N) +
          ∑ k ∈ Finset.range (Fintype.card (FrickeIdx N)),
            Polynomial.eval (j τ) (P k) * frickeF N i.1 τ ^ k = 0 := by
  have hdesc : ∀ k : ℕ, ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ kN N) ∧
      orbitCoeff (fun i : FrickeIdx N => frickeF N i.1) k =
        fun τ => Polynomial.eval (j τ) P := by
    intro k
    have hmem : orbitCoeff (fun i : FrickeIdx N => frickeF N i.1) k ∈ levelRingK (kN N) N := by
      have h1 := orbitCoeffOn_frickeF_mem_levelRingK (N := N) Finset.univ k
      simp [orbitCoeff] at h1
      exact h1
    exact kPole_invariant_eq_polynomial_j_mem (kPole_of_mem_levelRingK le_rfl hmem)
      (orbitCoeff_slash_invariant (fun i : FrickeIdx N => frickeF N i.1)
        (fun γ => frickeF_hperm γ) k)
  choose P hPmem hP using hdesc
  refine ⟨P, hPmem, fun i τ => ?_⟩
  set Q : Polynomial ℂ := ∏ i' : FrickeIdx N, (X - C (frickeF N i'.1 τ)) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun i' _ => monic_X_sub_C _
  have hQdeg : Q.natDegree = Fintype.card (FrickeIdx N) := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun i' _ => monic_X_sub_C _)]
    simp
  have hroot : Polynomial.eval (frickeF N i.1 τ) Q = 0 := by
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hexp := Polynomial.eval_eq_sum_range' (n := Fintype.card (FrickeIdx N) + 1)
    (by rw [hQdeg]; exact Nat.lt_succ_self _) (frickeF N i.1 τ) (p := Q)
  rw [Finset.sum_range_succ] at hexp
  have hlead : Q.coeff (Fintype.card (FrickeIdx N)) = 1 := by
    have h1 := hQmonic.coeff_natDegree
    rwa [hQdeg] at h1
  have hcoeffs : ∀ k, Q.coeff k = Polynomial.eval (j τ) (P k) := by
    intro k
    have h1 := congrFun (hP k) τ
    simpa [orbitCoeff, hQ] using h1
  rw [hroot.symm, hexp, hlead, one_mul, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hcoeffs k]

end B6InstanceK

section R4bBridge

open Aux
open FrickeFunctions.FrickeOrbit.Aux
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

private lemma periodPair_ext'' {L₁ L₂ : PeriodPair} (h₁ : L₁.ω₁ = L₂.ω₁)
    (h₂ : L₁.ω₂ = L₂.ω₂) : L₁ = L₂ := by
  cases L₁; cases L₂; simp_all

end R4bBridge

end Aux
open scoped FrickeFunctions.FrickeOrbit.Aux

open UpperHalfPlane hiding I in
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm in
open _root_.FrickeFunctions.FrickeOrbit.Aux in
/-- `j` is holomorphic with `j Δ ^ m` bounded at `i∞` for some `m`; each `f_v`, `v ≠ 0`, is
holomorphic with some `f_v Δ ^ m` bounded at `i∞`; and there are polynomials `P k` with
coefficients in `ℚ(ζ_N)` such that every `f_v`, `v ≠ 0`, satisfies `f_v ^ (N² - 1) + ∑_{k < N²
- 1} (P k) (j) f_v ^ k = 0`. -/
public theorem _root_.ModularForm.frickeFunction_orbit_package
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :
    (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf ∧
      ∃ m : ℕ, IsBoundedAtImInfty (jf * ModularForm.discriminant ^ m)) ∧
    (∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) ∧
      ∃ m : ℕ, IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ m)) ∧
    (∃ P : ℕ → Polynomial ℂ,
      (∀ k i, (P k).coeff i ∈
        IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / N)}) ∧
      ∀ v : Fin 2 → ZMod N, v ≠ 0 → ∀ τ : ℍ,
        fricke v τ ^ (N ^ 2 - 1) + ∑ k ∈ Finset.range (N ^ 2 - 1),
          (P k).eval (jf τ) * fricke v τ ^ k = 0) := by
  have hLpp : ∀ τ : ℍ, L τ = periodPairOfTau τ := fun τ =>
    periodPair_ext'' ((hL τ).1.trans (periodPairOfTau_ω₁ τ).symm)
      ((hL τ).2.trans (periodPairOfTau_ω₂ τ).symm)
  have hfr : ∀ v : Fin 2 → ZMod N, fricke v = frickeF N v := by
    intro v
    funext τ
    rw [hfricke v τ, hW v τ, hLpp τ]
    with_unfolding_all rfl
  have hjeq : jf = j := by
    funext τ
    rw [hjf τ]
    rfl
  have hcard : Fintype.card (FrickeIdx N) = N ^ 2 - 1 := by
    have h1 : Fintype.card (Fin 2 → ZMod N) = N ^ 2 := by
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have h2 : Fintype.card {a : Fin 2 → ZMod N // a = 0} = 1 := Fintype.card_subtype_eq 0
    have h3 := Fintype.card_subtype_compl (fun a : Fin 2 → ZMod N => a = 0)
    rw [h1, h2] at h3
    exact h3
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨h1, m, h2⟩ := poleBounded_j
    refine ⟨by rw [hjeq]; exact h1, m, ?_⟩
    rw [hjeq, ← CuspForm.coe_discriminant]
    exact h2
  · intro v hv
    obtain ⟨h1, m, h2⟩ := poleBounded_frickeF (⟨v, hv⟩ : FrickeIdx N)
    refine ⟨by rw [hfr]; exact h1, m, ?_⟩
    rw [hfr, ← CuspForm.coe_discriminant]
    exact h2
  · obtain ⟨P, hPmem, hPrel⟩ := frickeF_integral_over_j_mem_kN N
    refine ⟨P, fun k i => hPmem k i, fun v hv τ => ?_⟩
    have h := hPrel ⟨v, hv⟩ τ
    rw [hfr v, hjeq, ← hcard]
    exact h

end

end FrickeOrbit

end FrickeFunctions
