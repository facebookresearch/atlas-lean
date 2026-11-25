/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient.lean`
and
`P2M/Sol/S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient.lean`
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
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.FrickeOrbit
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.LevelFractionMonicRel
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.QExpansionLinearIndependent

/-!
# Integrality over `K[j]` of holomorphic Fricke quotients

This file shows that holomorphic quotients of Fricke polynomials over `ℚ(ζ_N)` are integral
over `ℚ(ζ_N)[j]`. Throughout, `j = E₄³ / Δ` and, for `v : Fin 2 → ZMod N`, the Fricke function
is `f_v τ = -(E₄ τ E₆ τ / Δ τ) / 2592 · (2πi)⁻² ℘_τ((v₀ τ + v₁) / N)`, where `℘_τ` is the
Weierstrass function of the lattice `ℤτ + ℤ`.

## Main statement

* `ModularForm.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient`
-/
namespace FrickeFunctions.FrickeQuotientMonicRel

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

section Descent

private lemma exists_K_point_of_C_point (K : IntermediateField ℚ ℂ) {n q : ℕ}
    (A : Fin q → Fin n → ↥K) (bv : Fin q → ↥K) (x : Fin n → ℂ)
    (hx : ∀ j, ∑ i, (A j i : ℂ) * x i = (bv j : ℂ)) :
    ∃ y : Fin n → ↥K, ∀ j, ∑ i, A j i * y i = bv j := by
  classical
  set cols : Fin n → (Fin q → ↥K) := fun i j => A j i with hcols
  have hmem : bv ∈ Submodule.span ↥K (Set.range cols) := by
    by_contra hbv
    set W : Submodule ↥K (Fin q → ↥K) := Submodule.span ↥K (Set.range cols) with hW
    have hq0 : W.mkQ bv ≠ 0 := by
      intro h0
      exact hbv ((Submodule.Quotient.mk_eq_zero W).mp (by simpa using h0))
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ↥K ((Fin q → ↥K) ⧸ W), φ (W.mkQ bv) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hq0 ((Module.forall_dual_apply_eq_zero_iff ↥K _).mp hall)
    set f : (Fin q → ↥K) →ₗ[↥K] ↥K := φ.comp W.mkQ with hf
    have hfcols : ∀ i, f (cols i) = 0 := by
      intro i
      have hmem' : cols i ∈ W := Submodule.subset_span (Set.mem_range_self i)
      simp only [hf, LinearMap.comp_apply, Submodule.mkQ_apply]
      rw [(Submodule.Quotient.mk_eq_zero W).mpr hmem', map_zero]
    set c : Fin q → ↥K := fun j => f (fun j' => if j = j' then 1 else 0) with hc
    have hf_eq : ∀ w : Fin q → ↥K, f w = ∑ j, w j * c j := by
      intro w
      conv_lhs => rw [pi_eq_sum_univ w]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
    have h1 : ∀ i, ∑ j, (A j i : ℂ) * (c j : ℂ) = 0 := by
      intro i
      have h0 : (∑ j, A j i * c j : ↥K) = 0 := by
        have := hfcols i
        rwa [hf_eq] at this
      have h0' := congrArg (fun z : ↥K => (z : ℂ)) h0
      push_cast at h0'
      exact h0'
    have hC : ((f bv : ↥K) : ℂ) = 0 := by
      rw [hf_eq]
      push_cast
      have h3 : ∑ j, (bv j : ℂ) * (c j : ℂ) =
          ∑ j, (∑ i, (A j i : ℂ) * x i) * (c j : ℂ) :=
        Finset.sum_congr rfl fun j _ => by rw [hx j]
      rw [h3]
      have h4 : ∑ j, (∑ i, (A j i : ℂ) * x i) * (c j : ℂ) =
          ∑ i, x i * ∑ j, (A j i : ℂ) * (c j : ℂ) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [h4]
      simp [h1]
    have hfbv : f bv = 0 := by exact_mod_cast hC
    exact hφ (by simpa [hf] using hfbv)
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ↥K).mp hmem
  refine ⟨y, fun j => ?_⟩
  have := congrFun hy j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcols] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Descent

section GlueBFold

open ModularForm

namespace R8cGlue

section Kit

variable {N : ℕ}

private lemma jf_smul {jf : ℍ → ℂ} (hjf : ∀ τ : ℍ,
    jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (γ : SL(2, ℤ)) (τ : ℍ) : jf (γ • τ) = jf τ := by
  have hγ : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  rw [CuspForm.coe_discriminant] at hΔ
  rw [show (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ = γ • τ from rfl] at h4 hΔ
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  rw [hjf, hjf, h4, hΔ, zpow_ofNat, zpow_ofNat]
  field_simp

variable (jf : ℍ → ℂ) (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)

private def gen : Option {v : Fin 2 → ZMod N // v ≠ 0} → ℍ → ℂ :=
  fun o => o.elim jf fun v => fricke v.1

variable {jf fricke}

private def genPerm (γ : SL(2, ℤ)) :
    Option {v : Fin 2 → ZMod N // v ≠ 0} → Option {v : Fin 2 → ZMod N // v ≠ 0} :=
  Option.map fun v => ⟨Matrix.vecMul v.1
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)), by
    intro h
    apply v.2
    have := congrArg (fun w => Matrix.vecMul w
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ⁻¹ :
        Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) h
    simp only [Matrix.zero_vecMul, Matrix.vecMul_vecMul] at this
    rwa [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one] at this⟩

private lemma aeval_gen_comp_smul {R : Type*} [CommSemiring R] [Algebra R ℂ]
    (hjinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), jf (γ • τ) = jf τ)
    (hfslash : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ)
    (γ : SL(2, ℤ)) (P : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) R) :
    (MvPolynomial.aeval (gen jf fricke) P : ℍ → ℂ) ∘ (γ • ·) =
      MvPolynomial.aeval (gen jf fricke) (MvPolynomial.rename (genPerm γ) P) := by
  let Cγ : (ℍ → ℂ) →ₐ[R] (ℍ → ℂ) :=
    { toFun := fun F => F ∘ (γ • ·)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun r => by
        funext τ
        simp only [Function.comp_apply, Pi.algebraMap_apply] }
  have h1 : (MvPolynomial.aeval (gen jf fricke) P : ℍ → ℂ) ∘ (γ • ·) =
      Cγ (MvPolynomial.aeval (gen jf fricke) P) := rfl
  have h2 : (fun o => Cγ (gen jf fricke o)) = gen jf fricke ∘ genPerm γ := by
    funext o
    cases o with
    | none => funext τ; exact hjinv γ τ
    | some v => funext τ; exact hfslash v.1 γ τ
  rw [MvPolynomial.aeval_rename, h1, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, h2]

private lemma mem_adjoin_gen_iff {R : Type*} [CommRing R] [Algebra R ℂ] {x : ℍ → ℂ} :
    x ∈ Algebra.adjoin R (Set.range (gen jf fricke)) ↔
      ∃ P : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) R,
        MvPolynomial.aeval (gen jf fricke) P = x := by
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range]

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

private lemma mul_discPow_mono {f : ℍ → ℂ} {m m' : ℕ} (hm : m ≤ m')
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

end Kit

section Analysis

variable {N : ℕ}

private lemma eq_zero_of_forall_im_ge {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {A : ℝ}
    (h : ∀ τ : ℍ, A ≤ τ.im → f τ = 0) : f = 0 := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have han := hf.analyticOnNhd hU
  have hB : 0 < max A 0 + 1 := lt_of_le_of_lt (le_max_right A 0) (lt_add_one _)
  have hz₀ : (⟨0, max A 0 + 1⟩ : ℂ) ∈ {z : ℂ | 0 < z.im} := hB
  have hev : f ∘ ofComplex =ᶠ[𝓝 (⟨0, max A 0 + 1⟩ : ℂ)] 0 := by
    have hopen : IsOpen {z : ℂ | max A 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have hmem : (⟨0, max A 0 + 1⟩ : ℂ) ∈ {z : ℂ | max A 0 < z.im} := by
      change max A 0 < max A 0 + 1
      exact lt_add_one _
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : 0 < z.im := lt_of_le_of_lt (le_max_right A 0) hz
    simp only [Function.comp_apply, Pi.zero_apply, ofComplex_apply_of_im_pos hz']
    exact h ⟨z, hz'⟩ ((le_max_left A 0).trans (le_of_lt hz))
  have key := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected hz₀ hev
  funext τ
  have := key τ.im_pos
  simpa [ofComplex_apply] using this

private lemma exists_qParam_pow_le [NeZero N] {Q : ℍ → ℂ} (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Q)
    (hper : Function.Periodic (Q ∘ ofComplex) N) (hbd : IsBoundedAtImInfty Q) (hQ0 : Q ≠ 0) :
    ∃ (r : ℕ) (C A : ℝ), 0 < C ∧
      ∀ τ : ℍ, A ≤ τ.im → C * ‖Function.Periodic.qParam N τ‖ ^ r ≤ ‖Q τ‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hg : AnalyticAt ℂ (cuspFunction N Q) 0 := analyticAt_cuspFunction_zero hN hper hhol hbd
  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam N τ) atImInfty (𝓝 0) :=
    qParam_tendsto_atImInfty hN
  have heq : ∀ τ : ℍ, cuspFunction N Q (Function.Periodic.qParam N τ) = Q τ := fun τ =>
    eq_cuspFunction τ hN.ne' hper
  by_cases h0 : ∀ᶠ z in 𝓝 (0 : ℂ), cuspFunction N Q z = 0
  · exfalso
    apply hQ0
    have h1 : ∀ᶠ τ : ℍ in atImInfty, Q τ = 0 :=
      (hq.eventually h0).mono fun τ hτ => by rwa [heq τ] at hτ
    rw [Filter.Eventually, atImInfty_mem] at h1
    obtain ⟨A, hA⟩ := h1
    exact eq_zero_of_forall_im_ge hhol hA
  · obtain ⟨r, u, hu, hu0, hfe⟩ := hg.exists_eventuallyEq_pow_smul_ne_zero_iff.mpr h0
    have hpos : 0 < ‖u 0‖ / 2 := by positivity
    have hu_lb : ∀ᶠ z in 𝓝 (0 : ℂ), ‖u 0‖ / 2 ≤ ‖u z‖ := by
      have ht : Tendsto (fun z => ‖u z‖) (𝓝 0) (𝓝 ‖u 0‖) := hu.continuousAt.norm
      exact (ht.eventually_const_lt (half_lt_self (norm_pos_iff.mpr hu0))).mono fun z hz => hz.le
    have hloc : ∀ᶠ z in 𝓝 (0 : ℂ), ‖u 0‖ / 2 * ‖z‖ ^ r ≤ ‖cuspFunction N Q z‖ := by
      filter_upwards [hfe, hu_lb] with z hz hz'
      rw [hz, sub_zero, norm_smul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_left hz' (pow_nonneg (norm_nonneg _) _)
    have hev : ∀ᶠ τ : ℍ in atImInfty,
        ‖u 0‖ / 2 * ‖Function.Periodic.qParam N τ‖ ^ r ≤ ‖Q τ‖ :=
      (hq.eventually hloc).mono fun τ hτ => by rwa [heq τ] at hτ
    rw [Filter.Eventually, atImInfty_mem] at hev
    obtain ⟨A, hA⟩ := hev
    exact ⟨r, ‖u 0‖ / 2, A, hpos, fun τ hτ => hA τ hτ⟩

private lemma map_T_pow_eq_one :
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (ModularGroup.T ^ (N : ℤ)) :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_T_zpow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma periodic_comp_ofComplex_of_T {x : ℍ → ℂ}
    (h : ∀ τ : ℍ, x (ModularGroup.T ^ (N : ℤ) • τ) = x τ) :
    Function.Periodic (x ∘ ofComplex) N := by
  intro w
  by_cases! hw : 0 < im w
  · have hw' : 0 < im (w + N) := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← h ⟨w, hw⟩]
    congr 1
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  · have hw' : im (w + N) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos hw]

end Analysis

section Quotient

variable {N : ℕ} [NeZero N] {jf : ℍ → ℂ} {fricke : (Fin 2 → ZMod N) → ℍ → ℂ}

private structure GenData (jf : ℍ → ℂ) (fricke : (Fin 2 → ZMod N) → ℍ → ℂ) : Prop where
  jmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf
  jbd : ∃ m : ℕ, IsBoundedAtImInfty (jf * ⇑CuspForm.discriminant ^ m)
  fmd : ∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v)
  fbd : ∀ v : Fin 2 → ZMod N, v ≠ 0 →
    ∃ m : ℕ, IsBoundedAtImInfty (fricke v * ⇑CuspForm.discriminant ^ m)
  jinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), jf (γ • τ) = jf τ
  fslash : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ),
    fricke v (γ • τ) = fricke (Matrix.vecMul v
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
        Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ

omit [NeZero N] in
private lemma adjoin_props (hg : GenData jf fricke) {x : ℍ → ℂ}
    (hx : x ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) x ∧
      (∃ m : ℕ, IsBoundedAtImInfty (x * ⇑CuspForm.discriminant ^ m)) ∧
      ∀ τ : ℍ, x (ModularGroup.T ^ (N : ℤ) • τ) = x τ := by
  induction hx using Algebra.adjoin_induction with
  | mem g hg' =>
    obtain ⟨o, rfl⟩ := hg'
    cases o with
    | none => exact ⟨hg.jmd, hg.jbd, fun τ => hg.jinv _ τ⟩
    | some v =>
      refine ⟨hg.fmd v.1 v.2, hg.fbd v.1 v.2, fun τ => ?_⟩
      change fricke v.1 _ = fricke v.1 τ
      rw [hg.fslash, map_T_pow_eq_one, Matrix.vecMul_one]
  | algebraMap c =>
    refine ⟨mdifferentiable_const, ⟨0, ?_⟩, fun τ => rfl⟩
    rw [pow_zero, mul_one]
    exact Filter.const_boundedAtFilter atImInfty c
  | add x y _ _ ihx ihy =>
    obtain ⟨hxm, ⟨m, hm⟩, hxT⟩ := ihx
    obtain ⟨hym, ⟨n, hn⟩, hyT⟩ := ihy
    refine ⟨hxm.add hym, ⟨max m n, ?_⟩, fun τ => by simp only [Pi.add_apply, hxT, hyT]⟩
    rw [add_mul]
    exact (mul_discPow_mono (le_max_left m n) hm).add (mul_discPow_mono (le_max_right m n) hn)
  | mul x y _ _ ihx ihy =>
    obtain ⟨hxm, ⟨m, hm⟩, hxT⟩ := ihx
    obtain ⟨hym, ⟨n, hn⟩, hyT⟩ := ihy
    refine ⟨hxm.mul hym, ⟨m + n, ?_⟩, fun τ => by simp only [Pi.mul_apply, hxT, hyT]⟩
    have : (x * y * ⇑CuspForm.discriminant ^ (m + n) : ℍ → ℂ) =
        (x * ⇑CuspForm.discriminant ^ m) * (y * ⇑CuspForm.discriminant ^ n) := by
      rw [pow_add]; ring
    rw [this]
    exact hm.mul hn

omit [NeZero N] in
private lemma comp_smul_mem_adjoin (hg : GenData jf fricke) (γ : SL(2, ℤ)) {x : ℍ → ℂ}
    (hx : x ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke))) :
    x ∘ (γ • ·) ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke)) := by
  rw [mem_adjoin_gen_iff] at hx ⊢
  obtain ⟨P, rfl⟩ := hx
  exact ⟨_, (aeval_gen_comp_smul hg.jinv hg.fslash γ P).symm⟩

private theorem exists_isBoundedAtImInfty_of_mul_eq (hg : GenData jf fricke) {h q p : ℍ → ℂ}
    (hq : q ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke)))
    (hp : p ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke))) (hq0 : q ≠ 0) (hhq : h * q = p) :
    ∃ m : ℕ, IsBoundedAtImInfty (h * ⇑CuspForm.discriminant ^ m) := by
  obtain ⟨hqm, ⟨mq, hmq⟩, hqT⟩ := adjoin_props hg hq
  obtain ⟨_, ⟨mp, hmp⟩, _⟩ := adjoin_props hg hp
  have hQhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (q * ⇑CuspForm.discriminant ^ mq) :=
    hqm.mul (mdiff_discPow mq)
  have hQper : Function.Periodic ((q * ⇑CuspForm.discriminant ^ mq : ℍ → ℂ) ∘ ofComplex) N :=
    (periodic_comp_ofComplex_of_T hqT).mul (periodic_discPow_comp_ofComplex mq N)
  have hQ0 : (q * ⇑CuspForm.discriminant ^ mq : ℍ → ℂ) ≠ 0 := by
    intro hz
    apply hq0
    funext τ
    have := congrFun hz τ
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff',
      ne_eq] at this
    rcases this with h1 | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 (ModularForm.discriminant_ne_zero τ)
  obtain ⟨r, C, A, hC, hlb⟩ := exists_qParam_pow_le hQhol hQper hmq hQ0
  obtain ⟨Mp, Ap, hMp⟩ := isBoundedAtImInfty_iff.mp hmp
  obtain ⟨MΔ, AΔ, hMΔ⟩ := isBoundedAtImInfty_iff.mp isBoundedAtImInfty_discriminant
  obtain ⟨c, hc, hcO⟩ := (CuspFormClass.exp_decay_atImInfty (h := 1) CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL).exists_pos
  have hcO' := hcO.bound
  rw [Filter.Eventually, atImInfty_mem] at hcO'
  obtain ⟨Ac, hAc⟩ := hcO'
  refine ⟨mp + r, isBoundedAtImInfty_iff.mpr ⟨Mp * c ^ r * MΔ ^ mq / C,
    max (max A Ap) (max AΔ Ac), fun τ hτ => ?_⟩⟩
  have hA' : A ≤ τ.im := (le_max_left _ _).trans ((le_max_left _ _).trans hτ)
  have hAp' : Ap ≤ τ.im := (le_max_right _ _).trans ((le_max_left _ _).trans hτ)
  have hAΔ' : AΔ ≤ τ.im := (le_max_left _ _).trans ((le_max_right _ _).trans hτ)
  have hAc' : Ac ≤ τ.im := (le_max_right _ _).trans ((le_max_right _ _).trans hτ)
  set a : ℝ := ‖Function.Periodic.qParam N τ‖ with ha
  set d : ℝ := ‖CuspForm.discriminant τ‖ with hd
  have ha0 : 0 < a := by rw [ha, norm_pos_iff]; exact Complex.exp_ne_zero _
  have hd0 : 0 ≤ d := norm_nonneg _
  have hB := hlb τ hA'
  have hBpos : 0 < ‖(q * ⇑CuspForm.discriminant ^ mq) τ‖ := lt_of_lt_of_le (by positivity) hB
  have hY : ‖(p * ⇑CuspForm.discriminant ^ mp) τ‖ ≤ Mp := hMp τ hAp'
  have hMp0 : 0 ≤ Mp := (norm_nonneg _).trans hY
  have hdM : d ≤ MΔ := hMΔ τ hAΔ'
  have hMΔ0 : 0 ≤ MΔ := hd0.trans hdM
  have hde : d ≤ c * a := by
    have h1 : d ≤ c * ‖Real.exp (-2 * π * τ.im / 1)‖ := hAc τ hAc'
    have h2 : Real.exp (-2 * π * τ.im / 1) ≤ a := by
      rw [ha, Function.Periodic.norm_qParam]
      apply Real.exp_le_exp.mpr
      rw [div_one, UpperHalfPlane.coe_im]
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
      have hN0 : (0 : ℝ) < N := one_pos.trans_le hN1
      rw [div_eq_mul_inv, neg_mul, neg_mul, neg_mul, neg_le_neg_iff]
      have : 2 * π * τ.im * (N : ℝ)⁻¹ ≤ 2 * π * τ.im * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [inv_le_one_iff₀]
        exact Or.inr hN1
      simpa using this
    calc d ≤ c * ‖Real.exp (-2 * π * τ.im / 1)‖ := h1
      _ = c * Real.exp (-2 * π * τ.im / 1) := by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ c * a := mul_le_mul_of_nonneg_left h2 hc.le
  have hX : ‖(h * ⇑CuspForm.discriminant ^ (mp + r)) τ‖ * ‖(q * ⇑CuspForm.discriminant ^ mq) τ‖
      = ‖(p * ⇑CuspForm.discriminant ^ mp) τ‖ * d ^ r * d ^ mq := by
    rw [← hhq]
    simp only [Pi.mul_apply, Pi.pow_apply, norm_mul, norm_pow, hd, pow_add]
    ring
  have hnum0 : 0 ≤ ‖(p * ⇑CuspForm.discriminant ^ mp) τ‖ * d ^ r * d ^ mq := by positivity
  calc ‖(h * ⇑CuspForm.discriminant ^ (mp + r)) τ‖
      = ‖(p * ⇑CuspForm.discriminant ^ mp) τ‖ * d ^ r * d ^ mq /
          ‖(q * ⇑CuspForm.discriminant ^ mq) τ‖ := by
        rw [eq_div_iff hBpos.ne', hX]
    _ ≤ ‖(p * ⇑CuspForm.discriminant ^ mp) τ‖ * d ^ r * d ^ mq / (C * a ^ r) :=
        div_le_div_of_nonneg_left hnum0 (by positivity) hB
    _ ≤ Mp * (c * a) ^ r * MΔ ^ mq / (C * a ^ r) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul (mul_le_mul hY (pow_le_pow_left₀ hd0 hde r) (by positivity) hMp0)
          (pow_le_pow_left₀ hd0 hdM mq) (by positivity) (by positivity)
    _ = Mp * c ^ r * MΔ ^ mq / C := by
        rw [mul_pow]
        field_simp

private theorem isBoundedAtImInfty_smul_quotient_of_aeval
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
    (hR4c : ∀ (v : Fin 2 → ZMod N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ)
    (hR4b12 : (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf ∧
        ∃ m : ℕ, IsBoundedAtImInfty (jf * ModularForm.discriminant ^ m)) ∧
      (∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) ∧
        ∃ m : ℕ, IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ m)))
    {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P₀ Q₀ : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q₀.map (algebraMap ↥K ℂ)) ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (Q₀.map (algebraMap ↥K ℂ)) =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (P₀.map (algebraMap ↥K ℂ))) :
    ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ m : ℕ,
      IsBoundedAtImInfty ((G ∘ (γ • ·)) * ModularForm.discriminant ^ m) := by
  have _hL := hL
  have _hW := hW
  have _hfricke := hfricke
  have _hK := hK
  have _hG := hG
  intro γ
  have hg : GenData jf fricke := ⟨hR4b12.1.1, by simpa only [CuspForm.coe_discriminant] using
    hR4b12.1.2, fun v hv => (hR4b12.2 v hv).1, fun v hv => by
      simpa only [CuspForm.coe_discriminant] using (hR4b12.2 v hv).2, jf_smul hjf, hR4c⟩
  have hgen : (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} => o.elim jf fun v => fricke v.1) =
      gen jf fricke := rfl
  rw [hgen] at hQ0 hGQ
  set q : ℍ → ℂ := MvPolynomial.aeval (gen jf fricke) (Q₀.map (algebraMap ↥K ℂ)) with hqdef
  set p : ℍ → ℂ := MvPolynomial.aeval (gen jf fricke) (P₀.map (algebraMap ↥K ℂ)) with hpdef
  have hqmem : q ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke)) := mem_adjoin_gen_iff.mpr ⟨_, rfl⟩
  have hpmem : p ∈ Algebra.adjoin ℂ (Set.range (gen jf fricke)) := mem_adjoin_gen_iff.mpr ⟨_, rfl⟩
  have hq0' : q ∘ (γ • ·) ≠ 0 := by
    intro hz
    apply hQ0
    funext τ
    have := congrFun hz (γ⁻¹ • τ)
    simpa only [comp_apply, smul_inv_smul, Pi.zero_apply] using this
  have hhq : (G ∘ (γ • ·)) * (q ∘ (γ • ·)) = p ∘ (γ • ·) := by
    funext τ
    exact congrFun hGQ (γ • τ)
  simpa only [CuspForm.coe_discriminant] using exists_isBoundedAtImInfty_of_mul_eq hg
    (comp_smul_mem_adjoin hg γ hqmem) (comp_smul_mem_adjoin hg γ hpmem) hq0' hhq

end Quotient

end R8cGlue

end GlueBFold

section QKitA

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

end QKitA

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

section QKitB

open ModularForm

variable {N : ℕ} {K : IntermediateField ℚ ℂ}

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

end QKitB

section AevalKit

open ModularForm

variable {N : ℕ} {K : IntermediateField ℚ ℂ}

private lemma kPole_fricke [NeZero N] {fricke : (Fin 2 → ZMod N) → ℍ → ℂ}
    {v : Fin 2 → ZMod N}
    (hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v))
    (hper : Function.Periodic ((fricke v * ModularForm.discriminant ^ 1) ∘
      UpperHalfPlane.ofComplex) N)
    (hbd : IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ 1))
    (hmem : ∀ n : ℕ, (qExpansion N (fricke v * ModularForm.discriminant ^ 1)).coeff n ∈ K) :
    KPole K N (fricke v) := by
  have hsh : (fricke v * ⇑CuspForm.discriminant ^ 1 : ℍ → ℂ) =
      fricke v * ModularForm.discriminant ^ 1 := by
    funext τ
    simp only [Pi.mul_apply, pow_one]
    rw [congrFun CuspForm.coe_discriminant τ]
  exact ⟨hmd, 1, by rw [hsh]; exact hper, by rw [hsh]; exact hbd, by rw [hsh]; exact hmem⟩

private lemma kPole_aeval [NeZero N]
    {fricke : (Fin 2 → ZMod N) → ℍ → ℂ} {jf : ℍ → ℂ}
    (hkjf : KPole K N jf)
    (hkfr : ∀ v : {v : Fin 2 → ZMod N // v ≠ 0}, KPole K N (fricke v.1))
    (p : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K) :
    KPole K N (MvPolynomial.aeval
      (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} => o.elim jf fun v => fricke v.1)
      (p.map (algebraMap ↥K ℂ))) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
    have htower : (algebraMap ℂ (ℍ → ℂ)) ((algebraMap ↥K ℂ) c) =
        algebraMap ↥K (ℍ → ℂ) c := by
      rw [← IsScalarTower.algebraMap_apply]
    rw [htower]
    exact kPole_algebraMap c
  | add p q hp hq =>
    rw [map_add, map_add]
    exact KPole.add hp hq
  | mul_X p o hp =>
    rw [map_mul, MvPolynomial.map_X, map_mul, MvPolynomial.aeval_X]
    refine KPole.mul hp ?_
    cases o with
    | none => exact hkjf
    | some v => exact hkfr v

end AevalKit

end Aux

open _root_.FrickeFunctions.FrickeQuotientMonicRel.Aux Aux.R8cGlue in
/-- Let `K = ℚ(ζ_N)` and let `P₀`, `Q₀` be polynomials over `K` in `j` and the Fricke functions
`f_v`, `v ≠ 0`, with `Q₀ ≠ 0` after evaluation. If `G` is holomorphic and `G Q₀ = P₀` after
evaluation, then `G` satisfies a monic equation `G ^ d + ∑_{i < d} p_i (j) G ^ i = 0` with
`p_i` having coefficients in `K`. -/
public theorem _root_.ModularForm.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient
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
    (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (P₀ Q₀ : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q₀.map (algebraMap ↥K ℂ)) ≠ 0)
    (hGQ : G * MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (Q₀.map (algebraMap ↥K ℂ)) =
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke v.1) (P₀.map (algebraMap ↥K ℂ)))
    :
    ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), (∀ (i : Fin d) (n : ℕ), (p i).coeff n ∈ K) ∧
      ∀ τ : ℍ, G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) = 0 := by
  have hR6h3 : ∀ {a b F : ℍ → ℂ},
      a ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) →
      b ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) →
      b ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → F * b = a →
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∃ m : ℕ,
        IsBoundedAtImInfty ((F ∘ (γ • ·)) * ModularForm.discriminant ^ m)) →
      ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), ∀ τ : ℍ,
        F τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * F τ ^ (i : ℕ) = 0 :=
    fun ha hb hb0 hF hFb hpb =>
      ModularForm.exists_monicRel_j_of_mdifferentiable_levelFraction N L hL W hW fricke hfricke jf
          hjf
        ha hb hb0 hF hFb hpb
  have hR7a : ∀ {ι : Type} (f : ι → ℍ → ℂ),
      (∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i) ∧ ∃ m : ℕ,
        Function.Periodic ((f i * ModularForm.discriminant ^ m) ∘
          UpperHalfPlane.ofComplex) N ∧
        IsBoundedAtImInfty (f i * ModularForm.discriminant ^ m) ∧
        ∀ n : ℕ, (UpperHalfPlane.qExpansion N
          (f i * ModularForm.discriminant ^ m)).coeff n ∈ K) →
      LinearIndependent ↥K f → LinearIndependent ℂ f :=
    fun f hf hli => UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem N K f hf hli
  have hR4b12 : (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf ∧
        ∃ m : ℕ, IsBoundedAtImInfty (jf * ModularForm.discriminant ^ m)) ∧
      (∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) ∧
        ∃ m : ℕ, IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ m)) :=
    ⟨(ModularForm.frickeFunction_orbit_package N L hL W hW fricke hfricke jf hjf).1,
      (ModularForm.frickeFunction_orbit_package N L hL W hW fricke hfricke jf hjf).2.1⟩
  have hR4c : ∀ (v : Fin 2 → ZMod N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ := by
    intro v γ τ; exact ModularForm.frickeFunction_smul N L hL W hW fricke hfricke v γ τ
  have hQrat : ∀ v : Fin 2 → ZMod N, v ≠ 0 →
      Function.Periodic ((fricke v * ModularForm.discriminant ^ 1) ∘
        UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty (fricke v * ModularForm.discriminant ^ 1) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N
        (fricke v * ModularForm.discriminant ^ 1)).coeff n ∈ K := by
    intro v hv; rw [pow_one, hK]
    exact ⟨ModularForm.periodic_frickeFunction_mul_discriminant N L hL W hW fricke hfricke hv,
      ModularForm.isBoundedAtImInfty_frickeFunction_mul_discriminant N L hL W hW fricke hfricke hv,
      ModularForm.qExpansion_coeff_frickeFunction_mul_discriminant_mem N L hL W hW fricke hfricke
        hv⟩
  classical
  set gen : Option {v : Fin 2 → ZMod N // v ≠ 0} → ℍ → ℂ :=
    fun o => o.elim jf fun v => fricke v.1 with hgen
  set Pt : ℍ → ℂ := MvPolynomial.aeval gen (P₀.map (algebraMap ↥K ℂ)) with hPt
  set Qt : ℍ → ℂ := MvPolynomial.aeval gen (Q₀.map (algebraMap ↥K ℂ)) with hQt
  have hkjf : KPole K N jf := kPole_jf K hjf
  have hkfr : ∀ v : {v : Fin 2 → ZMod N // v ≠ 0}, KPole K N (fricke v.1) := fun v =>
    kPole_fricke ((hR4b12.2 v.1 v.2).1) (hQrat v.1 v.2).1 (hQrat v.1 v.2).2.1
      (hQrat v.1 v.2).2.2
  have hkA : ∀ r : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K,
      KPole K N (MvPolynomial.aeval gen (r.map (algebraMap ↥K ℂ))) := fun r =>
    kPole_aeval hkjf hkfr r
  have hrange : Set.range gen =
      insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v} := by
    ext g
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Set.mem_insert _ _
      | some v => exact Set.mem_insert_of_mem _ ⟨v.1, v.2, rfl⟩
    · rintro (rfl | ⟨v, hv, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨some ⟨v, hv⟩, rfl⟩
  have hmemA : ∀ r : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ℂ,
      MvPolynomial.aeval gen r ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) := by
    intro r
    rw [← hrange, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨r, rfl⟩
  have hpb := R8cGlue.isBoundedAtImInfty_smul_quotient_of_aeval N L hL W hW fricke hfricke
    jf hjf K hK hR4c hR4b12 hG P₀ Q₀ hQ0 hGQ
  obtain ⟨d, p, hrel⟩ := hR6h3 (hmemA (P₀.map (algebraMap ↥K ℂ)))
    (hmemA (Q₀.map (algebraMap ↥K ℂ))) hQ0 hG hGQ hpb
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · exfalso
    have h0 := hrel ⟨Complex.I, by simp⟩
    subst hd0
    simp at h0
  have hGQτ : ∀ τ : ℍ, G τ * Qt τ = Pt τ := fun τ => by
    have := congrFun hGQ τ
    simpa using this
  have hpow : ∀ (τ : ℍ) (k : ℕ), G τ ^ k * Qt τ ^ k = Pt τ ^ k := fun τ k => by
    rw [← mul_pow, hGQτ τ]
  set D : ℕ := (Finset.univ.sup fun i : Fin d => (p i).natDegree) + 1 with hD
  have hdeg : ∀ i : Fin d, (p i).natDegree < D := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i : Fin d => (p i).natDegree)
      (Finset.mem_univ i))
  have hcleared : ∀ τ : ℍ, Pt τ ^ d + ∑ i : Fin d, ∑ k ∈ Finset.range D,
      (p i).coeff k * (jf τ ^ k * (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ))) = 0 := by
    intro τ
    have h1 : (G τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ)) * Qt τ ^ d = 0 := by
      rw [hrel τ, zero_mul]
    rw [add_mul, Finset.sum_mul] at h1
    have hterm : ∀ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) * Qt τ ^ d =
        ∑ k ∈ Finset.range D,
          (p i).coeff k * (jf τ ^ k * (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ))) := by
      intro i
      rw [Polynomial.eval_eq_sum_range' (hdeg i), Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsplit : Qt τ ^ d = Qt τ ^ (d - (i : ℕ)) * Qt τ ^ (i : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt i.2)]
      rw [hsplit]
      linear_combination (p i).coeff k * jf τ ^ k * Qt τ ^ (d - (i : ℕ)) * hpow τ (i : ℕ)
    calc Pt τ ^ d + ∑ i : Fin d, ∑ k ∈ Finset.range D,
          (p i).coeff k * (jf τ ^ k * (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ)))
        = G τ ^ d * Qt τ ^ d +
            ∑ i : Fin d, (p i).eval (jf τ) * G τ ^ (i : ℕ) * Qt τ ^ d := by
          rw [hpow τ d]
          exact congrArg₂ (· + ·) rfl
            (Finset.sum_congr rfl fun i _ => (hterm i).symm)
      _ = 0 := h1
  set u : Option (Fin d × Fin D) → ℍ → ℂ := fun o => o.elim
    (MvPolynomial.aeval gen ((P₀ ^ d).map (algebraMap ↥K ℂ)))
    (fun ik => MvPolynomial.aeval gen
      ((MvPolynomial.X none ^ (ik.2 : ℕ) *
        (Q₀ ^ (d - (ik.1 : ℕ)) * P₀ ^ (ik.1 : ℕ))).map (algebraMap ↥K ℂ))) with hu
  have hu_top : ∀ τ : ℍ, u none τ = Pt τ ^ d := by
    intro τ
    simp only [hu, Option.elim, map_pow, Pi.pow_apply, hPt]
  have hu_mon : ∀ (ik : Fin d × Fin D) (τ : ℍ), u (some ik) τ =
      jf τ ^ (ik.2 : ℕ) * (Qt τ ^ (d - (ik.1 : ℕ)) * Pt τ ^ (ik.1 : ℕ)) := by
    intro ik τ
    simp only [hu, Option.elim, map_mul, map_pow, MvPolynomial.map_X,
      MvPolynomial.aeval_X, Pi.mul_apply, Pi.pow_apply, hPt, hQt, hgen]
  have hkU : ∀ o, KPole K N (u o) := by
    intro o
    cases o with
    | none => exact hkA _
    | some ik => exact hkA _
  set lam : Fin d × Fin D → ℂ := fun ik => (p ik.1).coeff ik.2 with hlam
  have hfunrel : u none + ∑ ik : Fin d × Fin D, lam ik • u (some ik) = 0 := by
    funext τ
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [hu_top τ]
    have hsum : ∑ ik : Fin d × Fin D, lam ik * u (some ik) τ =
        ∑ i : Fin d, ∑ k ∈ Finset.range D,
          (p i).coeff k * (jf τ ^ k * (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ))) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_range fun k => (p i).coeff k *
        (jf τ ^ k * (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ)))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hu_mon (i, k) τ, hlam]
    rw [hsum]
    exact hcleared τ
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent ↥K (Set.range u)
  have hbfin : b.Finite := (Set.finite_range u).subset hbsub
  have : Fintype ↥b := hbfin.fintype
  have hdata : ∀ w : ↥b, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((w : ℍ → ℂ)) ∧ ∃ m : ℕ,
      Function.Periodic (((w : ℍ → ℂ) * ModularForm.discriminant ^ m) ∘
        UpperHalfPlane.ofComplex) N ∧
      IsBoundedAtImInfty ((w : ℍ → ℂ) * ModularForm.discriminant ^ m) ∧
      ∀ n : ℕ, (UpperHalfPlane.qExpansion N
        ((w : ℍ → ℂ) * ModularForm.discriminant ^ m)).coeff n ∈ K := by
    intro w
    obtain ⟨o, ho⟩ := hbsub w.2
    obtain ⟨hmd, m, hper, hbd, hmem⟩ := ho ▸ hkU o
    have hsh : ((w : ℍ → ℂ) * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) =
        (w : ℍ → ℂ) * ModularForm.discriminant ^ m := by
      funext τ
      simp only [Pi.mul_apply, Pi.pow_apply]
      rw [congrFun CuspForm.coe_discriminant τ]
    rw [hsh] at hper hbd hmem
    exact ⟨hmd, m, hper, hbd, hmem⟩
  have hCind : LinearIndependent ℂ (fun w : ↥b => (w : ℍ → ℂ)) :=
    hR7a (fun w : ↥b => (w : ℍ → ℂ)) hdata hbind
  have hcoords : ∀ o, ∃ c : ↥b → ↥K, ∑ w : ↥b, c w • (w : ℍ → ℂ) = u o := by
    intro o
    have h1 : u o ∈ Submodule.span ↥K (Set.range ((↑) : b → ℍ → ℂ)) := by
      rw [Subtype.range_coe, hbspan]
      exact Submodule.subset_span (Set.mem_range_self o)
    exact (Submodule.mem_span_range_iff_exists_fun ↥K).mp h1
  choose co hco using hcoords
  have hKsmul : ∀ (c : ↥K) (g : ℍ → ℂ), c • g = (c : ℂ) • g := fun c g =>
    (algebraMap_smul ℂ c g).symm
  have hpiece : ∀ o, ∑ w : ↥b, (co o w : ℂ) • (w : ℍ → ℂ) = u o := by
    intro o
    rw [← hco o]
    exact Finset.sum_congr rfl fun w _ => (hKsmul _ _).symm
  have hsys : ∀ w : ↥b, (co none w : ℂ) +
      ∑ ik : Fin d × Fin D, lam ik * (co (some ik) w : ℂ) = 0 := by
    have hcomb : ∑ w : ↥b, ((co none w : ℂ) +
        ∑ ik : Fin d × Fin D, lam ik * (co (some ik) w : ℂ)) • (w : ℍ → ℂ) = 0 := by
      have hstep : ∑ w : ↥b, ((co none w : ℂ) +
          ∑ ik : Fin d × Fin D, lam ik * (co (some ik) w : ℂ)) • (w : ℍ → ℂ) =
          ∑ w : ↥b, (co none w : ℂ) • (w : ℍ → ℂ) +
          ∑ ik : Fin d × Fin D, lam ik •
            ∑ w : ↥b, (co (some ik) w : ℂ) • (w : ℍ → ℂ) := by
        simp only [add_smul, Finset.sum_smul, mul_smul]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ik _ => (Finset.smul_sum).symm
      rw [hstep, hpiece none]
      rw [Finset.sum_congr rfl fun ik _ => congrArg (lam ik • ·) (hpiece (some ik))]
      exact hfunrel
    intro w
    exact (Fintype.linearIndependent_iff.mp hCind) _ hcomb w
  set em : (Fin d × Fin D) ≃ Fin (Fintype.card (Fin d × Fin D)) :=
    Fintype.equivFin (Fin d × Fin D) with hem
  set eb : ↥b ≃ Fin (Fintype.card ↥b) := Fintype.equivFin ↥b with heb
  obtain ⟨y0, hy0⟩ := exists_K_point_of_C_point K
    (A := fun j i => co (some (em.symm i)) (eb.symm j))
    (bv := fun j => - co none (eb.symm j))
    (x := fun i => lam (em.symm i))
    (by
      intro j
      have h0 := hsys (eb.symm j)
      calc ∑ i, ((co (some (em.symm i)) (eb.symm j) : ↥K) : ℂ) * lam (em.symm i)
          = ∑ ik : Fin d × Fin D, (co (some ik) (eb.symm j) : ℂ) * lam ik :=
            Equiv.sum_comp em.symm fun ik => (co (some ik) (eb.symm j) : ℂ) * lam ik
        _ = ∑ ik : Fin d × Fin D, lam ik * (co (some ik) (eb.symm j) : ℂ) :=
            Finset.sum_congr rfl fun ik _ => mul_comm _ _
        _ = ((- co none (eb.symm j) : ↥K) : ℂ) := by
            push_cast
            linear_combination h0)
  set y : Fin d × Fin D → ↥K := fun ik => y0 (em ik) with hy
  have hyK : ∀ w : ↥b, co none w + ∑ ik : Fin d × Fin D, co (some ik) w * y ik = 0 := by
    intro w
    have h0 := hy0 (eb w)
    simp only [Equiv.symm_apply_apply] at h0
    have hre : ∑ ik : Fin d × Fin D, co (some ik) w * y ik =
        ∑ i, co (some (em.symm i)) w * y0 i := by
      rw [← Equiv.sum_comp em.symm (fun ik => co (some ik) w * y ik)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hy]
      simp only [Equiv.apply_symm_apply]
    rw [hre, h0]
    ring
  set p' : Fin d → Polynomial ℂ := fun i =>
    ∑ k : Fin D, Polynomial.C ((y (i, k) : ↥K) : ℂ) * Polynomial.X ^ (k : ℕ) with hp'
  have hp'coeff : ∀ (i : Fin d) (n : ℕ), (p' i).coeff n ∈ K := by
    intro i n
    rw [hp', Polynomial.finsetSum_coeff]
    refine sum_mem fun k _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    split
    · rw [mul_one]
      exact SetLike.coe_mem _
    · rw [mul_zero]
      exact zero_mem _
  have hp'eval : ∀ (i : Fin d) (z : ℂ),
      (p' i).eval z = ∑ k : Fin D, ((y (i, k) : ↥K) : ℂ) * z ^ (k : ℕ) := by
    intro i z
    rw [hp', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hKfun : u none + ∑ ik : Fin d × Fin D, ((y ik : ↥K) : ℂ) • u (some ik) = 0 := by
    calc u none + ∑ ik : Fin d × Fin D, ((y ik : ↥K) : ℂ) • u (some ik)
        = ∑ w : ↥b, ((co none w : ℂ) +
            ∑ ik : Fin d × Fin D, (co (some ik) w : ℂ) * ((y ik : ↥K) : ℂ)) •
              (w : ℍ → ℂ) := by
          rw [← hpiece none,
            Finset.sum_congr rfl fun ik _ =>
              congrArg (((y ik : ↥K) : ℂ) • ·) (hpiece (some ik)).symm]
          simp only [Finset.smul_sum]
          rw [Finset.sum_comm, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [add_smul, Finset.sum_smul]
          congr 1
          refine Finset.sum_congr rfl fun ik _ => ?_
          rw [smul_smul, mul_comm]
      _ = 0 := by
          refine Finset.sum_eq_zero fun w _ => ?_
          have h3 : (co none w : ℂ) +
              ∑ ik : Fin d × Fin D, (co (some ik) w : ℂ) * ((y ik : ↥K) : ℂ) = 0 := by
            exact_mod_cast congrArg (fun z : ↥K => (z : ℂ)) (hyK w)
          rw [h3, zero_smul]
  have hfinal0 : ∀ τ : ℍ, Pt τ ^ d + ∑ ik : Fin d × Fin D,
      ((y ik : ↥K) : ℂ) * (jf τ ^ (ik.2 : ℕ) *
        (Qt τ ^ (d - (ik.1 : ℕ)) * Pt τ ^ (ik.1 : ℕ))) = 0 := by
    intro τ
    have h0 := congrFun hKfun τ
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at h0
    rw [hu_top τ] at h0
    have hsum2 : ∑ ik : Fin d × Fin D, ((y ik : ↥K) : ℂ) * u (some ik) τ =
        ∑ ik : Fin d × Fin D, ((y ik : ↥K) : ℂ) * (jf τ ^ (ik.2 : ℕ) *
          (Qt τ ^ (d - (ik.1 : ℕ)) * Pt τ ^ (ik.1 : ℕ))) :=
      Finset.sum_congr rfl fun ik _ => by rw [hu_mon ik τ]
    rw [hsum2] at h0
    exact h0
  have hback : ∀ τ : ℍ,
      (G τ ^ d + ∑ i : Fin d, (p' i).eval (jf τ) * G τ ^ (i : ℕ)) * Qt τ ^ d = 0 := by
    intro τ
    have hterm : ∀ i : Fin d, (p' i).eval (jf τ) * G τ ^ (i : ℕ) * Qt τ ^ d =
        ∑ k : Fin D, ((y (i, k) : ↥K) : ℂ) * (jf τ ^ (k : ℕ) *
          (Qt τ ^ (d - (i : ℕ)) * Pt τ ^ (i : ℕ))) := by
      intro i
      rw [hp'eval, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hsplit : Qt τ ^ d = Qt τ ^ (d - (i : ℕ)) * Qt τ ^ (i : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt i.2)]
      rw [hsplit]
      linear_combination ((y (i, k) : ↥K) : ℂ) * jf τ ^ (k : ℕ) *
        Qt τ ^ (d - (i : ℕ)) * hpow τ (i : ℕ)
    rw [add_mul, Finset.sum_mul, hpow τ d,
      Finset.sum_congr rfl fun i _ => hterm i]
    have h0 := hfinal0 τ
    rw [Fintype.sum_prod_type] at h0
    exact h0
  have hQtmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Qt := (hkA Q₀).1
  have hjfmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := hR4b12.1.1
  have hhmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ => G τ ^ d + ∑ i : Fin d, (p' i).eval (jf τ) * G τ ^ (i : ℕ)) := by
    have hsummd : ∀ i : Fin d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (fun τ => (p' i).eval (jf τ) * G τ ^ (i : ℕ)) := by
      intro i
      have hev : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (p' i).eval (jf τ)) := by
        have hsh : (fun τ => (p' i).eval (jf τ)) =
            fun τ => ∑ k : Fin D, ((y (i, k) : ↥K) : ℂ) * jf τ ^ (k : ℕ) := by
          funext τ
          rw [hp'eval]
        rw [hsh]
        have : ∀ s : Finset (Fin D), MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
            (fun τ => ∑ k ∈ s, ((y (i, k) : ↥K) : ℂ) * jf τ ^ (k : ℕ)) := by
          intro s
          induction s using Finset.induction_on with
          | empty => simpa using mdifferentiable_const
          | insert a t ha ih =>
            have hsh2 : (fun τ => ∑ k ∈ insert a t,
                ((y (i, k) : ↥K) : ℂ) * jf τ ^ (k : ℕ)) =
                (fun τ => ((y (i, a) : ↥K) : ℂ) * jf τ ^ (a : ℕ)) +
                fun τ => ∑ k ∈ t, ((y (i, k) : ↥K) : ℂ) * jf τ ^ (k : ℕ) := by
              funext τ
              simp [Finset.sum_insert ha]
            rw [hsh2]
            exact (mdifferentiable_const.mul (hjfmd.pow _)).add ih
        exact this Finset.univ
      exact hev.mul (hG.pow _)
    have : ∀ s : Finset (Fin d), MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (fun τ => ∑ i ∈ s, (p' i).eval (jf τ) * G τ ^ (i : ℕ)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using mdifferentiable_const
      | insert a t ha ih =>
        have hsh2 : (fun τ => ∑ i ∈ insert a t, (p' i).eval (jf τ) * G τ ^ (i : ℕ)) =
            (fun τ => (p' a).eval (jf τ) * G τ ^ (a : ℕ)) +
            fun τ => ∑ i ∈ t, (p' i).eval (jf τ) * G τ ^ (i : ℕ) := by
          funext τ
          simp [Finset.sum_insert ha]
        rw [hsh2]
        exact (hsummd a).add ih
    exact (hG.pow d).add (this Finset.univ)
  have hmul0 : ((fun τ => G τ ^ d + ∑ i : Fin d, (p' i).eval (jf τ) * G τ ^ (i : ℕ)) *
      Qt ^ d : ℍ → ℂ) = 0 := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    exact hback τ
  rcases mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero hhmd (hQtmd.pow d) hmul0 with
    hzero | hzero
  · refine ⟨d, p', hp'coeff, fun τ => ?_⟩
    exact congrFun hzero τ
  · exfalso
    apply hQ0
    funext τ
    have h1 := congrFun hzero τ
    simp only [Pi.pow_apply, Pi.zero_apply] at h1
    have h2 := pow_eq_zero_iff hdpos.ne' |>.mp h1
    simpa using h2

end

end FrickeQuotientMonicRel

end FrickeFunctions
