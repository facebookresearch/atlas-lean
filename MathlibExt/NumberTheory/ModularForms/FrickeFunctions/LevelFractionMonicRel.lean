/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction.lean`
and
`P2M/Sol/S_WLight_exists_monicRel_j_of_mdifferentiable_levelFraction.lean`
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

/-!
# Integrality over `ℂ[j]` of holomorphic quotients of Fricke polynomials

This file shows that holomorphic quotients of polynomials in the Fricke functions are integral
over `ℂ[j]`. Throughout, `j = E₄³ / Δ` and, for `v : Fin 2 → ZMod N`, the Fricke function is
`f_v τ = -(E₄ τ E₆ τ / Δ τ) / 2592 · (2πi)⁻² ℘_τ((v₀ τ + v₁) / N)`, where `℘_τ` is the
Weierstrass function of the lattice `ℤτ + ℤ`.

## Main statement

* `ModularForm.exists_monicRel_j_of_mdifferentiable_levelFraction`
-/
namespace FrickeFunctions.LevelFractionMonicRel

noncomputable section

open Complex
open Real
open UpperHalfPlane
open ModularForm
open Polynomial
open Real.Polynomial
open scoped Topology Manifold MatrixGroups ModularForm

namespace Aux
open Aux

section ValuationEngine

private theorem le_meromorphicOrderAt_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} (s : Finset ι) {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) (m : WithTop ℤ)
    (hm : ∀ i ∈ s, m ≤ meromorphicOrderAt (f i) x) :
    m ≤ meromorphicOrderAt (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc m ≤ min (meromorphicOrderAt (f a) x) (meromorphicOrderAt (∑ i ∈ s, f i) x) := by
            refine le_min (hm a (Finset.mem_insert_self a s)) ?_
            exact ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
              (fun i hi ↦ hm i (Finset.mem_insert_of_mem hi))
      _ ≤ meromorphicOrderAt (f a + ∑ i ∈ s, f i) x := by
            apply meromorphicOrderAt_add (hf a (Finset.mem_insert_self a s))
            exact MeromorphicAt.sum (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

private theorem meromorphicOrderAt_le_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ} {τ : 𝕜}
    (hF : AnalyticAt 𝕜 F τ) (hG : AnalyticAt 𝕜 G τ)
    (hGord : meromorphicOrderAt G τ ≠ ⊤) (hc : ∀ k < n, AnalyticAt 𝕜 (c k) τ)
    (hrel : F ^ n + (∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) =ᶠ[𝓝 τ] 0) :
    meromorphicOrderAt G τ ≤ meromorphicOrderAt F τ := by
  by_contra hlt
  rw [not_le] at hlt
  lift meromorphicOrderAt G τ to ℤ using hGord with m hm
  have hFord : meromorphicOrderAt F τ ≠ ⊤ := hlt.ne_top
  lift meromorphicOrderAt F τ to ℤ using hFord with r hr
  have hrm : r < m := WithTop.coe_lt_coe.mp hlt
  set S := ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k with hS
  have hMerS : ∀ k ∈ Finset.range n, MeromorphicAt (c k * G ^ (n - k) * F ^ k) τ := by
    intro k hk
    exact (((hc k (Finset.mem_range.mp hk)).mul ((hG.pow _))).mul (hF.pow _)).meromorphicAt
  have hsum_ord : (↑(n * r) + 1 : WithTop ℤ) ≤ meromorphicOrderAt S τ := by
    refine le_meromorphicOrderAt_sum _ hMerS _ ?_
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hterm : meromorphicOrderAt (c k * G ^ (n - k) * F ^ k) τ
        = meromorphicOrderAt (c k) τ + ((n - k : ℕ) * meromorphicOrderAt G τ
            + k * meromorphicOrderAt F τ) := by
      rw [meromorphicOrderAt_mul (((hc k hk').mul (hG.pow (n - k))).meromorphicAt)
            ((hF.pow k).meromorphicAt),
          meromorphicOrderAt_mul (hc k hk').meromorphicAt ((hG.pow (n - k)).meromorphicAt),
          meromorphicOrderAt_pow hG.meromorphicAt (n := n - k),
          meromorphicOrderAt_pow hF.meromorphicAt (n := k), add_assoc]
    rw [hterm, ← hm, ← hr]
    have hc_ord : (0 : WithTop ℤ) ≤ meromorphicOrderAt (c k) τ :=
      (hc k hk').meromorphicOrderAt_nonneg
    have hnk : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by omega
    have key : (↑(n * r) + 1 : WithTop ℤ)
        ≤ (↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r := by
      rw [show ((n - k : ℕ) : WithTop ℤ) = (((n - k : ℕ) : ℤ) : WithTop ℤ) by push_cast; rfl,
          show ((k : ℕ) : WithTop ℤ) = (((k : ℕ) : ℤ) : WithTop ℤ) by push_cast; rfl,
          ← WithTop.coe_mul, ← WithTop.coe_mul, ← WithTop.coe_add,
          ← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe, hnk]
      have h1 : (1 : ℤ) ≤ (n : ℤ) - k := by omega
      nlinarith [h1, hrm]
    calc (↑(n * r) + 1 : WithTop ℤ)
        ≤ (↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r := key
      _ = 0 + ((↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r) := (zero_add _).symm
      _ ≤ meromorphicOrderAt (c k) τ + ((↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r) := by
          gcongr
  have hFn_ord : meromorphicOrderAt (F ^ n) τ = (↑(n * r) : WithTop ℤ) := by
    rw [meromorphicOrderAt_pow hF.meromorphicAt, ← hr]; push_cast; ring_nf
  have hlt2 : meromorphicOrderAt (F ^ n) τ < meromorphicOrderAt S τ := by
    rw [hFn_ord]
    refine lt_of_lt_of_le ?_ hsum_ord
    exact_mod_cast lt_add_one (n * r)
  have heq : meromorphicOrderAt (F ^ n + S) τ = meromorphicOrderAt (F ^ n) τ :=
    meromorphicOrderAt_add_eq_left_of_lt
      (MeromorphicAt.sum (fun i hi ↦ hMerS i hi)) hlt2
  have hzero : (F ^ n + S) =ᶠ[𝓝[≠] τ] 0 :=
    hrel.filter_mono nhdsWithin_le_nhds
  have htop : meromorphicOrderAt (F ^ n + S) τ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]; exact hzero
  rw [heq, hFn_ord] at htop
  exact WithTop.coe_ne_top htop

open WithTop.LinearOrderedAddCommGroup in
private theorem meromorphicOrderAt_div_nonneg_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ} {τ : 𝕜}
    (hF : AnalyticAt 𝕜 F τ) (hG : AnalyticAt 𝕜 G τ)
    (hGord : meromorphicOrderAt G τ ≠ ⊤) (hc : ∀ k < n, AnalyticAt 𝕜 (c k) τ)
    (hrel : F ^ n + (∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) =ᶠ[𝓝 τ] 0) :
    0 ≤ meromorphicOrderAt (F / G) τ := by
  have hle := meromorphicOrderAt_le_of_monicRel hF hG hGord hc hrel
  rw [meromorphicOrderAt_div hF.meromorphicAt hG.meromorphicAt,
      ← LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top hGord]
  exact (LinearOrderedAddCommGroupWithTop.sub_le_sub_iff_left_of_ne_top hGord).mpr hle

end ValuationEngine

section HBridge

private lemma analyticOnNhd_comp_ofComplex {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet

private lemma mdifferentiable_of_analyticOnNhd {f : ℍ → ℂ}
    (hf : AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  UpperHalfPlane.mdifferentiable_iff.mpr hf.differentiableOn

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

end HBridge

section JfFacts

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

variable {jf : ℍ → ℂ}
  (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
include hjf

private lemma mdiff_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  have : jf = fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := funext hjf
  rw [this]
  exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
    ModularForm.discriminant_ne_zero

private lemma jf_smul (γ : SL(2, ℤ)) (τ : ℍ) : jf (γ • τ) = jf τ := by
  have hγ : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have h4 := SlashInvariantForm.slash_action_eqn'' ModularForm.E₄ hγ τ
  have hΔ := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
  rw [CuspForm.coe_discriminant] at hΔ
  rw [show (Matrix.SpecialLinearGroup.mapGL ℝ γ) • τ = γ • τ from rfl] at h4 hΔ
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
  rw [hjf, hjf, h4, hΔ, zpow_ofNat, zpow_ofNat]
  field_simp

end JfFacts

section AdjoinFacts

variable {N : ℕ} [NeZero N] {jf : ℍ → ℂ} {fricke : (Fin 2 → ZMod N) → ℍ → ℂ}

omit [NeZero N] in
private lemma map_castRingHom_eq_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem'] at hγ
  rw [hγ, Matrix.SpecialLinearGroup.coe_one]

omit [NeZero N] in
private lemma mdiff_of_mem_adjoin
    (hjmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf)
    (hfmd : ∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v))
    {x : ℍ → ℂ}
    (hx : x ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v})) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) x := by
  induction hx using Algebra.adjoin_induction with
  | mem g hg =>
    rcases hg with rfl | ⟨v, hv, rfl⟩
    · exact hjmd
    · exact hfmd v hv
  | algebraMap r => exact mdifferentiable_const
  | add x y _ _ ihx ihy => exact ihx.add ihy
  | mul x y _ _ ihx ihy => exact ihx.mul ihy

omit [NeZero N] in
private lemma invariant_of_mem_adjoin
    (hjinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ), jf (γ • τ) = jf τ)
    (hfslash : ∀ (v : Fin 2 → ZMod N) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ)
    {x : ℍ → ℂ}
    (hx : x ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hγ : γ ∈ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    x (γ • τ) = x τ := by
  induction hx using Algebra.adjoin_induction with
  | mem g hg =>
    rcases hg with rfl | ⟨v, hv, rfl⟩
    · exact hjinv γ τ
    · rw [hfslash v γ τ, map_castRingHom_eq_one hγ, Matrix.vecMul_one]
  | algebraMap r => rfl
  | add x y _ _ ihx ihy => simp only [Pi.add_apply, ihx, ihy]
  | mul x y _ _ ihx ihy => simp only [Pi.mul_apply, ihx, ihy]

end AdjoinFacts

section GammaOrbit

variable {N : ℕ} [NeZero N]

private lemma mdiff_comp_smul {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ∘ (γ • ·)) := by
  have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ∣[(0 : ℤ)] γ) := hF.slash 0 _
  have h2 : F ∣[(0 : ℤ)] γ = F ∘ (γ • ·) := by
    funext τ
    simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
    rfl
  rwa [h2] at h1

variable (N) in
private def gammaOrbit (F : ℍ → ℂ)
    (hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∘ (γ • ·) = F) :
    (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N) → ℍ → ℂ :=
  Quotient.lift (fun γ : Matrix.SpecialLinearGroup (Fin 2) ℤ => F ∘ (γ • ·)) (by
    intro γ γ' hrel
    replace hrel : γ⁻¹ * γ' ∈ CongruenceSubgroup.Gamma N :=
      QuotientGroup.leftRel_apply.mp hrel
    have hconj : γ * (γ⁻¹ * γ') * γ⁻¹ ∈ CongruenceSubgroup.Gamma N :=
      (CongruenceSubgroup.Gamma_normal N).conj_mem _ hrel γ
    funext τ
    have h1 := congrFun (hFinv _ hconj) (γ • τ)
    simp only [Function.comp_apply] at h1 ⊢
    rw [← mul_smul, show γ * (γ⁻¹ * γ') * γ⁻¹ * γ = γ' by group] at h1
    exact h1.symm)

omit [NeZero N] in
private lemma gammaOrbit_mk (F : ℍ → ℂ)
    (hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∘ (γ • ·) = F)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    gammaOrbit N F hFinv (QuotientGroup.mk γ) = F ∘ (γ • ·) := rfl

omit [NeZero N] in
private lemma gammaOrbit_one (F : ℍ → ℂ)
    (hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∘ (γ • ·) = F) :
    gammaOrbit N F hFinv (QuotientGroup.mk 1) = F := by
  rw [gammaOrbit_mk]
  funext τ
  simp [one_smul]

variable (N) in
private def orbitPerm (γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Equiv.Perm (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N) where
  toFun := Quotient.map (· * γ₀) (by
    intro x y h
    replace h : x⁻¹ * y ∈ CongruenceSubgroup.Gamma N := QuotientGroup.leftRel_apply.mp h
    refine QuotientGroup.leftRel_apply.mpr ?_
    have := (CongruenceSubgroup.Gamma_normal N).conj_mem _ h γ₀⁻¹
    simpa [mul_assoc, mul_inv_rev] using this)
  invFun := Quotient.map (· * γ₀⁻¹) (by
    intro x y h
    replace h : x⁻¹ * y ∈ CongruenceSubgroup.Gamma N := QuotientGroup.leftRel_apply.mp h
    refine QuotientGroup.leftRel_apply.mpr ?_
    have := (CongruenceSubgroup.Gamma_normal N).conj_mem _ h γ₀
    simpa [mul_assoc, mul_inv_rev] using this)
  left_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ => simp [Quotient.map_mk, mul_assoc]
  right_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ => simp [Quotient.map_mk, mul_assoc]

omit [NeZero N] in
private lemma orbitPerm_mk (γ₀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    orbitPerm N γ₀ (QuotientGroup.mk γ) = QuotientGroup.mk (γ * γ₀) := rfl

omit [NeZero N] in
private lemma gammaOrbit_perm (F : ℍ → ℂ)
    (hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∘ (γ • ·) = F)
    (γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (q : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N) (τ : ℍ) :
    gammaOrbit N F hFinv q (γ₀ • τ) = gammaOrbit N F hFinv (orbitPerm N γ₀ q) τ := by
  induction q using QuotientGroup.induction_on with
  | H γ =>
    rw [orbitPerm_mk, gammaOrbit_mk, gammaOrbit_mk]
    simp only [Function.comp_apply, mul_smul]

end GammaOrbit

section OrbitEngine

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
private lemma mdiff_orbitCoeff_prod (hhol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h i)) (s : Finset I)
    (k : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((fun τ : ℍ => (∏ i ∈ s, (X - C (h i τ))).coeff k) : ℍ → ℂ) := by
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
    (hperm : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (k : ℕ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    orbitCoeff h k ∣[(0 : ℤ)] γ = orbitCoeff h k := by
  obtain ⟨σ, hσ⟩ := hperm γ
  funext τ
  simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
  change (∏ i, (X - C (h i (γ • τ)))).coeff k = (∏ i, (X - C (h i τ))).coeff k
  refine congrArg (fun p : Polynomial ℂ => p.coeff k) ?_
  calc ∏ i, (X - C (h i (γ • τ)))
      = ∏ i, (X - C (h (σ i) τ)) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [hσ i τ]
    _ = ∏ i, (X - C (h i τ)) := Equiv.prod_comp σ (fun i' => X - C (h i' τ))

variable {jf : ℍ → ℂ}

private theorem exists_poly_j_orbitCoeff
    (hR3 : ∀ (m' : ℕ) (g : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, g ∣[(0 : ℤ)] γ = g) →
      IsBoundedAtImInfty (g * ModularForm.discriminant ^ m') →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m' ∧ g = fun τ => P.eval (jf τ))
    (hperm : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (hhol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h i))
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) (k : ℕ) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ (Fintype.card I - k) * m ∧
      orbitCoeff h k = fun τ => P.eval (jf τ) := by
  refine hR3 ((Fintype.card I - k) * m) (orbitCoeff h k)
    (mdiff_orbitCoeff_prod h hhol Finset.univ k)
    (orbitCoeff_slash_invariant h hperm k) ?_
  have hb := bounded_orbitCoeff_prod h m hbd Finset.univ k
  rw [Finset.card_univ] at hb
  have hshape : ((orbitCoeff h k * ModularForm.discriminant ^ ((Fintype.card I - k) * m)
      : ℍ → ℂ)) =
      fun τ : ℍ => (∏ i, (X - C (h i τ))).coeff k *
        CuspForm.discriminant τ ^ ((Fintype.card I - k) * m) := by
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply, orbitCoeff, ← CuspForm.coe_discriminant]
  rw [hshape]
  exact hb

private theorem orbit_integral_over_j
    (hR3 : ∀ (m' : ℕ) (g : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, g ∣[(0 : ℤ)] γ = g) →
      IsBoundedAtImInfty (g * ModularForm.discriminant ^ m') →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m' ∧ g = fun τ => P.eval (jf τ))
    (hperm : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ σ : Equiv.Perm I, ∀ i τ, h i (γ • τ) = h (σ i) τ)
    (hhol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h i))
    (hbd : ∀ i, IsBoundedAtImInfty (h i * ⇑CuspForm.discriminant ^ m)) :
    ∃ P : ℕ → Polynomial ℂ, (∀ k, (P k).natDegree ≤ (Fintype.card I - k) * m) ∧
      ∀ (i : I) (τ : ℍ), h i τ ^ Fintype.card I +
        ∑ k ∈ Finset.range (Fintype.card I),
          Polynomial.eval (jf τ) (P k) * h i τ ^ k = 0 := by
  choose P hPdeg hP using fun k => exists_poly_j_orbitCoeff h m hR3 hperm hhol hbd k
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
  have hcoeffs : ∀ k, Q.coeff k = Polynomial.eval (jf τ) (P k) := by
    intro k
    have := congrFun (hP k) τ
    simpa [orbitCoeff, hQ] using this
  rw [hroot.symm, hexp, hlead, one_mul, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [hcoeffs k]

end OrbitEngine

section HeadThree

private theorem exists_monicRel_j_of_mdifferentiable_levelFraction_of_deps
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
    (hR3 : ∀ (m' : ℕ) (g : ℍ → ℂ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g →
      (∀ γ : SL(2, ℤ), g ∣[(0 : ℤ)] γ = g) →
      IsBoundedAtImInfty (g * ModularForm.discriminant ^ m') →
      ∃ P : Polynomial ℂ, P.natDegree ≤ m' ∧ g = fun τ => P.eval (jf τ))
    (hR4a : ∀ v : Fin 2 → ZMod N, v ≠ 0 → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v))
    (hR4c : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ),
      fricke v (γ • τ) = fricke (Matrix.vecMul v
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) τ)
    {a b F : ℍ → ℂ}
    (ha : a ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb : b ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb0 : b ≠ 0)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hFb : F * b = a)
    (hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ModularForm.discriminant ^ m)) :
    ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), ∀ τ : ℍ,
      F τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * F τ ^ (i : ℕ) = 0 := by
  have _hL := hL
  have _hW := hW
  have _hfricke := hfricke
  classical
  have hbmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b := mdiff_of_mem_adjoin (mdiff_jf hjf) hR4a hb
  have hainv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, a (γ • τ) = a τ := fun γ hγ τ =>
    invariant_of_mem_adjoin (fun γ' τ' => jf_smul hjf γ' τ') hR4c ha hγ τ
  have hbinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, b (γ • τ) = b τ := fun γ hγ τ =>
    invariant_of_mem_adjoin (fun γ' τ' => jf_smul hjf γ' τ') hR4c hb hγ τ
  have hFinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, F ∘ (γ • ·) = F := by
    intro γ hγ
    have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F ∘ (γ • ·) - F) :=
      (mdiff_comp_smul hF γ).sub hF
    have hprod : (F ∘ (γ • ·) - F) * b = 0 := by
      funext τ
      have h1 : F (γ • τ) * b (γ • τ) = a (γ • τ) := congrFun hFb (γ • τ)
      have h2 : F τ * b τ = a τ := congrFun hFb τ
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply, Function.comp_apply]
      rw [sub_mul, h2]
      rw [show F (γ • τ) * b τ = F (γ • τ) * b (γ • τ) by rw [hbinv γ hγ τ], h1,
        hainv γ hγ τ, sub_self]
    rcases mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero hdiff hbmd hprod with h | h
    · funext τ
      have := congrFun h τ
      simpa [sub_eq_zero] using this
    · exact absurd h hb0
  have : Fintype (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N) :=
      Fintype.ofFinite _
  set orb := gammaOrbit N F (fun γ hγ => hFinv γ hγ) with horb
  have hperm : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ σ : Equiv.Perm (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N),
        ∀ q τ, orb q (γ • τ) = orb (σ q) τ :=
    fun γ => ⟨orbitPerm N γ, fun q τ => gammaOrbit_perm F _ γ q τ⟩
  have hhol : ∀ q, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (orb q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H γ => exact mdiff_comp_smul hF γ
  choose mq hmq using fun q : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N =>
      hpb q.out
  set M := Finset.univ.sup mq with hM
  have hbd : ∀ q, IsBoundedAtImInfty (orb q * ⇑CuspForm.discriminant ^ M) := by
    intro q
    have hq : orb q = F ∘ (q.out • ·) := by
      conv_lhs => rw [horb, ← Quotient.out_eq q]
      rfl
    have h1 : IsBoundedAtImInfty ((F ∘ (q.out • ·)) * ⇑CuspForm.discriminant ^ mq q) := by
      rw [CuspForm.coe_discriminant]
      exact hmq q
    rw [hq]
    exact IsBoundedAtImInfty.mul_discPow_mono (Finset.le_sup (Finset.mem_univ q)) h1
  obtain ⟨P, -, hP⟩ := orbit_integral_over_j orb M hR3 hperm hhol hbd
  set d := Fintype.card (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma N) with hd
  refine ⟨d, fun i => P (i : ℕ), fun τ => ?_⟩
  have h1 := hP (QuotientGroup.mk 1) τ
  rw [show orb (QuotientGroup.mk 1) = F from gammaOrbit_one F _] at h1
  have h2 : (∑ i : Fin d, (P (i : ℕ)).eval (jf τ) * F τ ^ (i : ℕ))
      = ∑ k ∈ Finset.range d, Polynomial.eval (jf τ) (P k) * F τ ^ k :=
    Fin.sum_univ_eq_sum_range (fun k => Polynomial.eval (jf τ) (P k) * F τ ^ k) d
  rw [h2]
  exact h1

end HeadThree

end Aux

open UpperHalfPlane hiding I in
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm in
open _root_.FrickeFunctions.LevelFractionMonicRel.Aux in
/-- Let `a`, `b` lie in the `ℂ`-algebra generated by `j` and the Fricke functions `f_v`, `v ≠ 0`,
with `b ≠ 0`, and let `F` be holomorphic with `F b = a` such that every translate `(F ∘ (γ •
·)) Δ ^ m` is bounded at `i∞` for some `m`. Then `F` satisfies a monic polynomial equation with
coefficients in `ℂ[j]`. -/
public theorem _root_.ModularForm.exists_monicRel_j_of_mdifferentiable_levelFraction
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
    {a b F : ℍ → ℂ}
    (ha : a ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb : b ∈ Algebra.adjoin ℂ
      (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}))
    (hb0 : b ≠ 0)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hFb : F * b = a)
    (hpb : ∀ γ : SL(2, ℤ), ∃ m : ℕ,
      IsBoundedAtImInfty ((F ∘ (γ • ·)) * ModularForm.discriminant ^ m)) :
    ∃ (d : ℕ) (p : Fin d → Polynomial ℂ), ∀ τ : ℍ,
      F τ ^ d + ∑ i : Fin d, (p i).eval (jf τ) * F τ ^ (i : ℕ) = 0:= by
  refine exists_monicRel_j_of_mdifferentiable_levelFraction_of_deps N L hL W hW fricke hfricke
      jf hjf ?_ ?_ ?_ ha hb hb0 hF hFb hpb
  · intro m' g hg hinv hbd
    obtain ⟨P, hdeg, heq⟩ := ModularForm.levelOne_hauptmodul_package.1 m' g hg hinv hbd
    refine ⟨P, hdeg, ?_⟩
    rw [show (fun τ : ℍ => P.eval (jf τ))
        = fun τ : ℍ => Polynomial.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) P from
      funext fun τ => by rw [hjf τ]]
    exact heq
  · intro v hv
    exact ModularForm.mdifferentiable_frickeFunction N L hL W hW fricke hfricke hv
  · intro v γ τ
    exact ModularForm.frickeFunction_smul N L hL W hW fricke hfricke v γ τ

end

end LevelFractionMonicRel

end FrickeFunctions
