/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean`
and
`P2M/Sol/S_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean`
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
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.DiscriminantCuspOrder
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.EisensteinPowMul
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.FrickeModularity
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.FrickeQuotientSigmaTransport
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.SLTwoZModSurjective

/-!
# Galois transport of `Γ₁(N)` cusp forms with Fricke-rational expressions

This file transports a `Γ₁(N)` cusp form with a Fricke-rational expression along an embedding
of `ℚ(ζ_N)`, using the results of the other files in this directory. Throughout, `j = E₄³ / Δ`
and, for `v : Fin 2 → ZMod N`, the Fricke function is `f_v τ = -(E₄ τ E₆ τ / Δ τ) / 2592 ·
(2πi)⁻² ℘_τ((v₀ τ + v₁) / N)`, where `℘_τ` is the Weierstrass function of the lattice `ℤτ + ℤ`.

## Main statement

* `CuspForm.exists_gamma1_frickeRational_sigmaTransport`
-/
namespace FrickeFunctions.Gamma1FrickeRationalTransport

set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology

namespace FrickeCuspTransport

local notation "Δ" => ModularForm.discriminant

section Analytic

private theorem differentiableAt_comp_ofComplex {u : ℍ →
    ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (τ : ℍ) :
    DifferentiableAt ℂ (u ∘ ofComplex) (τ : ℂ) :=
  UpperHalfPlane.mdifferentiableAt_iff.1 (hu τ)

private theorem eq_zero_of_mul_eq_zero {u v : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hv : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) v) (huv : ∀ τ : ℍ, u τ * v τ = 0) {τ₀ : ℍ} (hv0 : v τ₀ ≠ 0) :
    u = 0 := by
  have hvc : ContinuousAt (v ∘ ofComplex) (τ₀ : ℂ) :=
      (differentiableAt_comp_ofComplex hv τ₀).continuousAt
  have hv0' : (v ∘ ofComplex) (τ₀ : ℂ) ≠ 0 := by simpa [Function.comp, ofComplex_apply] using hv0
  have hu0 : (u ∘ ofComplex) =ᶠ[𝓝 (τ₀ : ℂ)] 0 := by
    filter_upwards [hvc.eventually_ne hv0'] with z hz
    have := huv (ofComplex z)
    simp only [Function.comp_apply, Pi.zero_apply] at hz ⊢
    exact (mul_eq_zero.1 this).resolve_right hz
  have hEq := ((UpperHalfPlane.mdifferentiable_iff.1 hu).analyticOnNhd
    isOpen_upperHalfPlaneSet).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected τ₀.im_pos hu0
  funext τ
  simpa [Function.comp, ofComplex_apply] using hEq τ.im_pos

private theorem exists_ne_zero {v : ℍ → ℂ} (hv : v ≠ 0) : ∃ τ, v τ ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (funext h)

private theorem pow_ne_zero_fun {v : ℍ → ℂ} (hv : v ≠ 0) (p : ℕ) : v ^ p ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_ne_zero hv
  intro h
  have := congrFun h τ
  simp only [Pi.pow_apply, Pi.zero_apply] at this
  exact pow_ne_zero p hτ this

private theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := by
  rw [← CuspForm.coe_discriminant]; exact CuspForm.discriminant.holo'

private theorem disc_ne_zero (τ : ℍ) : Δ τ ≠ 0 := discriminant_ne_zero τ

private theorem periodic_disc_one : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1 := by
  have := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL
  rwa [CuspForm.coe_discriminant] at this

private theorem isBoundedAtImInfty_disc : IsBoundedAtImInfty (Δ : ℍ → ℂ) := by
  have := ModularFormClass.bdd_at_infty CuspForm.discriminant
  rwa [CuspForm.coe_discriminant] at this

private theorem periodic_ofComplex_natCast {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) 1) (n : ℕ) :
    Periodic (g ∘ ofComplex) n := by
  simpa using h.nat_mul n

private theorem periodic_disc (N : ℕ) : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) N :=
    periodic_ofComplex_natCast periodic_disc_one N

private theorem periodic_sub {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g - g') ∘ ofComplex) c := by
  intro z; have h1 := h z; have h2 := h' z
  simp only [comp_apply, Pi.sub_apply] at h1 h2 ⊢; rw [h1, h2]

private theorem periodic_div_disc_pow {N : ℕ} {g : ℍ → ℂ} (h : Periodic (g ∘ ofComplex) N) (e : ℕ) :
    Periodic ((fun τ => g τ / Δ τ ^ e) ∘ ofComplex) N := by
  intro z; have h1 := h z; have h2 := periodic_disc N z
  simp only [comp_apply] at h1 h2 ⊢; rw [h1, h2]

private theorem mdifferentiable_inv {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (h0 : ∀ τ : ℍ,
    g τ ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => (g τ)⁻¹) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have h1 := UpperHalfPlane.mdifferentiable_iff.1 hg
  exact (h1.inv fun z _ => h0 _).congr fun z _ => by simp [comp_apply]

private theorem mdifferentiable_div_disc_pow {g : ℍ →
    ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (r : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => g τ / Δ τ ^ r) := by
  have := hg.mul (mdifferentiable_inv (mdifferentiable_disc.pow r) fun τ =>
      pow_ne_zero _ (disc_ne_zero τ))
  exact this

private theorem tendsto_E {k : ℕ} (hk3 : 3 ≤ k) (hk2 : Even k) :
    Tendsto (⇑(ModularForm.E hk3) : ℍ → ℂ) atImInfty (𝓝 1) := by
  have hanal := ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.E hk3) one_pos
    one_mem_strictPeriods_SL
  have hper :=
      SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E hk3) one_mem_strictPeriods_SL
  have hval : cuspFunction 1 (⇑(ModularForm.E hk3)) 0 = 1 := by
    have h0 := qExpansion_coeff (⇑(ModularForm.E hk3)) (h := (1 : ℝ)) 0
    rw [EisensteinSeries.E_qExpansion_coeff_zero hk3 hk2] at h0
    simpa using h0.symm
  have := (hanal.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)).congr
    (fun τ => eq_cuspFunction τ one_ne_zero hper)
  simpa [hval] using this

private theorem tendsto_E₄ : Tendsto (⇑E₄ : ℍ → ℂ) atImInfty (𝓝 1) :=
    tendsto_E (by norm_num) ⟨2, rfl⟩
private theorem tendsto_E₆ : Tendsto (⇑E₆ : ℍ → ℂ) atImInfty (𝓝 1) :=
    tendsto_E (by norm_num) ⟨3, rfl⟩

private theorem bdd_of_mul_tendsto_one {h e : ℍ → ℂ} (hhe : IsBoundedAtImInfty (h * e))
    (he : Tendsto e atImInfty (𝓝 1)) : IsBoundedAtImInfty h := by
  have hne : ∀ᶠ τ in atImInfty, e τ ≠ 0 := he.eventually_ne one_ne_zero
  have hinv : Tendsto (fun τ => (e τ)⁻¹) atImInfty (𝓝 1) := by simpa using he.inv₀ one_ne_zero
  have hb : IsBoundedAtImInfty ((h * e) * fun τ => (e τ)⁻¹) := hhe.mul (hinv.isBigO_one ℝ)
  refine (hb.congr' ?_ EventuallyEq.rfl)
  filter_upwards [hne] with τ hτ
  simp only [Pi.mul_apply]
  field_simp

private theorem bdd_pow {f : ℍ →
    ℂ} (hf : IsBoundedAtImInfty f) (n : ℕ) : IsBoundedAtImInfty (f ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact Filter.const_boundedAtFilter atImInfty (1 : ℂ)
  | succ n ih => rw [pow_succ]; exact ih.mul hf

private theorem mem_SL (A : SL(2, ℤ)) : (A : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨A, rfl⟩

private theorem E₄_smul (A : SL(2, ℤ)) (τ : ℍ) :
    E₄ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (4 : ℤ) * E₄ τ := by
  have := SlashInvariantForm.slash_action_eqn'' E₄ (Γ := 𝒮ℒ) (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [← ModularGroup.sl_moeb] at this
  exact_mod_cast this

private theorem disc_smul (A : SL(2, ℤ)) (τ : ℍ) :
    Δ (A • τ) = denom (A : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * Δ τ := by
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ)
    (γ := (A : GL (Fin 2) ℝ)) (mem_SL A) τ
  rw [CuspForm.coe_discriminant, ← ModularGroup.sl_moeb] at this
  exact this

private theorem exists_E₄_ne_zero : ∃ τ : ℍ, E₄ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₄ : ModularForm 𝒮ℒ 4) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨2, rfl⟩ this

private theorem exists_E₆_ne_zero : ∃ τ : ℍ, E₆ τ ≠ 0 := by
  by_contra h
  push Not at h
  have : (E₆ : ModularForm 𝒮ℒ 6) = 0 := DFunLike.ext _ _ fun τ => by simpa using h τ
  exact EisensteinSeries.E_ne_zero (by norm_num) ⟨3, rfl⟩ this

end Analytic

section Params

variable {N : ℕ} [NeZero N]
variable (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
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
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)

private abbrev Idx (N : ℕ) : Type := Option {v : Fin 2 → ZMod N // v ≠ 0}

private def gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) : Idx N → ℍ → ℂ :=
  fun o => o.elim jf fun v => fricke (t v.1)

private def ev (t : (Fin 2 → ZMod N) → (Fin 2 →
    ZMod N)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) : ℍ → ℂ :=
  MvPolynomial.aeval (gen fricke jf t) (MvPolynomial.map ψ R)

private def ds (s : ℕ) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := ![v 0, (s : ZMod N) * v 1]

private theorem ds_ne_zero {s : ℕ} (hs : s.Coprime N) {v : Fin 2 →
    ZMod N} (hv : v ≠ 0) : ds s v ≠ 0 := by
  intro h
  apply hv
  have h0 : v 0 = 0 := by simpa [ds] using congrFun h 0
  have h1 : (s : ZMod N) * v 1 = 0 := by simpa [ds] using congrFun h 1
  have hu : IsUnit (s : ZMod N) := (ZMod.unitOfCoprime s hs).isUnit
  have h1' : v 1 = 0 := by simpa using hu.mul_left_cancel (h1.trans (mul_zero _).symm)
  funext i; fin_cases i <;> simp [h0, h1']

private theorem ev_mul (t : (Fin 2 → ZMod N) → (Fin 2 →
    ZMod N)) (ψ : K →+* ℂ) (R S : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (R * S) = ev fricke jf K t ψ R * ev fricke jf K t ψ S := by
  simp [ev]

private theorem ev_pow (t : (Fin 2 → ZMod N) → (Fin 2 →
    ZMod N)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) (n : ℕ) :
    ev fricke jf K t ψ (R ^ n) = ev fricke jf K t ψ R ^ n := by
  simp [ev]

private theorem ev_sub (t : (Fin 2 → ZMod N) → (Fin 2 →
    ZMod N)) (ψ : K →+* ℂ) (R S : MvPolynomial (Idx N) K) :
    ev fricke jf K t ψ (R - S) = ev fricke jf K t ψ R - ev fricke jf K t ψ S := by
  simp [ev]

private theorem ev_X (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (o : Idx N) :
    ev fricke jf K t ψ (MvPolynomial.X o) = gen fricke jf t o := by
  simp [ev, MvPolynomial.map_X]

private theorem ev_C (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : K →+* ℂ) (c : K) :
    ev fricke jf K t ψ (MvPolynomial.C c) = fun _ => ψ c := by
  funext τ
  simp only [ev, MvPolynomial.map_C, MvPolynomial.aeval_C, Pi.algebraMap_apply,
      Algebra.algebraMap_self,
    RingHom.id_apply]

include hL hW hfricke in
private theorem mdifferentiable_fricke {v : Fin 2 →
    ZMod N} (hv : v ≠ 0) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fricke v) :=
  ModularForm.mdifferentiable_frickeFunction N L hL W hW fricke hfricke hv

include hjf in
private theorem mdifferentiable_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf := by
  have : jf = fun τ => E₄ τ ^ 3 / Δ τ := funext hjf
  rw [this]
  intro τ
  exact ((E₄.holo' τ).pow 3).div (mdifferentiable_disc τ) (discriminant_ne_zero τ)

include hL hW hfricke hjf in
private theorem mdifferentiable_gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v,
    v ≠ 0 → t v ≠ 0)
    (o : Idx N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen fricke jf t o) := by
  cases o with
  | none => exact mdifferentiable_jf jf hjf
  | some v => exact mdifferentiable_fricke L hL W hW fricke hfricke (ht v.1 v.2)

include hL hW hfricke hjf in
private theorem mdifferentiable_ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v,
    v ≠ 0 → t v ≠ 0)
    (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ev fricke jf K t ψ
        R) := by
  rw [ev]
  induction (MvPolynomial.map ψ R) using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact mdifferentiable_const
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact hp.mul (mdifferentiable_gen L hL W hW fricke hfricke jf hjf t ht o)

include hjf in
private theorem jf_smul (α : SL(2, ℤ)) (τ : ℍ) : jf (α • τ) = jf τ := by
  have hd : denom (α : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  have hΔ : Δ τ ≠ 0 := discriminant_ne_zero τ
  rw [hjf, hjf, disc_smul, E₄_smul]
  field_simp

include hjf in
private theorem E₄_cube_eq (τ : ℍ) : E₄ τ ^ 3 = jf τ * Δ τ := by
  rw [hjf]; field_simp [disc_ne_zero τ]

include hjf in
private theorem E₆_sq_eq (τ : ℍ) : E₆ τ ^ 2 = (jf τ - 1728) * Δ τ := by
  have h := discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [hjf, sub_mul, div_mul_cancel₀ _ (disc_ne_zero τ)]
  linear_combination (1728 : ℂ) * h

include hjf in
private theorem exists_jf_ne_zero : ∃ τ : ℍ, jf τ ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_E₄_ne_zero
  exact ⟨τ, fun h => pow_ne_zero 3 hτ (by rw [E₄_cube_eq jf hjf, h, zero_mul])⟩

include hjf in
private theorem exists_jf_sub_ne_zero : ∃ τ : ℍ, jf τ - 1728 ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_E₆_ne_zero
  exact ⟨τ, fun h => pow_ne_zero 2 hτ (by rw [E₆_sq_eq jf hjf, h, zero_mul])⟩

private def redN (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  (γ : Matrix (Fin 2) (Fin 2) ℤ).map ((↑) : ℤ → ZMod N)

private def vm (γ : SL(2, ℤ)) (v : Fin 2 → ZMod N) : Fin 2 → ZMod N := Matrix.vecMul v (redN γ)

private theorem redN_eq (γ : SL(2, ℤ)) :
    redN (N := N) γ = (Int.castRingHom (ZMod N)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) ℤ) := rfl

private theorem redN_mul (γ γ' : SL(2, ℤ)) : redN (N := N) (γ * γ') = redN γ * redN γ' := by
  rw [redN_eq, redN_eq, redN_eq, Matrix.SpecialLinearGroup.coe_mul, map_mul]

private theorem redN_one : redN (N := N) 1 = 1 := by
  rw [redN, Matrix.SpecialLinearGroup.coe_one]; simp

private theorem vm_mul (γ γ' : SL(2, ℤ)) (v : Fin 2 → ZMod N) : vm (γ * γ') v = vm γ' (vm γ v) := by
  simp only [vm, redN_mul, Matrix.vecMul_vecMul]

private theorem vm_one (v : Fin 2 → ZMod N) : vm (N := N) 1 v = v := by simp [vm, redN_one]

private theorem vm_ne_zero (γ : SL(2, ℤ)) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : vm γ v ≠ 0 := by
  intro h
  apply hv
  have : vm γ⁻¹ (vm γ v) = v := by rw [← vm_mul, mul_inv_cancel, vm_one]
  rw [← this, h, vm, Matrix.zero_vecMul]

private def idxMap (α : SL(2, ℤ)) : Idx N → Idx N :=
  fun o => o.map fun v => ⟨vm α v.1, vm_ne_zero α v.2⟩

private def cw (G : ℍ → ℂ) (α : SL(2, ℤ)) : ℍ → ℂ := fun τ => G (α • τ)

private theorem cw_apply (G : ℍ → ℂ) (α : SL(2, ℤ)) (τ : ℍ) : cw G α τ = G (α • τ) := rfl

private theorem cw_mul (G : ℍ → ℂ) (α β : SL(2, ℤ)) : cw G (α * β) = cw (cw G α) β := by
  funext τ; simp [cw, mul_smul]

private theorem cw_one (G : ℍ → ℂ) : cw G 1 = G := by funext τ; simp [cw]

private theorem cw_eq_slash (G : ℍ → ℂ) (α : SL(2, ℤ)) : cw G α = G ∣[(0 : ℤ)] α := by
  funext τ
  rw [ModularForm.SL_slash_apply, cw_apply, neg_zero, zpow_zero, mul_one]

private theorem mdifferentiable_cw {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G) (α : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cw G α) := by
  rw [cw_eq_slash, ModularForm.SL_slash]; exact hG.slash _ _

private def cwAlgHom (α : SL(2, ℤ)) : (ℍ → ℂ) →ₐ[ℂ] (ℍ → ℂ) where
  toFun G := cw G α
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem cw_mul_fun (G G' : ℍ → ℂ) (α : SL(2, ℤ)) : cw (G * G') α = cw G α * cw G' α := rfl

private theorem cw_ne_zero {b : ℍ → ℂ} (hb : b ≠ 0) (γ : SL(2, ℤ)) : cw b γ ≠ 0 := by
  intro h
  apply hb
  have : cw (cw b γ) γ⁻¹ = b := by rw [← cw_mul, mul_inv_cancel, cw_one]
  rw [← this, h]; rfl

private theorem cw_aeval {ι : Type} (g : ι → ℍ → ℂ) (R : MvPolynomial ι ℂ) (α : SL(2, ℤ)) :
    cw (MvPolynomial.aeval g R) α = MvPolynomial.aeval (fun i => cw (g i) α) R := by
  have := MvPolynomial.comp_aeval g (cwAlgHom α)
  exact congrArg (fun F => F R) this

include hL hW hfricke in
private theorem fricke_smul (v : Fin 2 → ZMod N) (γ : SL(2,
    ℤ)) (τ : ℍ) : fricke v (γ • τ) = fricke (vm γ v) τ :=
  ModularForm.frickeFunction_smul N L hL W hW fricke hfricke v γ τ

include hL hW hfricke hjf in
private theorem cw_gen {t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)} {α α' : SL(2, ℤ)}
    (h : ∀ v, vm α (t v) = t (vm α' v)) (o : Idx N) :
    cw (gen fricke jf t o) α = gen fricke jf t (idxMap α' o) := by
  cases o with
  | none => funext τ; exact jf_smul jf hjf α τ
  | some v => funext τ; rw [cw_apply, gen, gen, Option.elim, fricke_smul L hL W hW fricke hfricke,
                h]; rfl

include hL hW hfricke hjf in
private theorem cw_ev {t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)} {α α' : SL(2, ℤ)}
    (h : ∀ v, vm α (t v) = t (vm α' v)) (ψ : K →+* ℂ) (R : MvPolynomial (Idx N) K) :
    cw (ev fricke jf K t ψ R) α = ev fricke jf K t ψ (MvPolynomial.rename (idxMap α') R) := by
  rw [ev, ev, cw_aeval, MvPolynomial.map_rename, MvPolynomial.aeval_rename]
  have : (fun i => cw (gen fricke jf t i) α) = gen fricke jf t ∘ idxMap α' :=
    funext fun o => cw_gen L hL W hW fricke hfricke jf hjf h o
  rw [this]

private theorem T_zpow_mem_Gamma1 (n : ℤ) : ModularGroup.T ^ n ∈ Gamma1 N := by
  rw [Gamma1_mem, ModularGroup.coe_T_zpow]
  simp

include hs in
private theorem exists_gamma1_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    ∃ γ' ∈ Gamma1 N, ∀ v : Fin 2 → ZMod N, vm γ (ds s v) = ds s (vm γ' v) := by
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime s hs with hu
  set t : ℤ := (((u⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ) with ht
  have hst : (s : ZMod N) * (t : ZMod N) = 1 := by
    have h1 : ((u : ZMod N)) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := Units.mul_inv u
    rw [ht, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact h1
  obtain ⟨h00, h11, h10⟩ := (Gamma1_mem N γ).1 hγ
  refine ⟨ModularGroup.T ^ ((γ 0 1 : ℤ) * t), T_zpow_mem_Gamma1 _, fun v => ?_⟩
  have hT : redN (N :=
      N) (ModularGroup.T ^ ((γ 0 1 : ℤ) * t)) = !![1, ((γ 0 1 : ℤ) : ZMod N) * t; 0, 1] := by
    rw [redN, ModularGroup.coe_T_zpow]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hγm : redN (N := N) γ = !![1, ((γ 0 1 : ℤ) : ZMod N); 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [redN, h00, h11, h10]
  funext i
  simp only [vm, hT, hγm, ds]
  fin_cases i
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    linear_combination (-(v 0 * ((γ 0 1 : ℤ) : ZMod N))) * hst

include hs in
private theorem exists_SL2_conj (A : SL(2, ℤ)) :
    ∃ A' : SL(2, ℤ), ∀ v : Fin 2 → ZMod N, vm A (ds s v) = ds s (vm A' v) := by
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime s hs with hu
  set tN : ZMod N := ((u⁻¹ : (ZMod N)ˣ) : ZMod N) with htN
  have hst : (s : ZMod N) * tN = 1 := Units.mul_inv u
  have hts : tN * (s : ZMod N) = 1 := Units.inv_mul u
  let D : Matrix (Fin 2) (Fin 2) (ZMod N) := !![1, 0; 0, (s : ZMod N)]
  let Di : Matrix (Fin 2) (Fin 2) (ZMod N) := !![1, 0; 0, tN]
  have hDDi : Di * D = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [D, Di, Matrix.mul_apply, Fin.sum_univ_two, hts]
  have hds : ∀ v : Fin 2 → ZMod N, ds s v = Matrix.vecMul v D := by
    intro v; funext i; fin_cases i <;> simp [ds, D, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        mul_comm]
  set M' : Matrix (Fin 2) (Fin 2) (ZMod N) := D * redN A * Di with hM'
  have hdetA : (redN (N := N) A).det = 1 := by
    rw [redN_eq, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]
  have hdet : M'.det = 1 := by
    rw [hM', Matrix.det_mul, Matrix.det_mul, hdetA]
    simp [D, Di, Matrix.det_fin_two, hst]
  obtain ⟨A', hA'⟩ := Matrix.SpecialLinearGroup.map_intCastRingHom_zmod_surjective N ⟨M', hdet⟩
  have hred : redN (N := N) A' = M' := by
    have := congrArg (fun y : SL(2, ZMod N) => (y : Matrix (Fin 2) (Fin 2) (ZMod N))) hA'
    simpa [redN_eq] using this
  refine ⟨A', fun v => ?_⟩
  rw [vm, vm, hds, hds, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hred, hM', Matrix.mul_assoc,
    Matrix.mul_assoc, hDDi, Matrix.mul_one]

private def TD (m₀ : ℕ) (u u' : ℍ → ℂ) : Prop := ∀ M : ℕ, m₀ ≤ M →
  (Function.Periodic ((u * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
    IsBoundedAtImInfty (u * ModularForm.discriminant ^ M) ∧
    ∀ n : ℕ, (UpperHalfPlane.qExpansion N (u * ModularForm.discriminant ^ M)).coeff n ∈ K) ∧
  (Function.Periodic ((u' * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
    IsBoundedAtImInfty (u' * ModularForm.discriminant ^ M) ∧
    ∀ n : ℕ, (UpperHalfPlane.qExpansion N (u' * ModularForm.discriminant ^ M)).coeff n ∈ K) ∧
  ∀ (n : ℕ) (z : ↥K),
    (z : ℂ) = (UpperHalfPlane.qExpansion N (u * ModularForm.discriminant ^ M)).coeff n →
    (UpperHalfPlane.qExpansion N (u' * ModularForm.discriminant ^ M)).coeff n = φ z

include hL hW hfricke hjf hK hs hφ in
private theorem transportT {u : ℍ →
    ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (P Q : MvPolynomial (Idx N) K)
    (hQ0 : ev fricke jf K id (algebraMap K ℂ) Q ≠ 0)
    (huQ : u * ev fricke jf K id (algebraMap K ℂ) Q = ev fricke jf K id (algebraMap K ℂ) P) :
    ev fricke jf K (ds s) φ Q ≠ 0 ∧ ∃ u' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u' ∧
      u' * ev fricke jf K (ds s) φ Q = ev fricke jf K (ds s) φ P ∧ ∃ m₀ : ℕ, TD (N :=
          N) K φ m₀ u u' :=
  ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient N L hL W hW fricke
      hfricke jf hjf K hK
    s hs φ hφ u hu P Q hQ0 huQ

private theorem natCast_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

private theorem eq_of_TD {u F₁ F₂ : ℍ →
    ℂ} (h₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F₁) (h₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F₂)
    {m₁ m₂ : ℕ} (hT₁ : TD (N := N) K φ m₁ u F₁) (hT₂ : TD (N := N) K φ m₂ u F₂) : F₁ = F₂ := by
  set M : ℕ := m₁ + m₂ with hM
  obtain ⟨⟨-, -, hmem⟩, ⟨hper₁, hbd₁, -⟩, hco₁⟩ := hT₁ M (Nat.le_add_right _ _)
  obtain ⟨-, ⟨hper₂, hbd₂, -⟩, hco₂⟩ := hT₂ M (Nat.le_add_left _ _)
  have hexp : qExpansion N (F₁ * Δ ^ M) = qExpansion N (F₂ * Δ ^ M) := by
    ext n
    obtain ⟨z, hz⟩ : ∃ z : K, (z : ℂ) = (qExpansion N (u * Δ ^ M)).coeff n := ⟨⟨_, hmem n⟩, rfl⟩
    rw [hco₁ n z hz, hco₂ n z hz]
  have hmd₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F₁ * Δ ^ M) := h₁.mul (mdifferentiable_disc.pow M)
  have hmd₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F₂ * Δ ^ M) := h₂.mul (mdifferentiable_disc.pow M)
  have han₁ := analyticAt_cuspFunction_zero (natCast_pos (N := N)) hper₁ hmd₁ hbd₁
  have han₂ := analyticAt_cuspFunction_zero (natCast_pos (N := N)) hper₂ hmd₂ hbd₂
  have hzero : qExpansion N (F₁ * Δ ^ M - F₂ * Δ ^ M) = 0 := by
    rw [qExpansion_sub han₁ han₂, hexp, sub_self]
  rw [qExpansion_eq_zero_iff (natCast_pos (N :=
      N)) (periodic_sub hper₁ hper₂) (hmd₁.sub hmd₂) (hbd₁.sub hbd₂)]
    at hzero
  funext τ
  have := congrFun hzero τ
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at this
  have hΔ : Δ τ ^ M ≠ 0 := pow_ne_zero _ (disc_ne_zero τ)
  have : (F₁ τ - F₂ τ) * Δ τ ^ M = 0 := by rw [sub_mul]; exact this
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hΔ)

private theorem isZero_of_TD {u u' : ℍ →
    ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (hu' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u')
    {m₀ : ℕ} (hT : TD (N := N) K φ m₀ u u') (r : ℕ) (hz : IsZeroAtImInfty (u * Δ ^ r)) :
    IsZeroAtImInfty (u' * Δ ^ r) := by
  set M : ℕ := m₀ + 1 + r with hM
  obtain ⟨⟨hper, hbd, hmem⟩, ⟨hper', hbd', -⟩, hco⟩ := hT M (by omega)
  have hΔ : ∀ τ : ℍ, Δ τ ≠ 0 := disc_ne_zero
  have gen_facts : ∀ (w : ℍ → ℂ),
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) w → Periodic ((w * Δ ^ M) ∘ ofComplex) N →
      let F : ℍ → ℂ := fun τ => w τ * Δ τ ^ r / Δ τ
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ Periodic (F ∘ ofComplex) N ∧
        F * Δ = w * Δ ^ r ∧ F * Δ ^ (m₀ + 2) = w * Δ ^ M := by
    intro w hw hwper F
    have hF1 : F * Δ = w * Δ ^ r := by
      funext τ; have hΔτ := hΔ τ; simp only [F, Pi.mul_apply, Pi.pow_apply]; field_simp
    have hF2 : F * Δ ^ (m₀ + 2) = w * Δ ^ M := by
      funext τ; have hΔτ := hΔ τ
      simp only [F, Pi.mul_apply, Pi.pow_apply]
      rw [div_mul_eq_mul_div, div_eq_iff hΔτ, hM]
      ring
    have hFeq : F = fun τ => (w * Δ ^ M) τ / Δ τ ^ (m₀ + 2) := by
      funext τ
      have := congrFun hF2 τ
      simp only [Pi.mul_apply, Pi.pow_apply] at this ⊢
      rw [← this, mul_div_assoc, div_self (pow_ne_zero _ (hΔ τ)), mul_one]
    refine ⟨?_, ?_, hF1, hF2⟩
    · have hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => Δ τ ^ r / Δ τ) := by
        have h' : (fun τ : ℍ => Δ τ ^ r / Δ τ) = (fun τ => (Δ ^ r : ℍ → ℂ) τ / Δ τ ^ 1) := by
          funext τ; simp
        rw [h']; exact mdifferentiable_div_disc_pow (mdifferentiable_disc.pow r) 1
      have : F = w * fun τ => Δ τ ^ r / Δ τ := by funext τ; simp only [F, Pi.mul_apply]; ring
      rw [this]; exact hw.mul hq
    · rw [hFeq]; exact periodic_div_disc_pow hwper (m₀ + 2)
  have hM1 : 1 ≤ m₀ + 2 := by omega
  obtain ⟨hFhol, hFper, hF1, hF2⟩ := gen_facts u hu hper
  have hcoef :=
      (ModularForm.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le N hM1 hFhol hFper
        (by rw [hF2]; exact hbd)).1
    (by rw [hF1]; exact hz)
  rw [hF2] at hcoef
  obtain ⟨hFhol', hFper', hF1', hF2'⟩ := gen_facts u' hu' hper'
  have := (ModularForm.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le N hM1 hFhol' hFper'
    (by rw [hF2']; exact hbd')).2
  rw [hF1', hF2'] at this
  refine this fun n hn => ?_
  obtain ⟨z, hz'⟩ : ∃ z : K, (z : ℂ) = (qExpansion N (u * Δ ^ M)).coeff n := ⟨⟨_, hmem n⟩, rfl⟩
  have hz0 : z = 0 := by
    apply Subtype.val_injective
    rw [hz', hcoef n hn]; rfl
  rw [hco n z hz', hz0, map_zero]

section Main

local notation "𝔢" => ev fricke jf K id (algebraMap K ℂ)
local notation "𝔢'" => ev fricke jf K (ds s) φ
local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable (k : ℤ) (a b m : ℕ) (hk : k + 4 * (a : ℤ) + 6 * (b : ℤ) = 12 * (m : ℤ))

include hL hW hfricke hjf hK hs hφ in
private theorem transport_pow_div (p q : ℕ) (E : ℍ → ℂ) (J₀ : MvPolynomial (Idx N) K)
    (hEJ : ∀ τ : ℍ, E τ ^ p = 𝔢 J₀ τ * Δ τ) (hJ' : 𝔢' J₀ = 𝔢 J₀) (hJ0 : ∃ τ : ℍ, 𝔢 J₀ τ ≠ 0)
    {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) {P Q : MvPolynomial (Idx N) K} (hQ0 : 𝔢 Q ≠ 0)
    (huQ : u * 𝔢 Q = 𝔢 P) {F : ℍ → ℂ} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hQ'0 : 𝔢' Q ≠ 0)
    (hFQ : F * 𝔢' Q = 𝔢' P)
    (h : ∃ G : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : ℍ,
        (u τ * Δ τ ^ m) ^ p = E τ ^ (p * q) * G τ) :
    ∃ G' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G' ∧
      ∀ τ : ℍ, (F τ * Δ τ ^ m) ^ p = E τ ^ (p * q) * G' τ := by
  obtain ⟨G, hG, hGrel⟩ := h
  set J : ℍ → ℂ := 𝔢 J₀ with hJdef
  have hJhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) J :=
      mdifferentiable_ev L hL W hW fricke hfricke jf hjf K id (fun v hv => hv) _ J₀
  have hΔ : ∀ τ : ℍ, Δ τ ≠ 0 := disc_ne_zero
  have hΔm : ∀ τ : ℍ, Δ τ ^ m ≠ 0 := fun τ => pow_ne_zero _ (hΔ τ)
  let W₁ : ℍ → ℂ := fun τ => G τ * Δ τ ^ q / (Δ τ ^ m) ^ p
  have hW₁hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) W₁ := by
    have := mdifferentiable_div_disc_pow (hG.mul (mdifferentiable_disc.pow q)) (m * p)
    convert this using 1
    funext τ; simp only [W₁, pow_mul, Pi.mul_apply, Pi.pow_apply]
  have huW : ∀ τ : ℍ, u τ ^ p = J τ ^ q * W₁ τ := by
    intro τ
    have e1 : u τ ^ p * (Δ τ ^ m) ^ p = J τ ^ q * Δ τ ^ q * G τ := by
      rw [← mul_pow, hGrel τ, pow_mul, hEJ τ, mul_pow]
    have hp : (Δ τ ^ m) ^ p ≠ 0 := pow_ne_zero _ (hΔm τ)
    simp only [W₁]
    field_simp
    linear_combination e1
  have hden : 𝔢 (J₀ ^ q * Q ^ p) ≠ 0 := by
    rw [ev_mul, ev_pow, ev_pow]
    intro h0
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero (pow_ne_zero_fun hQ0 p)
    have hz := eq_zero_of_mul_eq_zero (hJhol.pow q)
      ((mdifferentiable_ev L hL W hW fricke hfricke jf hjf K id (fun v hv => hv) _ Q).pow p)
      (fun τ => by simpa using congrFun h0 τ) hτ₀
    obtain ⟨τ₁, hτ₁⟩ := hJ0
    exact pow_ne_zero q hτ₁ (by simpa using congrFun hz τ₁)
  have hW₁Q : W₁ * 𝔢 (J₀ ^ q * Q ^ p) = 𝔢 (P ^ p) := by
    rw [ev_mul, ev_pow, ev_pow, ev_pow, ← huQ, mul_pow]
    funext τ
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [huW τ]; ring
  obtain ⟨-, W₁', hW₁', hW₁'Q, -⟩ :=
      transportT L hL W hW fricke hfricke jf hjf K hK s hs φ hφ hW₁hol _ _ hden hW₁Q
  have hFW : F ^ p = J ^ q * W₁' := by
    have hrel : ∀ τ : ℍ, (F ^ p - J ^ q * W₁') τ * (𝔢' Q ^ p) τ = 0 := by
      intro τ
      have e1 := congrFun hW₁'Q τ
      have e2 := congrFun hFQ τ
      rw [ev_mul, ev_pow, ev_pow, ev_pow, hJ'] at e1
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply] at e1 e2 ⊢
      rw [← e2, mul_pow] at e1
      linear_combination -e1
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero (pow_ne_zero_fun hQ'0 p)
    have := eq_zero_of_mul_eq_zero ((hF.pow p).sub ((hJhol.pow q).mul hW₁'))
      ((mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv =>
          ds_ne_zero hs hv) φ Q).pow p)
      hrel hτ₀
    exact sub_eq_zero.1 this
  refine ⟨fun τ => W₁' τ * (Δ τ ^ m) ^ p / Δ τ ^ q, ?_, fun τ => ?_⟩
  · have := mdifferentiable_div_disc_pow (hW₁'.mul ((mdifferentiable_disc.pow m).pow p)) q
    convert this using 1
  · have h1 := congrFun hFW τ
    simp only [Pi.pow_apply, Pi.mul_apply] at h1
    have hq0 : Δ τ ^ q ≠ 0 := pow_ne_zero _ (hΔ τ)
    rw [mul_pow, h1, pow_mul, hEJ τ, mul_pow]
    field_simp

variable {k a b m}

private def Φ (f : CuspForm (Γ₁ℝ N) k) : ℍ → ℂ := fun τ => f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m

private theorem Φ_apply (f : CuspForm (Γ₁ℝ N) k) (τ : ℍ) : Φ (a := a) (b := b) (m :=
    m) f τ = f τ * (E₄ τ ^ a * E₆ τ ^ b) / Δ τ ^ m := rfl

private theorem Φ_mul_disc (f : CuspForm (Γ₁ℝ N) k) (τ : ℍ) :
    f τ * (E₄ τ ^ a * E₆ τ ^ b) = Φ (a := a) (b := b) (m := m) f τ * Δ τ ^ m := by
  rw [Φ_apply, div_mul_cancel₀ _ (pow_ne_zero _ (disc_ne_zero τ))]

private theorem mdifferentiable_Φ (f : CuspForm (Γ₁ℝ N) k) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Φ (a :=
    a) (b := b) (m := m) f) :=
  mdifferentiable_div_disc_pow (f.holo'.mul ((E₄.holo'.pow a).mul (E₆.holo'.pow b))) m

include hL hW hfricke hjf hK hs hφ hk in
private theorem main (f : CuspForm (Γ₁ℝ N) k) (P Q : MvPolynomial (Idx N) K) (hQ0 : 𝔢 Q ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (E₄ τ ^ a * E₆ τ ^ b) * 𝔢 Q τ = Δ τ ^ m * 𝔢 P τ) :
    ∃ f' : CuspForm (Γ₁ℝ N) k, 𝔢' Q ≠ 0 ∧
      ∀ τ : ℍ, f' τ * (E₄ τ ^ a * E₆ τ ^ b) * 𝔢' Q τ = Δ τ ^ m * 𝔢' P τ := by
  set G : ℍ → ℂ := Φ (a := a) (b := b) (m := m) f with hGdef
  have hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := mdifferentiable_Φ f
  have hGQ : G * 𝔢 Q = 𝔢 P := by
    funext τ
    have h1 := hid τ
    simp only [Pi.mul_apply]
    apply mul_left_cancel₀ (pow_ne_zero m (disc_ne_zero τ))
    rw [← h1, Φ_mul_disc f τ]
    ring
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
      (CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Gamma1 N) k a b m hk G hG).1
    ⟨f, Φ_mul_disc f⟩
  obtain ⟨hQ'0, F, hF, hFQ, mF, hTF⟩ :=
      transportT L hL W hW fricke hfricke jf hjf K hK s hs φ hφ hG P Q hQ0 hGQ
  have h₄' : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, F (γ • τ) = F τ := by
    intro γ hγ
    obtain ⟨γ', hγ', hconj⟩ := exists_gamma1_conj s hs hγ
    have hGinv : cw G γ' = G := funext fun τ => h₄ γ' hγ' τ
    have hQγ : 𝔢 (MvPolynomial.rename (idxMap γ') Q) ≠ 0 := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := γ') (α' := γ') (fun v => rfl)]
      exact cw_ne_zero hQ0 γ'
    have hGQγ : G * 𝔢 (MvPolynomial.rename (idxMap γ') Q)
        = 𝔢 (MvPolynomial.rename (idxMap γ') P) := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := γ') (α' := γ') (fun v => rfl),
        ← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := γ') (α' :=
            γ') (fun v => rfl), ← hGinv,
        ← cw_mul_fun, hGQ]
    obtain ⟨hQ'γ, F₂, hF₂, hF₂Q, m₂, hT₂⟩ :=
        transportT L hL W hW fricke hfricke jf hjf K hK s hs φ hφ hG _ _ hQγ hGQγ
    have hFF₂ : F = F₂ := eq_of_TD K φ hF hF₂ hTF hT₂
    have hcwF : cw F γ * 𝔢' (MvPolynomial.rename (idxMap γ') Q)
        = 𝔢' (MvPolynomial.rename (idxMap γ') P) := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K hconj,
          ← cw_ev L hL W hW fricke hfricke jf hjf K hconj,
        ← cw_mul_fun, hFQ]
    have hdiff : ∀ τ : ℍ, (cw F γ - F₂) τ * 𝔢' (MvPolynomial.rename (idxMap γ') Q) τ = 0 := by
      intro τ
      have e1 := congrFun hcwF τ
      have e2 := congrFun hF₂Q τ
      simp only [Pi.mul_apply, Pi.sub_apply] at e1 e2 ⊢
      rw [sub_mul, e1, e2, sub_self]
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero hQ'γ
    have hz := eq_zero_of_mul_eq_zero ((mdifferentiable_cw hF γ).sub hF₂)
      (mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv =>
          ds_ne_zero hs hv) φ _) hdiff hτ₀
    intro τ
    have := congrFun hz τ
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero, cw_apply] at this
    rw [this, ← hFF₂]
  have hJ₄ : 𝔢 (MvPolynomial.X none) = jf := by rw [ev_X]; rfl
  have hJ₄' : 𝔢' (MvPolynomial.X none) = 𝔢 (MvPolynomial.X none) := by rw [ev_X, ev_X]; rfl
  have h₁' :=
      transport_pow_div L hL W hW fricke hfricke jf hjf K hK s hs φ hφ m 3 a (E₄ : ℍ →
      ℂ) (MvPolynomial.X none)
    (fun τ =>
        by rw [hJ₄]; exact E₄_cube_eq jf hjf τ) hJ₄' (by rw [hJ₄]; exact exists_jf_ne_zero jf hjf)
    hG hQ0 hGQ hF hQ'0 hFQ h₁
  set c1728 : K := algebraMap ℚ K 1728 with hc
  have hc' : ((c1728 : K) : ℂ) = 1728 := by
    rw [hc, eq_ratCast, SubfieldClass.coe_ratCast]; norm_num
  have hcφ : φ c1728 = 1728 := by
    rw [hc, ← RingHom.comp_apply, eq_ratCast]; norm_num
  have hJ₆ : 𝔢 (MvPolynomial.X none - MvPolynomial.C c1728) = fun τ => jf τ - 1728 := by
    rw [ev_sub, ev_X, ev_C]; funext τ; simp only [Pi.sub_apply, gen, Option.elim]; rw [← hc']; rfl
  have hJ₆' : 𝔢' (MvPolynomial.X none - MvPolynomial.C c1728) = 𝔢 (MvPolynomial.X none
      - MvPolynomial.C c1728) := by
    rw [hJ₆, ev_sub, ev_X, ev_C, hcφ]; rfl
  have h₂' := transport_pow_div L hL W hW fricke hfricke jf hjf K hK s hs φ hφ m 2 b (E₆ : ℍ → ℂ)
    (MvPolynomial.X none - MvPolynomial.C c1728)
    (fun τ =>
        by rw [hJ₆]; exact E₆_sq_eq jf hjf τ) hJ₆' (by rw [hJ₆]; exact exists_jf_sub_ne_zero jf hjf)
    hG hQ0 hGQ hF hQ'0 hFQ h₂
  have h₃' : ∀ A : SL(2, ℤ), IsZeroAtImInfty ((F ∘ (A • ·)) * Δ ^ m) := by
    intro A
    obtain ⟨A', hconj⟩ := exists_SL2_conj s hs A
    have hQA : 𝔢 (MvPolynomial.rename (idxMap A') Q) ≠ 0 := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := A') (α' := A') (fun v => rfl)]
      exact cw_ne_zero hQ0 A'
    have hGQA : cw G A' * 𝔢 (MvPolynomial.rename (idxMap A') Q)
        = 𝔢 (MvPolynomial.rename (idxMap A') P) := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := A') (α' := A') (fun v => rfl),
        ← cw_ev L hL W hW fricke hfricke jf hjf K (t := id) (α := A') (α' :=
            A') (fun v => rfl), ← cw_mul_fun, hGQ]
    obtain ⟨hQ'A, F₂, hF₂, hF₂Q, m₂, hT₂⟩ :=
        transportT L hL W hW fricke hfricke jf hjf K hK s hs φ hφ
      (mdifferentiable_cw hG A') _ _ hQA hGQA
    have hcwF : cw F A * 𝔢' (MvPolynomial.rename (idxMap A') Q)
        = 𝔢' (MvPolynomial.rename (idxMap A') P) := by
      rw [← cw_ev L hL W hW fricke hfricke jf hjf K hconj,
          ← cw_ev L hL W hW fricke hfricke jf hjf K hconj,
        ← cw_mul_fun, hFQ]
    have hdiff : ∀ τ : ℍ, (cw F A - F₂) τ * 𝔢' (MvPolynomial.rename (idxMap A') Q) τ = 0 := by
      intro τ
      have e1 := congrFun hcwF τ
      have e2 := congrFun hF₂Q τ
      simp only [Pi.mul_apply, Pi.sub_apply] at e1 e2 ⊢
      rw [sub_mul, e1, e2, sub_self]
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero hQ'A
    have hz := eq_zero_of_mul_eq_zero ((mdifferentiable_cw hF A).sub hF₂)
      (mdifferentiable_ev L hL W hW fricke hfricke jf hjf K (ds s) (fun v hv =>
          ds_ne_zero hs hv) φ _) hdiff hτ₀
    have hcwF₂ : cw F A = F₂ := sub_eq_zero.1 hz
    have : (F ∘ (A • ·)) = cw F A := rfl
    rw [this, hcwF₂]
    exact isZero_of_TD K φ (mdifferentiable_cw hG A') hF₂ hT₂ m (h₃ A')
  obtain ⟨f', hf'⟩ :=
      (CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Gamma1 N) k a b m hk F hF).2 ⟨h₁', h₂', h₃',
      h₄'⟩
  refine ⟨f', hQ'0, fun τ => ?_⟩
  have e1 := congrFun hFQ τ
  simp only [Pi.mul_apply] at e1
  rw [hf' τ, mul_comm (F τ), mul_assoc, e1]

end Main

end Params

end FrickeCuspTransport

end

open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

/-- Galois transport of `Γ₁(N)` cusp forms with a Fricke-rational expression. Let `K = ℚ(ζ_N)`, `s`
coprime to `N`, `φ : K →+* ℂ` with `φ ζ_N = ζ_N ^ s`, and `k + 4a + 6b = 12m`. Let `f` be a
cusp form of weight `k` on `Γ₁(N)` and let `P`, `Q` be polynomials over `K` in `j` and the
Fricke functions `f_v`, `v ≠ 0`, such that `Q` evaluates to a nonzero function and `f E₄ ^ a E₆
^ b Q = Δ ^ m P` after evaluation. Then there is a cusp form `f'` of weight `k` on `Γ₁(N)` such
that `Q.map φ`, evaluated at `j` and the transported Fricke functions `f_{(v₀, s v₁)}`, is
nonzero and `f' E₄ ^ a E₆ ^ b (Q.map φ) = Δ ^ m (P.map φ)` after evaluation. The conclusion
includes nonvanishing of the transported denominator; the theorem does not assert that every
cusp form admits such an expression. -/
public theorem _root_.CuspForm.exists_gamma1_frickeRational_sigmaTransport
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
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) τ =
      ModularForm.discriminant τ ^ m *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (P.map (algebraMap ↥K ℂ)) τ) :
    ∃ f' : CuspForm (CongruenceSubgroup.Gamma1 N) k,
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) ≠ 0 ∧
      ∀ τ : ℍ, f' τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
          MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
            o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) τ =
        ModularForm.discriminant τ ^ m *
          MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
            o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (P.map φ) τ :=
  FrickeCuspTransport.main L hL W hW fricke hfricke jf hjf K hK s hs φ hφ hk f P Q hQ0 hid

end Gamma1FrickeRationalTransport

end FrickeFunctions
