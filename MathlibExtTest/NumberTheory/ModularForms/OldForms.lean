/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.OldForms
public import Mathlib.NumberTheory.ModularForms.Discriminant

@[expose] public section

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- Source-shaped consumer: the original binders, in the original form. -/
example {R M : ℕ} [NeZero M] (h : 1 * R ∣ M) (hRM : R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) :
    CuspForm.rescaleLin h k f = CuspForm.levelInclusionLin hRM k f :=
  CuspForm.rescaleLin_eq_levelInclusionLin h hRM k f

/-- The rescaling map at `d = 1` is computed by the same underlying
function as the level inclusion. -/
example {R M : ℕ} [NeZero M] (h : 1 * R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) :
    ⇑(CuspForm.rescaleLin h k f) = ⇑f := by
  rw [CuspForm.coe_rescaleLin_apply, ModularForm.heckeDiagMatrix_one,
    SlashAction.slash_one]

/-- Nontrivial rescaling: at levels `R = 1`, `d = M = 2`, the underlying
function of any rescaled form is the original function slashed by the
diagonal matrix `!![2, 0; 0, 1]`. -/
example (k : ℤ) (f : CuspForm (Gamma0 1) k) :
    ⇑(CuspForm.rescaleLin (M := 2) (d := 2) (by norm_num) k f)
      = ⇑f ∣[k] ModularForm.heckeDiagMatrix 2 :=
  CuspForm.coe_rescaleLin_apply _ k f

/-- The `Γ₀(1)` subgroup of `GL (Fin 2) ℝ` is the image of `SL(2, ℤ)`. -/
private lemma Gamma0One_coe_eq :
    ((Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  have h0 : Gamma0 1 = ⊤ := by
    ext g
    simp only [CongruenceSubgroup.Gamma0_mem, Subgroup.mem_top, iff_true]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (one_dvd _)
  rw [← CongruenceSubgroup.Gamma_one_coe_eq_SL, h0,
    CongruenceSubgroup.Gamma_one_top]

/-- The modular discriminant, viewed as a cusp form on `Γ₀(1)`. -/
private noncomputable def discrGamma0One : CuspForm (Gamma0 1) 12 :=
  CuspForm.mcast rfl CuspForm.discriminant Gamma0One_coe_eq

private lemma coe_discrGamma0One :
    ⇑discrGamma0One = ModularForm.discriminant := CuspForm.coe_discriminant

/-- Rescaling by `2` moves the discriminant: the rescaled cusp form at
level `Γ₀(2)` differs from the level inclusion of the same form. The
rescaled function is `2048 • Δ(2τ)` while `Δ(τ) / q(τ)` tends to `1` at
infinity and the rescaled ratio tends to `0`. -/
example : CuspForm.rescaleLin (M := 2) (d := 2) (by norm_num) 12 discrGamma0One ≠
    CuspForm.levelInclusionLin (by norm_num) 12 discrGamma0One := by
  intro h
  have hfun : (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix 2)
      = ModularForm.discriminant := by
    have hc := congrArg (fun g : CuspForm (Gamma0 2) 12 => (g : ℍ → ℂ)) h
    rwa [CuspForm.coe_rescaleLin_apply, CuspForm.coe_levelInclusionLin_apply,
      coe_discrGamma0One] at hc
  have hq0 : ∀ τ : ℍ, Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 := fun τ => by
    simp [Function.Periodic.qParam]
  have hP : Filter.Tendsto
      (fun τ : ℍ => ModularForm.discriminant τ / Function.Periodic.qParam 1 (τ : ℂ))
      UpperHalfPlane.atImInfty (nhds 1) := by
    refine ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr
      (fun τ => ?_)
    rw [ModularForm.discriminant_eq_q_prod, mul_div_cancel_left₀ _ (hq0 τ)]
  have hP2 : Filter.Tendsto
      (fun τ : ℍ => ModularForm.discriminant (ModularForm.heckeDiagMatrix 2 • τ) /
        Function.Periodic.qParam 1 ((ModularForm.heckeDiagMatrix 2 • τ : ℍ) : ℂ))
      UpperHalfPlane.atImInfty (nhds 1) :=
    hP.comp (UpperHalfPlane.tendsto_smul_atImInfty (by simp))
  have h2048 : ∀ τ : ℍ, (ModularForm.discriminant ∣[(12 : ℤ)]
        ModularForm.heckeDiagMatrix 2) τ / Function.Periodic.qParam 1 (τ : ℂ)
      = (2048 : ℂ) * (Function.Periodic.qParam 1 (τ : ℂ) *
        (ModularForm.discriminant (ModularForm.heckeDiagMatrix 2 • τ) /
          Function.Periodic.qParam 1 ((ModularForm.heckeDiagMatrix 2 • τ : ℍ) : ℂ))) := by
    intro τ
    have hq2 : Function.Periodic.qParam 1 ((ModularForm.heckeDiagMatrix 2 • τ : ℍ) : ℂ)
        = (Function.Periodic.qParam 1 (τ : ℂ)) ^ 2 := by
      rw [ModularForm.coe_heckeDiagMatrix_smul (show (2 : ℕ) ≠ 0 by norm_num)]
      simp only [Function.Periodic.qParam, Nat.cast_ofNat, div_one, pow_two,
        ← Complex.exp_add]
      congr 1
      ring
    calc (ModularForm.discriminant ∣[(12 : ℤ)] ModularForm.heckeDiagMatrix 2) τ /
          Function.Periodic.qParam 1 (τ : ℂ)
        = (2048 : ℂ) * ModularForm.discriminant
            (ModularForm.heckeDiagMatrix 2 • τ) / Function.Periodic.qParam 1 (τ : ℂ) := by
          rw [ModularForm.slash_heckeDiagMatrix_apply 12
            (show (2 : ℕ) ≠ 0 by norm_num)]
          norm_num
      _ = (2048 : ℂ) * (Function.Periodic.qParam 1 (τ : ℂ) *
            (ModularForm.discriminant (ModularForm.heckeDiagMatrix 2 • τ) /
              Function.Periodic.qParam 1
                ((ModularForm.heckeDiagMatrix 2 • τ : ℍ) : ℂ))) := by
          rw [← mul_div_cancel₀ (ModularForm.discriminant
                (ModularForm.heckeDiagMatrix 2 • τ))
              (hq0 (ModularForm.heckeDiagMatrix 2 • τ)), hq2]
          have hqτ := hq0 τ
          field_simp
  have hratio : Filter.Tendsto
      (fun τ : ℍ => (ModularForm.discriminant ∣[(12 : ℤ)]
        ModularForm.heckeDiagMatrix 2) τ / Function.Periodic.qParam 1 (τ : ℂ))
      UpperHalfPlane.atImInfty (nhds 0) := by
    refine Filter.Tendsto.congr (fun τ => (h2048 τ).symm) ?_
    simpa using Filter.Tendsto.const_mul (2048 : ℂ)
      (Filter.Tendsto.mul (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one) hP2)
  have ht1 : Filter.Tendsto
      (fun τ : ℍ => (ModularForm.discriminant ∣[(12 : ℤ)]
        ModularForm.heckeDiagMatrix 2) τ / Function.Periodic.qParam 1 (τ : ℂ))
      UpperHalfPlane.atImInfty (nhds 1) := by
    refine hP.congr (fun τ => ?_)
    rw [hfun]
  exact one_ne_zero (tendsto_nhds_unique ht1 hratio)
