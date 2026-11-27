/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CuspForm_qCoeff_rescaleLin.lean`,
`Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean`,
`Definitions/Def_ModularForm_HeckeOperator.lean`,
`Definitions/Def_FLTPrelim_Modularity.lean`,
`Theorems/Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.lean`,
`Theorems/Thm_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean`,
`P2M/Sol/S_CuspForm_qCoeff_rescaleLin.lean`,
`P2M/Sol/S_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.lean` and
`P2M/Sol/S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and arguments are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj
public import MathlibExt.NumberTheory.ModularForms.OldForms
import MathlibExt.NumberTheory.ModularForms.StrictPeriodsGamma0

/-!
# Rescaling cusp forms and their `q`-coefficients

For `d * R ∣ M`, slashing a cusp form on `Γ₀(R)` by the diagonal matrix
`diag(d, 1)` gives a cusp form on `Γ₀(M)`.  Its `q`-coefficients vanish
unless `d ∣ n`, in which case they are `d ^ (k - 1)` times the
`(n / d)`-th coefficient of the original form.
-/

@[expose] public section

open Matrix UpperHalfPlane CongruenceSubgroup ModularForm
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace ModularFormClass

/-- `qCoeff` (defined in `CuspFormConj`) unfolds to the `q`-expansion coefficient. -/
lemma qCoeff_def (f : ℍ → ℂ) (n : ℕ) :
    qCoeff f n = (UpperHalfPlane.qExpansion 1 f).coeff n :=
  rfl

end ModularFormClass

/-- A copy of `ℍ → ℂ` carrying the identity `FunLike` instance, used to
apply `q`-expansion coefficient uniqueness to a bare function. -/
private def QExpFn : Type :=
  ℍ → ℂ

private instance : FunLike QExpFn ℍ ℂ where
  coe f := f
  coe_injective _ _ h := h

namespace UpperHalfPlane

private theorem heckeDiagMatrix_smul_ofComplex {d : ℕ} (hd : d ≠ 0) {z : ℂ}
    (hz : 0 < z.im) :
    ModularForm.heckeDiagMatrix d • ofComplex z = ofComplex ((d : ℂ) * z) := by
  have hz' : 0 < ((d : ℂ) * z).im := by
    rw [show ((d : ℂ) * z).im = d * z.im by simp]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    positivity
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul hd, ofComplex_apply_of_im_pos hz,
    ofComplex_apply_of_im_pos hz']

private theorem periodic_comp_smul {d : ℕ} (hd : d ≠ 0) {F : ℍ → ℂ}
    (hper : Function.Periodic (F ∘ ofComplex) 1) :
    Function.Periodic ((fun τ ↦ F (ModularForm.heckeDiagMatrix d • τ)) ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply]
    rw [heckeDiagMatrix_smul_ofComplex hd hw1, heckeDiagMatrix_smul_ofComplex hd hw,
      mul_add, mul_one]
    have h := hper.nat_mul d ((d : ℂ) * w)
    simpa using h
  · push Not at hw
    have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw,
      ofComplex_apply_of_im_nonpos hw1]

private theorem mdifferentiable_comp_smul {d : ℕ} (hd : d ≠ 0) {F : ℍ → ℂ}
    (hhol : MDiff F) :
    MDiff (fun τ ↦ F (ModularForm.heckeDiagMatrix d • τ)) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have h := (hhol.slash 0 (ModularForm.heckeDiagMatrix d)).const_smul (d : ℂ)
  convert h using 1
  funext τ
  rw [Pi.smul_apply, ModularForm.slash_heckeDiagMatrix_apply 0 hd, smul_eq_mul,
    zero_sub, _root_.zpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

private theorem isBoundedAtImInfty_comp_smul {d : ℕ} (hd : d ≠ 0) {F : ℍ → ℂ}
    (hbdd : IsBoundedAtImInfty F) :
    IsBoundedAtImInfty (fun τ ↦ F (ModularForm.heckeDiagMatrix d • τ)) := by
  refine hbdd.comp_tendsto ?_
  rw [atImInfty, Filter.tendsto_comap_iff]
  have him : (UpperHalfPlane.im ∘ fun τ : ℍ ↦ ModularForm.heckeDiagMatrix d • τ)
      = fun τ ↦ (d : ℝ) * τ.im := by
    funext τ
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.im_smul_eq_div_normSq, ModularForm.denom_heckeDiagMatrix hd,
      ModularForm.det_heckeDiagMatrix hd]
    simp
  rw [him]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  exact (Filter.tendsto_id.const_mul_atTop hd0).comp Filter.tendsto_comap

set_option maxHeartbeats 800000 in
private theorem qCoeff_comp_smul {d : ℕ} {F : ℍ → ℂ}
    (hper : Function.Periodic (F ∘ ofComplex) 1) (hhol : MDiff F)
    (hbdd : IsBoundedAtImInfty F) (hd : d ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (fun τ ↦ F (ModularForm.heckeDiagMatrix d • τ)) n =
      if d ∣ n then ModularFormClass.qCoeff F (n / d) else 0 := by
  set G : ℍ → ℂ := fun τ ↦ F (ModularForm.heckeDiagMatrix d • τ) with hG
  have han : AnalyticAt ℂ (cuspFunction 1 G) 0 :=
    analyticAt_cuspFunction_zero one_pos (periodic_comp_smul hd hper)
      (mdifferentiable_comp_smul hd hhol) (isBoundedAtImInfty_comp_smul hd hbdd)
  set c : ℕ → ℂ := fun n ↦ if d ∣ n then (qExpansion 1 F).coeff (n / d) else 0 with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam 1 τ ^ m) (G τ) := by
    intro τ
    have hq : Function.Periodic.qParam 1 ((ModularForm.heckeDiagMatrix d • τ : ℍ) : ℂ)
        = Function.Periodic.qParam 1 τ ^ d := by
      simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul,
        ModularForm.coe_heckeDiagMatrix_smul hd]
      congr 1
      push_cast
      ring
    have hs := hasSum_qExpansion one_pos hper hhol hbdd
      (ModularForm.heckeDiagMatrix d • τ)
    simp_rw [hq, ← pow_mul] at hs
    have hinj : Function.Injective (fun m : ℕ ↦ d * m) :=
      mul_right_injective₀ hd
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ ↦ d * m),
        (fun m ↦ c m • Function.Periodic.qParam 1 τ ^ m) x = 0 := by
      intro x hx
      have hndvd : ¬ d ∣ x := by
        rintro ⟨e, rfl⟩
        exact hx ⟨e, rfl⟩
      simp [hc, hndvd]
    refine (hinj.hasSum_iff hsupp).mp ?_
    convert hs using 1
    ext m
    simp [hc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd)]
  have key := UpperHalfPlane.qExpansion_coeff_unique (show QExpFn from G)
    one_pos han hsum n
  show (qExpansion 1 G).coeff n = if d ∣ n then (qExpansion 1 F).coeff (n / d) else 0
  exact key.symm

end UpperHalfPlane

/-- Composing with `τ ↦ d • τ` on the upper half plane rescales the
`q`-coefficients: only indices divisible by `d` survive. -/
theorem ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul
    {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ}
    [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)) n =
      if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0 := by
  haveI : Fact (IsCusp OnePoint.infty Γ) :=
    ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact UpperHalfPlane.qCoeff_comp_smul
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) hd n

namespace CuspForm

private theorem aux_neZero_d {d R M : ℕ} [NeZero M] (hdRM : d * R ∣ M) :
    d ≠ 0 := by
  rintro rfl
  exact NeZero.ne M (Nat.eq_zero_of_zero_dvd (by simpa using hdRM))


private theorem qCoeff_coe_smul {R : ℕ} (k : ℤ) (c : ℂ)
    (f : CuspForm (Gamma0 R) k) (m : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) m
      = c * ModularFormClass.qCoeff (⇑f) m := by
  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 R
  have han := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  unfold ModularFormClass.qCoeff
  rw [FunLike.coe_smul, UpperHalfPlane.qExpansion_smul han c]
  simp [smul_eq_mul]

/-- The `q`-coefficients of a rescaled cusp form: zero unless `d ∣ n`,
otherwise `d ^ (k - 1)` times the `(n / d)`-th coefficient. -/
theorem qCoeff_rescaleLin {d R M : ℕ} [NeZero M] (hdRM : d * R ∣ M) (k : ℤ)
    (f : CuspForm (Gamma0 R) k) (n : ℕ) :
    ModularFormClass.qCoeff (rescaleLin hdRM k f) n
      = if d ∣ n then (d : ℂ) ^ (k - 1) * ModularFormClass.qCoeff f (n / d)
        else 0 := by
  have hd : d ≠ 0 := aux_neZero_d hdRM
  have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 R
  have hfun : (⇑(rescaleLin hdRM k f) : UpperHalfPlane → ℂ)
      = fun τ => (⇑(((d : ℂ) ^ (k - 1)) • f))
          (ModularForm.heckeDiagMatrix d • τ) := by
    funext τ
    rw [coe_rescaleLin_apply, ModularForm.slash_heckeDiagMatrix_apply k hd,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hfun, ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul
    (((d : ℂ) ^ (k - 1)) • f) hΓ hd n]
  split_ifs with h
  · rw [qCoeff_coe_smul]
  · rfl

end CuspForm

end
