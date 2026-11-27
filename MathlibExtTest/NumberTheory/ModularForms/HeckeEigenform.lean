/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
The source statements restated in this file are copied from
`Theorems/Thm_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul.lean`,
`Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeT.lean`,
`Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin.lean`,
`Theorems/Thm_ModularFormClass_heckeT_eq_smul_iff.lean`,
`Theorems/Thm_ModularFormClass_heckeU_eq_smul_iff.lean`, and
`Theorems/Thm_Module_End_exists_forall_apply_eq_smul_of_pairwise_commute.lean`
in https://github.com/anthropics/fermats-last-theorem, compared with the source files at
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import MathlibExt.NumberTheory.ModularForms.HeckeEigenform
import MathlibExt.LinearAlgebra.Eigenspace.CommonEigenvector

@[expose] public section

/-- exactSource consumer: the original binders apply verbatim. -/
example {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) :
    ModularForm.heckeT k p ⇑f = c • ⇑f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n
        = c * ModularFormClass.qCoeff f n :=
  ModularFormClass.heckeT_eq_smul_iff f hΓ hp c

/-- exactSource consumer: the original binders apply verbatim. -/
example {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F)
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) :
    ModularForm.heckeU k p ⇑f = c • ⇑f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n
        = c * ModularFormClass.qCoeff f n :=
  ModularFormClass.heckeU_eq_smul_iff f hΓ hp c

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔
      (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
        ((¬ p ∣ N → ModularForm.heckeT 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f) ∧
          (p ∣ N → ModularForm.heckeU 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f))) :=
  CuspForm.isNormalizedEigenform_iff_heckeT f

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ (p : ℕ) (hp : p.Prime),
      ((hpN : ¬ p ∣ N) → CuspForm.heckeTLin 2 hp hpN f = ModularFormClass.qCoeff f p • f) ∧
      ((hpN : p ∣ N) → CuspForm.heckeULin 2 hpN f = ModularFormClass.qCoeff f p • f)) :=
  CuspForm.isNormalizedEigenform_iff_heckeTLin f

/-- exactSource restatement, from `Module.End.exists_common_eigenvector_of_commute` on `main`:
the source's pairwise hypothesis and per-member eigenvalues are that theorem's form. -/
example {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    {ι : Type*} (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v := by
  obtain ⟨χ, v, hv0, hv⟩ := Module.End.exists_common_eigenvector_of_commute T fun i j =>
    (eq_or_ne i j).elim (fun h => h ▸ Commute.refl (T i)) fun h => hT h
  exact ⟨v, hv0, fun i => ⟨χ i, hv i⟩⟩

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N]
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g ≠ 0) (a : ℕ → ℂ) (S : Set ℕ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN g = a ℓ • g) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 N) 2, h.IsNormalizedEigenform ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ModularFormClass.qCoeff h ℓ = a ℓ :=
  CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul hg a S hT
