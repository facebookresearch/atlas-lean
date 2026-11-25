/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeEigenform

@[expose] public section

/-- exactSource consumer: the original binders apply verbatim. -/
example (N : ℕ) [NeZero N] (k : ℤ) :
    FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k) :=
  CuspForm.finiteDimensional_Gamma0 N k

/-- The finite-dimensionality is found by instance search, here at level `11`. -/
example : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 11) 2) := inferInstance

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ModularFormClass.qCoeff f 0 = 0 :=
  CuspForm.qCoeff_zero f

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
example {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔
      (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
        ((¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT 2 p (ModularFormClass.qCoeff f) n
            = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) ∧
          (p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n
            = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n))) :=
  CuspForm.isNormalizedEigenform_iff_coeffHecke f

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

/-- exactSource consumer: the original binders apply verbatim. -/
example (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 1) : ∀ p : ℕ, p.Prime → c p = a p :=
  ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one k N a c hT hU h1

/-- exactSource consumer: the original binders apply verbatim. -/
example (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 0) : ∀ n : ℕ, n ≠ 0 → a n = 0 :=
  ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero k N a c hT hU h1

/-- Boundary case: the zero sequence is a Hecke eigenvector for every eigenvalue, and it
vanishes away from `0`. -/
example (k : ℤ) (N : ℕ) (c : ℕ → ℂ) : ∀ n : ℕ, n ≠ 0 → (fun _ : ℕ ↦ (0 : ℂ)) n = 0 :=
  ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero k N (fun _ ↦ 0) c
    (fun _ _ _ n ↦ by simp [ModularForm.coeffHeckeT_apply])
    (fun _ _ _ n ↦ by simp [ModularForm.coeffHeckeU_apply]) rfl

/-- exactSource consumer: the original binders apply verbatim. -/
example {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    {ι : Type*} (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v :=
  Module.End.exists_forall_apply_eq_smul_of_pairwise_commute T hT

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N]
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g ≠ 0) (a : ℕ → ℂ) (S : Set ℕ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ∉ S →
      CuspForm.heckeTLin 2 hℓ hℓN g = a ℓ • g) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 N) 2, h.IsNormalizedEigenform ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → ModularFormClass.qCoeff h ℓ = a ℓ :=
  CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul hg a S hT

