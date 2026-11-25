/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeEigenformIntegral

@[expose] public section

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) (ℓ : ℕ)
    (hℓ : ℓ.Prime) : ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ :=
  CuspForm.IsNormalizedEigenform.exists_integralClosure_coe_eq_qCoeff hN hf ℓ hℓ

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : f.IsNormalizedEigenform) (S : Set ℕ) :
    ∃ χ : CuspForm.heckeAlgebra N 2 S →+* ℂ,
      (∀ t : CuspForm.heckeAlgebra N 2 S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = χ t • f) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = ModularFormClass.qCoeff f ℓ) ∧
      ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
        χ (CuspForm.heckeAlgebra.U hq hqN hqS) = ModularFormClass.qCoeff f q :=
  CuspForm.IsNormalizedEigenform.exists_ringHom_heckeAlgebra hf S

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) (S : Set ℕ) :
    ∃ χ : CuspForm.heckeAlgebra N 2 S →+* integralClosure ℤ ℂ,
      ∀ t : CuspForm.heckeAlgebra N 2 S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = (χ t : ℂ) • f :=
  CuspForm.IsNormalizedEigenform.exists_ringHom_heckeAlgebra_integralClosure hN hf S

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2)
    (𝔭 : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) (h𝔭 : 𝔭.IsPrime)
    (hchar : ∀ n : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) n ∈ 𝔭 → n = 0) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), f.IsNormalizedEigenform ∧
      ∀ t : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N},
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = 0 → t ∈ 𝔭 :=
  CuspForm.exists_isNormalizedEigenform_ker_le_of_isPrime hN 𝔭 h𝔭 hchar

/-- exactSource consumer: the original binders apply verbatim. -/
example {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2)
    (𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N})) (h𝔪₁ : 𝔪₁.IsMaximal) {p : ℕ}
    (hp𝔪 : (p : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁) :
    ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (b : ℤ),
        CuspForm.heckeAlgebra.T hℓ hℓN hℓN - (b : CuspForm.heckeAlgebra N 2 {ℓ | ℓ ∣ N}) ∈ 𝔪₁ →
        ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          a - (b : integralClosure ℤ ℂ) ∈ 𝔪' :=
  CuspForm.exists_isNormalizedEigenform_congruent_of_isMaximal hN 𝔪₁ h𝔪₁ hp𝔪

/-- Boundary case: the Hecke character of a normalized eigenform sends `1` to `1`, so the
eigenform is fixed by the identity of the Hecke algebra. -/
example {N : ℕ} [NeZero N] {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : f.IsNormalizedEigenform) (S : Set ℕ) :
    ∃ χ : CuspForm.heckeAlgebra N 2 S →+* ℂ, χ 1 = 1 ∧
      ∀ t : CuspForm.heckeAlgebra N 2 S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f = χ t • f := by
  obtain ⟨χ, hχ, -⟩ := hf.exists_ringHom_heckeAlgebra S
  exact ⟨χ, map_one χ, hχ⟩
