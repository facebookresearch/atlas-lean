/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.WeightTwoEigenformCongruence

@[expose] public section

open CuspForm CongruenceSubgroup ModularFormClass EisensteinWeightOne

/-- Consumer with the original binders of the `T_ℓ`-congruence form. -/
private theorem exactSource_heckeT_congr
    {N : ℕ} [NeZero N] (h : CuspForm.HasIntegralBasis N) {a : ℕ → ℤ}
    (h1 : a 1 = 1)
    (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a))
    (hreal : CuspForm.IsLatticeRealized N a) :
    ∃ (f : CuspForm (Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧
      ((3 : ℕ) : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (_ : ℓ.Prime) (_ : ¬ ℓ ∣ N),
        ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          c - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪' :=
  CuspForm.exists_isNormalizedEigenform_congruent_of_heckeT_congr h h1 hT hreal

/-- Consumer with the original binders of the eigensystem form. -/
private theorem exactSource_isLatticeRealized
    {N : ℕ} [NeZero N] (h : CuspForm.HasIntegralBasis N) {a : ℕ → ℤ}
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a)
    (hreal : CuspForm.IsLatticeRealized N a) :
    ∃ (f : CuspForm (Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧
      ((3 : ℕ) : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (_ : ℓ.Prime) (_ : ¬ ℓ ∣ N),
        ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          c - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪' :=
  CuspForm.exists_isNormalizedEigenform_congruent_of_isLatticeRealized h heig hreal

/-- The eigenform produced has first coefficient `1`, so it is nonzero: the conclusion is
never satisfied vacuously by the zero form. -/
example {N : ℕ} [NeZero N] (h : CuspForm.HasIntegralBasis N) {a : ℕ → ℤ} (h1 : a 1 = 1)
    (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a))
    (hreal : CuspForm.IsLatticeRealized N a) :
    ∃ f : CuspForm (Gamma0 N) 2, f ≠ 0 := by
  obtain ⟨f, hf, -⟩ := CuspForm.exists_isNormalizedEigenform_congruent_of_heckeT_congr
    h h1 hT hreal
  refine ⟨f, fun hf0 => ?_⟩
  have h1f := hf.qCoeff_one
  rw [hf0] at h1f
  simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero] at h1f
