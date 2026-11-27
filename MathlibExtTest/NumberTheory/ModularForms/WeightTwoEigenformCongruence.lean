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
`Definitions/Def_CuspForm_IntegralLattice.lean`,
`Theorems/Thm_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_heckeT_congr.lean`, and
`Theorems/Thm_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_isLatticeRealized.lean`
in https://github.com/anthropics/fermats-last-theorem, compared with the source files at
commit `6e837e75355538c7f80bab5b956861e86c4eacc2`.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.ModularForms.WeightTwoEigenformCongruence

@[expose] public section

open CuspForm CongruenceSubgroup ModularFormClass EisensteinWeightOne

/-- The source's weight-two cusp forms on `Γ₀(N)` with integral `q`-expansion coefficients. -/
private def srcIntegralSet (N : ℕ) : Set (CuspForm (Gamma0 N) 2) :=
  {f | ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ (⊥ : Subring ℂ)}

/-- The source's `HasIntegralBasis N`: the forms in `srcIntegralSet N` span everything over
`ℂ`. -/
private def SrcHasIntegralBasis (N : ℕ) : Prop :=
  Submodule.span ℂ (srcIntegralSet N) = ⊤

/-- The source's `IsLatticeRealized N a`, with the integral cusp form taken from
`srcIntegralSet N`. -/
private def SrcIsLatticeRealized (N : ℕ) (a : ℕ → ℤ) : Prop :=
  ∃ f : CuspForm (Gamma0 N) 2, f ∈ srcIntegralSet N ∧
    ∃ af : ℕ → ℤ, (∀ n, (af n : ℂ) = ModularFormClass.qCoeff f n) ∧
      ∀ n, (3 : ℤ) ∣ af n - (bridgeProduct a).coeff n

private theorem coe_intLattice_two (N : ℕ) :
    ((CuspForm.intLattice N 2 : Submodule ℤ (CuspForm (Gamma0 N) 2)) :
      Set (CuspForm (Gamma0 N) 2)) = srcIntegralSet N := by
  ext f
  simp only [SetLike.mem_coe, CuspForm.mem_intLattice_iff, srcIntegralSet, Set.mem_ofPred_eq,
    Subring.mem_bot, ModularFormClass.qCoeff_eq]
  exact forall_congr' fun n => ⟨fun ⟨m, hm⟩ => ⟨m, hm.symm⟩, fun ⟨m, hm⟩ => ⟨m, hm.symm⟩⟩

private theorem hasIntegralStructure_of_src {N : ℕ} (h : SrcHasIntegralBasis N) :
    CuspForm.HasIntegralStructure N 2 := by
  rw [CuspForm.hasIntegralStructure_iff, coe_intLattice_two]
  exact h

private theorem isLatticeRealized_of_src {N : ℕ} {a : ℕ → ℤ} (h : SrcIsLatticeRealized N a) :
    CuspForm.IsLatticeRealized N a := by
  obtain ⟨f, hf, hcong⟩ := h
  exact ⟨f, by rwa [← SetLike.mem_coe, coe_intLattice_two], hcong⟩

/-- Consumer with the original binders of the `T_ℓ`-congruence form: the source's integral basis
and lattice realization, restated with the copies of its definitions above. -/
private theorem exactSource_heckeT_congr
    {N : ℕ} [NeZero N] (h : SrcHasIntegralBasis N) {a : ℕ → ℤ}
    (h1 : a 1 = 1)
    (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a))
    (hreal : SrcIsLatticeRealized N a) :
    ∃ (f : CuspForm (Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧
      ((3 : ℕ) : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (_ : ℓ.Prime) (_ : ¬ ℓ ∣ N),
        ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          c - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪' :=
  CuspForm.exists_isNormalizedEigenform_congruent_of_heckeT_congr
    (hasIntegralStructure_of_src h) h1 hT (isLatticeRealized_of_src hreal)

/-- Consumer with the original binders of the eigensystem form, the source's integral basis and
lattice realization included. -/
private theorem exactSource_isLatticeRealized
    {N : ℕ} [NeZero N] (h : SrcHasIntegralBasis N) {a : ℕ → ℤ}
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a)
    (hreal : SrcIsLatticeRealized N a) :
    ∃ (f : CuspForm (Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧
      ((3 : ℕ) : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (_ : ℓ.Prime) (_ : ¬ ℓ ∣ N),
        ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          c - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪' :=
  CuspForm.exists_isNormalizedEigenform_congruent_of_isLatticeRealized
    (hasIntegralStructure_of_src h) heig (isLatticeRealized_of_src hreal)

/-- The eigenform produced has first coefficient `1`, so it is nonzero: the conclusion is
never satisfied vacuously by the zero form. -/
example {N : ℕ} [NeZero N] (hN : CuspForm.HasIntegralStructure N 2) {a : ℕ → ℤ} (h1 : a 1 = 1)
    (hT : ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ N → ∀ n : ℕ, (3 : ℤ) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a))
    (hreal : CuspForm.IsLatticeRealized N a) :
    ∃ f : CuspForm (Gamma0 N) 2, f ≠ 0 := by
  obtain ⟨f, hf, -⟩ := CuspForm.exists_isNormalizedEigenform_congruent_of_heckeT_congr
    hN h1 hT hreal
  refine ⟨f, fun hf0 => ?_⟩
  have h1f := hf.qCoeff_one
  rw [hf0] at h1f
  simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero] at h1f
