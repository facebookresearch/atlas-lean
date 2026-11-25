/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.CyclotomicEigenspaceVanishing

@[expose] public section

namespace PadicComplex

/-- Consumer with the original binders. -/
private theorem exactSource (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (k : ℤ) (hk : k ≠ 0) (c : ℂ_[p])
    (hc : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup →
      σ • c =
        (algebraMap ℚ_[p] ℂ_[p]
            (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv :
                ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ k * c) :
    c = 0 :=
  eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul
    p K k hk c hc

/-- Boundary example: the hypothesis `k ≠ 0` matters. For `k = 0` the
element `1` satisfies the eigenrelation for every automorphism and is
nonzero. -/
private theorem boundary_k_ne_zero_matters (p : ℕ) [Fact p.Prime] :
    ∃ c : ℂ_[p], c ≠ 0 ∧
      ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        σ ∈ (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)).fixingSubgroup →
        σ • c =
          (algebraMap ℚ_[p] ℂ_[p]
              (((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv :
                  ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])) ^ (0 : ℤ) * c :=
  ⟨1, one_ne_zero, fun σ _ => by simp⟩

end PadicComplex
