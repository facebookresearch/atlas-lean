/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.FrobeniusExists

@[expose] public section

/-- Source-shaped consumer: the original binders, in the original order. -/
example {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) :
    ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), A.IsFrobeniusAt φ q :=
  ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hq A hA

/-- Source-shaped consumer: the original binders, in the original order. -/
example (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ ∧
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ :=
  ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ

/-- A Frobenius element at a place over `2` is not the identity: the residue
field has characteristic `2` and contains a root of `X ^ 2 + X + 1`, which
squaring does not fix. -/
private theorem isFrobeniusAt_two_ne_one {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime 2) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : A.IsFrobeniusAt σ 2) : σ ≠ 1 := by
  rintro rfl
  obtain ⟨y, hy⟩ := IsAlgClosed.isSquare (-3 : AlgebraicClosure ℚ)
  have hω : ((y - 1) / 2) ^ 2 + (y - 1) / 2 + 1 = 0 := by
    field_simp
    linear_combination -hy
  set ω : AlgebraicClosure ℚ := (y - 1) / 2
  have hωA : ω ∈ A := by
    rcases A.mem_or_inv_mem ω with h | h
    · exact h
    · have hω0 : ω ≠ 0 := by
        rintro h0
        rw [h0] at hω
        norm_num at hω
      have : ω = -1 - ω⁻¹ := by
        field_simp
        linear_combination hω
      rw [this]
      exact sub_mem (neg_mem (one_mem A)) h
  have h0 : (⟨ω, hωA⟩ : A) ^ 2 + ⟨ω, hωA⟩ + 1 = 0 := by
    ext
    simpa using hω
  have hx : IsLocalRing.residue A ⟨ω, hωA⟩ ^ 2 + IsLocalRing.residue A ⟨ω, hωA⟩ + 1 = 0 := by
    have := congrArg (IsLocalRing.residue A) h0
    rwa [map_add, map_add, map_pow, map_one, map_zero] at this
  have h2 : (2 : IsLocalRing.ResidueField A) = 0 := by
    have h2A : (((2 : ℕ) : A) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
    rw [ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff,
      map_natCast] at h2A
    exact_mod_cast h2A
  have hfix := hσ.smul_residue_eq (IsLocalRing.residue A ⟨ω, hωA⟩)
  rw [show (⟨1, hσ.mem_decompositionSubgroup⟩ : A.decompositionSubgroup ℚ) = 1 from rfl,
    one_smul] at hfix
  have h10 : (1 : IsLocalRing.ResidueField A) = 0 := by
    linear_combination hx + hfix - IsLocalRing.residue A ⟨ω, hωA⟩ * h2
  exact one_ne_zero h10

/-- Concrete instance: at the prime `2` some place has a Frobenius element in
its decomposition subgroup, and that element is not the identity. -/
example : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 ∧
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ A.decompositionSubgroup ℚ ∧ σ ≠ 1 := by
  obtain ⟨A, hA, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat 2 Nat.prime_two
  exact ⟨A, hA, σ, hσ.mem_decompositionSubgroup, isFrobeniusAt_two_ne_one hA hσ⟩

/-- Concrete instance: every place over `2` has a Frobenius element that is not
the identity. -/
example (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime 2) :
    ∃ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt φ 2 ∧ φ ≠ 1 := by
  obtain ⟨φ, hφ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime Nat.prime_two A hA
  exact ⟨φ, hφ, isFrobeniusAt_two_ne_one hA hφ⟩
