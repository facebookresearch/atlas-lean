/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.InertiaSubgroupIn

@[expose] public section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

-- The definition is the image of Mathlib's inertia subgroup under the
-- inclusion of the decomposition subgroup.
example (A : ValuationSubring L) :
    A.inertiaSubgroupIn K = (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype :=
  rfl

-- Every element of Mathlib's inertia subgroup lies in `inertiaSubgroupIn`.
example (A : ValuationSubring L) (τ : A.decompositionSubgroup K)
    (hτ : τ ∈ A.inertiaSubgroup K) : (τ : L ≃ₐ[K] L) ∈ A.inertiaSubgroupIn K :=
  Subgroup.mem_map_of_mem _ hτ

-- Conversely, an element of `inertiaSubgroupIn` stabilizes `A` and, as an
-- element of the decomposition subgroup, lies in the inertia subgroup.
example (A : ValuationSubring L) {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.inertiaSubgroupIn K) :
    ∃ h : σ ∈ A.decompositionSubgroup K,
      (⟨σ, h⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K := by
  obtain ⟨τ, hτ, rfl⟩ := hσ
  exact ⟨τ.2, hτ⟩

-- `inertiaSubgroupIn` lies in the decomposition subgroup.
example (A : ValuationSubring L) : A.inertiaSubgroupIn K ≤ A.decompositionSubgroup K := by
  rintro _ ⟨τ, -, rfl⟩
  exact τ.2

-- Boundary: for the valuation subring `⊤`, whose residue field is all of `L`,
-- the inertia subgroup is trivial, although every automorphism lies in the
-- decomposition subgroup of `⊤`.
example : (⊤ : ValuationSubring L).inertiaSubgroupIn K = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨τ, hτ, rfl⟩
  rw [Subgroup.mem_bot]
  ext x
  set a : ↥(⊤ : ValuationSubring L) := ⟨x, ValuationSubring.mem_top x⟩
  have hker : MulSemiringAction.toRingAut (ValuationSubring.decompositionSubgroup K ⊤)
      (IsLocalRing.ResidueField ↥(⊤ : ValuationSubring L)) τ = 1 := MonoidHom.mem_ker.mp hτ
  have hres : IsLocalRing.residue _ (τ • a) = IsLocalRing.residue _ a := by
    rw [IsLocalRing.ResidueField.residue_smul]
    have h := congrArg (fun e : RingAut (IsLocalRing.ResidueField ↥(⊤ : ValuationSubring L)) =>
      e (IsLocalRing.residue _ a)) hker
    simpa [MulSemiringAction.toRingAut_apply] using h
  have hmem : τ • a - a ∈ IsLocalRing.maximalIdeal ↥(⊤ : ValuationSubring L) :=
    Ideal.Quotient.eq.mp hres
  have hzero : τ • a - a = 0 := by
    by_contra hne
    have hne' : ((τ • a - a : ↥(⊤ : ValuationSubring L)) : L) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    refine (IsLocalRing.mem_maximalIdeal _).mp hmem ?_
    refine IsUnit.of_mul_eq_one (⟨((τ • a - a : ↥(⊤ : ValuationSubring L)) : L)⁻¹,
      ValuationSubring.mem_top _⟩ : ↥(⊤ : ValuationSubring L)) ?_
    exact Subtype.ext (mul_inv_cancel₀ hne')
  have h := congrArg (fun b : ↥(⊤ : ValuationSubring L) => (b : L)) (sub_eq_zero.mp hzero)
  exact h
