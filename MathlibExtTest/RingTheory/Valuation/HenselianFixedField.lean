/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.HenselianFixedField

@[expose] public section

universe u

-- Exact-source consumer, with the original binders.
theorem exactSource
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L)
    (I : Subgroup (L ≃ₐ[K] L)) (hI : I ≤ A.inertiaSubgroupIn K) :
    HenselianLocalRing ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) :=
  ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn A I hI

-- Higher-universe consumer: the fields live in `Type 1`.
example
    {K L : Type 1} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L)
    (I : Subgroup (L ≃ₐ[K] L)) (hI : I ≤ A.inertiaSubgroupIn K) :
    HenselianLocalRing ↥(A.toSubring ⊓ (IntermediateField.fixedField I).toSubring) :=
  ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn A I hI

-- Boundary: for the trivial subgroup the fixed field is all of `L`, so the
-- intersection is the valuation subring itself, which is Henselian.
example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] (A : ValuationSubring L) :
    HenselianLocalRing ↥A.toSubring := by
  have h := ValuationSubring.henselianLocalRing_inf_fixedField_of_le_inertiaSubgroupIn
    A (⊥ : Subgroup (L ≃ₐ[K] L)) bot_le
  have hsub : A.toSubring ⊓
      (IntermediateField.fixedField (⊥ : Subgroup (L ≃ₐ[K] L))).toSubring
      = A.toSubring := by
    ext x
    simp [IntermediateField.mem_fixedField_iff]
  rwa [hsub] at h
