/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.ExtendHomologyFunctor

@[expose] public section

open CategoryTheory Category Limits

namespace ComplexShape

/-- An integer index is outside the image of `embeddingUpNat`
exactly when it is negative. -/
lemma notMem_range_embeddingUpNat_iff (z : ℤ) :
    (∀ n : ℕ, embeddingUpNat.f n ≠ z) ↔ z < 0 := by
  constructor
  · intro h
    by_contra hz
    apply h z.toNat
    change (z.toNat : ℤ) = z
    exact Int.toNat_of_nonneg (by omega)
  · intro hz n
    change (n : ℤ) ≠ z
    omega

end ComplexShape

section Homology

/-- Cycles functor isomorphism for the `up ℕ → up ℤ` embedding. -/
noncomputable def HomologicalComplex.cyclesFunctorExtendUpNatIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    [CategoryWithHomology C] (n : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor C ⋙
      cyclesFunctor C (ComplexShape.up ℤ) (n : ℤ) ≅
      cyclesFunctor C (ComplexShape.up ℕ) n :=
  HomologicalComplex.extendCyclesFunctorIso
    ComplexShape.embeddingUpNat n (n : ℤ) rfl

/-- Opcycles functor isomorphism for the `up ℕ → up ℤ` embedding. -/
noncomputable def HomologicalComplex.opcyclesFunctorExtendUpNatIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    [CategoryWithHomology C] (n : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor C ⋙
      opcyclesFunctor C (ComplexShape.up ℤ) (n : ℤ) ≅
      opcyclesFunctor C (ComplexShape.up ℕ) n :=
  HomologicalComplex.extendOpcyclesFunctorIso
    ComplexShape.embeddingUpNat n (n : ℤ) rfl

/-- Homology functor isomorphism for the `up ℕ → up ℤ` embedding. -/
noncomputable def HomologicalComplex.homologyFunctorExtendUpNatIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    [CategoryWithHomology C] (n : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor C ⋙
      homologyFunctor C (ComplexShape.up ℤ) (n : ℤ) ≅
      homologyFunctor C (ComplexShape.up ℕ) n :=
  HomologicalComplex.extendHomologyFunctorIso
    ComplexShape.embeddingUpNat n (n : ℤ) rfl

/-- The extended cochain complex has zero homology in negative degrees. -/
lemma HomologicalComplex.isZero_homology_extendUpNat_neg
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℕ) (z : ℤ) (hz : z < 0)
    [(K.extend ComplexShape.embeddingUpNat).HasHomology z] :
    IsZero ((K.extend ComplexShape.embeddingUpNat).homology z) :=
  HomologicalComplex.isZero_homology_extend_of_notMem_range K
    ComplexShape.embeddingUpNat z
    ((ComplexShape.notMem_range_embeddingUpNat_iff z).mpr hz)

end Homology
