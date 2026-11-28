/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.ExtendHomologyFunctor

/-!
# Natural cochains extended to integer degrees

Extension along n↦(n:ℤ) retains a natural cochain complex in nonnegative
degrees and inserts zero objects in negative degrees. Cycles, opcycles and
homology at a selected natural degree are identified naturally with those
of the original complex.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace ComplexShape

/--
For the cochain embedding e:ℕ→ℤ given by e(n)=n, an integer z is outside the image exactly
when z<0: (∀n∈ℕ, e(n)≠z) ↔ z<0.
-/
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

/--
Let C have zero morphisms, a zero object and homology for short complexes. Extend a natural
cochain complex K to integer degrees along n↦(n:ℤ), with zero terms at negative degrees. At
n∈ℕ, the cycles of the extension in integer degree n are canonically isomorphic to Zⁿ(K).
These comparisons are natural in K.
-/
noncomputable abbrev HomologicalComplex.cyclesFunctorExtendUpNatIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    [CategoryWithHomology C] (n : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor C ⋙
      cyclesFunctor C (ComplexShape.up ℤ) (n : ℤ) ≅
      cyclesFunctor C (ComplexShape.up ℕ) n :=
  HomologicalComplex.extendCyclesFunctorIso
    ComplexShape.embeddingUpNat n (n : ℤ) rfl

/--
Let C have zero morphisms, a zero object and homology for short complexes. Extend a natural
cochain complex K to integer degrees along n↦(n:ℤ), with zero terms at negative degrees. At
n∈ℕ, opcycles of the extension in integer degree n are canonically isomorphic to the original
quotient of Kⁿ by incoming boundaries. The comparisons are natural in K.
-/
noncomputable abbrev HomologicalComplex.opcyclesFunctorExtendUpNatIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    [CategoryWithHomology C] (n : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor C ⋙
      opcyclesFunctor C (ComplexShape.up ℤ) (n : ℤ) ≅
      opcyclesFunctor C (ComplexShape.up ℕ) n :=
  HomologicalComplex.extendOpcyclesFunctorIso
    ComplexShape.embeddingUpNat n (n : ℤ) rfl

/--
Let C have zero morphisms, a zero object and homology for short complexes. Extend a natural
cochain complex K to integer degrees along n↦(n:ℤ), with zero terms at negative degrees. At
n∈ℕ, the extension has homology canonically isomorphic to Hⁿ(K). This is a natural isomorphism
of the extension–homology composite with natural-degree homology.
-/
noncomputable abbrev HomologicalComplex.homologyFunctorExtendUpNatIso
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    [CategoryWithHomology C] (n : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor C ⋙
      homologyFunctor C (ComplexShape.up ℤ) (n : ℤ) ≅
      homologyFunctor C (ComplexShape.up ℕ) n :=
  HomologicalComplex.extendHomologyFunctorIso
    ComplexShape.embeddingUpNat n (n : ℤ) rfl

/--
Let C be an abelian category and K a natural cochain complex extended by zero to integer
degrees. For z<0, assuming the extension has homology at z, its homology object Hᶻ is zero.
-/
lemma HomologicalComplex.isZero_homology_extendUpNat_neg
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℕ) (z : ℤ) (hz : z < 0)
    [(K.extend ComplexShape.embeddingUpNat).HasHomology z] :
    IsZero ((K.extend ComplexShape.embeddingUpNat).homology z) :=
  HomologicalComplex.isZero_homology_extend_of_notMem_range K
    ComplexShape.embeddingUpNat z
    ((ComplexShape.notMem_range_embeddingUpNat_iff z).mpr hz)

end Homology
