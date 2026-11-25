/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import MathlibExt.Algebra.Homology.Embedding.UpNatToInt
public import MathlibExt.Algebra.Homology.LinearHomCochainComplex

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe w v u

variable (R : Type w) [Ring R]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]

noncomputable def linearHomCochainComplexIntBifunctor :
    C ⥤ (ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  linearHomCochainComplexBifunctor R C ⋙
    (Functor.whiskeringRight (ChainComplex C ℕ)ᵒᵖ
      (CochainComplex (ModuleCat.{v} R) ℕ)
      (CochainComplex (ModuleCat.{v} R) ℤ)).obj
      (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R))

noncomputable def linearHomCochainHomologyBifunctor (n : ℕ) :
    C ⥤ (ChainComplex C ℕ)ᵒᵖ ⥤ ModuleCat.{v} R :=
  linearHomCochainComplexBifunctor R C ⋙
    (Functor.whiskeringRight (ChainComplex C ℕ)ᵒᵖ
      (CochainComplex (ModuleCat.{v} R) ℕ) (ModuleCat.{v} R)).obj
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℕ) n)

noncomputable def linearHomCochainHomologyIntBifunctor (z : ℤ) :
    C ⥤ (ChainComplex C ℕ)ᵒᵖ ⥤ ModuleCat.{v} R :=
  linearHomCochainComplexIntBifunctor R C ⋙
    (Functor.whiskeringRight (ChainComplex C ℕ)ᵒᵖ
      (CochainComplex (ModuleCat.{v} R) ℤ) (ModuleCat.{v} R)).obj
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) z)

noncomputable def linearHomCochainHomologyNatToIntBifunctorIso (n : ℕ) :
    linearHomCochainHomologyIntBifunctor R C (n : ℤ) ≅
      linearHomCochainHomologyBifunctor R C n :=
  Functor.associator (linearHomCochainComplexBifunctor R C)
    ((Functor.whiskeringRight (ChainComplex C ℕ)ᵒᵖ
      (CochainComplex (ModuleCat.{v} R) ℕ)
      (CochainComplex (ModuleCat.{v} R) ℤ)).obj
      (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R)))
    ((Functor.whiskeringRight (ChainComplex C ℕ)ᵒᵖ
      (CochainComplex (ModuleCat.{v} R) ℤ) (ModuleCat.{v} R)).obj
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
        (ComplexShape.up ℤ) (n : ℤ))) ≪≫
    Functor.isoWhiskerLeft (linearHomCochainComplexBifunctor R C)
      ((Functor.whiskeringRight (ChainComplex C ℕ)ᵒᵖ
        (CochainComplex (ModuleCat.{v} R) ℕ) (ModuleCat.{v} R)).mapIso
        (HomologicalComplex.homologyFunctorExtendUpNatIso
          (C := ModuleCat.{v} R) n))

theorem isZero_linearHomCochainComplexInt_X_of_neg (G : C)
    (K : ChainComplex C ℕ) (z : ℤ) (hz : z < 0) :
    IsZero ((((linearHomCochainComplexIntBifunctor R C).obj G).obj
      (Opposite.op K)).X z) := by
  have hmem : ∀ n : ℕ, ComplexShape.embeddingUpNat.f n ≠ z :=
    (ComplexShape.notMem_range_embeddingUpNat_iff z).mpr hz
  exact HomologicalComplex.isZero_extend_X
    (((linearHomCochainComplexBifunctor R C).obj G).obj (Opposite.op K))
    ComplexShape.embeddingUpNat z hmem

theorem isZero_linearHomCochainHomologyInt_of_neg (z : ℤ) (hz : z < 0)
    (G : C) (K : ChainComplex C ℕ) :
    IsZero ((((linearHomCochainHomologyIntBifunctor R C z).obj G).obj
      (Opposite.op K))) := by
  dsimp [linearHomCochainHomologyIntBifunctor,
    linearHomCochainComplexIntBifunctor]
  exact HomologicalComplex.isZero_homology_extendUpNat_neg
    (((linearHomCochainComplexBifunctor R C).obj G).obj (Opposite.op K)) z hz

end HomologicalComplex
