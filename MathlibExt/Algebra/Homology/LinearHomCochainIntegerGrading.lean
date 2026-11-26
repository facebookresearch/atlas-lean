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

/-!
# Integer-graded linear Hom cochains

Let R be a ring in universe w and C a preadditive R-linear category with independent object
universe u and morphism universe v. For G∈C and a chain complex K of shape down ℕ, the linear
Hom cochain complex has degree-n term Hom_C(K_n,G), an R-module in v, and differential
h↦d_K(n+1,n)≫h. It is covariant in G by postcomposition and contravariant in K by
precomposition.

Extending these cochains along ℕ→ℤ by zero gives an integer-indexed cochain bifunctor. Its terms
and cohomology vanish in every negative degree. At each n∈ℕ, integer cohomology is canonically
isomorphic to the cohomology of the natural-indexed Hom cochains, naturally in both G and K.
Homology is taken in the category of R-modules, so no abelian structure on C or resolution
assumption on K is required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe w v u

variable (R : Type w) [Ring R]
variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]

/-- Let R be a ring in universe w and C a preadditive R-linear category with object universe u and
morphism universe v, all independent. For G∈C and a chain complex K of shape down ℕ, this
integer cochain complex has term Hom_C(K_n,G) at z=n≥0 and zero at z<0. Its nonnegative
differential sends h:K_n→G to d_K(n+1,n)≫h. A map G→G′ acts by postcomposition, while a chain
map K′→K acts by precomposition in each term. All cochain modules lie in v. -/
noncomputable def linearHomCochainComplexIntBifunctor :
    C ⥤ (ChainComplex C ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℤ :=
  linearHomCochainComplexBifunctor R C ⋙
    (Functor.whiskeringRight (ChainComplex C ℕ)ᵒᵖ
      (CochainComplex (ModuleCat.{v} R) ℕ)
      (CochainComplex (ModuleCat.{v} R) ℤ)).obj
      (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{v} R))

/-- Let R be a ring in universe w and C a preadditive R-linear category with object universe u and
morphism universe v, all independent. For fixed n∈ℕ, this bifunctor sends G∈C and
K∈ChainComplex(C,ℕ)ᵒᵖ to H^n of the cochain complex D^i=Hom_C(K_i,G), with differential
h↦d_K(i+1,i)≫h. Its values are R-modules in v, covariant in G and contravariant in the chain
complex. -/
noncomputable def linearHomCochainHomologyBifunctor (n : ℕ) :
    C ⥤ (ChainComplex C ℕ)ᵒᵖ ⥤ ModuleCat.{v} R :=
  linearHomCochainComplexBifunctor R C ⋙
    (Functor.whiskeringRight (ChainComplex C ℕ)ᵒᵖ
      (CochainComplex (ModuleCat.{v} R) ℕ) (ModuleCat.{v} R)).obj
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℕ) n)

/-- Let R be a ring in universe w and C a preadditive R-linear category with object universe u and
morphism universe v, all independent. For fixed z∈ℤ, this bifunctor assigns H^z(E D) to G∈C and
a chain complex K of shape down ℕ, where D^n=Hom_C(K_n,G) and E extends D by zero to negative
degrees. The cohomology module lies in v, and the maps are induced by postcomposition in G and
precomposition in K. -/
noncomputable def linearHomCochainHomologyIntBifunctor (z : ℤ) :
    C ⥤ (ChainComplex C ℕ)ᵒᵖ ⥤ ModuleCat.{v} R :=
  linearHomCochainComplexIntBifunctor R C ⋙
    (Functor.whiskeringRight (ChainComplex C ℕ)ᵒᵖ
      (CochainComplex (ModuleCat.{v} R) ℤ) (ModuleCat.{v} R)).obj
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) z)

/-- Let R be a ring in universe w and C a preadditive R-linear category with object universe u and
morphism universe v, all independent. For n∈ℕ, zero extension gives a canonical isomorphism
H^n(E Hom_C(K,G))≅H^n(Hom_C(K,G)) between the integer-indexed and natural-indexed cochain
homology modules. These components form an isomorphism of bifunctors, covariant in G and
contravariant in K. The integer degree on the source is the natural degree n embedded in ℤ. -/
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

/-- Let R be a ring in universe w and C a preadditive R-linear category with object universe u and
morphism universe v, all independent. For G∈C, a chain complex K of shape down ℕ and z∈ℤ with
z<0, the degree-z term of the integer Hom cochain complex is the zero R-module. It lies outside
the image of the nonnegative cochain index embedding. -/
theorem isZero_linearHomCochainComplexInt_X_of_neg (G : C)
    (K : ChainComplex C ℕ) (z : ℤ) (hz : z < 0) :
    IsZero ((((linearHomCochainComplexIntBifunctor R C).obj G).obj
      (Opposite.op K)).X z) := by
  have hmem : ∀ n : ℕ, ComplexShape.embeddingUpNat.f n ≠ z :=
    (ComplexShape.notMem_range_embeddingUpNat_iff z).mpr hz
  exact HomologicalComplex.isZero_extend_X
    (((linearHomCochainComplexBifunctor R C).obj G).obj (Opposite.op K))
    ComplexShape.embeddingUpNat z hmem

/-- Let R be a ring in universe w and C a preadditive R-linear category with object universe u and
morphism universe v, all independent. For G∈C, a chain complex K of shape down ℕ and z∈ℤ with
z<0, H^z of the integer-extended Hom cochain complex is zero as an R-module. The complex is
extended by zero in every negative degree, so the negative-degree homology vanishes. -/
theorem isZero_linearHomCochainHomologyInt_of_neg (z : ℤ) (hz : z < 0)
    (G : C) (K : ChainComplex C ℕ) :
    IsZero ((((linearHomCochainHomologyIntBifunctor R C z).obj G).obj
      (Opposite.op K))) := by
  dsimp [linearHomCochainHomologyIntBifunctor,
    linearHomCochainComplexIntBifunctor]
  exact HomologicalComplex.isZero_homology_extendUpNat_neg
    (((linearHomCochainComplexBifunctor R C).obj G).obj (Opposite.op K)) z hz

end HomologicalComplex
