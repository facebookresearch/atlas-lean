/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedDGModuli
public import MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
public import MathlibExt.AlgebraicTopology.FullEnhancedSubcategory
public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

/-!
# Ordinary complexes extracted from the actual DG moduli vertices

The coefficient module is the literal value of vertexBimodule at the
chosen scalar-frame object. Its ordinary A-complex has its complete
underlying cochain object, every differential, every homogeneous map
component and its A-action fixed by the native N(const A) module.
It is associated to the actual small étale structure sheaf by the
source-normalized tilde/pullback realization.

The source ordinary comparison is restricted to the universally glueable
locus. Its groupoid truncation is the native fundamental groupoid of
that full simplicial subcomplex. Restriction to ordinary coefficients
alone still retains higher moduli homotopy and is not this groupoid.

References: Toën--Vaquié, math/0503269v5, §3.1 pp36--37 and p8
(the open no-negative-Ext locus); Stacks 0DLD/0DLE. The full comparison
construction and equivalence proof remain separate Wanted requests.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
  _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedDGModuli
open MathlibExt.AlgebraicGeometry.ClassicalComplexesSourceModels
open scoped Simplicial

universe u

variable {k : Type u} [CommRing k]

/-- The source k-linear scalar category has the actual tensor-unit Hom complex. -/
def scalarCategory (k : Type u) [CommRing k] : DGCat k :=
  algebraCategory (Mon.mk (𝟙_ (Cochains k)))

/-- Forget only the algebra structure, retaining the actual coefficient ring. -/
def ordinaryRing (A : CommAlgCat.{u} k) : CommRingCat.{u} := CommRingCat.of A

/-- Native normalization of the constant algebra in every degree. -/
structure OrdinaryCoefficientSource (N : ShuffleAlgebraFunctor k) (A : CommAlgCat.{u} k) where
  degreeZero : (N.functor.obj (ordinaryAlgebras.obj A)).X.X 0 ≃ₗ[k] A
  degreeZero_eq : ∀ a : (N.functor.obj (ordinaryAlgebras.obj A)).X.X 0,
    degreeZero a = coefficient (ordinaryAlgebras.obj A) 0
      (((N.model (ordinaryAlgebras.obj A)).complexIso.hom.f 0).hom a)
  otherDegrees : ∀ i : ℤ, i ≠ 0 → IsZero ((N.functor.obj (ordinaryAlgebras.obj A)).X.X i)

/-- The prescribed ordinary A-module realization, including all homogeneous components. -/
structure OrdinaryModuleSource {N : ShuffleAlgebraFunctor k} {A : CommAlgCat.{u} k}
    (C : OrdinaryCoefficientSource N A) where
  functor : RightModule k (coefficientCategory N (ordinaryAlgebras.obj A)) ⥤
    CochainComplex (ModuleCat.{u} A) ℤ
  underlyingIso : functor ⋙
    (ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (.up ℤ) ≅
      moduleEvaluationFunctor (op PUnit.unit)
  action : ∀ (M : RightModule k (coefficientCategory N (ordinaryAlgebras.obj A)))
    (i : ℤ) (a : A) (x : (functor.obj M).X i),
    (((underlyingIso.hom.app M).f i).hom (a • x)) =
      cochainEval k (((underlyingIso.hom.app M).f i).hom x) 0 i (by omega)
        (M.toEnrichedFunctor.dgMap 0 (C.degreeZero.symm a))
  homogeneousMap : ∀ (M M' : RightModule k (coefficientCategory N (ordinaryAlgebras.obj A)))
    (i : ℤ), DGHom k i M M' → CochainComplex.HomComplex.Cochain
      (functor.obj M) (functor.obj M') i
  homogeneousMap_eq : ∀ (M M' : RightModule k (coefficientCategory N (ordinaryAlgebras.obj A)))
    (i p q : ℤ) (h : p + i = q) (a : DGHom k i M M') (x : (functor.obj M).X p),
    (((underlyingIso.hom.app M').f q).hom
      (((homogeneousMap M M' i a).v p q h).hom x)) =
        cochainEval k (((underlyingIso.hom.app M).f p).hom x) i q h
          (DGFunctor.dgApp k (C := (coefficientCategory N (ordinaryAlgebras.obj A))ᵒᵖ)
            i (op PUnit.unit) a)

/-- A frame object mapping to the unique actual scalar object. -/
structure ScalarFramePoint (R : DGFrame k (oppositeCategory (scalarCategory k))) where
  point : R.diagram.obj ⦋0⦌

/-- The exact coefficient-perfect module at the chosen scalar-frame object. -/
def vertexModule {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
    RightModule k (coefficientCategory N (ordinaryAlgebras.obj A)) :=
  ((P.realization (ordinaryAlgebras.obj A)).obj (E.obj r.point)).obj

/-- This module is literally the indicated value of the native vertex bimodule. -/
theorem vertexModule_eq_bimodule {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
    vertexModule r P A E =
      (vertexBimodule R P (ordinaryAlgebras.obj A) E).toEnrichedFunctor.obj r.point := rfl

/-- The ordinary complex is extracted from the complete actual coefficient module. -/
def vertexOrdinaryComplex {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    {C : OrdinaryCoefficientSource N A} (V : OrdinaryModuleSource C)
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  V.functor.obj (vertexModule r P A E)

/-- Its source small étale derived object uses that same ordinary complex in every degree. -/
def vertexEtaleDerived {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    {C : OrdinaryCoefficientSource N A} (V : OrdinaryModuleSource C)
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X}
    (J : AffineEtaleModuleSource O (ordinaryRing A))
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) :
    EtaleDerived O (Spec (ordinaryRing A)) :=
  associatedEtaleDerived J (vertexOrdinaryComplex r P A V E)

/-- The locus is the actual perfect/no-negative-field-Ext source condition. -/
def IsUniversallyGlueableVertex {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    {C : OrdinaryCoefficientSource N A} (V : OrdinaryModuleSource C)
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} (L : EtalePullbackSystem O)
    (J : AffineEtaleModuleSource O (ordinaryRing A))
    (E : ((underivedModuliFunctor R P).obj A) _⦋0⦌) : Prop :=
  ComplexesProperty L J (vertexEtaleDerived r P A V J E)

/-- All higher simplices whose vertices satisfy that condition remain present. -/
def universallyGlueableSpace {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    {C : OrdinaryCoefficientSource N A} (V : OrdinaryModuleSource C)
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} (L : EtalePullbackSystem O)
    (J : AffineEtaleModuleSource O (ordinaryRing A)) : SSet.{u + 1} :=
  (((underivedModuliFunctor R P).obj A).fullEnhancedSubcategory
    (IsUniversallyGlueableVertex r P A V L J)).toSSet

/-- Correct source groupoid truncation, after imposing the actual glueable locus. -/
abbrev universallyGlueableGroupoid {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {R : DGFrame k (oppositeCategory (scalarCategory k))}
    (r : ScalarFramePoint R) (P : StrictPerfectSystem N S) (A : CommAlgCat.{u} k)
    {C : OrdinaryCoefficientSource N A} (V : OrdinaryModuleSource C)
    {O : ∀ X : Scheme.{u}, EtaleStructureSource X} (L : EtalePullbackSystem O)
    (J : AffineEtaleModuleSource O (ordinaryRing A)) :=
  SSet.FundamentalGroupoid (universallyGlueableSpace r P A V L J)

end MathlibExt.AlgebraicGeometry.DerivedOrdinaryComplexModels
