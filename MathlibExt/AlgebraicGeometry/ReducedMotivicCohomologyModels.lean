/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PointedMotivicModels
public import MathlibExt.AlgebraicTopology.SpectraSource.LinearAlgebra.Finsupp.ReducedFree
public import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
# Reduced Nisnevich chains and actual motivic cohomology pullbacks

The reduced free modules use the native quotient of the free Z-module by
the basepoint generator. Each presheaf, simplex and space-map action is
fixed on every generator. Sheafification, normalized Moore chains and
negative-index extension give the actual reduced source complex.

Reduced motivic groups are native derived Homs into the independently
constructed Tate coefficient complexes. Pullback is actual precomposition
by the free reduced chain map; coefficient change is actual postcomposition.
No operation, Thom or A1 comparison is part of these definitions.

Reference: Voevodsky arXiv:math/0107109v1, §2 p.6, and MVW Lecture 14.
Reduced free module bodies retain their Apache source provenance.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ReducedMotivicCohomologyModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open FiniteTransferCycleModels FiniteTransferProductModels MotivicStandardSchemes
open NisnevichTransferModels EffectiveMotivicComplexModels PointedMotivicModels
open MathlibExt.SpectraSource
open scoped Simplicial ZeroObject

variable {k : Type} [Field k]
variable [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]

/-- The reduced free system is fixed on all actual simplices and all module generators. -/
structure ReducedFreeNisSystem (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] where
  functor : PointedSpaces (k := k) ⥤ SimplexCategoryᵒᵖ ⥤ (SmoothScheme k)ᵒᵖ ⥤ ModuleCat.{1} ℤ
  valueIso : ∀ (F : PointedSpaces (k := k)) (n : SimplexCategoryᵒᵖ) (U : (SmoothScheme k)ᵒᵖ)
    (t : ((𝟙_ (Spaces (k := k))).obj U).obj n),
    ((functor.obj F).obj n).obj U ≅
      ModuleCat.of ℤ (ReducedFreeModule ℤ (((F.hom.app U).app n) t))
  simplex_eq : ∀ (F : PointedSpaces (k := k)) (n m : SimplexCategoryᵒᵖ) (a : n ⟶ m)
    (U : (SmoothScheme k)ᵒᵖ)
    (t : ((𝟙_ (Spaces (k := k))).obj U).obj n) (s : ((𝟙_ (Spaces (k := k))).obj U).obj m)
    (h : ((𝟙_ (Spaces (k := k))).obj U).map a t = s) (x : (F.right.obj U).obj n),
    (valueIso F m U s).hom (((functor.obj F).map a).app U
      ((valueIso F n U t).inv (ReducedFreeModule.mk ℤ x))) =
        ReducedFreeModule.mk ℤ ((F.right.obj U).map a x)
  restriction_eq : ∀ (F : PointedSpaces (k := k)) (n : SimplexCategoryᵒᵖ)
    (U V : (SmoothScheme k)ᵒᵖ) (a : U ⟶ V)
    (t : ((𝟙_ (Spaces (k := k))).obj U).obj n) (s : ((𝟙_ (Spaces (k := k))).obj V).obj n)
    (h : (((𝟙_ (Spaces (k := k))).map a).app n) t = s) (x : (F.right.obj U).obj n),
    (valueIso F n V s).hom (((functor.obj F).obj n).map a
      ((valueIso F n U t).inv (ReducedFreeModule.mk ℤ x))) =
        ReducedFreeModule.mk ℤ (((F.right.map a).app n) x)
  map_eq : ∀ (F H : PointedSpaces (k := k)) (a : F ⟶ H)
    (n : SimplexCategoryᵒᵖ) (U : (SmoothScheme k)ᵒᵖ)
    (t : ((𝟙_ (Spaces (k := k))).obj U).obj n) (x : (F.right.obj U).obj n),
    (valueIso H n U t).hom (((functor.map a).app n).app U
      ((valueIso F n U t).inv (ReducedFreeModule.mk ℤ x))) =
        ReducedFreeModule.mk ℤ (((a.right.app U).app n) x)

def reducedComplexFunctor (F : ReducedFreeNisSystem k) :
    PointedSpaces (k := k) ⥤ CochainComplex (NisModules (k := k)) ℤ :=
  F.functor ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ
      ((SmoothScheme k)ᵒᵖ ⥤ ModuleCat.{1} ℤ) (NisModules (k := k))).obj
        (presheafToSheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)) ⋙
    AlgebraicTopology.normalizedMooreComplex (NisModules (k := k)) ⋙
      negativeEmbedding.extendFunctor (NisModules (k := k))

attribute [local instance] HasDerivedCategory.standard

variable {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}
  {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R)}
  {N : NisTensorSystem k}
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R) (S := S) T N)
  (F : ReducedFreeNisSystem k)

/-- Reduced motivic hypercohomology of the actual free source complex. -/
abbrev ReducedCohomology (X : PointedSpaces (k := k)) (p q : ℤ) (V : ModuleCat.{1} ℤ) :=
  DerivedCategory.Q.obj ((reducedComplexFunctor F).obj X) ⟶
    (DerivedCategory.Q.obj ((B.weightFunctor q).obj V))⟦p⟧

def pullback {X Y : PointedSpaces (k := k)} (a : X ⟶ Y) (p q : ℤ) (V : ModuleCat.{1} ℤ) :
    ReducedCohomology B F Y p q V → ReducedCohomology B F X p q V :=
  fun u => DerivedCategory.Q.map ((reducedComplexFunctor F).map a) ≫ u

def coefficientMap (X : PointedSpaces (k := k)) (p q : ℤ)
    {V W : ModuleCat.{1} ℤ} (a : V ⟶ W) :
    ReducedCohomology B F X p q V → ReducedCohomology B F X p q W :=
  fun u => u ≫ (DerivedCategory.Q.map ((B.weightFunctor q).map a))⟦p⟧'

end MathlibExt.AlgebraicGeometry.ReducedMotivicCohomologyModels
