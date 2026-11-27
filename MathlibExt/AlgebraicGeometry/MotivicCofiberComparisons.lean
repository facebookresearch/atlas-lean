/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PointedMotivicQuotients
public import MathlibExt.AlgebraicGeometry.ReducedMotivicCohomologyModels
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Canonical reduced-chain cofiber comparison and connecting maps

The source is the native mapping cone of the actual reduced-free chain
map. Its comparison to the literal pointed cofiber is exactly the native
cone descent with zero homotopy and the actual cofiber quotient map.
There is no freely supplied connecting map or cohomology isomorphism.

When the original pointed map is objectwise monic, quasi-isomorphism of
this fixed comparison is a genuine source construction/proof request.
The derived boundary and cohomology connecting maps use its image and
the native mapping-cone triangle/shift maps.

Sources: Voevodsky arXiv:math/0107109v1, Sections 2 and 4;
Mazza--Voevodsky--Weibel, Lecture 14; native Mathlib mapping-cone source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicCofiberComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels PointedMotivicQuotients
open CochainComplex.HomComplex
open scoped ZeroObject

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  (F : ReducedFreeNisSystem k)

/-- The actual map whose native mapping cone is being compared. -/
def sourceMap {X Y : PointedSpaces (k := k)} (a : X ⟶ Y) :=
  (reducedComplexFunctor F).map a

/-- The actual quotient map on those same reduced source complexes. -/
def quotientMap {X Y : PointedSpaces (k := k)} (a : X ⟶ Y) :=
  (reducedComplexFunctor F).map (cofiberQuotient a)

/-- The cone comparison is the native descent of the actual quotient
with zero homotopy. The null-composite proof carries no cofiber conclusion. -/
def coneComparison {X Y : PointedSpaces (k := k)} (a : X ⟶ Y)
    (h : sourceMap F a ≫ quotientMap F a = 0) :
    CochainComplex.mappingCone (sourceMap F a) ⟶
      (reducedComplexFunctor F).obj (cofiber a) :=
  CochainComplex.mappingCone.desc (sourceMap F a) 0 (quotientMap F a) (by
    simp only [δ_zero, h, Cochain.ofHom_zero])

/-- Source comparison data for a monic pointed map. The only comparison
is the specified native mapping-cone descent above. -/
structure CofiberChainSource {X Y : PointedSpaces (k := k)} (a : X ⟶ Y) where
  zero : sourceMap F a ≫ quotientMap F a = 0
  quasi : QuasiIso (coneComparison F a zero)

attribute [local instance] HasDerivedCategory.standard

/-- The actual derived boundary of the fixed reduced-chain cofiber. -/
def boundary {X Y : PointedSpaces (k := k)} {a : X ⟶ Y}
    (S : CofiberChainSource F a) :
    DerivedCategory.Q.obj ((reducedComplexFunctor F).obj (cofiber a)) ⟶
      (DerivedCategory.Q.obj ((reducedComplexFunctor F).obj X))⟦(1 : ℤ)⟧ := by
  haveI : QuasiIso (coneComparison F a S.zero) := S.quasi
  exact (asIso (DerivedCategory.Q.map (coneComparison F a S.zero))).inv ≫
    DerivedCategory.Q.map (CochainComplex.mappingCone.triangle (sourceMap F a)).mor₃ ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app ((reducedComplexFunctor F).obj X)

variable {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S₀ : TransferSheafificationModel D G}
  {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)} {N : NisTensorSystem k}
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S₀) T N)

/-- Cohomology connecting maps are the native boundary postcomposed
with the shifted input class and the standard addition-of-shifts map. -/
def connecting {X Y : PointedSpaces (k := k)} {a : X ⟶ Y}
    (S : CofiberChainSource F a) (p q : ℤ) (V : ModuleCat.{1} ℤ)
    (u : ReducedCohomology B F X p q V) :
    ReducedCohomology B F (cofiber a) (p + 1) q V :=
  boundary F S ≫ u⟦(1 : ℤ)⟧' ≫
    ((shiftFunctorAdd _ p (1 : ℤ)).app
      (DerivedCategory.Q.obj ((B.weightFunctor q).obj V))).inv

end MathlibExt.AlgebraicGeometry.MotivicCofiberComparisons
