/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SingularHomology.PointedRelativeReducedComparison
import MathlibExt.AlgebraicTopology.SingularHomology.Sphere.Zero
import MathlibExt.Topology.Category.TopCat.SpherePointed
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Data.Matrix.Mul

/-!
# Pointed relative/reduced singular-homology comparison tests

These tests exercise the literal component, space and coefficient naturality,
degree zero and a positive degree, independent universes, and coefficient
categories beyond commutative rings.  The pointed zero-sphere keeps the
degree-zero test nonvacuous.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

universe w v u

namespace MathlibExtTest.AlgebraicTopology.SingularHomology
namespace PointedRelativeReducedComparisonTests

private noncomputable def pointedPoint : PointedTopCat.{w} :=
  Under.mk (𝟙 (TopCat.of PUnit : TopCat.{w}))

private noncomputable def pointToSphereZero :
    pointedPoint.{0} ⟶ TopCat.pointedSphere.{0} 0 :=
  Under.homMk (TopCat.sphereBasepoint 0) (by
    simp [pointedPoint, TopCat.pointedSphere])

private abbrev IntModule := ModuleCat.of ℤ ℤ

private noncomputable def doubleIntModule : IntModule ⟶ IntModule :=
  ModuleCat.ofHom (LinearMap.lsmul ℤ IntModule (2 : ℤ))

private abbrev MatrixRing := Matrix (Fin 2) (Fin 2) ℤ

private abbrev MatrixModule := ModuleCat.of MatrixRing MatrixRing

section PublicContract

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]
variable (R : C) (n : ℕ) (X : PointedTopCat.{w})

example :
    reducedSingularHomology C R n X.right ≅
      (relativeSingularHomologyFunctor C R n).obj
        (PointedTopCat.pointedPair.obj X) :=
  (pointedRelativeReducedSingularHomologyNatIso C R n).app X

example :
    (pointedRelativeReducedSingularHomologyNatIso C R n).hom.app X =
      (reducedSingularHomologyι C R n).app X.right ≫
        HomologicalComplex.homologyMap
          (relativeSingularChainQuotient C R
            (PointedTopCat.pointedPair.obj X)) n :=
  pointedRelativeReducedSingularHomologyNatIso_hom_app C R n X

end PublicContract

section Degrees

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C] (R : C)

example :
    reducedSingularHomology C R 0 pointedPoint.{w}.right ≅
      (relativeSingularHomologyFunctor C R 0).obj
        (PointedTopCat.pointedPair.obj pointedPoint.{w}) :=
  (pointedRelativeReducedSingularHomologyNatIso C R 0).app pointedPoint

example :
    reducedSingularHomology C R 1 pointedPoint.{w}.right ≅
      (relativeSingularHomologyFunctor C R 1).obj
        (PointedTopCat.pointedPair.obj pointedPoint.{w}) :=
  (pointedRelativeReducedSingularHomologyNatIso C R 1).app pointedPoint

end Degrees

section SphereZero

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{0} C] (R : C)

example :
    reducedSingularHomology C R 0
        (TopCat.pointedSphere.{0} 0).right ≅
      (relativeSingularHomologyFunctor C R 0).obj
        (PointedTopCat.pointedPair.obj (TopCat.pointedSphere.{0} 0)) :=
  (pointedRelativeReducedSingularHomologyNatIso C R 0).app
    (TopCat.pointedSphere 0)

example :
    reducedSingularHomology C R 0 (TopCat.sphere.{0} 0) ≅ R :=
  sphereZeroReducedH0Iso (C := C) R

end SphereZero

section SpaceNaturality

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{0} C] (R : C) (n : ℕ)

example :
    ((Under.forget (TopCat.of PUnit) ⋙
        reducedSingularHomologyFunctor C R n).map pointToSphereZero) ≫
      (pointedRelativeReducedSingularHomologyNatIso C R n).hom.app
        (TopCat.pointedSphere 0) =
    (pointedRelativeReducedSingularHomologyNatIso C R n).hom.app
        pointedPoint ≫
      ((PointedTopCat.pointedPair ⋙
        relativeSingularHomologyFunctor C R n).map pointToSphereZero) :=
  (pointedRelativeReducedSingularHomologyNatIso C R n).hom.naturality
    pointToSphereZero

end SpaceNaturality

section CoefficientNaturality

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]
variable {R S : C} (a : R ⟶ S) (n : ℕ) (X : PointedTopCat.{w})

example :
    ((reducedSingularHomologyCoefficientFunctor C n).map a).app X.right ≫
        (pointedRelativeReducedSingularHomologyNatIso C S n).hom.app X =
      (pointedRelativeReducedSingularHomologyNatIso C R n).hom.app X ≫
        ((relativeSingularHomologyCoefficientFunctor (C := C) n).map a).app
          (PointedTopCat.pointedPair.obj X) :=
  pointedRelativeReducedSingularHomologyNatIso_hom_naturality_coefficient
    (C := C) (n := n) a X

end CoefficientNaturality

section ConcreteCoefficients

variable {A : Type u} [Ring A]

example (X : PointedTopCat.{u}) :
    reducedSingularHomology (ModuleCat.{u} A)
        (⊥_ (ModuleCat.{u} A)) 0 X.right ≅
      (relativeSingularHomologyFunctor (ModuleCat.{u} A)
        (⊥_ (ModuleCat.{u} A)) 0).obj
          (PointedTopCat.pointedPair.obj X) :=
  (pointedRelativeReducedSingularHomologyNatIso
    (ModuleCat.{u} A) (⊥_ (ModuleCat.{u} A)) 0).app X

example (X : PointedTopCat.{0}) :=
  pointedRelativeReducedSingularHomologyNatIso_hom_naturality_coefficient
    (C := ModuleCat.{0} ℤ) (n := 0) doubleIntModule X

example (X : PointedTopCat.{0}) :=
  pointedRelativeReducedSingularHomologyNatIso_hom_naturality_coefficient
    (C := ModuleCat.{0} ℤ) (n := 0)
      (0 : IntModule ⟶ IntModule) X

end ConcreteCoefficients

section Noncommutative

example : True := by
  fail_if_success let _ : CommRing MatrixRing := inferInstance
  trivial

example (X : PointedTopCat.{0}) :
    reducedSingularHomology (ModuleCat.{0} MatrixRing)
        MatrixModule 0 X.right ≅
      (relativeSingularHomologyFunctor (ModuleCat.{0} MatrixRing)
        MatrixModule 0).obj (PointedTopCat.pointedPair.obj X) :=
  (pointedRelativeReducedSingularHomologyNatIso
    (ModuleCat.{0} MatrixRing) MatrixModule 0).app X

end Noncommutative

section Universes

example {C : Type 1} [Category.{1} C] [Abelian C]
    [HasCoproducts.{1} C] (R : C) (X : PointedTopCat.{1}) :
    reducedSingularHomology C R 0 X.right ≅
      (relativeSingularHomologyFunctor C R 0).obj
        (PointedTopCat.pointedPair.obj X) :=
  (pointedRelativeReducedSingularHomologyNatIso C R 0).app X

example {C : Type} [Category C] [Abelian C]
    [HasCoproducts.{0} C] (R : C) (X : PointedTopCat.{0}) :
    reducedSingularHomology C R 1 X.right ≅
      (relativeSingularHomologyFunctor C R 1).obj
        (PointedTopCat.pointedPair.obj X) :=
  (pointedRelativeReducedSingularHomologyNatIso C R 1).app X

end Universes

section PremiseBoundary

example {C : Type u} [Category.{v} C] [Abelian C]
    (_R : C) (_X : PointedTopCat.{w}) : True := by
  fail_if_success
    exact (pointedRelativeReducedSingularHomologyNatIso C _R 0).app _X
  trivial

end PremiseBoundary

#check pointedRelativeReducedSingularHomologyNatIso
#check pointedRelativeReducedSingularHomologyNatIso_hom_app
#check pointedRelativeReducedSingularHomologyNatIso_hom_naturality_coefficient

#print axioms pointedRelativeReducedSingularHomologyNatIso
#print axioms pointedRelativeReducedSingularHomologyNatIso_hom_app
#print axioms pointedRelativeReducedSingularHomologyNatIso_hom_naturality_coefficient

end PointedRelativeReducedComparisonTests
end MathlibExtTest.AlgebraicTopology.SingularHomology
