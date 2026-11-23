/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatConstant
public import Mathlib.Basic.Real.Basic

/-! # Tests for constant local systems on TopCat and CGWH spaces -/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatConstantTests

universe uR uK uX

section GenericTopCat

variable {R : Type uR} [CommRing R]
variable {X : TopCat.{uX}}
variable (M : ModuleCat.{max uR uX} R)

example : TopCat.LocalSystem R X := TopCat.constantLocalSystem M

example :
    (TopCat.constantLocalSystem (X := X) M).toSingular ≅
      SSet.constantLocalSystem (X := TopCat.toSSet.obj X) M :=
  TopCat.LocalSystem.constantToSingularIso (X := X) M

example (x : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (TopCat.LocalSystem.constantToSingularIso (X := X) M).hom.app x = 𝟙 M :=
  TopCat.LocalSystem.constantToSingularIso_hom_app (X := X) M x

example (x : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (TopCat.LocalSystem.constantToSingularIso (X := X) M).inv.app x = 𝟙 M :=
  TopCat.LocalSystem.constantToSingularIso_inv_app (X := X) M x

example :
    TopCat.localCoefficientChainComplex
        (TopCat.constantLocalSystem (X := X) M) ≅
      SSet.localCoefficientChainComplex
        (SSet.constantLocalSystem (X := TopCat.toSSet.obj X) M) :=
  TopCat.constantToSingularChainIso (X := X) M

example (n : ℕ) :
    (TopCat.constantToSingularChainIso (X := X) M).hom.f n =
      SSet.localCoefficientMap
        (X := TopCat.toSSet.obj X)
        (TopCat.LocalSystem.constantToSingularIso (X := X) M).hom n :=
  TopCat.constantToSingularChainIso_hom_f (X := X) M n

example :
    TopCat.localCoefficientChainComplex
        (TopCat.constantLocalSystem (X := X) M) ≅
      ((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat.{max uR uX} R)).obj M).obj X :=
  TopCat.constantLocalCoefficientChainIso (X := X) M

example (n : ℕ) :
    (TopCat.constantLocalCoefficientChainIso (X := X) M).hom.f n =
      SSet.localCoefficientMap
          (X := TopCat.toSSet.obj X)
          (TopCat.LocalSystem.constantToSingularIso (X := X) M).hom n ≫
        (SSet.constantLocalCoefficientChainIso
          (X := TopCat.toSSet.obj X) M).hom.f n :=
  TopCat.constantLocalCoefficientChainIso_hom_f (X := X) M n

example {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    TopCat.constantLocalCoefficientι (X := X) M σ ≫
        (TopCat.constantLocalCoefficientChainIso (X := X) M).hom.f n =
      (TopCat.toSSet.obj X).ιChainComplex σ :=
  TopCat.constantLocalCoefficientι_comp_chainIso_hom (X := X) M σ

end GenericTopCat

section SpaceShapes

variable {R : Type uR} [CommRing R]
variable (M : ModuleCat.{uR} R)

example :
    TopCat.localCoefficientChainComplex
        (TopCat.constantLocalSystem (X := TopCat.of PUnit) M) ≅
      ((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat.{uR} R)).obj M).obj (TopCat.of PUnit) :=
  TopCat.constantLocalCoefficientChainIso (X := TopCat.of PUnit) M

example :
    TopCat.localCoefficientChainComplex
        (TopCat.constantLocalSystem (X := TopCat.of ℝ) M) ≅
      ((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat.{uR} R)).obj M).obj (TopCat.of ℝ) :=
  TopCat.constantLocalCoefficientChainIso (X := TopCat.of ℝ) M

end SpaceShapes

section RaisedTopCatUniverses

variable {R₁ : Type 1} [CommRing R₁]
variable {X₂ : TopCat.{2}}
variable (M₂ : ModuleCat.{2} R₁)

example :
    TopCat.localCoefficientChainComplex
        (TopCat.constantLocalSystem (X := X₂) M₂) ≅
      ((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat.{2} R₁)).obj M₂).obj X₂ :=
  TopCat.constantLocalCoefficientChainIso (X := X₂) M₂

variable {R₂ : Type 2} [CommRing R₂]
variable {X₁ : TopCat.{1}}
variable (M₁ : ModuleCat.{2} R₂)

example :
    TopCat.localCoefficientChainComplex
        (TopCat.constantLocalSystem (X := X₁) M₁) ≅
      ((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat.{2} R₂)).obj M₁).obj X₁ :=
  TopCat.constantLocalCoefficientChainIso (X := X₁) M₁

end RaisedTopCatUniverses

section CGWHWrapper

variable {R : Type uR} [CommRing R]
variable {X : CGWH.{uK, uX}}
variable (M : ModuleCat.{max uR uX} R)

example : CGWH.LocalSystem R X := CGWH.constantLocalSystem (X := X) M

example :
    CGWH.localCoefficientChainComplex
        (CGWH.constantLocalSystem (X := X) M) ≅
      ((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat.{max uR uX} R)).obj M).obj X.toTop :=
  CGWH.constantLocalCoefficientChainIso (X := X) M

example {n : ℕ} (σ : (TopCat.toSSet.obj X.toTop) _⦋n⦌) :
    CGWH.constantLocalCoefficientι (X := X) M σ ≫
        (CGWH.constantLocalCoefficientChainIso (X := X) M).hom.f n =
      (TopCat.toSSet.obj X.toTop).ιChainComplex σ :=
  CGWH.constantLocalCoefficientι_comp_chainIso_hom (X := X) M σ

end CGWHWrapper

section RaisedCGWHCompactUniverse

variable {R : Type 1} [CommRing R]
variable {X : CGWH.{3, 2}}
variable (M : ModuleCat.{2} R)

example :
    CGWH.localCoefficientChainComplex
        (CGWH.constantLocalSystem (X := X) M) ≅
      ((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat.{2} R)).obj M).obj X.toTop :=
  CGWH.constantLocalCoefficientChainIso (X := X) M

end RaisedCGWHCompactUniverse

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check TopCat.constantLocalCoefficientHomologyIso

#guard_msgs (error, substring := true) in
#check TopCat.constantLocalCoefficientMap

#guard_msgs (error, substring := true) in
#check CGWH.constantLocalCoefficientHomologyIso

end StoppingBoundary

#print axioms TopCat.constantLocalSystem
#print axioms TopCat.LocalSystem.constantToSingularIso
#print axioms TopCat.LocalSystem.constantToSingularIso_hom_app
#print axioms TopCat.LocalSystem.constantToSingularIso_inv_app
#print axioms TopCat.constantToSingularChainIso
#print axioms TopCat.constantToSingularChainIso_hom_f
#print axioms TopCat.constantLocalCoefficientChainIso
#print axioms TopCat.constantLocalCoefficientChainIso_hom_f
#print axioms TopCat.constantLocalCoefficientι
#print axioms TopCat.constantLocalCoefficientι_comp_chainIso_hom
#print axioms CGWH.constantLocalSystem
#print axioms CGWH.constantLocalCoefficientChainIso
#print axioms CGWH.constantLocalCoefficientι
#print axioms CGWH.constantLocalCoefficientChainIso_hom_f
#print axioms CGWH.constantLocalCoefficientι_comp_chainIso_hom

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.TopCatConstantTests
