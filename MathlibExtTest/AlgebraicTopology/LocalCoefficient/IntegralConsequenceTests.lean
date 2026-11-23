/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.IntegralConsequence

/-!
# Tests for the ordinary integral consequence

These clients pin the module-forgetful comparison, its naturality, and the
one-way TopCat and CGWH consequences.  They deliberately do not expose a
converse, acyclicity, or plus-recognition theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w u

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.IntegralConsequenceTests

section ForgetfulComparison

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ)

example :
    (AlgebraicTopology.forgetIntegralModule.{u}.mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.singularIntegralModuleChainComplex X) ≅
      AlgebraicTopology.singularIntegralChainFunctor.obj X :=
  AlgebraicTopology.moduleIntegralChainIso X

example :
    AlgebraicTopology.forgetIntegralModule.{u}.obj
        (((AlgebraicTopology.singularHomologyFunctor
          (ModuleCat.{u} ℤ) n).obj
            AlgebraicTopology.singularIntegralModuleCoefficients.{u}).obj X) ≅
      AlgebraicTopology.singularIntegralHomology n X :=
  AlgebraicTopology.moduleIntegralHomologyIso X n

example :
    AlgebraicTopology.forgetIntegralModule.{u}.map
        (((AlgebraicTopology.singularHomologyFunctor
          (ModuleCat.{u} ℤ) n).obj
            AlgebraicTopology.singularIntegralModuleCoefficients.{u}).map f) ≫
      (AlgebraicTopology.moduleIntegralHomologyIso Y n).hom =
    (AlgebraicTopology.moduleIntegralHomologyIso X n).hom ≫
      (AlgebraicTopology.singularIntegralHomologyFunctor n).map f :=
  AlgebraicTopology.moduleIntegralHomologyIso_naturality f n

end ForgetfulComparison

section TopCatConsequence

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

example (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f) :=
  hf.isIntegral n

example (X : TopCat.{u})
    (hf : TopCat.IsLocalCoefficientHomologyEquivalence (𝟙 X)) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map (𝟙 X)) :=
  hf.isIntegral n

private noncomputable def collapse : TopCat.I.{0} ⟶ TopCat.I.{0} :=
  TopCat.const (X := TopCat.I.{0}) (0 : TopCat.I.{0})

example (hf : TopCat.IsLocalCoefficientHomologyEquivalence collapse) (n : ℕ) :
    IsIso
      ((AlgebraicTopology.singularIntegralHomologyFunctor.{0} n).map
        collapse) :=
  hf.isIntegral n

end TopCatConsequence

section CGWHConsequence

variable {X Y : CGWH.{w, u}} (f : X ⟶ Y)

example (hf : CGWH.IsLocalCoefficientHomologyEquivalence f) :
    CGWH.IsIntegralHomologyEquivalence f :=
  hf.isIntegral

end CGWHConsequence

section RaisedUniverses

variable {X Y : TopCat.{2}} (f : X ⟶ Y)

example (hf : TopCat.IsLocalCoefficientHomologyEquivalence f) (n : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor n).map f) :=
  hf.isIntegral n

variable {P Q : CGWH.{3, 2}} (g : P ⟶ Q)

example (hg : CGWH.IsLocalCoefficientHomologyEquivalence g) :
    CGWH.IsIntegralHomologyEquivalence g :=
  hg.isIntegral

end RaisedUniverses

section StoppingBoundary

#guard_msgs (error, substring := true) in
#check CGWH.IsIntegralHomologyEquivalence.isLocalCoefficient

#guard_msgs (error, substring := true) in
#check TopCat.IsLocalCoefficientHomologyEquivalence.isAcyclic

#guard_msgs (error, substring := true) in
#check CGWH.IsLocalCoefficientHomologyEquivalence.isPlusConstructionAlong

end StoppingBoundary

#print axioms AlgebraicTopology.moduleIntegralHomologyNatIso
#print axioms AlgebraicTopology.moduleIntegralHomologyIso_naturality
#print axioms TopCat.IsLocalCoefficientHomologyEquivalence.isIntegral
#print axioms CGWH.IsLocalCoefficientHomologyEquivalence.isIntegral

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.IntegralConsequenceTests
