/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.TorusBorelEulerModels

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open IntegralChowChernModels ComplexAnalytification CoefficientBettiModels
open CoefficientCompactSupportModels CoefficientProperDualityModels TorusBorelEulerModels

namespace TorusBorelEulerModelsTest

variable {O : OrientationData} {X : SchemeData} {E : X.scheme.left.Modules} {r : ℕ}

-- The duality and purity of a zero-section geometry are those of its orientation datum: the
-- Euler class depends on orientations only through the one shared datum.
example (G : ZeroEulerGeometry O X E r) :
    haveI := G.baseSeparated
    haveI := G.baseQuasiCompact
    G.basePurity = O.purity X.scheme G.dimension := rfl

example (G : ZeroEulerGeometry O X E r) :
    G.totalPurity = O.purity G.bundle.total (G.dimension + r) := rfl

-- The rank-zero Euler class, computed by the actual zero-section push, is the unit class for
-- every orientation datum, with no further hypothesis.
example (G : ZeroEulerGeometry O X E 0) : G.euler = unitClass ℂ (space X.scheme) :=
  G.euler_eq_unitClass

-- The zero section of a rank-zero bundle is an isomorphism, found by instance search.
example (G : ZeroEulerGeometry O X E 0) : IsIso (GlobalZeroSectionRecipe.zeroSection G.bundle) :=
  inferInstance

-- Pullback preserves the unit class, and the purity identification sends the fundamental class
-- to the unit class.
example {Z W : TopCat.{0}} (f : Z ⟶ W) :
    cohomologyPullback ℂ f 0 (unitClass ℂ W) = unitClass ℂ Z :=
  cohomologyPullback_unitClass ℂ f

example (Z : TopCat.{0}) (D : DualizingComplex ℂ Z) (d : ℕ)
    (e : D.obj ≅ (coefficientUnit ℂ Z)⟦(2*d : ℤ)⟧) :
    purityHomologyEquiv ℂ Z D d e (2*d) (fundamentalClass ℂ Z D d e) =
      cohomologyCast (by omega) (unitClass ℂ Z) :=
  purityHomologyEquiv_fundamentalClass Z D d e

end TorusBorelEulerModelsTest
