/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MeromorphicGroupFactorizationPuncturedParameterUnit
import MathlibExt.AlgebraicGeometry.MeromorphicCoefficientCompletion

/-!
Tests for the punctured parameter unit: a right inverse and the finite-pole map.
-/

set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicCoefficientCompletion

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.MeromorphicGroupFactorizationPuncturedParameterUnit

/-- The restricted parameter has a right inverse. -/
theorem punctured_parameter_right_inv
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (A : CartierAtlas p E d U) (Q : PoleChart p E d U) :
    ∃ w, sectionMap p E Q.puncture.map Q.parameter * w = 1 :=
  (WantedExt.AlgebraicGeometry.MeromorphicGroupFactorization.punctured_parameter_unit
    p E d U A Q).exists_right_inv

/-- The finite-pole restriction map via the proved unit. -/
def testPuncturedMap
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (A : CartierAtlas p E d U) (Q : PoleChart p E d U) :
    MeromorphicRing p E d U Q →+* SectionRing p E Q.puncture.space :=
  puncturedMap p E d U Q
    (WantedExt.AlgebraicGeometry.MeromorphicGroupFactorization.punctured_parameter_unit
      p E d U A Q)

/-- The constructed map restricts coefficients by the section map. -/
theorem testPuncturedMap_coefficients
    (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
    {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
    (A : CartierAtlas p E d U) (Q : PoleChart p E d U)
    (a : SectionRing p E Q.space) :
    testPuncturedMap p E d U A Q (algebraMap _ (MeromorphicRing p E d U Q) a) =
      sectionMap p E Q.puncture.map a :=
  puncturedMap_coefficients p E d U Q _ a

end MathlibExtTest.AlgebraicGeometry.MeromorphicGroupFactorizationPuncturedParameterUnit
