/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RelativeWittUnramifiedNormalization
import MathlibExt.AlgebraicGeometry.RelativeWittGroupIndModels
import MathlibExt.AlgebraicGeometry.WittFramingComparisonModels

/-!
# Original coefficient-square and native framed-map axiom probes

The original Witt coefficient survives tensor base change, p-inversion
and the direct W(R) comparison in one square. Public definitions and
source map proofs are audited independently of every Wanted constructor.
-/

set_option autoImplicit false

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.RelativeWittLoopTests
open MathlibExt.AlgebraicGeometry.RelativeWittUnramifiedNormalization

private theorem coefficient_square (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
    {R S : PerfectAlgebra p k} (f : R ⟶ S) (b : WittVector p k) :
    rationalEquiv p k S
      (rationalMap p k (WittVector p k) (p : WittVector p k) f
        (algebraMap _ _ (coefficient p k (WittVector p k) R b))) =
      algebraMap (WittVector p S.obj) (Localization.Away (p : WittVector p S.obj))
        (wittScalars p k S b) := by
  rw [rationalMap_unit, rationalEquiv_unit, integralMap_coefficient, integralEquiv_coefficient]

#print axioms coefficient_square
#print axioms integralEquiv_tensor
#print axioms integralEquiv_naturality
#print axioms rationalEquiv_naturality
#print axioms UnramifiedModel.functor
#print axioms UnramifiedModel.act
#print axioms MathlibExt.AlgebraicGeometry.RelativeWittGroupIndModels.IncreasingStages.pointsDiagram
#print axioms MathlibExt.AlgebraicGeometry.WittDiscTorsorModels.baseGroupSheaf
#print axioms MathlibExt.AlgebraicGeometry.WittDiscTorsorModels.actionPullback
#print axioms MathlibExt.AlgebraicGeometry.WittFramingComparisonModels.sheafRestrictionSquare
#print axioms MathlibExt.AlgebraicGeometry.WittFramingComparisonModels.framing
#print axioms MathlibExt.AlgebraicGeometry.WittFramingComparisonModels.identifyFrameTarget
