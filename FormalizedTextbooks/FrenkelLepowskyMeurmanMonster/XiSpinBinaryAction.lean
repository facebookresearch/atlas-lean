/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit binary matrix of the source spin normalizer, in the fixed frame. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinHolomorph

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

/-- Coordinate lifts of the 24 fixed hyperbolic basis vectors. -/
def xiSpinBinaryBasisLift (j : Fin 24) : Q := ⟨ofAdd (Pi.single j 1), 1⟩

/-- Columns obtained from the explicit, proved Gaussian conjugation formulas. -/
noncomputable def xiSpinBinaryMatrix : Matrix (Fin 24) (Fin 24) (ZMod 2) := fun i j =>
  toAdd (xiSpinGImage (xiSpinGammaImage (xiSpinBinaryBasisLift j))).base i

set_option maxRecDepth 4096 in
/-- The matrix columns describe the actual normalizer's action on Q/Z(Q). -/
theorem xiSpinBinaryMatrix_column (j : Fin 24) :
    spinBinaryAction xiSpinHolomorph (Pi.single j 1) = xiSpinBinaryMatrix.col j := by
  have h := qBinaryAction_apply (spinConjugation xiSpinHolomorph) (xiSpinBinaryBasisLift j)
  change spinBinaryAction xiSpinHolomorph (Pi.single j 1) =
    toAdd (spinConjugation xiSpinHolomorph (xiSpinBinaryBasisLift j)).base at h
  rw [xiSpinHolomorph_conjugation] at h
  exact h

set_option maxRecDepth 4096 in
/-- All binary vectors are acted on by the explicit matrix, by basis extensionality. -/
theorem xiSpinBinaryAction_matrix :
    (spinBinaryAction xiSpinHolomorph).toLinearMap = xiSpinBinaryMatrix.mulVecLin := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
  intro j
  simpa only [Pi.basisFun_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one] using xiSpinBinaryMatrix_column j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
