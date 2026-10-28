/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorInputData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMatrixData

/-! Exact rational spatial covariance of the actual Ninth matrix numerator. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option maxRecDepth 100000

/-- Literal integer numerator matrix of one compact lower source spatial action. -/
def generatedNinthLowerSpinMatrixNumerator (i : Fin 11) : Matrix (Fin 24) (Fin 24) ℤ :=
  generatedNinthLowerSpinTensorSpatialNumerator i

/-- Every covariance equation uses the whole original actual Ninth matrix numerator. -/
def generatedNinthLowerSpinMatrixCondition (i : Fin 11) (j k : Fin 24) : Prop :=
  (generatedNinthLowerSpinMatrixNumerator i * Matrix.of generatedNinthMatrixNumerator *
      (generatedNinthLowerSpinMatrixNumerator i).transpose) j k =
    (generatedNinthLowerSpinTensorSpatialDenominator i : ℤ) ^ 2 *
      generatedNinthMatrixNumerator j k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
