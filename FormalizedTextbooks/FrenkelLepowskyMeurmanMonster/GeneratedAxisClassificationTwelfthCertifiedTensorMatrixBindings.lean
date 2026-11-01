/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCertifiedMatrixData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorInputData

/-! Complete original tensor matrices agree with the constructed lattice candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The complete tensor spatial numerators equal the corresponding certified lattice matrices. -/
theorem generatedTwelfth_certified_tensor_matrix_entries : ∀ (g : Fin 12) (i j : Fin 24),
    generatedTwelfthSpinTensorSpatialNumerator g i j =
      generatedTwelfthCertifiedNumerator g i j := by
  decide +kernel

/-- Each rational denominator is retained exactly in both complete constructions. -/
theorem generatedTwelfth_certified_tensor_denominators : ∀ g : Fin 12,
    generatedTwelfthSpinTensorSpatialDenominator g = generatedTwelfthCertifiedDenominator g := by
  decide +kernel

/-- The full numerator matrix used by genuine tensor replay is the candidate physical matrix. -/
theorem generatedTwelfth_certified_tensor_matrices (g : Fin 12) :
    generatedTwelfthSpinTensorSpatialNumerator g = generatedTwelfthCertifiedNumerator g := by
  ext i j
  exact generatedTwelfth_certified_tensor_matrix_entries g i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
