/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00MatrixPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00ShortPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00TensorPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01MatrixPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01ShortPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison01TensorPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02MatrixPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02ShortPairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison02TensorPairing

/-! Exact complete original pairing certificates for three genuine odd-axis source comparisons. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every full physical matrix, short and tensor pairing equals the original squared axis norm. -/
theorem generatedAxisGlobalOddComparisonPairing_certificate (k : Fin 3) :
    generatedAxisGlobalOddComparisonPairingQ k = 128 := by
  fin_cases k
  · change generatedAxisGlobalOddComparisonPairingQ 0 = 128
    rw [generatedAxisGlobalOddComparisonPairingQ,
      generatedAxisGlobalOddComparison00MatrixPairing,
      generatedAxisGlobalOddComparison00ShortPairing,
      generatedAxisGlobalOddComparison00TensorPairing]
    norm_num
  · change generatedAxisGlobalOddComparisonPairingQ 1 = 128
    rw [generatedAxisGlobalOddComparisonPairingQ,
      generatedAxisGlobalOddComparison01MatrixPairing,
      generatedAxisGlobalOddComparison01ShortPairing,
      generatedAxisGlobalOddComparison01TensorPairing]
    norm_num
  · change generatedAxisGlobalOddComparisonPairingQ 2 = 128
    rw [generatedAxisGlobalOddComparisonPairingQ,
      generatedAxisGlobalOddComparison02MatrixPairing,
      generatedAxisGlobalOddComparison02ShortPairing,
      generatedAxisGlobalOddComparison02TensorPairing]
    norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
