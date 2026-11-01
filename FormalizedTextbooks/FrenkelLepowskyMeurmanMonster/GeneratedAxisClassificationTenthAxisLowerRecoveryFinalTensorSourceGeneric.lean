/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalShortSourceTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRationalTrialityTensor

/-! Ungated full original final tensor source formula; incoming tensor difference is retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Complete original incoming C in its genuine denominator16 normalization. -/
def generatedTenthFinalTensorSourceIncomingCQ (r : GriessShortIndex) : ℚ :=
  (generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient r : ℚ) / 16

/-- All eight original incoming tensor factors retain both Omega rows and their true denominators.
-/
def generatedTenthFinalTensorSourceIncomingTQ (t : SpinIndex) (i : Fin 24) : ℚ :=
  generatedTenthFinalShortSourceTensorQ (nortonUIntegerLabel t) i

/-- The complete outgoing rational numerator includes the odd C source and the incoming tensor
Omega difference, with the exact physical signs and denominator64 times sqrt2. -/
def generatedTenthFinalTensorSourceQ (k : Fin 4096) (i : Fin 24) : ℚ :=
  64 * generatedAxisGlobalTrialityScaledTensorQ generatedTenthFinalTensorSourceIncomingCQ
    generatedTenthFinalTensorSourceIncomingTQ (golayLabelCoefficients k) i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
