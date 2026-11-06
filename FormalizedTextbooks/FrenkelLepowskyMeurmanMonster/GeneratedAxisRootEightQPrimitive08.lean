/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQPrimitiveData

/-! Every coordinate and central sign of original primitive 8 is checked in the original Q group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 64000000 in
-- Evaluate all 24 source generators through the full original finite Q formulas.
set_option maxRecDepth 100000 in
-- Check all original positive binary generators, retaining their entire central coordinates.
/-- Primitive 8 agrees with every stated complete original Q basis image. -/
theorem generatedRootEight_Q_primitive_08_actual : ∀ i : Fin 24,
    generatedRootEightQPrimitiveImage 8 (qCoordinateGenerator i) =
      generatedRootEightQPrimitiveBasisImage 8 i := by
  have hb : ∀ i j : Fin 24, Multiplicative.toAdd
      (generatedRootEightQPrimitiveImage 8 (qCoordinateGenerator i)).base j =
        Multiplicative.toAdd (generatedRootEightQPrimitiveBasisImage 8 i).base j := by
    decide +kernel
  have hc : ∀ i : Fin 24, Multiplicative.toAdd
      (generatedRootEightQPrimitiveImage 8 (qCoordinateGenerator i)).coeff =
        Multiplicative.toAdd (generatedRootEightQPrimitiveBasisImage 8 i).coeff := by
    decide +kernel
  intro i
  apply NormalizedCocycleExtension.Extension.ext
  · apply Multiplicative.toAdd.injective
    exact funext (hb i)
  · apply Multiplicative.toAdd.injective
    exact hc i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
