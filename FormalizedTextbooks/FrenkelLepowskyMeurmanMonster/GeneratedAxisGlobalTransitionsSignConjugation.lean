/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignQImage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit

/-! Executable genuine local and generated conjugation by every low source sign. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual local source sign conjugates every Q element by its explicit phase-correct image. -/
theorem generatedAxisGlobalSignLow_local_conjugation (a : Fin 2048) (q : Q) :
    generatedFifthSignLocal (generatedAxisGlobalSignLowCode a) 0 * inclQ q *
        (generatedFifthSignLocal (generatedAxisGlobalSignLowCode a) 0)⁻¹ =
      inclQ (generatedAxisGlobalSignSpinImage a q) := by
  have h := inclQ_spinConjugation
    (generatedFifthSignFiber (generatedAxisGlobalSignLowCode a) 0) q
  rw [generatedFifth_sign_fiber_local, generatedAxisGlobalSignLow_QImage] at h
  exact h.symm

/-- The literal source word has the same complete Q conjugation in the actual generated group. -/
theorem generatedAxisGlobalSignLow_generated_conjugation (a : Fin 2048) (q : Q) :
    sourceGeneratedY (generatedAxisGlobalSignLowCode a) 0 * qIntoGenerated q *
        (sourceGeneratedY (generatedAxisGlobalSignLowCode a) 0)⁻¹ =
      qIntoGenerated (generatedAxisGlobalSignSpinImage a q) := by
  have h := congrArg localIntoGenerated
    (generatedAxisGlobalSignLow_local_conjugation a q)
  rw [map_mul, map_mul, map_inv, generatedFifth_sign_local_generated] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
