/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSignCacheData

/-! Complete genuine integer source-sign action from bounded original phase data. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every four-input source sign coefficient, retaining both original phase factors. -/
def generatedTwelfthTensorSourceSignSpinCompact (j : Fin 3) (u : Fin 4096 → ℤ)
    (k : Fin 4096) : ℤ :=
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode (generatedTwelfthTensorSourceSignCode j) e
  generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
      generatedTwelfthTensorSourceSignPhase j 0 e *
      (u (generatedAxisGlobalTensorLowLabel d) - u (generatedAxisGlobalTensorHighLabel d)) +
    generatedTwelfthTensorSourceSignPhase j 1 e *
      (u (generatedAxisGlobalTensorLowLabel e) + u (generatedAxisGlobalTensorHighLabel e))

/-- The complete original source sign is the exact compact four-input formula. -/
theorem generatedTwelfth_tensor_source_sign_spin_compact (j : Fin 3)
    (hc : ∀ e : Fin 2048,
      generatedAxisGlobalIntSign
          (golayLabelCoefficients (generatedTwelfthTensorSourceSignCode j) 11) *
          generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
            (generatedTwelfthTensorSourceSignCode j) 0
            (generatedAxisGlobalSignInputCode (generatedTwelfthTensorSourceSignCode j) e) e) =
        generatedTwelfthTensorSourceSignPhase j 0 e ∧
      generatedTwelfthTensorPhysicalSign (generatedTwelfthTensorSourceSignCode j) 0 *
          generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase
            (generatedTwelfthTensorSourceSignCode j) e 0) =
        generatedTwelfthTensorSourceSignPhase j 1 e)
    (u : Fin 4096 → ℤ) :
    generatedTwelfthTensorSignSpinInteger (generatedTwelfthTensorSourceSignCode j) u =
      generatedTwelfthTensorSourceSignSpinCompact j u := by
  funext k
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode (generatedTwelfthTensorSourceSignCode j) e
  unfold generatedTwelfthTensorSignSpinInteger generatedTwelfthTensorSourceSignSpinCompact
  linear_combination
    generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
      (u (generatedAxisGlobalTensorLowLabel d) - u (generatedAxisGlobalTensorHighLabel d)) *
        (hc e).1 +
    (u (generatedAxisGlobalTensorLowLabel e) + u (generatedAxisGlobalTensorHighLabel e)) * (hc e).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
