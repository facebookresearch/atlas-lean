/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthSignCacheCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthSignCacheCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthSignCacheCheck02

/-! The root-two source signs with codes `0`, `1024` and `2304` as compact four-input formulas. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every four-input source sign coefficient, retaining both phase factors. -/
def generatedFeasibleAmbientTenthSignSpinCompact (j : Fin 3) (u : Fin 4096 → ℤ) (k : Fin 4096) : ℤ
    :=
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode (generatedFeasibleAmbientTenthSignCode j) e
  generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
      generatedFeasibleAmbientTenthSignPhase j 0 e *
      (u (generatedAxisGlobalTensorLowLabel d) - u (generatedAxisGlobalTensorHighLabel d)) +
    generatedFeasibleAmbientTenthSignPhase j 1 e *
      (u (generatedAxisGlobalTensorLowLabel e) + u (generatedAxisGlobalTensorHighLabel e))

/-- The source sign of code `j` is the compact four-input formula. -/
theorem generatedFeasibleAmbientTenth_sign_cached_actual (j : Fin 3) (u : Fin 4096 → ℤ) :
    generatedTwelfthTensorSignSpinInteger (generatedFeasibleAmbientTenthSignCode j) u =
        generatedFeasibleAmbientTenthSignSpinCompact j u := by
  have hc : ∀ e : Fin 2048,
      generatedAxisGlobalIntSign (golayLabelCoefficients (generatedFeasibleAmbientTenthSignCode j)
          11) *
          generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
              (generatedFeasibleAmbientTenthSignCode j) 0
            (generatedAxisGlobalSignInputCode (generatedFeasibleAmbientTenthSignCode j) e) e) =
        generatedFeasibleAmbientTenthSignPhase j 0 e ∧
      generatedTwelfthTensorPhysicalSign (generatedFeasibleAmbientTenthSignCode j) 0 *
          generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase
              (generatedFeasibleAmbientTenthSignCode j) e 0) =
        generatedFeasibleAmbientTenthSignPhase j 1 e := by
    intro e
    fin_cases j
    · exact generatedFeasibleAmbientTenth_sign_cache_check00 e
    · exact generatedFeasibleAmbientTenth_sign_cache_check01 e
    · exact generatedFeasibleAmbientTenth_sign_cache_check02 e
  funext k
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode (generatedFeasibleAmbientTenthSignCode j) e
  unfold generatedTwelfthTensorSignSpinInteger generatedFeasibleAmbientTenthSignSpinCompact
  linear_combination
    generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
      (u (generatedAxisGlobalTensorLowLabel d) - u (generatedAxisGlobalTensorHighLabel d)) *
        (hc e).1 +
    (u (generatedAxisGlobalTensorLowLabel e) + u (generatedAxisGlobalTensorHighLabel e)) * (hc e).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
