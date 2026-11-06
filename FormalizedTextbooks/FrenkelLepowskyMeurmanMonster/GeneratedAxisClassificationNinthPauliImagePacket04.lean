/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliImageData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSelectedPhase

/-! Full original Q-image certificate for sixteen reconstruction witnesses in block4. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Bind only sixteen actual full Q images, retaining both binary coordinates and central phases.
/-- Every reconstruction witness in this block has its checked original full-phase Q image. -/
theorem generatedNinth_pauli_image_packet_04 (v : Fin 16) :
    let q : Fin 128 := ⟨64 + v.val, by omega⟩
    generatedNinthQImage (generatedNinthPauliQ (generatedNinthPauliWitnessLabels q 0)
      (generatedNinthPauliWitnessLabels q 1)) = generatedNinthPauliImage q := by
  dsimp only
  rw [generatedNinth_QCoordinateEvaluation_eq]
  have hb : ∀ v : Fin 16,
      let q : Fin 128 := ⟨64 + v.val, by omega⟩
      (fun j : Fin 24 => toAdd (generatedNinthQCoordinateEvaluation
        (generatedNinthPauliQ (generatedNinthPauliWitnessLabels q 0)
          (generatedNinthPauliWitnessLabels q 1))).base j) =
        (fun j : Fin 24 => toAdd (generatedNinthPauliImage q).base j) := by
    decide +kernel
  have hc : ∀ v : Fin 16,
      let q : Fin 128 := ⟨64 + v.val, by omega⟩
      generatedNinthSelectedPhase
        (generatedNinthPauliQ (generatedNinthPauliWitnessLabels q 0)
          (generatedNinthPauliWitnessLabels q 1)) =
        toAdd (generatedNinthPauliImage q).coeff := by
    decide +kernel
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact hb v
  · apply toAdd.injective
    rw [← generatedNinth_QCoordinateEvaluation_eq, generatedNinth_selected_phase]
    exact hc v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
