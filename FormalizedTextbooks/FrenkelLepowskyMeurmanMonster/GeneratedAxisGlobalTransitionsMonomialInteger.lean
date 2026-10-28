/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMonomialTensor
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsXiInteger

/-! Literal original permutation words transport complete exact integer tensor packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual signed spin pullback and physical coordinate permutation of a literal word. -/
def generatedAxisGlobalMonomialIntegerAction (w : List (Fin 2 × Bool))
    (N : Fin 4096 → Fin 24 → ℤ) (k : Fin 4096) (i : Fin 24) : ℤ :=
  let r := generatedFourthMonomialWordPull w (golayLabelCoefficients k)
  generatedAxisGlobalIntSign r.1 * N (generatedAxisGlobalSpinLabel r.2)
    (((w.map generatedFourthMonomialPermutationLetter).prod).val.symm i)

/-- Every displayed integer coefficient is exactly the literal word's actual real coefficient. -/
theorem generatedAxisGlobalMonomialIntegerAction_coefficient (w : List (Fin 2 × Bool))
    (N : Fin 4096 → Fin 24 → ℤ) (D : ℕ) (k : Fin 4096) (i : Fin 24) :
    localTensorRepresentation ((w.map generatedFourthMonomialFiberLetter).prod)
      (generatedAxisGlobalTensorIntegerPacket N D) (golayLabelCoefficients k) i =
        (generatedAxisGlobalMonomialIntegerAction w N k i : ℝ) /
          ((D : ℝ) * Real.sqrt 2) := by
  rw [generatedAxisGlobalMonomial_tensor_coordinate]
  simp only [generatedAxisGlobalTensorIntegerPacket, generatedAxisGlobalMonomialIntegerAction,
    Int.cast_mul, generatedAxisGlobalIntSign_real]
  ring

/-- Literal original words preserve the denominator and transport every physical tensor row. -/
theorem generatedAxisGlobalMonomialInteger_packet (w : List (Fin 2 × Bool))
    (N : Fin 4096 → Fin 24 → ℤ) (D : ℕ) :
    localTensorRepresentation ((w.map generatedFourthMonomialFiberLetter).prod)
      (generatedAxisGlobalTensorIntegerPacket N D) =
        generatedAxisGlobalTensorIntegerPacket (generatedAxisGlobalMonomialIntegerAction w N) D :=
  by
    funext t i
    obtain ⟨k, rfl⟩ := golayLabelCoefficients_bijective.2 t
    rw [generatedAxisGlobalTensorIntegerPacket_coefficient]
    exact generatedAxisGlobalMonomialIntegerAction_coefficient w N D k i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
