/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSparse

/-! Packed integer Q action retains an arbitrary original central coefficient. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual Q lift with arbitrary translation, modulation and central coefficient. -/
def generatedNinthPauliLift (a b : Fin 4096) (c : ZMod 2) : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients a) (golayLabelCoefficients b)), ofAdd c⟩

private theorem generatedNinthUIntegerSign_add (c d : ZMod 2) :
    nortonUIntegerSign (c + d) = nortonUIntegerSign c * nortonUIntegerSign d := by
  revert c d
  decide +kernel

/-- Every actual central-phase lift acts by the corresponding signed sparse integer operator. -/
theorem generatedNinth_pauli_lift_integer (a b : Fin 4096) (c : ZMod 2)
    (v : NortonUIntegerVector) :
    nortonUIntegerQ (generatedNinthPauliLift a b c) v =
      fun n => nortonUIntegerSign c * generatedNinthPauliSparse a b v n := by
  ext n
  have hp := congrFun (generatedNinth_pauli_integer a b v) n
  change nortonUIntegerSign (spinPhase (generatedNinthPauliQ a b)
    (golayLabelCoefficients n)) *
      v (nortonUIntegerLabel (golayLabelCoefficients n +
        spinTranslation (generatedNinthPauliQ a b))) = _ at hp
  have hz : toAdd (generatedNinthPauliQ a b).coeff = (0 : ZMod 2) := rfl
  rw [spinPhase, hz, zero_add] at hp
  have ht : spinTranslation (generatedNinthPauliLift a b c) =
      spinTranslation (generatedNinthPauliQ a b) := rfl
  have hm : spinModulation (generatedNinthPauliLift a b c) =
      spinModulation (generatedNinthPauliQ a b) := rfl
  change nortonUIntegerSign (spinPhase (generatedNinthPauliLift a b c)
    (golayLabelCoefficients n)) *
      v (nortonUIntegerLabel (golayLabelCoefficients n +
        spinTranslation (generatedNinthPauliLift a b c))) = _
  rw [spinPhase, show toAdd (generatedNinthPauliLift a b c).coeff = c from rfl,
    hm, ht, generatedNinthUIntegerSign_add, mul_assoc, hp, generatedNinth_pauli_sparse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
