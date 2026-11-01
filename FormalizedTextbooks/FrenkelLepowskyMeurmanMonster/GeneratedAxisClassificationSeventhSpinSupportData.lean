/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpinOrbitBound

/-! Three genuine fixing modulations describe the exact rank-nine spin support carrier. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Three independent actual pure-modulation masks fixing the original middle state. -/
def generatedSeventhSpinSupportModulation : Fin 3 → Fin 4096 := ![1504, 3079, 912]

/-- The exact three homogeneous binary support equations. -/
def generatedSeventhSpinSupportMatrix : Matrix (Fin 3) (Fin 12) (ZMod 2) :=
  fun j i => golayLabelCoefficients (generatedSeventhSpinSupportModulation j) i

/-- A literal complement to the nine certified translation columns. -/
def generatedSeventhSpinSupportComplement : Matrix (Fin 12) (Fin 3) (ZMod 2) :=
  fun i j => golayLabelCoefficients (![3072, 2048, 512] j) i

/-- The exact translation projection and modulation complement sum to the identity. -/
theorem generatedSeventh_spin_support_projection_certificate :
    generatedSeventhSpinPauliTranslationMatrix * generatedSeventhSpinPauliLeftInverse +
      generatedSeventhSpinSupportComplement * generatedSeventhSpinSupportMatrix = 1 := by
  decide +kernel

/-- Each original translation column satisfies all three support equations. -/
theorem generatedSeventh_spin_support_translation_certificate :
    generatedSeventhSpinSupportMatrix * generatedSeventhSpinPauliTranslationMatrix = 0 := by
  decide +kernel

/-- Products of the actual twelve fixing Pauli elements giving the pure support equations. -/
def generatedSeventhSpinSupportPauliProduct (j : Fin 3) : Q :=
  (List.ofFn (fun k : Fin 12 =>
    (generatedSeventhSpinPauliCache k 7) ^
      (if (![1360, 1056, 672] j : Nat).testBit k.val then 1 else 0))).prod

/-- Each support operator is the original full Pauli product with central bit zero. -/
theorem generatedSeventh_spin_support_pauli_certificate (j : Fin 3) :
    generatedSeventhSpinSupportPauliProduct j =
      cocodeQ (golayLabelCoefficients (generatedSeventhSpinSupportModulation j)) := by
  fin_cases j <;> apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

/-- All three actual pure modulations genuinely fix the actual middle spin state. -/
theorem generatedSeventh_spin_support_modulation_fixed (j : Fin 3) :
    spinRepresentation
      (cocodeQ (golayLabelCoefficients (generatedSeventhSpinSupportModulation j)))
      generatedSeventhSpinState = generatedSeventhSpinState := by
  rw [← generatedSeventh_spin_support_pauli_certificate]
  change generatedSeventhSpinSupportPauliProduct j ∈ generatedSeventhSpinStateStabilizer
  apply generatedSeventhSpinStateStabilizer.list_prod_mem
  intro q hq
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hq
  apply generatedSeventhSpinStateStabilizer.pow_mem
  exact generatedSeventh_spin_pauli_final_fixed k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
