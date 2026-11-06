/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddSpinOrbit
public import Mathlib.GroupTheory.GroupAction.Quotient

/-! The actual Q stabilizer of the distinguished Hadamard spin state. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Pauli vector action, preferred to generic pointwise scalar actions. -/
noncomputable instance (priority := 2000) generatedOddSpinActualSmul : SMul Q SpinSpace where
  smul q v := spinRepresentation q v

/-- The original faithful spin representation supplies its genuine group action. -/
noncomputable instance generatedOddSpinActualAction : MulAction Q SpinSpace where
  smul q v := spinRepresentation q v
  one_smul v := by
    change spinRepresentation 1 v = v
    rw [spinRepresentation.map_one]
    rfl
  mul_smul q k v := by
    change spinRepresentation (q * k) v = spinRepresentation q (spinRepresentation k v)
    rw [spinRepresentation.map_mul]
    rfl

/-- The genuine stabilizer of the distinguished two-point spin state. -/
noncomputable def generatedOddSpinStateStabilizer : Subgroup Q :=
  MulAction.stabilizer Q (generatedOddSpinState 0 1 0)

/-- Exactly 2^12 actual extraspecial elements fix the distinguished spin state. -/
theorem generatedOddSpinStateStabilizer_card :
    Nat.card generatedOddSpinStateStabilizer = 2 ^ 12 := by
  have he := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup Q (generatedOddSpinState 0 1 0))
  rw [Nat.card_prod] at he
  change Nat.card (Set.range (fun q : Q => spinOperator q (generatedOddSpinState 0 1 0))) *
    Nat.card generatedOddSpinStateStabilizer = Nat.card Q at he
  rw [generatedOddSpinOrbit_card, q_card] at he
  norm_num only [Nat.reducePow] at he ⊢
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
