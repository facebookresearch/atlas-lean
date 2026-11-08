/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Freivalds

/-!
# Freivalds public proof interface

These consumers import the public entry module. The combined contract binds
the repeated acceptance law and charged executor to the same matrix inputs;
zero-trial acceptance has no product-correctness assumption.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

open scoped ENNReal

namespace CSLibExtTest.Algorithms.Matrix

open Cslib.Algorithms.Lean.Matrix

private theorem repeatedContract {n k : Nat}
    (A B C : Vector (Vector (ZMod 2) n) n)
    (wrong : freivaldsMatrix A * freivaldsMatrix B ≠ freivaldsMatrix C)
    (history : Fin k → Fin n → ZMod 2) :
    freivaldsRepeatLaw k A B C true ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ ∧
      (freivaldsRepeat A B C history).time = (3 * k * n ^ 2, 3 * k * n ^ 2) :=
  ⟨freivaldsRepeatLaw_sound k A B C wrong, freivaldsRepeat_time A B C history⟩

private theorem zeroTrialsLaw {n : Nat} (A B C : Vector (Vector (ZMod 2) n) n) :
    freivaldsRepeatLaw 0 A B C true = 1 := by
  rw [freivaldsRepeatLaw_acceptance_power]
  exact pow_zero _

#check repeatedContract
#print axioms repeatedContract
#check zeroTrialsLaw
#print axioms zeroTrialsLaw

#check freivaldsTrial
#print axioms freivaldsTrial
#check freivaldsTrial_time
#print axioms freivaldsTrial_time
#check freivaldsMatrix
#print axioms freivaldsMatrix
#check freivaldsTrial_accept_iff
#print axioms freivaldsTrial_accept_iff
#check freivaldsTrial_accept_discrepancy_iff
#print axioms freivaldsTrial_accept_discrepancy_iff
#check freivaldsTrial_complete
#print axioms freivaldsTrial_complete
#check freivaldsTrial_empty
#print axioms freivaldsTrial_empty
#check freivaldsTrial_acceptanceCard_bound
#print axioms freivaldsTrial_acceptanceCard_bound
#check freivaldsTrialLaw
#print axioms freivaldsTrialLaw
#check freivaldsSeed_pointMass
#print axioms freivaldsSeed_pointMass
#check freivaldsTrialLaw_acceptance
#print axioms freivaldsTrialLaw_acceptance
#check freivaldsTrialLaw_complete
#print axioms freivaldsTrialLaw_complete
#check freivaldsTrialLaw_sound
#print axioms freivaldsTrialLaw_sound
#check freivaldsRepeat
#print axioms freivaldsRepeat
#check freivaldsRepeat_time
#print axioms freivaldsRepeat_time
#check freivaldsRepeat_accept_iff
#print axioms freivaldsRepeat_accept_iff
#check freivaldsRepeat_complete
#print axioms freivaldsRepeat_complete
#check freivaldsRepeat_zero
#print axioms freivaldsRepeat_zero
#check freivaldsRepeat_empty
#print axioms freivaldsRepeat_empty
#check freivaldsRepeatLaw
#print axioms freivaldsRepeatLaw
#check freivaldsHistory_pointMass
#print axioms freivaldsHistory_pointMass
#check freivaldsRepeat_acceptanceCard
#print axioms freivaldsRepeat_acceptanceCard
#check freivaldsRepeatLaw_acceptance_power
#print axioms freivaldsRepeatLaw_acceptance_power
#check freivaldsRepeatLaw_complete
#print axioms freivaldsRepeatLaw_complete
#check freivaldsRepeatLaw_sound
#print axioms freivaldsRepeatLaw_sound
#check freivalds_one_wrong
#print axioms freivalds_one_wrong
#check freivaldsTrial_one_accept_iff
#print axioms freivaldsTrial_one_accept_iff
#check freivaldsTrial_one_acceptanceCard
#print axioms freivaldsTrial_one_acceptanceCard
#check freivaldsTrialLaw_one_sharp
#print axioms freivaldsTrialLaw_one_sharp
#check freivaldsRepeatLaw_one_sharp
#print axioms freivaldsRepeatLaw_one_sharp

end CSLibExtTest.Algorithms.Matrix
