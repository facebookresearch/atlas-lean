/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportStructure

/-! Exact support transport and original packed-source zeros reduce signed operator checks to
supported values while retaining the complete4096-address operator identity. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Membership in the original checked256-address common support. -/
def generatedNinthPauliSupportContains (n : Fin 4096) : Prop :=
  (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit (n.val % 256) = true

set_option maxHeartbeats 40000000 in
-- Check the128 literal Pauli translations on only256 complete support addresses.
/-- Every original Pauli translation carries the entire displayed support into itself. -/
theorem generatedNinth_pauli_translation_support : ∀ q : Fin 128, ∀ m : Fin 256,
    generatedNinthPauliSupportContains
      (generatedSixthSpinLabelXor (generatedNinthPauliSupportLabel m)
        (generatedNinthPauliWitnessLabels q 0)) := by
  unfold generatedNinthPauliSupportContains
  decide +kernel

set_option maxHeartbeats 16000000 in
-- Check original packed-source zeros at each of the4096 addresses once.
/-- The original packed integer source is exactly zero outside the common support. -/
theorem generatedNinth_pauli_packed_source_zero : ∀ n : Fin 4096,
    ¬ generatedNinthPauliSupportContains n → generatedNinthColumnSpinPacked 0 n = 0 := by
  unfold generatedNinthPauliSupportContains
  decide +kernel

/-- Two successive original twelve-bit translations cancel exactly. -/
theorem generatedNinth_pauli_label_xor_cancel (n a : Fin 4096) :
    generatedSixthSpinLabelXor (generatedSixthSpinLabelXor n a) a = n := by
  apply Fin.ext
  exact Nat.xor_xor_cancel_right _ _

/-- Every original signed Pauli operator vanishes outside the exact common support. -/
theorem generatedNinth_pauli_operator_source_zero (q : Fin 128) (n : Fin 4096)
    (hn : ¬ generatedNinthPauliSupportContains n) :
    generatedNinthPauliSparse (generatedNinthPauliWitnessLabels q 0)
      (generatedNinthPauliWitnessLabels q 1) (generatedNinthColumnSpinPacked 0) n = 0 := by
  have hs : ¬ generatedNinthPauliSupportContains
      (generatedSixthSpinLabelXor n (generatedNinthPauliWitnessLabels q 0)) := by
    intro h
    obtain ⟨m, hm⟩ := generatedNinth_pauli_support_complete _ h
    have ht := generatedNinth_pauli_translation_support q m
    rw [hm, generatedNinth_pauli_label_xor_cancel] at ht
    exact hn ht
  have hz := generatedNinth_pauli_packed_source_zero _ hs
  simp only [generatedNinthPauliSparse, hz, ite_true]

/-- All supported-value checks and original source zeros imply the complete signed operator. -/
theorem generatedNinth_pauli_operator_actual_of_supported
    (h : ∀ q : Fin 128, ∀ m : Fin 256,
      generatedNinthPauliStateInteger ⟨q.val, by omega⟩ (generatedNinthPauliSupportLabel m) =
        generatedNinthPauliSparse (generatedNinthPauliWitnessLabels q 0)
          (generatedNinthPauliWitnessLabels q 1) (generatedNinthColumnSpinPacked 0)
          (generatedNinthPauliSupportLabel m)) (q : Fin 128) (n : Fin 4096) :
    generatedNinthPauliStateInteger ⟨q.val, by omega⟩ n =
      generatedNinthPauliSparse (generatedNinthPauliWitnessLabels q 0)
        (generatedNinthPauliWitnessLabels q 1) (generatedNinthColumnSpinPacked 0) n := by
  by_cases hn : generatedNinthPauliSupportContains n
  · obtain ⟨m, rfl⟩ := generatedNinth_pauli_support_complete n hn
    exact h q m
  · have hz : (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit
        (n.val % 256) = false := Bool.eq_false_iff.mpr hn
    rw [generatedNinth_pauli_state_zero _ _ hz, generatedNinth_pauli_operator_source_zero q n hn]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
