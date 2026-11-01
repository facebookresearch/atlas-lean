/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliSupportStructure
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthColumnInputFast

/-! Every original signed source address lies in the checked common support. This permits
source-value checks on that support and proves exact zeros at every other address. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

set_option maxHeartbeats 16000000 in
-- Check only the128 addresses of the original64 signed source rows in both spin halves.
/-- All original source addresses belong to the exact checked common support. -/
theorem generatedNinth_pauli_input_source_support : ∀ k : Fin 64, ∀ s : Fin 2,
    let n : Fin 4096 := ⟨(generatedFifthOddRootOutputData k).1.val + 2048 * s.val, by omega⟩
    (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit (n.val % 256) = true := by
  decide +kernel

/-- The literal64-term signed source input vanishes at every address outside the common support. -/
theorem generatedNinth_pauli_input_source_zero (i : Fin 24) (n : Fin 4096)
    (hn : (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit
      (n.val % 256) = false) : generatedNinthColumnInputSparse i n = 0 := by
  rw [generatedNinth_column_input_sparse_fast]
  unfold generatedNinthColumnInputFast
  apply Finset.sum_eq_zero
  intro k _
  have ha : n.val % 2048 ≠ (generatedFifthOddRootOutputData k).1.val := by
    intro h
    let s : Fin 2 := ⟨n.val / 2048, by omega⟩
    have hs := generatedNinth_pauli_input_source_support k s
    have he : (generatedFifthOddRootOutputData k).1.val + 2048 * s.val = n.val := by
      dsimp [s]
      omega
    dsimp only at hs
    have hh : (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit
        (n.val % 256) = true := by
      simpa only [he] using hs
    rw [hn] at hh
    cases hh
  simp only [ha, ite_false]

/-- Checked source values on the common support imply the original input identity everywhere. -/
theorem generatedNinth_pauli_input_actual_of_supported
    (h : ∀ b : Fin 8, ∀ m : Fin 256,
      generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩
        (generatedNinthPauliSupportLabel m) =
      generatedNinthColumnInputSparse (generatedNinthInputBasisColumn b)
        (generatedNinthPauliSupportLabel m)) (b : Fin 8) (n : Fin 4096) :
    generatedNinthPauliStateInteger ⟨128 + b.val, by omega⟩ n =
      generatedNinthColumnInputSparse (generatedNinthInputBasisColumn b) n := by
  by_cases hn : (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit
      (n.val % 256) = true
  · obtain ⟨m, rfl⟩ := generatedNinth_pauli_support_complete n hn
    exact h b m
  · have hz : (generatedNinthPauliSupportWords ⟨n.val / 256, by omega⟩).testBit
        (n.val % 256) = false := Bool.eq_false_iff.mpr hn
    rw [generatedNinth_pauli_state_zero _ _ hz, generatedNinth_pauli_input_source_zero _ _ hz]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
