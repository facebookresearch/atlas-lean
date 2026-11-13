/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.SpinWeightedRecurrence









namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

theorem ons_KWmatWeightedPhase_zero
    (L : ℕ) (omega u v : ℂ) :
    ons_KWmatWeightedPhase L (fun _ => 0) omega u v = 0 := by
  ext d2 d1
  simp [ons_KWmatWeightedPhase, ons_KWmatWeighted]

theorem ons_weightedSpinCharacterSum_zero
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) :
    ons_weightedSpinCharacterSum L (fun _ => 0) a b = 1 := by
  classical
  unfold ons_weightedSpinCharacterSum
  rw [Finset.sum_eq_single ∅]
  · simp [ons_spinCharacter, ons_evenHomology]
  · intro F hF hne
    have hnonempty : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨edge, hedge⟩ := hnonempty
    rw [Finset.prod_eq_zero hedge]
    rw [mul_zero]
    rfl
  · intro hempty
    exfalso
    apply hempty
    simp only [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset,
      Finset.empty_subset, true_and]
    exact isEvenSubgraph_empty

theorem ons_weightedRoot_zero
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) :
    ons_detWalkRoot (ons_KWmatWeightedPhase L (fun _ => 0) ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) =
      ons_weightedSpinCharacterSum L (fun _ => 0) a b := by
  rw [ons_KWmatWeightedPhase_zero, ons_detWalkRoot_zero,
    ons_weightedSpinCharacterSum_zero]

end StatMech.Onsager
