/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MaciasArithmeticProgressions

open MathlibExt.Topology.MaciasCoprimeTopologyWanted

/-- The initial term 5 is outside the generator indexed by 70, so a later term must hit it. -/
example : ∃ k : ℕ, 0 < k ∧ Nat.Coprime 70 (6 * k + 5) := by
  let := maciasTopology
  have hd := MetaMathlibExt.dense_maciasTopology_arithmeticProgression 6 5 (by decide)
  have ho : IsOpen (coprimeSet 70) := TopologicalSpace.isOpen_generateFrom_of_mem
    (show coprimeSet 70 ∈ maciasBasis from ⟨70, rfl⟩)
  obtain ⟨m, hm, k, hk⟩ := hd.inter_open_nonempty _ ho ⟨1, Nat.coprime_one_right 70⟩
  change Nat.Coprime 70 (m : ℕ) at hm
  rw [hk] at hm
  cases k with
  | zero => exact absurd hm (by decide)
  | succ k => exact ⟨k + 1, Nat.zero_lt_succ k, hm⟩
