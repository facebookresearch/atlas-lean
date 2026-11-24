/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MaciasArithmeticProgressions
import Mathlib.Data.Nat.PrimeFin

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

/-- Even the smallest prime alone does not form a dense set. -/
example : ¬ @Dense ℕ+ maciasTopology {2} := by
  have h := MetaMathlibExt.infinite_iff_dense_maciasTopology_of_subset_primes {2}
    (Set.singleton_nonempty _) (by rintro p rfl; exact Nat.prime_two)
  exact fun hd ↦ (h.mpr hd) (Set.finite_singleton _)

/-- Deleting the prime 2 leaves a dense proper subset of the primes. -/
example : @Dense ℕ+ maciasTopology (primeSet \ {2}) := by
  have h : primeSet.Infinite := by
    apply Nat.infinite_setOfPred_prime.preimage (f := PNat.val)
    intro p hp
    exact ⟨⟨p, hp.pos⟩, rfl⟩
  have hInf := h.sdiff (Set.finite_singleton (2 : ℕ+))
  exact (MetaMathlibExt.infinite_iff_dense_maciasTopology_of_subset_primes _ hInf.nonempty
    fun _ hp ↦ hp.1).mp hInf
