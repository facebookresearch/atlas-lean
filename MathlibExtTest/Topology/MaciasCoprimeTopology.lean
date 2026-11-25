/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MaciasCoprimeTopology

open MathlibExt.Topology.MaciasCoprimeTopologyWanted

/-- The generator indexed by 1 contains every positive integer. -/
example : coprimeSet 1 = Set.univ :=
  Set.eq_univ_of_forall fun m ↦ Nat.coprime_one_left (m : ℕ)

/-- Each coprime generator restricts to an open set in the subspace without 1. -/
example (n : ℕ+) : maciasTopology₁.IsOpen (Subtype.val ⁻¹' coprimeSet n) := by
  let := maciasTopology
  exact isOpen_induced_iff.mpr ⟨coprimeSet n, TopologicalSpace.isOpen_generateFrom_of_mem
    (show coprimeSet n ∈ maciasBasis from ⟨n, rfl⟩), rfl⟩

/-- Restricting the set of primes to the subspace agrees with its prime predicate. -/
example : primeSet₁ = Subtype.val ⁻¹' primeSet := rfl
