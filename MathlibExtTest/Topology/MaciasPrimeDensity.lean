/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.PrimeFin
import MathlibExt.Topology.MaciasPrimeDensity

open MathlibExt.Topology.MaciasCoprimeTopologyWanted

/-- The unit is a nonprime point in the closure of the primes. -/
example : (1 : ℕ+) ∈ @closure ℕ+ maciasTopology primeSet ∧ (1 : ℕ+) ∉ primeSet :=
  ⟨infinite_primes_iff_dense_primeSet.mp Nat.infinite_setOfPred_prime 1, Nat.not_prime_one⟩

/-- The density transfer and subspace result give ambient density without prime infinitude. -/
example : @Dense ℕ+ maciasTopology primeSet :=
  dense_primeSet_of_dense_primeSet₁ dense_primeSet₁

/-- A composite point lies in the closure of the primes in the space without 1. -/
example : (⟨⟨6, by decide⟩, by decide⟩ : {n : ℕ+ // (n : ℕ) ≠ 1}) ∈
    @closure _ maciasTopology₁ primeSet₁ :=
  dense_primeSet₁ _
