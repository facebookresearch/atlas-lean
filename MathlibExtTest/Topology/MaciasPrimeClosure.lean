/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.MaciasPrimeClosure

open MathlibExt.Topology.MaciasCoprimeTopologyWanted

/-- The closure of the singleton 2 contains the composite point 6. -/
example : (6 : ℕ+) ∈ @closure ℕ+ maciasTopology {2} := by
  rw [closure_singleton_prime_eq_multiples 2 (by decide)]
  decide

/-- The unit lies outside every prime singleton's closure. -/
example (p : ℕ+) (hp : Nat.Prime (p : ℕ)) : (1 : ℕ+) ∉ @closure ℕ+ maciasTopology {p} := by
  rw [closure_singleton_prime_eq_multiples p hp]
  exact hp.not_dvd_one
