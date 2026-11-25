/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.MaciasCoprimeTopology
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Topology.Inseparable

/-!
# Closure of a prime in Macías's coprime topology

The coprime set indexed by a prime separates it from each nonmultiple. Every coprime set
containing a multiple of the prime also contains the prime.
-/

namespace MathlibExt.Topology.MaciasCoprimeTopologyWanted

/-- **Closure of a prime in Macías's coprime topology.** If $p$ is a prime number, then the
closure of $\{p\}$ in the positive integers with Macías's coprime topology is the set of
positive integers divisible by $p$.

Source: Jhixon Macías, "Another Topological Proof of the
Infinitude of Prime Numbers", Lemma 1. -/
public theorem closure_singleton_prime_eq_multiples
    (p : ℕ+) (hp : Nat.Prime (p : ℕ)) :
    @closure ℕ+ maciasTopology {p} = {x : ℕ+ | (p : ℕ) ∣ (x : ℕ)} := by
  let := maciasTopology
  ext x
  rw [← specializes_iff_mem_closure, specializes_iff_pure, ← Filter.tendsto_id',
    maciasTopology, TopologicalSpace.tendsto_nhds_generateFrom_iff, maciasBasis,
    Set.forall_mem_range]
  change (∀ n : ℕ+, Nat.Coprime n x → Nat.Coprime n p) ↔ (p : ℕ) ∣ (x : ℕ)
  constructor
  · intro h
    by_contra hpx
    have hpp := h p (hp.coprime_iff_not_dvd.mpr hpx)
    exact hp.coprime_iff_not_dvd.mp hpp dvd_rfl
  · exact fun hpx n hnx ↦ hnx.of_dvd_right hpx

end MathlibExt.Topology.MaciasCoprimeTopologyWanted
