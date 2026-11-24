/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.MaciasCoprimeTopology
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Bases

/-!
# Density of the primes in Macías's coprime topology

The primes are infinite if and only if they are dense. A prime larger than the index of a
basic open set belongs to it. Conversely, a prime in the basic open set indexed by `n!`
must exceed `n`.
-/

namespace MathlibExt.Topology.MaciasCoprimeTopologyWanted

/-- **Infinitude of the primes as density.** There are infinitely many prime numbers if and only
if the set of prime numbers is dense in the positive integers with Macías's coprime topology.

Source: Jhixon Macías, "Another Topological Proof of the
Infinitude of Prime Numbers", Theorem 2. -/
public theorem infinite_primes_iff_dense_primeSet :
    Set.Infinite {p : ℕ | Nat.Prime p} ↔
      @Dense ℕ+ maciasTopology primeSet := by
  let := maciasTopology
  have hInter : FiniteInter maciasBasis := by
    constructor
    · exact ⟨1, Set.eq_univ_of_forall fun m ↦ Nat.coprime_one_left (m : ℕ)⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ⟨⟨a * b, Nat.mul_pos a.pos b.pos⟩, Set.ext fun _ ↦ Nat.coprime_mul_iff_left⟩
  rw [Set.infinite_iff_exists_gt,
    (TopologicalSpace.isTopologicalBasis_of_subbasis_of_finiteInter rfl hInter).dense_iff]
  constructor
  · rintro h _ ⟨n, rfl⟩ _
    obtain ⟨p, hp, hnp⟩ := h n
    exact ⟨⟨p, hp.pos⟩, (Nat.coprime_of_lt_prime n.ne_zero hnp hp).symm, hp⟩
  · intro h n
    let k : ℕ+ := ⟨n.factorial, Nat.factorial_pos n⟩
    obtain ⟨p, hcop, hp⟩ := h _ ⟨k, rfl⟩ ⟨1, Nat.coprime_one_right k⟩
    change Nat.Coprime n.factorial (p : ℕ) at hcop
    change Nat.Prime (p : ℕ) at hp
    exact ⟨p, hp, lt_of_not_ge fun hle ↦
      hp.coprime_iff_not_dvd.mp hcop.symm (Nat.dvd_factorial hp.pos hle)⟩

end MathlibExt.Topology.MaciasCoprimeTopologyWanted
