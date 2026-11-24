/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.MaciasCoprimeTopology
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Maps.Basic
import MathlibExt.Topology.MaciasPrimeClosure

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
  rw [Set.infinite_iff_exists_gt, maciasBasis_isTopologicalBasis.dense_iff]
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

open Set _root_.Topology

/-- **Density of the primes passes from the subspace without 1.** Let $X$ be the positive
integers with Macías's coprime topology and $X_1$ the subspace of positive integers different
from $1$. If the set of prime numbers is dense in $X_1$, then it is dense in $X$.

Source: Jhixon Macías, "Another Topological Proof of the
Infinitude of Prime Numbers", Lemma 2. -/
public theorem dense_primeSet_of_dense_primeSet₁ :
    @Dense {x : ℕ+ // (x : ℕ) ≠ 1} maciasTopology₁ primeSet₁ →
      @Dense ℕ+ maciasTopology primeSet := by
  intro h
  let := maciasTopology
  let := maciasTopology₁
  let v : {x : ℕ+ // (x : ℕ) ≠ 1} → ℕ+ := Subtype.val
  have hv : Continuous v := continuous_induced_dom
  apply maciasBasis_isTopologicalBasis.dense_iff.mpr
  rintro _ ⟨n, rfl⟩ _
  let q : ℕ+ := ⟨(n : ℕ) + 1, Nat.succ_pos _⟩
  have hq : (q : ℕ) ≠ 1 := by
    change (n : ℕ) + 1 ≠ 1
    have hn := n.pos
    omega
  let q₁ : {x : ℕ+ // (x : ℕ) ≠ 1} := ⟨q, hq⟩
  have hq₁ : q₁ ∈ v ⁻¹' coprimeSet n :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hopen : IsOpen (v ⁻¹' coprimeSet n) :=
    (maciasBasis_isTopologicalBasis.isOpen ⟨n, rfl⟩).preimage hv
  obtain ⟨p, hpn, hprime⟩ := h.inter_open_nonempty _ hopen ⟨q₁, hq₁⟩
  exact ⟨v p, hpn, hprime⟩

/-- **The primes are dense in the coprime topology without 1.** The set of prime numbers is dense
in the set of positive integers different from $1$, with the subspace topology induced by
Macías's coprime topology on the positive integers.

Source: Jhixon Macías, "Another Topological Proof of the
Infinitude of Prime Numbers", Theorem 3. -/
public theorem dense_primeSet₁ :
    @Dense {x : ℕ+ // (x : ℕ) ≠ 1} maciasTopology₁ primeSet₁ := by
  let := maciasTopology
  let := maciasTopology₁
  let v : {x : ℕ+ // (x : ℕ) ≠ 1} → ℕ+ := Subtype.val
  have hv : IsInducing v := ⟨rfl⟩
  intro x
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd x.property
  let q : ℕ+ := ⟨p, hp.pos⟩
  let q₁ : {x : ℕ+ // (x : ℕ) ≠ 1} := ⟨q, hp.ne_one⟩
  have hq₁ : q₁ ∈ primeSet₁ := hp
  have hx : v x ∈ closure ({q} : Set ℕ+) := by
    rw [closure_singleton_prime_eq_multiples q hp]
    exact hpx
  change x ∈ closure primeSet₁
  rw [hv.closure_eq_preimage_closure_image]
  have hmem : q ∈ v '' primeSet₁ := ⟨q₁, hq₁, rfl⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) hx

end MathlibExt.Topology.MaciasCoprimeTopologyWanted
