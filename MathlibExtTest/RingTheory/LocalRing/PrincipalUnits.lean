/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.PrincipalUnits

@[expose] public section

open IsLocalRing

universe u

-- `@exactSource` consumer: the exemplar theorem with its original binders.
example {R : Type*} [CommRing R] [IsLocalRing R]
    {k : ℕ} {u v : Rˣ} (hu : u ∈ principalUnits R k)
    (hv : v ∈ principalUnits R k) :
    ((u * v : Rˣ) : R) - 1 - (((u : R) - 1) + ((v : R) - 1)) ∈
      maximalIdeal R ^ (2 * k) :=
  IsLocalRing.coe_mul_sub_one_sub_mem_maximalIdeal_pow hu hv

-- Higher-universe consumer: the same statement over `Type u`.
example {R : Type u} [CommRing R] [IsLocalRing R]
    {k : ℕ} {u v : Rˣ} (hu : u ∈ principalUnits R k)
    (hv : v ∈ principalUnits R k) :
    ((u * v : Rˣ) : R) - 1 - (((u : R) - 1) + ((v : R) - 1)) ∈
      maximalIdeal R ^ (2 * k) :=
  IsLocalRing.coe_mul_sub_one_sub_mem_maximalIdeal_pow hu hv

-- Unfolding characterization: membership is `u - 1 ∈ 𝔪 ^ k` by definition,
-- and level `0` is the whole unit group (a nontrivial instance at level 0).
example {R : Type*} [CommRing R] [IsLocalRing R] {k : ℕ} {u : Rˣ} :
    u ∈ principalUnits R k ↔ (u : R) - 1 ∈ maximalIdeal R ^ k :=
  IsLocalRing.mem_principalUnits_iff

example {R : Type*} [CommRing R] [IsLocalRing R] :
    principalUnits R 0 = ⊤ :=
  IsLocalRing.principalUnits_zero

-- Representatives: every `x ∈ 𝔪 ^ k` with `k ≥ 1` is `u - 1` for a level-`k`
-- principal unit; at level `1` the filtration is the residue kernel, whose
-- index counts the units of the residue field.
example {R : Type*} [CommRing R] [IsLocalRing R]
    {k : ℕ} (hk : 1 ≤ k) {x : R} (hx : x ∈ maximalIdeal R ^ k) :
    ∃ u ∈ principalUnits R k, (u : R) - 1 = x :=
  IsLocalRing.exists_mem_principalUnits_coe_sub_one_eq hk hx

example {R : Type*} [CommRing R] [IsLocalRing R] :
    (principalUnits R 1).index = Nat.card (ResidueField R)ˣ :=
  IsLocalRing.index_principalUnits_one
