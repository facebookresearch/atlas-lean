/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Group.PUnit
import MathlibExt.GroupTheory.SylowMaximalSigmaSolubleSupplementKourovka19Problem87

open MathlibExt.GroupTheory.KourovkaNotebookShared

namespace MathlibExt.GroupTheory.SylowMaximalSigmaSolubleSupplementKourovka19Problem87Wanted

-- A finite group that is not σ-soluble has a maximal subgroup of a Sylow subgroup without any
-- σ-soluble supplement.
example (I : Type) (σ : I → Set ℕ) (hσ : IsPrimePartition σ) (G : Type) [Group G] [Finite G]
    (hG : ¬ IsSigmaSoluble σ G) :
    ∃ p : ℕ, p.Prime ∧ ∃ (P : Sylow p G) (V : Subgroup G), V ⋖ (P : Subgroup G) ∧
      ∀ T : Subgroup G, IsSigmaSoluble σ T → ∃ g : G, ∀ v ∈ V, ∀ t ∈ T, v * t ≠ g := by
  by_contra h
  push Not at h
  exact hG (sylowMaximalSigmaSolubleSupplement_holds I σ hσ G h)

-- In the trivial group every Sylow subgroup is trivial and has no maximal subgroup, so the
-- hypothesis holds vacuously.
example (I : Type) (σ : I → Set ℕ) (hσ : IsPrimePartition σ) : IsSigmaSoluble σ Unit :=
  sylowMaximalSigmaSolubleSupplement_holds I σ hσ Unit fun _ _ _ _ hV =>
    (hV.lt.ne (Subsingleton.elim _ _)).elim

/-- The partition `{2}, {3}, {5}, …` of the primes into singletons. -/
private abbrev singletons (p : Nat.Primes) : Set ℕ := {p.val}

private theorem isPrimePartition_singletons : IsPrimePartition singletons := by
  refine ⟨fun i => ⟨⟨i, rfl⟩, ?_⟩, ?_, fun p hp => ⟨⟨p, hp⟩, rfl⟩⟩
  · rintro p (rfl : p = i.val)
    exact i.property
  · intro i j hij
    exact Set.disjoint_singleton.mpr (fun h => hij (Subtype.ext h))

-- The classical case: if the maximal subgroups of the Sylow subgroups have supplements all of
-- whose chief factors have prime power index, then so do the chief factors of `G`.
example (G : Type) [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → ∀ (P : Sylow p G) (V : Subgroup G), V ⋖ (P : Subgroup G) →
      ∃ T : Subgroup G, IsSigmaSoluble singletons T ∧ ∀ g : G, ∃ v ∈ V, ∃ t ∈ T, v * t = g)
    (A B : Subgroup G) (hAB : IsChiefFactor A B) :
    ∃ p : Nat.Primes, ∀ q : ℕ, q.Prime → q ∣ B.relIndex A → q = p :=
  sylowMaximalSigmaSolubleSupplement_holds _ singletons isPrimePartition_singletons G h A B hAB

end MathlibExt.GroupTheory.SylowMaximalSigmaSolubleSupplementKourovka19Problem87Wanted
