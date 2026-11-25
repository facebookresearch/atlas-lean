/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RepresentationTheory.CoinducedFiniteRank
public import Mathlib.Algebra.Field.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RepresentationTheory.Coinduced

@[expose] public section

namespace MathlibExtTest.RepresentationTheory.CoinducedFiniteRank

open CategoryTheory

universe u v w

/-- Consumer with the original binders: field, group, subgroup, and
representation all in a single universe. -/
theorem exactSource {k G : Type u} [Field k] [Group G] (S : Subgroup G)
    [S.FiniteIndex] (N : Rep.{u} k S) [FiniteDimensional k N] :
    FiniteDimensional k (Rep.coind S.subtype N) ∧
      Module.finrank k (Rep.coind S.subtype N) =
        S.index * Module.finrank k N :=
  Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul S N

/-- Higher-universe consumer: the field, the group, and the representation
carrier may live in three distinct universes. -/
example {k : Type u} {G : Type v} [Field k] [Group G] (S : Subgroup G)
    [S.FiniteIndex] (N : Rep.{w} k S) [FiniteDimensional k N] :
    FiniteDimensional k (Rep.coind S.subtype N) ∧
      Module.finrank k (Rep.coind S.subtype N) =
        S.index * Module.finrank k N :=
  Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul S N

/-- Boundary at the whole group: the index is `1`, so coinduction does not
change the dimension. -/
example {k : Type u} {G : Type v} [Field k] [Group G]
    (N : Rep.{w} k (⊤ : Subgroup G)) [FiniteDimensional k N] :
    Module.finrank k (Rep.coind (⊤ : Subgroup G).subtype N) =
      Module.finrank k N := by
  have h := (Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul
    (⊤ : Subgroup G) N).2
  rwa [Subgroup.index_top, one_mul] at h

/-- Boundary at the trivial subgroup of a finite group: the index is the
order of the group, so the dimension is multiplied by that order; the
index factor cannot in general be omitted. -/
example {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
    (N : Rep.{w} k (⊥ : Subgroup G)) [FiniteDimensional k N] :
    Module.finrank k (Rep.coind (⊥ : Subgroup G).subtype N) =
      Nat.card G * Module.finrank k N := by
  have h := (Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul
    (⊥ : Subgroup G) N).2
  rwa [Subgroup.index_bot] at h

end MathlibExtTest.RepresentationTheory.CoinducedFiniteRank
