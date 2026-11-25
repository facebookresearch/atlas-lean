/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from `fairinternal/formal-math/MathlibExtTest/GroupTheory/Permutation/CameronBetweenness.lean`
at commit `5edfb3b6f668f04b907ff6ca3a98cb0ce1c2eb64`.
Original source SHA-256: ea25077400b4e1bdc621bc050a6dce27be7bb4ab15d56dcd2828d125fafebeaa
-/

module

public import MathlibExt.GroupTheory.Permutation.Betweenness
public import MathlibExt.GroupTheory.Permutation.HighlyHomogeneous
public import MathlibExt.GroupTheory.Permutation.PointwiseTopology

@[expose] public section

/-!
# Tests for the Cameron betweenness permutation APIs

Compile-time checks for `betweennessAutSubgroup`, `IsHighlyHomogeneous`,
and `Equiv.Perm.pointwiseTopology`.
-/

namespace CameronBetweennessTest

/-- The identity permutation preserves betweenness. -/
example {α : Type*} [LinearOrder α] :
    (1 : Equiv.Perm α) ∈ MetaMathlibExt.betweennessAutSubgroup α :=
  (MetaMathlibExt.betweennessAutSubgroup α).one_mem

/-- High homogeneity supplies pretransitivity on `k`-element subsets. -/
example {α : Type*} [DecidableEq α] {G : Subgroup (Equiv.Perm α)}
    (h : MetaMathlibExt.IsHighlyHomogeneous G) (k : ℕ) :
    MulAction.IsPretransitive G ↑(Set.powersetCard α k) :=
  h k

/-- The pointwise topology elaborates as a topology on permutations. -/
noncomputable example (α : Type*) : TopologicalSpace (Equiv.Perm α) :=
  Equiv.Perm.pointwiseTopology (α := α)

end CameronBetweennessTest
