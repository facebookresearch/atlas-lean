/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ChabautySpaceDisconnectedRealSubgroup

/-! # Regression tests for the negative answer to Kourovka Notebook Problem 8.61 -/

open MathlibExt.Topology.ChabautySpaceConnectedRealSubgroupKourovka8Problem61Wanted

-- Check the public refutation against the quantified statement, independently of the witness.
example : ¬ (∀ (G : Type) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G], (∃ φ : Multiplicative ℝ →* G, Topology.IsEmbedding φ) →
    @ConnectedSpace _ (chabautyTopology G)) :=
  chabautySpaceConnectedOfRealSubgroup_refuted

-- Both kinds of subbasic open remain available through the public topology definition.
example {G : Type} [Group G] [TopologicalSpace G] {U K : Set G} (hU : IsOpen U) (hK : IsCompact K) :
    letI := chabautyTopology G
    IsOpen {H : {H : Subgroup G // IsClosed (H : Set G)} | ((H.1 : Set G) ∩ U).Nonempty} ∧
      IsOpen {H : {H : Subgroup G // IsClosed (H : Set G)} | Disjoint (H.1 : Set G) K} :=
  ⟨TopologicalSpace.isOpen_generateFrom_of_mem (Or.inr ⟨U, hU, rfl⟩),
    TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl ⟨K, hK, rfl⟩)⟩
