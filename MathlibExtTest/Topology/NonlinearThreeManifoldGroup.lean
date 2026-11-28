/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.NonlinearThreeManifoldGroup
import Mathlib.Analysis.Normed.Module.Connected

/-! # Tests for `MathlibExt.Topology.NonlinearThreeManifoldGroup` -/

namespace MathlibExtTest.NonlinearThreeManifoldGroup

open MathlibExt.Topology.NonlinearThreeManifoldGroupWanted.Topology

-- Thurston's question (Kirby's Problem 3.33) has a negative answer over `ℝ`: not every closed
-- 3-manifold group has a faithful representation in `GL(4, ℝ)`.
example : ¬ ∀ (M : Closed3Manifold) (x : M.carrier),
    ∃ f : FundamentalGroup M.carrier x →* GL (Fin 4) ℝ, Function.Injective f := by
  intro h
  obtain ⟨M, x, hM⟩ := nonlinear_three_manifold_group
  obtain ⟨f, hf⟩ := h M x
  exact hM f hf

-- The witness is not simply connected: if its fundamental group were trivial, the trivial
-- homomorphism to `GL(4, ℝ)` would be injective.
example : ∃ (M : Closed3Manifold) (x : M.carrier), Nontrivial (FundamentalGroup M.carrier x) := by
  obtain ⟨M, x, hM⟩ := nonlinear_three_manifold_group
  refine ⟨M, x, ?_⟩
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hM 1 fun a b _ => Subsingleton.elim a b

-- The round 3-sphere is a closed 3-manifold.
noncomputable example : Closed3Manifold :=
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num
  have : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere hrank 0 zero_le_one)
  have : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  ⟨Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1⟩

-- A closed 3-manifold carries the bundled instances, and is locally compact because it is
-- modelled on `ℝ³`.
example (M : Closed3Manifold) : CompactSpace M.carrier ∧ ConnectedSpace M.carrier ∧
    LocallyCompactSpace M.carrier :=
  ⟨inferInstance, inferInstance,
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M.carrier⟩

end MathlibExtTest.NonlinearThreeManifoldGroup
