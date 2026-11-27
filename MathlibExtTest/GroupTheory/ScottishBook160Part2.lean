/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ScottishBook160Part2
import Mathlib.Topology.Connected.PathConnected

open MathlibExt.GroupTheory.ScottishBook160Part2Wanted

-- The refutation also rules out paths with the usual unit-interval domain.
example : ¬ ∀ (G : Type 1) [MetricSpace G] [Group G] [IsTopologicalGroup G],
    IsHausdorffConnected G → ∀ x y : G, Joined x y := by
  intro h
  apply scottishBook160Part2_refuted.{1}
  intro G _ _ _ hG x y
  obtain ⟨p⟩ := h G hG x y
  exact ⟨p.extend, p.continuous_extend, p.extend_zero, p.extend_one⟩

-- The closed-set definition also covers the empty space.
example {G : Type*} [TopologicalSpace G] [IsEmpty G] : IsHausdorffConnected G := by
  rintro ⟨_, _, _, _, ⟨x, _⟩, _⟩
  exact isEmptyElim x
