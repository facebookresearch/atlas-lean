/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ProfiniteCNGroupNotProsolubleKourovka20Problem90

open MathlibExt.GroupTheory.ProfiniteCNGroupNotProsolubleKourovka20Problem90Wanted

-- The trivial subgroup has trivial image in every open normal quotient.
example (G : Type) [Group G] [TopologicalSpace G] : IsPronilpotent (⊥ : Subgroup G) := by
  intro N _ _
  rw [Subgroup.map_bot]
  infer_instance

-- For a discrete group the quotient by the trivial subgroup detects nilpotence.
example (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    IsPronilpotent (⊤ : Subgroup G) ↔ Group.IsNilpotent G := by
  constructor
  · intro h
    have hbot := h ⊥ (isOpen_discrete _)
    change Group.IsNilpotent ((⊤ : Subgroup G).map (QuotientGroup.mk' ⊥)) at hbot
    rw [← MonoidHom.range_eq_map, QuotientGroup.range_mk', Group.isNilpotent_top] at hbot
    exact (Group.isNilpotent_congr QuotientGroup.quotientBot).mp hbot
  · intro h N _ _
    infer_instance
