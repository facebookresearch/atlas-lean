/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Topology.Algebra.OpenSubgroup
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

-- Extract an infinite profinite CN-group with a finite nonsoluble quotient.
example : ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
    (_ : CompactSpace G) (_ : T2Space G) (_ : TotallyDisconnectedSpace G), Infinite G ∧
    (∀ g : G, g ≠ 1 → IsPronilpotent (Subgroup.centralizer {g})) ∧
    ∃ (N : Subgroup G) (_ : N.Normal), IsOpen (N : Set G) ∧
      Finite (G ⧸ N) ∧ ¬ Group.IsSolvable (G ⧸ N) := by
  obtain ⟨G, grp, top, tg, cpt, t2, td, hinf, _, hcn, hns⟩ :=
    existsFGInfiniteProfiniteCNGroupNotProsoluble_holds
  refine ⟨G, grp, top, tg, cpt, t2, td, hinf, hcn, ?_⟩
  by_contra h
  apply hns
  intro N _ hopen
  by_contra hsol
  exact h ⟨N, ‹N.Normal›, hopen, Subgroup.quotient_finite_of_isOpen N hopen, hsol⟩
