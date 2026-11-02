/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitDartsOrbit
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitDartsOrbit`

* `exitDart_sameOrbit_of_far`, `exitDart_headSameComponent_of_far` and
  `exitDart_sameOrbit_iff_headSameComponent` for the all-closed configuration, whose origin cluster
  is `{0}` (interface-connected by `ifc_interfaceConnected`), with `R = 0`: the exit-dart heads
  `(k + 1, 0)` and `(-(k + 1), 0)` lie outside `box 2 0`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExitDartsOrbit

/-- The all-closed configuration. -/
def ω₀ : ConfigSpace (Sym2 (Site 2)) := fun _ => false

theorem cluster_ω₀ : cluster 2 ω₀ (Percolation.origin 2) = {Percolation.origin 2} := by
  have hbot : openSubgraph 2 ω₀ = ⊥ := by
    ext x y; simp [openSubgraph, IsOpenEdge, ω₀]
  ext y
  simp only [mem_cluster, Connected, hbot, SimpleGraph.reachable_bot, Set.mem_singleton_iff]
  exact eq_comm

theorem hfin : (cluster 2 ω₀ (Percolation.origin 2)).Finite := by
  rw [cluster_ω₀]; exact Set.finite_singleton _

theorem hInt : InterfaceConnected (cluster 2 ω₀ (Percolation.origin 2)) := by
  rw [cluster_ω₀]; exact ifc_interfaceConnected _

theorem hR : cluster 2 ω₀ (Percolation.origin 2) ⊆ box 2 0 := by
  rw [cluster_ω₀]; intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; intro i; simp [Percolation.origin]

theorem hr : (exitDart (ω := ω₀) hfin).head ∈ exterior 2 0 :=
  ⟨0, by simp [exitDart_head]; omega⟩

theorem hl : (leftExitDart (ω := ω₀) hfin).head ∈ exterior 2 0 :=
  ⟨0, by simp [leftExitDart_head]; omega⟩

example : exitDart_headSameComponent ω₀ hfin := exitDart_headSameComponent_of_far hfin 0 hR hr hl

example : ExitDartsSameOrbit ω₀ hfin := exitDart_sameOrbit_of_far hfin hInt 0 hR hr hl

example : ExitDartsSameOrbit ω₀ hfin :=
  (exitDart_sameOrbit_iff_headSameComponent hfin hInt).mpr
    (exitDart_headSameComponent_of_far hfin 0 hR hr hl)

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.ExitDartsOrbit
