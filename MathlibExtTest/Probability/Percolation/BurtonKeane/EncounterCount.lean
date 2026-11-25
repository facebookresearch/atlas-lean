/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Percolation.BurtonKeane.EncounterCount
import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarTopology

/-! # The one-dimensional lattice has no encounter points -/

open StatMech StatMech.Lattice
open MathlibExt.Probability.Percolation.BurtonKeaneWanted

-- Three distinct open neighbors are impossible, even at density one.
example (ω : ConfigSpace (Sym2 (Site 1))) (x : Site 1) : ¬ IsEncounterPoint 1 ω x := by
  classical
  rintro ⟨a, b, c, ⟨hab, hac, hbc⟩, ⟨ha, hb, hc⟩, _⟩
  let G := hypercubicLattice 1
  have hsub : ({a, b, c} : Finset _) ⊆ G.neighborFinset x := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr ha.1
    · exact (G.mem_neighborFinset _ _).mpr hb.1
    · exact (G.mem_neighborFinset _ _).mpr hc.1
  have hcard := Finset.card_le_card hsub
  simp [G, degree_eq, hab, hac, hbc] at hcard
