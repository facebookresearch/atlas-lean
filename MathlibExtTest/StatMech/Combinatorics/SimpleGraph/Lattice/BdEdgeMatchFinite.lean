/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchFinite
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchFinite`

* `bemc_bdEdgeMatch_iff_leftRegion_eq` and `bemc_compl_leftRegion_infinite` for the trivial
  closed walk at the origin (inside region empty): the empty set has the boundary edges of its
  inside, and the outside is infinite.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchFinite

/-- The trivial closed walk at the origin. -/
def nilLoop : (hypercubicLattice 2).Walk (fun _ => 0) (fun _ => 0) := .nil

theorem nilLoop_supp : ∀ p ∈ nilLoop.support, p ∈ box 2 0 := by
  intro p hp
  simp only [nilLoop, SimpleGraph.Walk.support_nil, List.mem_singleton] at hp
  subst hp
  intro i; simp

theorem leftRegion_nil : jec_leftRegion nilLoop = ∅ := by
  ext z
  simp [jec_rayCount, nilLoop]

example : pww_BdEdgeMatch ∅ nilLoop :=
  (bemc_bdEdgeMatch_iff_leftRegion_eq nilLoop 0 nilLoop_supp Set.finite_empty).mpr
    leftRegion_nil.symm

example : (jec_leftRegion nilLoop)ᶜ.Infinite := bemc_compl_leftRegion_infinite nilLoop 0 nilLoop_supp

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchFinite
