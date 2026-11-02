/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.RayAlternation
public import Mathlib

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.RayAlternation`

* `ral_oddRay_iff_oddCross_leftRegion` for the trivial closed walk at the origin and the trivial
  path (both parities are even).
* `ral_inRegion_rayCount_odd` and `ral_tailOdd_of_bdEdgeMatch` are not instantiated with a
  nonempty inside: that needs an explicit nontrivial loop with a computed `pww_BdEdgeMatch`.
-/

@[expose] public section

open StatMech StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RayAlternation

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

example : (¬ Even (jec_rayCount (fun _ => 0) nilLoop)) ↔
    (¬ Even (crossCount (jec_leftRegion nilLoop) (SimpleGraph.Walk.nil :
      (hypercubicLattice 2).Walk (fun _ => 0) (fun _ => 0)))) :=
  ral_oddRay_iff_oddCross_leftRegion nilLoop (fun p hp => by
    simp only [nilLoop, SimpleGraph.Walk.support_nil, List.mem_singleton] at hp
    rw [hp]) _

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.RayAlternation
