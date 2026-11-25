/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Topology.HomotopyGroups

@[expose] public section

namespace MathlibExtTest.Topology.HomotopyGroups

/-- The fundamental group of the circle is infinite cyclic. -/
example : Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) :=
  MathlibExt.Topology.HomotopyGroupsWanted.Topology.pi1_circle_mulEquiv_int

/-- The first homotopy group of the circle is nontrivial, as transported along
the isomorphism with `ℤ`. -/
example : Nontrivial (HomotopyGroup.Pi 1 Circle (1 : Circle)) := by
  obtain ⟨e⟩ := MathlibExt.Topology.HomotopyGroupsWanted.Topology.pi1_circle_mulEquiv_int
  refine ⟨e.symm (Multiplicative.ofAdd 1), 1, fun h => ?_⟩
  have h2 := congrArg e h
  rw [MulEquiv.apply_symm_apply, map_one e] at h2
  have h3 : (1 : ℤ) = 0 := by simpa using congrArg Multiplicative.toAdd h2
  exact one_ne_zero h3

end MathlibExtTest.Topology.HomotopyGroups
