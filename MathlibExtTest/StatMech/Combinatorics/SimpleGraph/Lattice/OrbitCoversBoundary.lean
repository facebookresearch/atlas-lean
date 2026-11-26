/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitCoversBoundary

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitCoversBoundary`

* `ocb_leftFence_data` at the unit cell and the domino.
* `ocb_windingWitness_of_leftFence_on_orbit` is instantiated at the unit cell: the left fence dart
  `leftDart (0, 0)` is the third dart of the orbit of `ucBase`.
* Not covered: `ocb_starHull_windingWitness_of_interfaceConnected` (needs `InterfaceConnected` of a
  star hull and a reachability hypothesis; Stage B notes both fail for some sets).
-/

@[expose] public section

open StatMech.Lattice

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitCoversBoundary

/-- The face loop of the unit cell is a cycle. -/
theorem unitCell_loop_isCycle : (mpl_orbitLoop unitCell ucBase).IsCycle :=
  mpl_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    shw_unitCell_faceInj

example : ∃ z₀ ∈ unitCell, IsBoundaryDart unitCell (leftDart z₀) ∧
    (leftDart z₀).dir = ![-1, 0] ∧ (leftDart z₀).tail 0 = z₀ 0 ∧ (∀ w ∈ unitCell, z₀ 0 ≤ w 0) :=
  ocb_leftFence_data unitCell unitCell_finite (Set.singleton_nonempty _)

example : ∃ z₀ ∈ domino, IsBoundaryDart domino (leftDart z₀) ∧
    (leftDart z₀).dir = ![-1, 0] ∧ (leftDart z₀).tail 0 = z₀ 0 ∧ (∀ w ∈ domino, z₀ 0 ≤ w 0) :=
  ocb_leftFence_data domino domino_finite ⟨_, Set.mem_insert _ _⟩

example : wei_WindingWitness unitCell ucBase :=
  ocb_windingWitness_of_leftFence_on_orbit unitCell unitCell_finite ucBase ![0, 0] 0 rfl
    (by intro w hw; rw [Set.mem_singleton_iff.mp hw]; rfl) unitCell_loop_isCycle
    ⟨2, iterate_ucDart_2⟩

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.OrbitCoversBoundary
