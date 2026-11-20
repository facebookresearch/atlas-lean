/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingLatticeGreen










open Filter Set Topology

namespace StatMech.FrontierA

open StatMech.Lattice



theorem isingLatticeGreen_eventually_small_outside_box
    {d : Nat} (hd : 2 < d) (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ R : Nat, ∀ x : Site d, x ∉ box d R ->
      |isingLatticeGreen d x| < epsilon := by
  obtain ⟨R, hR⟩ := isingDyadicTorusGreen_eventually_small_outside_box
    hd (epsilon / 2) (half_pos hepsilon)
  refine ⟨R, ?_⟩
  intro x hx
  have hlim := (isingDyadicTorusGreen_tendsto_latticeGreen hd x).abs
  have hle : |isingLatticeGreen d x| ≤ epsilon / 2 := by
    apply le_of_tendsto hlim
    filter_upwards [hR x hx] with k hk
    exact hk.le
  exact hle.trans_lt (half_lt_self hepsilon)

end StatMech.FrontierA
